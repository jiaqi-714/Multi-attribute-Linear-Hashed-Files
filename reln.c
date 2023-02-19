// reln.c ... functions on Relations
// part of Multi-attribute Linear-hashed Files
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "reln.h"
#include "page.h"
#include "tuple.h"
#include "chvec.h"
#include "bits.h"
#include "hash.h"

#define HEADERSIZE (3*sizeof(Count)+sizeof(Offset))

struct RelnRep {
	Count  nattrs; // number of attributes
	Count  depth;  // depth of main data file
	Offset sp;     // split pointer
    Count  npages; // number of main data pages
    Count  ntups;  // total number of tuples
	ChVec  cv;     // choice vector
	char   mode;   // open for read/write
	FILE  *info;   // handle on info file
	FILE  *data;   // handle on data file
	FILE  *ovflow; // handle on ovflow file
};

int dataTotupleList(char *start, Offset dataLength, char **dest);
int powOfTwo(int power) {
	if (power == 0) return 1;
	int result = 2;
	for (int i = 0; i < power - 1;i++) {
		result = result * 2;
	}
	return result;
}

// create a new relation (three files)
Status newRelation(char *name, Count nattrs, Count npages, Count d, char *cv)
{
    char fname[MAXFILENAME];
	Reln r = malloc(sizeof(struct RelnRep));
	r->nattrs = nattrs; r->depth = d; r->sp = 0;
	r->npages = npages; r->ntups = 0; r->mode = 'w';
	assert(r != NULL);
	if (parseChVec(r, cv, r->cv) != OK) return ~OK;
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,"w");
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,"w");
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,"w");
	assert(r->ovflow != NULL);
	int i;
	for (i = 0; i < npages; i++) addPage(r->data);
	closeRelation(r);
	return 0;
}

// check whether a relation already exists

Bool existsRelation(char *name)
{
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	FILE *f = fopen(fname,"r");
	if (f == NULL)
		return FALSE;
	else {
		fclose(f);
		return TRUE;
	}
}

// set up a relation descriptor from relation name
// open files, reads information from rel.info

Reln openRelation(char *name, char *mode)
{
	Reln r;
	r = malloc(sizeof(struct RelnRep));
	assert(r != NULL);
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,mode);
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,mode);
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,mode);
	assert(r->ovflow != NULL);
	// Naughty: assumes Count and Offset are the same size
	int n = fread(r, sizeof(Count), 5, r->info);
	assert(n == 5);
	n = fread(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
	assert(n == MAXCHVEC);
	r->mode = (mode[0] == 'w' || mode[1] =='+') ? 'w' : 'r';
	return r;
}

// release files and descriptor for an open relation
// copy latest information to .info file

void closeRelation(Reln r)
{
	// make sure updated global data is put in info
	// Naughty: assumes Count and Offset are the same size
	if (r->mode == 'w') {
		fseek(r->info, 0, SEEK_SET);
		// write out core relation info (#attr,#pages,d,sp)
		int n = fwrite(r, sizeof(Count), 5, r->info);
		assert(n == 5);
		// write out choice vector
		n = fwrite(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
		assert(n == MAXCHVEC);
	}
	fclose(r->info);
	fclose(r->data);
	fclose(r->ovflow);
	free(r);
}

// insert a new tuple into a relation
// returns index of bucket where inserted
// - index always refers to a primary data page
// - the actual insertion page may be either a data page or an overflow page
// returns NO_PAGE if insert fails completely

PageID addTupleToRelation(Reln r, Tuple t)
{
	Bits h, p;
	// char buf[MAXBITS+1];
	h = tupleHash(r,t);
	if (r->depth == 0)
		p = 0;
	else {
		p = getLower(h, r->depth);
		if (p < r->sp) p = getLower(h, r->depth+1);
	}
	// bitsString(h,buf); printf("hash = %s\n",buf);
	// bitsString(p,buf); printf("page = %s\n",buf);
	Page pg = getPage(r->data,p);
	if (addToPage(pg,t) == OK) {
		putPage(r->data,p,pg);
		r->ntups++;
		return p;
	}
	// primary data page full
	if (pageOvflow(pg) == NO_PAGE) {
		// add first overflow page in chain
		PageID newp = addPage(r->ovflow);
		pageSetOvflow(pg,newp);
		putPage(r->data,p,pg);
		Page newpg = getPage(r->ovflow,newp);
		// can't add to a new page; we have a problem
		if (addToPage(newpg,t) != OK) return NO_PAGE;
		putPage(r->ovflow,newp,newpg);
		r->ntups++;
		return p;
	}
	else {
		// scan overflow chain until we find space
		// worst case: add new ovflow page at end of chain
		Page ovpg, prevpg = NULL;
		PageID ovp, prevp = NO_PAGE;
		ovp = pageOvflow(pg);
		while (ovp != NO_PAGE) {
			ovpg = getPage(r->ovflow, ovp);
			if (addToPage(ovpg,t) != OK) {
				prevp = ovp; prevpg = ovpg;
				ovp = pageOvflow(ovpg);
			}
			else {
				if (prevpg != NULL) free(prevpg);
				putPage(r->ovflow,ovp,ovpg);
				r->ntups++;
				return p;
			}
		}
		// all overflow pages are full; add another to chain
		// at this point, there *must* be a prevpg
		assert(prevpg != NULL);
		// make new ovflow page
		PageID newp = addPage(r->ovflow);
		// insert tuple into new page
		Page newpg = getPage(r->ovflow,newp);
        if (addToPage(newpg,t) != OK) return NO_PAGE;
        putPage(r->ovflow,newp,newpg);
		// link to existing overflow chain
		pageSetOvflow(prevpg,newp);
		putPage(r->ovflow,prevp,prevpg);
        r->ntups++;
		return p;
	}
	return NO_PAGE;
}

// ----------------------------------------------------------
int pageSplit(Reln r) {
	FILE *df = dataFile(r);
	FILE *ovf = ovflowFile(r);
	Offset oldPageID = splitp(r);
	addPage(r->data);
	r->npages++;
	Page curPage = getPage(df, oldPageID);
	Page curOvfPage;

	Count totalTuple = 0;
	totalTuple = totalTuple + pageNTuples(curPage);
	Offset ovfPageID = pageOvflow(curPage);
	while (ovfPageID != NO_PAGE) {
      	// get overflow page
		curOvfPage = getPage(ovf, ovfPageID);
      	// add number of tuple in this page
		totalTuple += pageNTuples(curOvfPage);
      	// move to next overflow page
		ovfPageID = pageOvflow(curOvfPage);
	}
	
	// store all tuples in memory, clear up page after data transfer
	Tuple *finalTuples = malloc(totalTuple * sizeof(Tuple));

	char *curCh = pageData(curPage);
	Count hdr_size = 2*sizeof(Offset) + sizeof(Count);
	Offset dataEnd = PAGESIZE - pageFreeSpace(curPage) - hdr_size;
	char **tupleList = malloc(dataEnd*sizeof(char *));
	dataTotupleList(curCh, dataEnd, tupleList);

	// loop every tuple in current page
	Count curTuplePos = 0;

	for (int i = 0; i < pageNTuples(curPage); i++) {
		// printf("check for %s in page %d\n", tupleList[i], oldPageID);
		finalTuples[curTuplePos] = tupleList[i];
		curTuplePos++;
	}

	// clear normal page memory
	Page newpg = newPage();
	pageSetOvflow(newpg, ovfPageID);
	putPage(r->data, r->sp, newpg);

	// reset ovfPageID to store all tuple in overflow page
	ovfPageID = pageOvflow(curPage);
	PageID oldOvfPageID;
	// loop every tuple in overflow page
	while (ovfPageID != NO_PAGE) {
		curPage = getPage(ovf, ovfPageID);
		
		char *curCh = pageData(curPage);
		Count hdr_size = 2*sizeof(Offset) + sizeof(Count);
		Offset dataEnd = PAGESIZE - pageFreeSpace(curPage) - hdr_size;
		char **tupleList = malloc(dataEnd*sizeof(char *));
		dataTotupleList(curCh, dataEnd, tupleList);

		for (int i = 0; i < pageNTuples(curPage); i++) {
			// printf("check for %s in overflow page %d\n", tupleList[i], ovfPageID);
			finalTuples[curTuplePos] = tupleList[i];
			curTuplePos++;
		}

		// connect to next overflow page(if any) and clear current overflow page
		oldOvfPageID = ovfPageID;
		ovfPageID = pageOvflow(curPage);
		newpg = newPage();
		pageSetOvflow(newpg, ovfPageID);
		putPage(r->ovflow, oldOvfPageID, newpg);
	}

	// reset tuple number 
	r->ntups = r->ntups - totalTuple;
	// update split pointer
	r->sp++;
	if (r->sp == (1 << (r->depth))) {
		//update depth
		r->depth++;
		r->sp = 0;
	}

	// re insert
	PageID result = 0;
	for (int i = 0; i < totalTuple; i++) {
		result = addTupleToRelation(r, finalTuples[i]);
		assert(result != NO_PAGE);
		free(finalTuples[i]);
	}
	free(finalTuples);

	// debug use
	// for (int i = 0; i < curTuplePos; i++) {
	// 	printf("%s\n", finalTuples[i]);
	// }
	// printf("%d\n", curTuplePos);
	return OK;
}

// insert a new tuple into a relation
// returns index of bucket where inserted
// - index always refers to a primary data page
// - the actual insertion page may be either a data page or an overflow page
// returns NO_PAGE if insert fails completely
// TODO: include splitting and file expansion
PageID addToRelation(Reln r, Tuple t)
{
	Count n = nattrs(r); 
	int timeToSplit = 1024/(10*n);
	if (((r->ntups) != 0) && (((r->ntups) % timeToSplit) == 0)) {
		int res = pageSplit(r);
		assert(res == OK);
	}
	PageID result = addTupleToRelation(r, t);
	return result;
}


// external interfaces for Reln data

FILE *dataFile(Reln r) { return r->data; }
FILE *ovflowFile(Reln r) { return r->ovflow; }
Count nattrs(Reln r) { return r->nattrs; }
Count npages(Reln r) { return r->npages; }
Count ntuples(Reln r) { return r->ntups; }
Count depth(Reln r)  { return r->depth; }
Count splitp(Reln r) { return r->sp; }
ChVecItem *chvec(Reln r)  { return r->cv; }


// displays info about open Reln

void relationStats(Reln r)
{
	printf("Global Info:\n");
	printf("#attrs:%d  #pages:%d  #tuples:%d  d:%d  sp:%d\n",
	       r->nattrs, r->npages, r->ntups, r->depth, r->sp);
	printf("Choice vector\n");
	printChVec(r->cv);
	printf("Bucket Info:\n");
	printf("%-4s %s\n","#","Info on pages in bucket");
	printf("%-4s %s\n","","(pageID,#tuples,freebytes,ovflow)");
	for (Offset pid = 0; pid < r->npages; pid++) {
		printf("[%2d]  ",pid);
		Page p = getPage(r->data, pid);
		Count ntups = pageNTuples(p);
		Count space = pageFreeSpace(p);
		Offset ovid = pageOvflow(p);
		printf("(d%d,%d,%d,%d)",pid,ntups,space,ovid);
		free(p);
		while (ovid != NO_PAGE) {
			Offset curid = ovid;
			p = getPage(r->ovflow, ovid);
			ntups = pageNTuples(p);
			space = pageFreeSpace(p);
			ovid = pageOvflow(p);
			printf(" -> (ov%d,%d,%d,%d)",curid,ntups,space,ovid);
			free(p);
		}
		putchar('\n');
	}
}
