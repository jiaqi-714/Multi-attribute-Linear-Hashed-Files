// query.c ... query scan functions
// part of Multi-attribute Linear-hashed Files
// Manage creating and using Query objects
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "query.h"
#include "reln.h"
#include "tuple.h"
#include "hash.h"

// A suggestion ... you can change however you like

struct QueryRep {
	Reln    rel;       			// need to remember Relation info
	Bits    known;     			// the hash value from MAH
	Bits    unknown;  			// the unknown bits from MAH
	PageID  curpageID;   		// current page in scan
	PageID 	curovPageID;		// current overflow page in scan
	int     is_ovflow; 			// are we in the overflow pages?
	Offset  curtup;    			// offset of current tuple within page (in bytes)
	Offset  curtupReaded;    	// offset of current tuple within page (in tuple)
	char 	**vals;	   			// what actual in query like ("1234,?,abc,?")
	Tuple   result;				// the tuple we want
	//TODO
};

// take a query string (e.g. "1234,?,abc,?")
// set up a QueryRep object for the scan

Query startQuery(Reln r, char *q)
{
	Query new = malloc(sizeof(struct QueryRep));
	assert(new != NULL);
	// char buf[MAXBITS+1];
	// TODO
	// Partial algorithm:
	// form known bits from known attributes
	// form unknown bits from '?' attributes
	// compute PageID of first page
	//   using known bits and first "unknown" value
	// set all values in QueryRep object

	new->rel = r;
	ChVecItem *cv = chvec(r);
	// malloc field for attribute vals and extract attributes from q
	Count nvals = nattrs(r);
	char **vals = malloc(nvals*sizeof(char *));
	assert(vals != NULL);
	tupleVals(q, vals);
	new->vals = vals;

	// example (if attribute like '101,?,?,23,d', unknownAttMap will be 0 1 1 0 0)
	int *unknownAttMap = malloc(nvals*sizeof(int));

	for (int i = 0; i < nvals; i++) {  
		if (vals[i][0] == '?' && vals[i][1] == '\0') unknownAttMap[i] = 1;
	}

	Bits    known = 0;
	Bits    unknown = 0;
	// hash attributes and set hash's bit base on choice vector
	for (int i = 0; i < MAXCHVEC; i++) {
		if (unknownAttMap[cv[i].att]) unknown = setBit(unknown, i);
		else {
			Bits attHash = hash_any((unsigned char *)vals[cv[i].att],strlen(vals[cv[i].att]));
			if (bitIsSet(attHash, cv[i].bit)){
				known = setBit(known, i);
			}
		}
	}
	
	new->known = known;
	new->unknown = unknown;
	new->curpageID = 0;
	new->curovPageID = 0;
	new->is_ovflow = FALSE;
	new->curtup = 0;
	new->curtupReaded = 0;
	new->result = NULL;
	
	// for (int i = 0; i < nvals; i++) {  debug
	// 	printf("%d ", unknownAttMap[i]);
	// }
	// bitsString(known,buf);
	// printf("known hash bits = %s\n", buf);
	// bitsString(unknown,buf);
	// printf("unknown bits = %s\n", buf);

	return new;
}

// convert data(2,floodlight,fork,drill,sunglasses\03,bridge,torch,yellow,festival\0) 
// to list of tuple like (2,floodlight,fork,drill,sunglasses\0, 3,bridge,torch,yellow,festival\0), 
// send list to "dest"
int dataTotupleList(char *t, Offset dataLength, char **dest)
{
	char *c = t;
	char *curTuple = t;
	int counter = 0;
	for (int i = 0; i < dataLength; i++) {
		if (*c == '\0') {
			// end of tuple; add last field to vals
			dest[counter] = copyString(curTuple);
			counter++;
			curTuple = c + 1;
		}
		c++;
	}
	return counter;
}

// find tuple in current page, return true if found and false else
Bool getTupleInPage(Query q, Page curPage) {
	// store data to tuple list
	char *curCh = pageData(curPage);
	// go to the start of the memory we want to check (dismiss the memory we already check)
	curCh = curCh + q->curtup;
	Count hdr_size = 2*sizeof(Offset) + sizeof(Count);
	Offset dataEnd = PAGESIZE - pageFreeSpace(curPage) - hdr_size;
	char **tupleList = malloc(dataEnd*sizeof(char *));
	dataTotupleList(curCh, dataEnd, tupleList);
	
	// loop remaining tuple list
	int remainTuple = pageNTuples(curPage) - q->curtupReaded;
	for (int i = 0; i < remainTuple; i++) { 

		// calculate byte readed and tuple readed
		for (char *k = tupleList[i]; *k != '\0'; k++) q->curtup++;
		q->curtup++;
		q->curtupReaded++;
		// printf("page %d curtup %d\n", q->curpageID, q->curtup);

		// convert tuple to attribute and compare with query
		Count nvals = nattrs(q->rel);
		char **vals = malloc(nvals*sizeof(char *)); // need to be free!
		tupleVals(tupleList[i], vals);
		Bool findTuple = TRUE;
		// if (!q->is_ovflow) printf("check for %s in page %d\n", tupleList[i], q->curpageID);
		// else printf("check for %s in overflow page %d\n", tupleList[i], q->curovPageID);
		for (int j = 0; j < nvals; j++) {
			if (strcmp(q->vals[j], "?") != 0) {
				if (strcmp(vals[j], q->vals[j]) != 0) {
					findTuple = FALSE; 
					// printf(" unmatch!\n");
					break;
				}
			}
		}
		if (findTuple) {
			q->result = copyString(tupleList[i]); // q->result need to be free in select.c!
			freeVals(tupleList, remainTuple); // free whole page data
			return TRUE;
		} 
	}
	freeVals(tupleList, nattrs(q->rel));
	return FALSE;
}

// get next tuple during a scan

Tuple getNextTuple(Query q)
{
	// TODO
	// Partial algorithm:
	// if (more tuples in current page)
	//    get next matching tuple from current page
	// else if (current page has overflow)
	//    move to overflow page
	//    grab first matching tuple from page
	// else
	//    move to "next" bucket
	//    grab first matching tuple from data page
	// endif
	// if (current page has no matching tuples)
	//    go to next page (try again)
	// endif

	// printf("run select!!\n");
	Bits unknown = getLower(q->unknown, depth(q->rel));
	Bits known = getLower(q->known, depth(q->rel));
	FILE *df = dataFile(q->rel);
	FILE *ovf = ovflowFile(q->rel);
	Page curovPage;
	Page curPage;
	// loop every page, and find suitable page to check
	while (q->curpageID < (1 << depth(q->rel)) + splitp(q->rel)) {

		// check current page is suitable or not
		Bool pageSuitable = TRUE;
		for (int i = 0; i < depth(q->rel); i++) {
			if (!bitIsSet(unknown, i)) {
				if (bitIsSet(known, i) != bitIsSet(q->curpageID, i)) pageSuitable = FALSE;
				break;
			}
		}

		// pass this page if hash value is not same 
		if (!pageSuitable){
			q->curtup = 0;
			q->curtupReaded = 0;
			q->curpageID++;
			continue;
		}

		// printf("check page %d\n", q->curpageID);
		if (q->is_ovflow == 0){
			curPage = getPage(df, q->curpageID);
			Bool found = getTupleInPage(q, curPage);
			if (found) return q->result;
		}

		//if just goes from data page
		if (q->is_ovflow == 0) {
			q->curovPageID = pageOvflow(curPage); // get current overflow page id
			if (q->curovPageID != NO_PAGE) q->is_ovflow = 1; // set overflow flag
			q->curtup = 0;
			q->curtupReaded = 0;
		}

		// loop every overflow page as we can
		while (q->curovPageID != NO_PAGE) {
			curovPage = getPage(ovf, q->curovPageID);
			Bool found = getTupleInPage(q, curovPage);
			if (found) return q->result;

			// if get here, that means one overflow page is over, 
			// reset the counter and set page to new overflow page if any
			q->curtup = 0;
			q->curtupReaded = 0;
			q->curovPageID = pageOvflow(curovPage);
		}

		// if get here, that means one normal page is over, 
		// reset the counter and set page to new page
		q->is_ovflow = 0;
		q->curtup = 0;
		q->curtupReaded = 0;
		q->curpageID++;
	}

	// if get here, that means we pass all normal page and their overflow page, 
	// return null to end loop
	return NULL;

	// debug
	// for (int i = 0; i < pageNTuples(curPage); i++) { 
	// 	printf("%s\n", tupleList[i]);
	// }
	// for (int i = 0; i < dataEnd; i++) {
	// 	printf("%c",*curCh);
	// 	curCh++;
	// }
	// Count nvals = nattrs(q->rel);
	// for (int i = 0; i < nvals; i++) {
	// 	printf("%s ", q->vals[i]);
	// }
}

// clean up a QueryRep object and associated data

void closeQuery(Query q)
{
	// TODO
	freeVals(q->vals, nattrs(q->rel));
	free(q->result);
	free(q);
}
