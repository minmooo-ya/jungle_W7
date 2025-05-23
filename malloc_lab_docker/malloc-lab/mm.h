#include <stdio.h>
#include <math.h>


extern int mm_init (void);
extern void *mm_malloc (size_t size);
extern void mm_free (void *ptr);
extern void *mm_realloc(void *ptr, size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);          /* 인접 가용 블록 병합 */
static void *find_fit(size_t asize);      /* 가용 블록 탐색 */
static void place(void *bp, size_t asize);
static void remove_node(void *bp);
static void insert_node(void *bp);
static int find_size_class(size_t size);
/* 
 * Students work in teams of one or two.  Teams enter their team name, 
 * personal names and login IDs in a struct of this
 * type in their bits.c file.
 */
typedef struct {
    char *teamname; /* ID1+ID2 or ID1 */
    char *name1;    /* full name of first member */
    char *id1;      /* login ID of first member */
    char *name2;    /* full name of second member (if any) */
    char *id2;      /* login ID of second member */
} team_t;

extern team_t team;

