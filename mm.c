/*
 * mm.c
 *
 * Name: Benjamin Yu
 *
 * I defined some constant terms so that they will be easier to use and was shown in the textbook.
 * Then I made helper functinos to assist the implementation. This involed most of the macros in textbook to static functions
 * I used function protocals because my code got too messy with funcitons out of order
 * I referenced our textbook for help to implement this implicited free list simple allocator
 * I did an explicit free list, but with a LIFO implentatoin when inserting a block to the free list.
 * Then for removing a block, we check where the block is in the free list, and then remove it.
 * We then adjust the header and pointers in coalesce when we merge blocks together
 * This is all done with a doubly linked list, with one pointer pointing to the next block and one pointer point
 * to the previous block. THis is stored in the "payload" of the block.
 * I just implemented footer optimization to reduce fragmentation for explicit free list. I bit mask to see free or allocated for previous and
 * curr blocks
 * I just implemented seg free list. I did so by taking prof advice and creating a functino thta converts size to list index using powers of 2.
 * I hardcoded in the ranges. Then I went through and replaced every explicit free list pointer with a pointer to seg free list. I had to 
 * call to get index everytime and then use it to find the right range for the seg free list. Then I had to change my find fit because I had to
 * iterate through each seg free list until I found the right fit. I used the books find fit policy.
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"
/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16
#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<15)

//change chunk size to increase score, it still works because it is a multiple of 16

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int seg_index(size_t size);



static char *heap_pointer;
static char *seg_freelist_pointer[11]; //pointer pointing to explicit free list, change to seg list
//have 11 indexes, so we initialize it to 11


static size_t MAX(size_t a, size_t b)
{
    if (a>b)
    {
        return a;
    }
    else
        return b;
}

static size_t pack(size_t size, size_t alloc)
{
    return (size|alloc); //takes size and flag bit and OR them toget
}

static size_t get(void *p)
{
    return *((size_t *)p);  //reads word at adress from memory address
} //pointer type cast we saw in class concurrecny debugging powerpoint

static void put(void *p, size_t val)
{
    *((size_t *)p) = val; //writes word at adress from memory address
}  //pointer type cast we saw in class concurrecny debugging powerpoint

static size_t GET_SIZE(void *p)
{
    return get(p) & ~0x7; //bitmasking after gettomg the size of pointer
}

static size_t GET_ALLOC(void *p)
{
    return get(p) & 0x1; //bit masking like we did in class. gets size of pointer and mask until flag bit
}

static void *HDRP(void *bp)
{
    return ((char *)bp) - WSIZE; //from textbook
}

static void *FTRP(void *bp)
{
    return ((char *)bp) + GET_SIZE(HDRP(bp)) - DSIZE; //from texbook 
                                                      
}

static void *NEXT_BLKP(void *bp)
{
    return (char *)bp + GET_SIZE(((char *)bp) - WSIZE); //given a block pointer, we are copmuting address of the next block
}

static void *PREV_BLKP(void *bp)
{
    return (char *)bp - GET_SIZE(((char *)bp - DSIZE)); //given a block pointer, we are copmuting address of the prev block
}

// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}
//make implicit free list first, header, footer splitting the blocks, coalescing the blocks for Checkpoint 1. Build the helper functions

//epilogoue and prolouge
//each block begins wiht a header and ends with a footer, header and footer give the total size and status of the block.

//the size of any block includes the size of the blocks heaxer and footer, as well as size of block data



//my code was messy and I had all my fucntinos in random places, here I put them in order and added function protocols
//helped me identify issues


//need structure to add pointer to free list
//need structure to remove pointer from free list

//maybe change to inline?

static void* GET_PRED(void *bp) //pointer to get to prev pointer in free list where pred is in free block
{
    return (*(char **)(bp)); //char pointer to a pointer
}

static void* GET_SUCC(void *bp) //pointer to get to nextr pointer in free list
{
    return (*(char **)(bp + WSIZE)); //change to WSIZE. also char pointer to a pointer 
}

// function for footer optimization

static size_t HDRP_ALLOC(void *bp)
{
    return get(bp) & 0x2; //bit masking like GET_ALLOC, but for HDRP, so then we can see if the prev or next is allocated
}

static inline void removeFreeList(void *bp) //remove block from free list
{
    //from textbook, it says to use pred and succ pointers
    
    int i = seg_index(GET_SIZE(HDRP(bp)));

            
    if(GET_PRED(bp)==NULL && GET_SUCC(bp)==NULL) //only one block
    {
        seg_freelist_pointer[i] = NULL;
    }

    else if(GET_PRED(bp) != NULL && GET_SUCC(bp) == NULL) //it is the end block and rmeove it because nothing after
    {
        (*(char **)(GET_PRED(bp) + WSIZE)) = NULL; 
    }

    else if(GET_PRED(bp) == NULL && GET_SUCC(bp) != NULL)//removing fron beginign bc after is not null
    {
        seg_freelist_pointer[i] = GET_SUCC(bp);
        (*(char **)(seg_freelist_pointer[i])) = NULL; 
    }

    else //when both are not null it is in middle
    {
        (*(char **)(GET_SUCC(bp))) = (char *)GET_PRED(bp);
        (*(char **)(GET_PRED(bp) + WSIZE)) = (char *)GET_SUCC(bp); 
    }

}

static inline void addFreeList(void *bp)//add size so that we can scan through seg list 
{ //adding block to free list. Using LIFO becauase inserting at front when not empty. textbook 
    
    int i = seg_index(GET_SIZE(HDRP(bp)));
    
    if (seg_freelist_pointer[i] != NULL) //if free pointer is not empty, we insert at front
    {
        (*(char **)(bp)) = NULL; //using last in first out policy
        (*(char **)(bp + WSIZE)) = (char*)seg_freelist_pointer[i];
        (*(char **)(seg_freelist_pointer[i])) = (char *)bp;
        seg_freelist_pointer[i] = bp;
    }

    
    else //if free list pointer is empty, we insert 
    { 
        (*(char **)(bp + WSIZE)) = NULL; //using last in first out
        (*(char **)(bp)) = NULL;
        seg_freelist_pointer[i] = bp;

    }

    seg_freelist_pointer[i] = bp;
}

bool mm_init(void)
{ //textbook
    
    if ((heap_pointer = mm_sbrk(4*WSIZE)) == (void *)-1)
    {
        return false;
    }

    put(heap_pointer, 0); //for padding
    put(heap_pointer + (WSIZE), pack(DSIZE, 1)); //prolouge header
    put(heap_pointer + (2*WSIZE), pack(DSIZE, 1)); //prolouge footer
    put(heap_pointer + (3*WSIZE), pack(0, 3)); //epilouge header changed from 1 to 3, which means that previous and curr block allocated
    //3 is 11 in binary, left and right block is allcoated
    heap_pointer = heap_pointer+2*WSIZE; //16 is the double word size

    //freelist_pointer = NULL; //initializing the heap pointer
    //need seg list now

    int i = 0;
    //11 is the number of list i have
    while(i<11)
    {
        seg_freelist_pointer[i] = NULL;
        i++;
    } //initialzing the seg lists, prof said to use loop in init
        
    
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) //extend the empty heap with free block of chumsize bytes
    {
        mm_checkheap(__LINE__); //professor said in email to put it at end, and he specify before all returns
        return false;
    }

    mm_checkheap(__LINE__);

    return true;
}

void *malloc(size_t size) //frees a block and uses coalescing to merge it w any adjacent free blocks
{   //textbook
    // IMPLEMENT THIS

    mm_checkheap(__LINE__);
    size_t asize; //adjusteed block size
    size_t extendsize; // the amount to extend the heap if full

    char *bp;

    if (size == 0)
    {
        mm_checkheap(__LINE__);
        return NULL;
    }

    if (size <= (DSIZE))
    {
        asize = (2*DSIZE);
    }
    else
    {
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE); //DSIZEE

    }

    if ((bp = find_fit(asize)) != NULL) //finding the next fit and then placing it 
    {
        place(bp, asize);

        mm_checkheap(__LINE__);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE); //extend the size by the bigger value

    if((bp=extend_heap(extendsize/WSIZE)) == NULL)
    {
        mm_checkheap(__LINE__);
        return NULL;
    }
    place(bp, asize);


    mm_checkheap(__LINE__); //before the function returns

    return bp;
}


void free(void *ptr)
{ //textbook
    // IMPLEMENT THIS

    mm_checkheap(__LINE__);
    
    size_t size = GET_SIZE(HDRP(ptr));


    //need to change free for footer optimization
    
    put(HDRP(ptr), pack(size, HDRP_ALLOC(HDRP(ptr)))); //gets the alloc bits with bit masking
    put(FTRP(ptr), pack(size, 0));
    coalesce(ptr);

    mm_checkheap(__LINE__);
}

void *realloc(void *oldptr, size_t size)
{
    
    // IMPLEMENT THIS
    //OH Professor gave me clues about realloc

    mm_checkheap(__LINE__);
    void *newptr; //call malloc to get

    newptr = malloc(size);

    if ((int)size < 0)
    {
        mm_checkheap(__LINE__);
        return NULL;
    }
    
    if(oldptr  == NULL)
    {
        mm_checkheap(__LINE__);
        return malloc(size); //from hadnout
    }

    if(size == 0)
    {
        free(oldptr);

        mm_checkheap(__LINE__);
        return NULL; //from handout
    }
 
    
    memcpy(newptr, oldptr, size);
    free(oldptr); //changes the size of the memory pointed to by ptr to new new ptr. also from the mallco handout
    mm_checkheap(__LINE__);
    return (newptr);

}                

static void *extend_heap(size_t words) // textbook
{
    char *bp;

    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    //allocating even number of words to maintain alignment
    if ((long)(bp = mm_sbrk(size)) == -1)
    {
        return NULL;
    }

    //need to change heap so that we improve utilization
    
    put(HDRP(bp), pack(size, HDRP_ALLOC(HDRP(bp)))); //freeing block header
    put(FTRP(bp), pack(size, 0)); //free block footer
    put(HDRP(NEXT_BLKP(bp)), pack(0,1)); //settijng the new epilouge header because we want to extend


    return coalesce(bp);
}

static void *coalesce(void *block_pointer)
{//textbook
    
    size_t prev_alloc = HDRP_ALLOC(HDRP(block_pointer)); //gets the allocation bits
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(block_pointer)));
    size_t size = GET_SIZE(HDRP(block_pointer));

  
    
    if (prev_alloc && next_alloc) //case 1
    {
        //addFreeList(block_pointer); free block so we add to free list
        //put(HDRP(block_pointer), pack(size, 2));
        //        put(FTRP(block_pointer), pack(size, 0));
        // dont need to update the header/footer
        
        size_t* next_hdrp = HDRP(NEXT_BLKP(block_pointer)); //freeing next HDRP
        *next_hdrp = *next_hdrp & ~0x2; //everything expect gets bit mask, this way we free up the next hdrp block

    }
    
    else if (prev_alloc && !next_alloc)  //case 2
    { 
        
        size += GET_SIZE(HDRP(NEXT_BLKP(block_pointer)));

        removeFreeList((NEXT_BLKP(block_pointer))); //delete next free block
        
        put(HDRP(block_pointer), pack(size, 2)); //changed from 0 to 2
        put(FTRP(block_pointer), pack(size,0));

    }
    else if (!prev_alloc && next_alloc) //case 3
    {
       
        size += GET_SIZE(HDRP(PREV_BLKP(block_pointer)));
        
        removeFreeList(PREV_BLKP(block_pointer)); //delete prev free block from list
         
        put(FTRP(block_pointer), pack(size,0)); //update size of footer
        put(HDRP(PREV_BLKP(block_pointer)), pack(size,2)); //update size of header with the prev block allocated

        size_t* next_hdrp = HDRP(NEXT_BLKP(block_pointer)); //freeing next HDRP
        *next_hdrp = *next_hdrp & ~0x2; //everything expect gets bit mask, this way we free up the next hdrp block

        block_pointer = PREV_BLKP(block_pointer);
    }
    else
    {
                
        size += GET_SIZE(HDRP(PREV_BLKP(block_pointer)))+GET_SIZE(FTRP(NEXT_BLKP(block_pointer)));

        removeFreeList((PREV_BLKP(block_pointer))); //bothj free blocks are deleted
        removeFreeList((NEXT_BLKP(block_pointer)));
        
        put(HDRP(PREV_BLKP(block_pointer)), pack(size,2)); //update size of header
        put(FTRP(NEXT_BLKP(block_pointer)), pack(size,0)); //update size of footer

        block_pointer = PREV_BLKP(block_pointer);
    }
    
    addFreeList(block_pointer); //add coalesced block to free list
    //added the size so we can scan
    return block_pointer;
}


static void *find_fit(size_t new_size)
{//textbook
    void *bp;
    //need to find block that fits with the newsize bytes requested
    //finds free block in free list
    // i altered the books find fit and so it works with segragated

    int i = seg_index(new_size); //gets the index for that new size
    
    while (i<11) //searches throuhg the seg free list
    {
        bp = seg_freelist_pointer[i];

        while (bp) 
        {

            if(new_size > GET_SIZE(HDRP(bp))) //if the new size is bigger than the pointer size, we got to next poniter
            {
                bp = GET_SUCC(bp);

            }

            else
            {
                return bp; //if new size is smaller, we just return pointer

            }
        }
        
        i++;
    }
    return NULL; //No fit
}

static void place(void *bp, size_t asize)
{//textbook
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (DSIZE*2)) {
        //when block sized if bigger than asize, we do splicing
        removeFreeList(bp);
        put(HDRP(bp), pack(asize, 3)); //is 11 in binary, means prev and curr are allocated
     
        //removeFreeList(bp); //free block deleted
        
        bp = NEXT_BLKP(bp);
        put(HDRP(bp), pack(csize-asize, 2)); //is 10 in binary, means prev is allcoateed, and curr us free
        put(FTRP(bp), pack(csize-asize, 0));

        coalesce(bp);        
    }
    else { //getting the entire block otherwise

        put(HDRP(bp), pack(csize, 3));

        //gets the header of the next block so then we can bit mask to alloc the header of next block

        size_t* next_hdrp = HDRP(NEXT_BLKP(bp));//allocing next hdrp
        *next_hdrp = (*next_hdrp | 0x2); //is 10 in binary, which means that the previous block is allocated and curr bllock is free
        //left block is allocated
        
        removeFreeList(bp); //free block deleted
    }
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}
//use for seg list, realized i needed explicit list before seg list, so ill jusst comment it out

static int seg_index(size_t size) //power of 2's like professor zhu mentioned in class
{
    int x = 0;
    if(size <= 32)
    {
        x = 0;
    }
    else if(size <= 64)
    {
        x = 1;
    }
    else if(size <= 128)
    {
        x = 2;
    }
    else if(size <= 256)
    {
        x = 3;
    }
    else if(size <= 512)
    {
        x = 4;
    }
    else if(size <= 1024)
    {
        x = 5;
    }
    else if(size <= 2048)
    {
        x = 6;
    }
    else if(size <= 4096)
    {
        x = 7;
    }
    else if(size <= 8192)
    {
        x = 8;
    }
    else if(size <= 16384)
    {
        x = 9;
    }
    else
    {
        x = 10;
    }
    return x;
}


static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

 


bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    // Write code to check heap invariants here
    // IMPLEMENT THIS
    int i = 0;
    int count_heap = 0;
    int count_list = 0;

    char *temp_heap = heap_pointer;


    temp_heap = NEXT_BLKP(temp_heap); //passes the dummy block
    //temp_seg = seg_freelist_pointer[i];

    while (GET_ALLOC(HDRP(temp_heap)) == 1 && GET_SIZE(HDRP(temp_heap)) != 0) //that means that there are free blocks because size is
        //a value and alloc is 1, so that means it is allocated
        {
            if(GET_ALLOC(HDRP(temp_heap)) != 0)
                {
                    count_heap++; //keep count so we can comapre later
                }
            temp_heap = NEXT_BLKP(temp_heap); //moves to the next block in heap
        }

    char *temp_seg = seg_freelist_pointer[i];
    while(i<11 &&temp_seg != NULL)
    {
        
        if(!in_heap(temp_seg)) //fucntion given to us to check whether a poitner is in heap
        {
           printf("this pointer is not in heap");
           assert(false); //to exit the loop
        }

        if(GET_ALLOC(HDRP(temp_seg)) == 1) //if it is 0, that means it is not allcoated
        {
            printf("this is a free block");
            assert(false); // to exit the loop
        }

        count_list++; //keep count so we can compare later
        temp_seg = GET_SUCC(temp_seg); //moves to next block in the free list
    }
    
    if (count_heap != count_list) //compares free block in heap with seg free list
    {
        printf("heap and free list is off with free blocks");
        assert(false);
    }
           
#endif // DEBUG
    return true;
}

