//DONE BY --> SANCHIT AGARWAL , UID -> 105389151
/*
 My version of malloc is based on segregated free lists . My free list is organized in the first SEGLIST_LENGTH bytes of the heap . The seglist essentially acts like a Hash table and is ascending order to encourage best fit search to maximize . When a block is allocated if the padding is more than 2 * DSIZE then it is split and added to segregated free list . While mallocing , first the search is done through the segregated free list and then if nothing is found malloc is called . Blocks on heap are organized in the manner of simple allocator with header , footer and allocation bit .
*/
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>


#include "mm.h"
#include "memlib.h"

/*********************************************************
* NOTE TO STUDENTS: Before you do anything else, please
* provide your team information in the following struct.
********************************************************/

team_t team = {
  /* Team name */
  "N.A.",
  /* First member's full name */
  "Sanchit Agarwal",
  /*UID --> 105389151*/
  /* First member's email address */
  "sanchit1591@g.ucla.edu",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

//#########################################################################################//
//#########################################################################################//


///***********************************************/
///*/////////////////////////////////////////////*/
///*////////////////////MACROS///////////////////*/
///*/////////////////////////////////////////////*/
///***********************************************/


///////////////////////////////////////////////////
///////////////CONSTANT MACROS/////////////////////
///////////////////////////////////////////////////

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

#define WSIZE   4 /* Word and header footer size */
#define DSIZE   8 /* Double Word Size */
#define INITCHUNKSIZE   (1<<5) /* Extend the heap by this amount */
#define CHUNKSIZE (1<<12)

//This is the length of segregated list
#define SEGLIST_LENGTH 8

/////////////////////////////////////////////////////
///////////////FUNCTIONAL MACROS/////////////////////
/////////////////////////////////////////////////////

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//Routine max min functions
#define MAX(x,y) ((x) > (y)? (x) : (y))
#define MIN(x,y) ((x) > (y)? (y) : (x))

/* Pack a size and allocated bit into a word */
#define PACK(size,alloc) ((size) | (alloc))

/* Read and Write a word at address p */
//Any generic pointer
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
//block pointers
#define GET_SIZE(bp) (GET(HDRP(bp)) & ~0X7)
#define GET_ALLOC(bp) (GET(HDRP(bp)) & 0x1)

/* Check the allocation status of left and right blocks in the heap */
#define IS_LEFT_ALLOCATED(bp) (GET_ALLOC(PREV_BLK_PTR(bp)))
#define IS_RIGHT_ALLOCATED(bp) (GET_ALLOC(NEXT_BLK_PTR(bp)))

/* Free Block Accesors for the segregated free list*/
#define GET_PREV_PTR(bp) (*((char **)(bp)))
#define GET_NEXT_PTR(bp) (*((char **)((char *)(bp) + WSIZE)))

//gets the first element in the segregated fre list
#define GET_FIRST_PTR(list_ptr) (*((char **)(list_ptr)))

/* Free Block Mutators */
#define SET_PREV_PTR(bp , prev_p) *(unsigned int *)(bp) = (unsigned int) prev_p
#define SET_NEXT_PTR(bp , next_p) *(unsigned int *)((char *)(bp) + WSIZE) = (unsigned int) next_p

//sets the first element in the segregated free list
#define SET_FIRST_PTR(list_ptr , first_ptr) *(unsigned int *)(list_ptr) = (unsigned int) first_ptr

/* Allocated Block Accesors */
//Get block pointer from header
#define GET_BLOCK_PTR(hp) ((char *)(hp) + WSIZE)
#define HDRP(bp) ((char *)(bp) - WSIZE) //Getting header pointer from block pointer
#define FTRP(bp) ((char *)(bp) + GET_SIZE(bp) - DSIZE) //Getting footer from block pointer
#define NEXT_WORD(ptr) ((char *)(ptr) + WSIZE) //Next physical word in the heap

/* Get list pointer*/
#define GET_LIST_PTR(head_ptr , index) ((char *)(head_ptr) + index * WSIZE)


/* Given a block_ptr , compute the next and the previous PHYSICAL block_ptrs */
#define NEXT_BLK_PTR(bp) ((char *)(bp) + GET_SIZE(bp))
#define PREV_BLK_PTR(bp) ((char *)(bp) - (GET((char *)(bp) - DSIZE) & ~0X7))


//#########################################################################################//
//#########################################################################################//







//#########################################################################################//
//#########################################################################################//

///***********************************************/
///*/////////////////////////////////////////////*/
///*////////////////////GLOBAL///////////////////*/
///*/////////////////////////////////////////////*/
///***********************************************/


///////////////////////////////////////////////////
///////////////GLOBAL POINTERS/////////////////////
///////////////////////////////////////////////////

/* SEGLIST */
static void *seg_free_listp; //Points to the zero'th index of the seglist

//TODO:start --> JUST FOR mm_check ..... NOT NECESSARY AT ALL
static void *start;

///////////////////////////////////////////////////
///////////////HELPER FUNCTIONS////////////////////
///////////////////////////////////////////////////

/* Description of all the helper functions is given above the respective functions */
static void *extend_heap(size_t words);
static void insert_free_blk(void *free_blk_ptr,unsigned int seglist_index);
static void delete_free_blk(void *delete_blk_ptr);
static int seglist_index(size_t size_of_freeblk);
static void *coalesce(void *p);
static void *place(size_t size);
static int mm_check();

//#########################################################################################//
//#########################################################################################//








//#########################################################################################//
//#########################################################################################//

///***********************************************/
///*/////////////////////////////////////////////*/
///*//////HELPER FUNCTIONS IMPLEMENTATION////////*/
///*/////////////////////////////////////////////*/
///***********************************************/








///////////////////////////////////////////////////
///////////////EXTEND HEAP/////////////////////////
///////////////////////////////////////////////////

/* Extend the heap by a particular amount */
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;
  
  /* maintain alignment */
  size = ALIGN(words * WSIZE); //align according to 8 bytes
  
  /* demand for required space --> if not available return NULL */
  if((bp = mem_sbrk(size)) == (void *)-1)
      return NULL;
  
  /* Initialize free block header/footer and the new epilogue header */
  PUT(HDRP(bp), PACK(size, 0)); //Free Block Header
  PUT(FTRP(bp), PACK(size, 0)); //Free Block Footer
  PUT(HDRP(NEXT_BLK_PTR(bp)), PACK(0, 1)); //New Epilogue Header
  
  insert_free_blk(bp,seglist_index(size));
  //coalesce -> merge with nearby free blocks if present
  return coalesce(bp);
  
}









///////////////////////////////////////////////////
/////////////////INSERT FREE BLOCK/////////////////
///////////////////////////////////////////////////

/* Insert the free block in the segregated free list */
static void insert_free_blk(void *free_blk_ptr, unsigned int seglist_index)
{
    /* Get the respective seglist index*/
    void *first_block = GET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, seglist_index));

    //If that seglist index is NULL add the free block right there
    if(first_block == NULL)
    {
      SET_PREV_PTR(free_blk_ptr, NULL);
      SET_NEXT_PTR(free_blk_ptr, NULL);
      SET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, seglist_index) , free_blk_ptr);
      return;
    }

    else
    {
      void *current = first_block;
      void *pred  = first_block;
      //find appropriate place to insert the block in a particular size class (ascending order maintained)
      while(current != NULL && (GET_SIZE(current) < GET_SIZE(free_blk_ptr)))
      {
          pred = current;
          current = GET_NEXT_PTR(current);
      }
      
      //If apropriate place for the Block is the first position (EDGE CASE)
      if(current == first_block)
      {
          //printf("\n6\n");
          //set the free block first
          SET_PREV_PTR(free_blk_ptr, NULL);
          SET_NEXT_PTR(free_blk_ptr, current);
          //change connection afterwards
          SET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, seglist_index) , free_blk_ptr);
          SET_PREV_PTR(current, free_blk_ptr);
      }

      //General case --> If the block is either in the last or somewhere in between
      else
      {
          //set the free block first
          SET_PREV_PTR(free_blk_ptr, pred);
          SET_NEXT_PTR(free_blk_ptr, current);
          //change connections afterwards
          SET_NEXT_PTR(pred, free_blk_ptr);
          if(current != NULL)
          {
              SET_PREV_PTR(current, free_blk_ptr);
          }
      }
      return;
    }
}









///////////////////////////////////////////////////
/////////////////DELETE FREE BLOCK/////////////////
///////////////////////////////////////////////////


/* Delete a free block from the segregated free list*/
static void delete_free_blk(void *delete_blk_ptr)
{
    size_t size = GET_SIZE(delete_blk_ptr);
    int index = seglist_index(size);
    void *first_block = GET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, index));
    //save the previos and the next pointers of the target block to be deleted for easy access
    void *prev_ptr = GET_PREV_PTR(delete_blk_ptr);
    void *next_ptr = GET_NEXT_PTR(delete_blk_ptr);

    /* Case 1 --> If block lies in between (i.e it is surrounded by blocks on both sides */
    if(next_ptr != NULL && prev_ptr != NULL)
    {
      SET_NEXT_PTR(prev_ptr, next_ptr);
      SET_PREV_PTR(next_ptr, prev_ptr);
    }

    /* Case 2 --> If the block is the first block in that particular size class */
    else if(next_ptr != NULL && prev_ptr == NULL)
    {
      SET_PREV_PTR(next_ptr, NULL);
      SET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, index) , next_ptr);
    }
    
    /* Case 3 --> If the block is the last block in that particular size class */
    else if(next_ptr == NULL && prev_ptr != NULL)
    {
      SET_NEXT_PTR(prev_ptr, NULL);
    }
    
    /* Case 4 --> If the target block is the only block in that particular size class */
    else
    {
      SET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, index) , NULL);
    }

    return;
}







///////////////////////////////////////////////////
/////////////////SEGLIST INDEX/////////////////////
///////////////////////////////////////////////////

/* In my design --> instead of passing on sizes in each function --> I made a function that calulates the appropriate index for a particulart index thus determining which size class should it lie in */

static int seglist_index(size_t size_of_freeblk)
{
    int count = 0;

    while(size_of_freeblk > 1 && count < SEGLIST_LENGTH + 3)
    {
      size_of_freeblk >>= 1;
      count++;
    }
    return count - 4;
}








///////////////////////////////////////////////////
/////////////////////COALESCE//////////////////////
///////////////////////////////////////////////////

/* In order to avoid external fragmentation , adjacent blocks if free are merged to form a single large block */
static void *coalesce(void *p)
{
    size_t is_left_alloc = IS_LEFT_ALLOCATED(p);
    size_t is_right_alloc = IS_RIGHT_ALLOCATED(p);
    size_t size_of_p = GET_SIZE(p);

    /* If both left and right blocks are allocated */
    if(is_left_alloc && is_right_alloc)
    {
      return p;
    }
    
    /* If only the right block is free */
    else if(is_left_alloc && !is_right_alloc)
    {
      //remove the free blocks from seg list
      delete_free_blk(p);
      delete_free_blk(NEXT_BLK_PTR(p));
      //update size
      size_of_p += GET_SIZE(NEXT_BLK_PTR(p));
      //Pack info
      PUT(HDRP(p), PACK(size_of_p, 0));
      PUT(FTRP(p), PACK(size_of_p, 0));

    }
    
    
    /* If only the left block is Free */
    else if(!is_left_alloc && is_right_alloc)
    {
      //remove the free blocks from seg list
      delete_free_blk(p);
      delete_free_blk(PREV_BLK_PTR(p));
      //update size
      size_of_p += GET_SIZE(PREV_BLK_PTR(p));
      //Pack info
      PUT(FTRP(p), PACK(size_of_p, 0));
      PUT(HDRP(PREV_BLK_PTR(p)), PACK(size_of_p, 0));
      p = PREV_BLK_PTR(p);
    }

    else
    {
      //remove the free blocks from seg list
      delete_free_blk(p);
      delete_free_blk(NEXT_BLK_PTR(p));
      delete_free_blk(PREV_BLK_PTR(p));
      //update size
      size_of_p += GET_SIZE(NEXT_BLK_PTR(p));
      size_of_p += GET_SIZE(PREV_BLK_PTR(p));
      //pack info
      PUT(HDRP(PREV_BLK_PTR(p)), PACK(size_of_p, 0));
      PUT(FTRP(NEXT_BLK_PTR(p)), PACK(size_of_p, 0));
      p = PREV_BLK_PTR(p);

    }

    insert_free_blk(p, seglist_index(size_of_p));
    return p;
}










///////////////////////////////////////////////////
/////////////////////PLACE/////////////////////////
///////////////////////////////////////////////////

/* Place is just an outfunction for malloc to make it look simpler to understand and read (Personally i adopted this because the book suggested to) */
static void *place(size_t size)
{
    /* Setup the necesarry info such as size class to insert the block in the right locqation */
    int index = seglist_index(size);
    int fit_found = 0;
    void *current = GET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, index));
    void *split_block;
    
    /* Find a good fit by searching the asending linked list in the desired size class */
    while(index < SEGLIST_LENGTH && fit_found == 0)
    {
      //Setup current pointer to the first element of appropriate size class
      current = GET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, index));
      while(current != NULL)
      {
          //if fit is found --> set the flag and break from the loop
          if(GET_SIZE(current) >= size)
          {
              fit_found = 1;
              break;
          }
          current = GET_NEXT_PTR(current);
      }
      index++;
    }

    //IF NO SUITABLE BLOCK --> EXTEND HEAP
    if(fit_found == 0)
    {
      int extendsize = MAX(CHUNKSIZE,size);
      current = extend_heap(extendsize/WSIZE);
        
      //If heap can't be extended return Null
      if(current == NULL)
      {
          return NULL;
      }
    }
    size_t padding = GET_SIZE(current) - size;

    //deelete the desired free block from the seg_free list
    delete_free_blk(current);
    
    //If padding is more then the minimum block size --> split block
    if(padding > DSIZE*2)
    {
      //By experimentation I found that its generally beneficial to leave padding in front in case of large size
      if(size >= 100)
      {
          /* Pack the target box */
          PUT(HDRP(current), PACK(padding, 0));
          PUT(FTRP(current), PACK(padding, 0));
          
          split_block = (NEXT_BLK_PTR(current));
          
          /* Pack the free block */
          PUT(HDRP(split_block), PACK(size, 1));
          PUT(FTRP(split_block), PACK(size, 1));
          
          //Insert the free block in the seg_free list
          insert_free_blk(current, seglist_index(padding));
          return split_block;
      }
      
        //If the size is not so big the padded block comes afterwards
      else
      {
          //PACK THE BLOCK REQUIRED
          PUT(HDRP(current), PACK(size, 1));
          PUT(FTRP(current), PACK(size, 1));

          //COMPUTE PADDING BLOCK POINTER
          split_block = (NEXT_BLK_PTR(current));

          //PACK PADDING
          PUT(HDRP(split_block), PACK(padding, 0));
          PUT(FTRP(split_block), PACK(padding, 0));
          
          //Insert the free block in the seg_free list
          insert_free_blk(split_block, seglist_index(padding));
      }
    }
    
    //If the padding is not more than the minimum block size --> Pack the block as it is
    else
    {
      
      PUT(HDRP(current), PACK(GET_SIZE(current), 1));
      PUT(FTRP(current), PACK(GET_SIZE(current), 1));
    }
    return current;
}


//#########################################################################################//
//#########################################################################################//















//#########################################################################################//
//#########################################################################################//




///***********************************************/
///*/////////////////////////////////////////////*/
///*////////////////////MM_INIT//////////////////*/
///*/////////////////////////////////////////////*/
///***********************************************/

/*
mm_init - initialize the malloc package by initiating the heap by a certain amount and setting each index to a NULL pointer
*/
int mm_init(void)
{
  /* setup the segragated free list by pointing each index to NULL */
 seg_free_listp = mem_heap_lo();
 seg_free_listp = mem_sbrk(SEGLIST_LENGTH*WSIZE);
 unsigned int list_index = 0;
      
  while (list_index < SEGLIST_LENGTH)
 {
     SET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, list_index), NULL);
     list_index += 1;
 }
  
  /* point heap_listp to first byte after the seglist indicies */
  /* If the memory required to initiate the heap isn't present --> return -1 */
  void *heap_listp;
  if((long)(heap_listp = mem_sbrk(4 * WSIZE)) == -1)
      return -1;
  
  PUT(heap_listp,0); /* Alignment Padding */
  PUT(heap_listp + (1 * WSIZE),PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (2 * WSIZE),PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (3 * WSIZE),PACK(0, 1)); /* Epilogue header */
  heap_listp += DSIZE; /* points at prologue header */
  start = heap_listp;
    
  //Initiate the heap by extending it by a certain amount
  void *chunk_pointer = extend_heap(INITCHUNKSIZE/WSIZE);
  
  /* Extend the heap with a free block of chunksize bytes */
  if(chunk_pointer == NULL)
      return -1;
  
  
  /* local variables */
  //printf("\n2\n");
  return 0;
}

//#########################################################################################//
//#########################################################################################//









//#########################################################################################//
//#########################################################################################//




///***********************************************/
///*/////////////////////////////////////////////*/
///*////////////////////MM_MALLOC////////////////*/
///*/////////////////////////////////////////////*/
///***********************************************/

/*
* mm_malloc - Allocate a block by first serching the seg_free list
*/
void *mm_malloc(size_t size)
{
    //Ignore naive requests
    if(size == 0)
    {
      return NULL;
    }

    //Align size to two word boundary
    size_t alignedsize = ALIGN(size + DSIZE);

    //Place the pointer in the appropriate location via the place function
    void *ptr = place(alignedsize);
    /* ///////////////////////////////////////////////////////////////////////*/
    /////////UNCOMMENT BELOW LINE TO RUN HEAP CONSISTENCY CHECKER//////////////
    /* mm_check(); */
    /////////UNCOMMENT ABOVE LINE TO RUN HEAP CONSISTENCY CHECKER//////////////
    /* ///////////////////////////////////////////////////////////////////////*/
    return ptr;
}

/*
* mm_free - Freeing a block involves packing it with the correct header-footer and then add it to the segregated free list
*/
void mm_free(void *ptr)
{
    //Get the size to be freed
    size_t size = GET_SIZE(ptr);
    
    //Pack the header and footers with appropriate size and allocation bit info
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    //Insert the free block in the seg_list
    insert_free_blk(ptr, seglist_index(size));
    
    //coalesce the free blks
    coalesce(ptr);
    
    /* ///////////////////////////////////////////////////////////////////////*/
    /////////UNCOMMENT BELOW LINE TO RUN HEAP CONSISTENCY CHECKER//////////////
    /* mm_check(); */
    /////////UNCOMMENT ABOVE LINE TO RUN HEAP CONSISTENCY CHECKER//////////////
    /* ///////////////////////////////////////////////////////////////////////*/
    return;
}
//#########################################################################################//
//#########################################################################################//










//#########################################################################################//
//#########################################################################################//




///***********************************************/
///*/////////////////////////////////////////////*/
///*////////////////////MM_REALLOC///////////////*/
///*/////////////////////////////////////////////*/
///***********************************************/

/*
* mm_realloc - mm_realloc is implemented by the ideology that if adjacent blocks are free and the resultant coalesced block is big enough to accomodate the realloc request then go with that or else call malloc and free the existing location
*/

void *mm_realloc(void *ptr, size_t size)
{
    //Old size of the block
    size_t oldsize = GET_SIZE(ptr);
    
    //Get new size aligned according to and including header footer
    size_t alignedsize = ALIGN(size + DSIZE);

    //BASE CASE 1
    if(ptr == NULL)
    {
      return mm_malloc(size);
    }

    //BASE CASE 2
    if(size == 0)
    {
      mm_free(ptr);
      return NULL;
    }

    //If old-size is lgreater than aligned size no checking is required
    if(oldsize >= alignedsize)
    {
       //If resultant padding after realloc is greater than minimum block size
       if(oldsize - alignedsize > DSIZE)
       {
                                                       
           //PACK THE BLOCK REQUIRED
           PUT(HDRP(ptr), PACK(alignedsize, 1));
           PUT(FTRP(ptr), PACK(alignedsize, 1));

           //COMPUTE PADDING BLOCK POINTER
           void* split_block = (NEXT_BLK_PTR(ptr));

           //PACK PADDING
           size_t padding = oldsize - alignedsize;
           PUT(HDRP(split_block), PACK(padding, 0));
           PUT(FTRP(split_block), PACK(padding, 0));
                   
           //Insert the free block in the segregated free list
           insert_free_blk(split_block, seglist_index(padding));
           
           //Coalesce if nearby free blocks are available
           coalesce(split_block);
           return ptr;
       }
                                                   
       else
       {
           return ptr;
       }
    }

    //If the demand is greater than the old size look for nearby blocks if free
    if(oldsize < alignedsize)
    {
      
      //If left block is free
     if(!IS_LEFT_ALLOCATED(ptr))
     {
         void *left_ptr = PREV_BLK_PTR(ptr);
         void *right_ptr = NEXT_BLK_PTR(ptr);
         size_t c_size;
         //According to the case of right block being allocated or free --> update size accordingly
         if(!IS_RIGHT_ALLOCATED(ptr))
         {
             c_size = GET_SIZE(left_ptr) + GET_SIZE(ptr) + GET_SIZE(right_ptr);
         }
         
         else
         {
             c_size = GET_SIZE(left_ptr) + GET_SIZE(ptr);
         }
         
         //if size after coalescing can accomodate the request
         if(c_size >= alignedsize)
         {
             //if right is free delete it too
             if(!IS_RIGHT_ALLOCATED(ptr))
             {
                 delete_free_blk(right_ptr);
             }
             delete_free_blk(left_ptr);
             memcpy(left_ptr, ptr, oldsize - 8);
             
             //if padding is more than minimum block size
             if(c_size - alignedsize > DSIZE)
             {
                 //pack the target blcok
                 PUT(HDRP(left_ptr), PACK(alignedsize, 1));
                 PUT(FTRP(left_ptr), PACK(alignedsize, 1));
                 
                 void* split_block = (NEXT_BLK_PTR(left_ptr));
                 size_t padding = c_size - alignedsize;
                 
                 //pack the padding block
                 PUT(HDRP(split_block), PACK(padding, 0));
                 PUT(FTRP(split_block), PACK(padding, 0));
                 
                 //insert padding block in segregated - free list
                 insert_free_blk(split_block, seglist_index(padding));
                 
                 //coalesce if nearby free block
                 coalesce(split_block);
                 return left_ptr;
             }
             
             //if padding is not enough to create a free block
             if(c_size - alignedsize <= DSIZE)
             {
                 PUT(HDRP(left_ptr), PACK(c_size, 1));
                 PUT(FTRP(left_ptr), PACK(c_size, 1));
                 return left_ptr;
             }
         }
         
         //If no space availble by above coalescing --> call mm_malloc
         else
         {
             void* newptr = mm_malloc(size);
             memcpy(newptr, ptr, oldsize - 8);
             mm_free(ptr);
             return newptr;
         }

     }
      
      //If right block is free --> no need to shift info just chop off padding
      if(IS_LEFT_ALLOCATED(ptr) && !IS_RIGHT_ALLOCATED(ptr))
      {
          //Save the next block pointer to use later
          void *right_ptr = NEXT_BLK_PTR(ptr);
          size_t c_size = GET_SIZE(ptr) + GET_SIZE(right_ptr);
          
          //If after accounting for right block there is enough space
          if(c_size >= alignedsize)
          {
              //delete free block
              delete_free_blk(right_ptr);
              
              //if padding is greater than minimum block size
              if(c_size - alignedsize > DSIZE)
              {
                  //Pack the targeted block
                  PUT(HDRP(ptr), PACK(alignedsize, 1));
                  PUT(FTRP(ptr), PACK(alignedsize, 1));
                  
                  //save the padding block pointer
                  void* split_block = (NEXT_BLK_PTR(ptr));
                  size_t padding = c_size - alignedsize;
                  
                  //Pack the padding bloc k
                  PUT(HDRP(split_block), PACK(padding, 0));
                  PUT(FTRP(split_block), PACK(padding, 0));
                                                
                  //Insert the block in the seg_freelist
                  insert_free_blk(split_block, seglist_index(padding));
                  coalesce(split_block);
                  return ptr;
              }
              
              //If the padding is not enough to accomodate for a new block
              else
              {
                  PUT(HDRP(ptr), PACK(c_size, 1));
                  PUT(FTRP(ptr), PACK(c_size, 1));
                  return ptr;
              }
          }
          
          //If no space availble by above coalescing --> call mm_malloc
          else
          {
              void* newptr = mm_malloc(size);
              memcpy(newptr, ptr, oldsize - 8);
              mm_free(ptr);
              return newptr;
          }
      }
    
        
    //If no space availble by above coalescing --> call mm_malloc
    if(IS_LEFT_ALLOCATED(ptr) && IS_RIGHT_ALLOCATED(ptr))
    {
       void* newptr = mm_malloc(size);
       memcpy(newptr, ptr, oldsize - 8);
       mm_free(ptr);
       return newptr;
    }
      
    }
    /* ///////////////////////////////////////////////////////////////////////*/
    /////////UNCOMMENT BELOW LINE TO RUN HEAP CONSISTENCY CHECKER//////////////
    /* mm_check(); */
    /////////UNCOMMENT ABOVE LINE TO RUN HEAP CONSISTENCY CHECKER//////////////
    /* ///////////////////////////////////////////////////////////////////////*/
    
    return ptr;
}

//#########################################################################################//
//#########################################################################################//











//#########################################################################################//
//#########################################################################################//


///***********************************************/
///*/////////////////////////////////////////////*/
///*////////////////////MM_CHECK/////////////////*/
///*/////////////////////////////////////////////*/
///***********************************************/
      
//THE HEAP CONSISTENCY CHECKER
/*
    My heap consistency checker checks for

    ->All blocks in segregated free list are free

    ->Header and footer of any block in the heap matches

    ->8 word alignment is followed

    ->No Adjacent free blocks are free

    ->A block free in the heap is present in the segregated list
 */

/*
 TO RUN mm.c --> uncomment the call mm_check just before the return staements in mm_malloc,mm_free and mm_realloc
 */
static int mm_check()
{
    int consistent = 1; //set to 0(TRUE) if any error
    int index = 0;
    void *current = NULL; //point to the current block examing
    void *next = NULL; //points next to the block being examined
    
    /* Loop to the segregated free list to ensure all blocks are free */
    while(index < SEGLIST_LENGTH)
    {
      //Setup current pointer to the first element of appropriate size class
      current = GET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, index));
      while(current != NULL)
      {
          //if fit is found --> set the flag and break from the loop
          if(GET_ALLOC(current) == 1)
          {
              printf("free block not marked free \n");
              consistent = 0;
          }
          current = GET_NEXT_PTR(current);
      }
      index++;
    }
    
    /* loop through every block */
    next = NULL;
    current = start;
    while(!(GET_SIZE(current) == 0) && !(GET_ALLOC(current) == 1))
    {
        next = NEXT_BLK_PTR(current);
        
        /* check if the header and footer infortion match */
        if(GET(HDRP(current)) != GET(FTRP(current)))
        {
            printf("Header and Footer dosen't match \n");
            consistent = 0;
        }
        
        /* Check alignment according to double word boundaries */
        if(GET_SIZE(current) % DSIZE != 0)
        {
            printf("Improper Alignment \n");
            consistent = 0;
        }
        
        /* Check if adjacent blocks escaped coalesing */
        if(GET_ALLOC(current) == 0 && (GET_ALLOC(next) == 0 && GET_SIZE(next) != 0))
        {
            printf("Improper Coalesing \n");
            consistent = 0;
        }
        
        /* Check if a free block is actually present in the free list */
        if(!GET_ALLOC(current))
        {
            index = 0;
            int found = 0; //flag to determine if the target was found
            void *helper;
            while(index < SEGLIST_LENGTH)
            {
              //Setup current pointer to the first element of appropriate size class
              helper = GET_FIRST_PTR(GET_LIST_PTR(seg_free_listp, index));
              while(helper != NULL)
              {
                  //helper == current => target found
                  if(helper == current)
                  {
                      found = 1;
                  }
                  helper = GET_NEXT_PTR(helper);
              }
              index++;
            }
            
            //If target is not found
            if (found == 0)
            {
                printf("Free Block not in free list \n");
                consistent = 0;
            }
        }
        current = NEXT_BLK_PTR(current);
    }

    return consistent;
}
//#########################################################################################//
//#########################################################################################//



//#########################################################################################//
//                                         THE END
//#########################################################################################//
