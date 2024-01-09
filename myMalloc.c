#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
 // (void) raw_size;
 // assert(false);
 // exit(1);
  if(raw_size == 0) return NULL;
  size_t size8 = ((raw_size+7)/8)*8;
  if (size8 < 16) {
    size8 = 16;
  }
  size_t totalsize = size8+ALLOC_HEADER_SIZE;
  //gets correct size for memory
  int ilist = (size8/8)-1;
  if(ilist > N_LISTS - 1) {
    ilist = N_LISTS - 1;
  }
  header * freelist = &freelistSentinels[ilist];
//moves on to the next list if the current list is empty
  int noSpace = 1;
  header * obj = NULL;
  for (; ilist < N_LISTS; ilist++) {
    
    freelist = &freelistSentinels[ilist];
    if (freelist->next != freelist) {
    //PART 3 START
      if (ilist != N_LISTS - 1) {
      noSpace = 0;
      break;
      }
      //PART 3 END

    
   
    if (ilist == N_LISTS-1) {
      header * t = freelist->next;
      while (t != freelist) {
        if (totalsize <= get_size(t)) {
          obj = t;
          noSpace = 0;
          break;
        }
        t = t->next;
      }
     
    }
    }
  }

  if (obj == NULL) {
      obj = freelist ->next;
  }
  if (noSpace == 0) {
    //PART 1 BLOCK
    if (get_size(obj) - totalsize >= 16) {
      
    
  //converts to char * cuz 1 byte, splits the block of memory into what you need
      header * obj2 = (header*)((char*)obj + get_size(obj)-totalsize);
    //upto here
    //set size of block to be taken to size you need
      set_size_and_state(obj2, totalsize, ALLOCATED);
    //block split so one on left set to calculation
      obj2->left_size = get_size(obj)-totalsize;
    //obj is now on left so that is being updated to obj-sizeyouneed
      int inew = (get_size(obj)-ALLOC_HEADER_SIZE)/8-1;
      if (inew > N_LISTS-1) {
        inew = N_LISTS-1;
      }
      set_size(obj, get_size(obj) - totalsize);
    //the block on the right has to be set leftsize to new block
      int inew1 = (get_size(obj)-ALLOC_HEADER_SIZE)/8-1;
      if (inew1 > N_LISTS-1) {
        inew1 = N_LISTS-1;
      }
      if (inew != inew1) {
        obj->next->prev = obj->prev;
        obj->prev->next = obj->next;
        header * freelist = &freelistSentinels[inew1];
        obj->prev = freelist;
        obj->next = freelist->next;

        freelist->next->prev = obj;

        freelist->next = obj;
      }
      header *obj3 = get_right_header(obj2);
      obj3 ->left_size = totalsize;
      return (header *)obj2->data;
    } else {
      set_state(obj, ALLOCATED);
      obj->next->prev = obj->prev;
      obj->prev->next = obj->next;
      return (header * )obj->data;
    }
  } else {

    //PART 3 BLOCK
    header * newBlock = allocate_chunk(ARENA_SIZE);
    //gets the block in memory left to newly allocated block
    header * checkHeader = get_right_header(lastFencePost);
    
    //last fencepost of the new one is first fencepost of new one
    if (checkHeader == get_left_header(newBlock)/*gotta find how to get fencepost of newblock */) {
      header * left1 = get_left_header(lastFencePost);
      //left block unallocated too so merge together
      if (get_state(left1) == UNALLOCATED) {
        int leftS = get_size(left1) - ALLOC_HEADER_SIZE;
        set_size(left1, get_size(left1) + get_size(newBlock) + ALLOC_HEADER_SIZE*2);
        int i = leftS/8-1;
        if(i > N_LISTS - 1) {
          i = N_LISTS - 1;
        }
        if (i != N_LISTS-1) {
          left1->prev->next = left1->next;
          left1->next->prev = left1->prev;
          i = get_size(left1)-ALLOC_HEADER_SIZE;
          int i1 = i/8-1;
          if (i1 > N_LISTS-1) {
            i1 = N_LISTS-1;
          }
          
        freelist = &freelistSentinels[i1];
        left1->next = freelist->next;
        left1->prev = freelist;
        freelist->next->prev = left1;
        freelist->next = left1;
        }
      lastFencePost = get_right_header(newBlock);
      lastFencePost->left_size = get_size(left1);

      } else {
      //left block is allocated nothing to do
        int size = ALLOC_HEADER_SIZE * 2 + get_size(newBlock);
        set_size(lastFencePost, size);
        set_state(lastFencePost, UNALLOCATED);
        int i = (get_size(lastFencePost)-ALLOC_HEADER_SIZE)/8-1;
        if (i > N_LISTS-1) {
          i = N_LISTS-1;
        }
        
        freelist = &freelistSentinels[i];
        lastFencePost->next = freelist->next;
        lastFencePost->prev = freelist;
        freelist->next->prev = lastFencePost;
        freelist->next = lastFencePost;
        lastFencePost = get_right_header(newBlock);
        lastFencePost->left_size = size;
      }


    } else {
      insert_os_chunk(get_left_header(newBlock));
      int i = (get_size(newBlock)-ALLOC_HEADER_SIZE)/8-1;
      if (i > N_LISTS-1) {
        i = N_LISTS-1;
      }
      freelist = &freelistSentinels[i];
      newBlock->next = freelist->next;
      newBlock->prev = freelist;
      freelist->next->prev = newBlock;
      freelist->next = newBlock;
      lastFencePost = get_right_header(newBlock);

    }
    return allocate_object(raw_size);
  }


}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  //(void) p;
  //assert(false);
  //exit(1);

  if (p != NULL) {
    for (int i = 0; i < N_LISTS; i++) {
      header * cur = &freelistSentinels[i];
      header * next1 = cur->next;
      while(next1 != cur) {
        if ((char *) next1 + get_size(next1) >= (char *) p && (char * )next1 <= (char*) p) {
          printf("Double Free Detected\n");
          assert(false);
        }
        next1 = next1->next;
      }

    }
    header * head = ptr_to_header(p);
    header * right = get_right_header(head);
    header * left = get_left_header(head);
    //if unallocated then its one big block not much to do 
    if (get_state(right) != UNALLOCATED && get_state(left) != UNALLOCATED) {
      int the_size = (get_size(head)- ALLOC_HEADER_SIZE)/8-1;
      //gets which list it is in
      //if it is bigger than nlists make it the last list
      if (the_size >= N_LISTS) {
        the_size = N_LISTS-1;
      }
      //add to the freelist chosen
      header * the_free_list = &freelistSentinels[the_size];
      head->next = the_free_list->next;
      head->prev = the_free_list;
      head->next->prev =  head;
      the_free_list->next = head;
      set_state(head, UNALLOCATED);
      return;
    }
    if (get_state(right) != UNALLOCATED && get_state(left) == UNALLOCATED) {
      int lsize = get_size(left)-ALLOC_HEADER_SIZE;
      set_size(left, get_size(left) + get_size(head));
      int i = lsize/8-1;
      if (i >= N_LISTS) {
        i = N_LISTS - 1;
      }
      if (i != N_LISTS - 1) {
        left->prev->next = left->next;
        left->next->prev = left->prev;
        int size = get_size(left) - ALLOC_HEADER_SIZE;
        int s = (size)/8-1;
        if (s >= N_LISTS) {
          s = N_LISTS -1;
        }
        header * i1 = &freelistSentinels[s];
        left->next = i1->next;
        left->prev = i1;
        left->next->prev = left;
        i1->next = left;
        
      }
      right->left_size = get_size(left);
      return;
    }
    
    if (get_state(left) != UNALLOCATED && get_state(right) == UNALLOCATED) {

      int rsize = get_size(right)-ALLOC_HEADER_SIZE;
      set_size(head, get_size(right) + get_size(head));
      int i = rsize/8-1;
      if (i >= N_LISTS) {
        i = N_LISTS - 1;
      }
      if (i != N_LISTS - 1) {
        right->prev->next = right->next;
        right->next->prev = right->prev;
        int size = get_size(head) - ALLOC_HEADER_SIZE;
        int s = (size)/8-1;
        if (s >= N_LISTS) {
          s = N_LISTS - 1;
        }
        header * i1 = &freelistSentinels[s];
        head->next = i1->next;
        head->prev = i1;
        head->next->prev = head;
        i1->next = head;
      } else {
        head->next = right->next;
        head->prev = right->prev;
        right->prev->next = head;
        head->next->prev = head;


      }
      header* the_right = get_right_header(head);
      the_right->left_size = get_size(head);
      set_state(head, UNALLOCATED);
      return;
    }




    if(get_state(right) == UNALLOCATED && get_state(left) == UNALLOCATED) {
      int lsize = get_size(left) - ALLOC_HEADER_SIZE;
      set_size(left, get_size(head) + get_size(right) + get_size(left));
      int i = lsize/8-1;
      right->prev->next = right->next;
      right->next->prev = right->prev;

      if (i >= N_LISTS) {
        i = N_LISTS - 1;

      }
      if (i != N_LISTS - 1) {
        left->prev->next = left->next;
        left->next->prev = left->prev;
        int s = (get_size(left) - ALLOC_HEADER_SIZE)/8-1;
        if (s >= N_LISTS) {
          s = N_LISTS - 1;
        }
        header * i1 = &freelistSentinels[s];
        left->next = i1->next;
        left->prev = i1;
        left->next->prev = left;
        i1->next = left;
        
      }
      header * the_right = get_right_header(left);
      the_right->left_size = get_size(left);


    }

  }
  return;
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
