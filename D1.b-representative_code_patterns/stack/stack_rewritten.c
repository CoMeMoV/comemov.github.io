#define TableLength (2000)
#define MaxNumOfCollections (500)

#define GET_COLLECTIONSIZE(idx) ((Registry[idx]) & 0xff)
#define GET_COLLECTIONMAXSIZE(idx) ((Registry[idx]) >> 8)
// #define SET_COLLECTIONSIZE(ptr,size) (*(ptr) = (size) + (*(ptr) & 0xff00))
// #define SET_COLLECTIONMAXSIZE(ptr,maxsize) (*(ptr) = (*(ptr) & 0xff) + ((maxsize) << 8))

typedef unsigned short ushort;
typedef unsigned char uchar;

typedef struct RegistryCellTag {
  uchar CollectionSize; //size of the collection
  uchar CollectionMaxSize; //maximum size of the collection
} RegistryCell ;


ushort Registry[MaxNumOfCollections];
ushort Table[TableLength];

// Current collection
ushort* CurrentCollectionStart;
ushort* NextFreeCell;
uchar CurrentCollectionMaxSize;
ushort* NextFreeRegister;


//@ ghost int g_CollectionStart_idx[MaxNumOfCollections+1]; 
// +1 as it needs to store the current collection even if the registry is already full
//@ ghost int g_CurrentCollectionStart_idx;
//@ ghost int g_NextFreeCell_idx;
//@ ghost int g_NextFreeRegister_idx;

/*@
  // Size of the current collection
  logic integer current_collection_size{L} =
    g_NextFreeCell_idx - g_CurrentCollectionStart_idx;
*/

#define valid_Registry ( \
  ( \forall integer i; 0 <= i < g_NextFreeRegister_idx ==> \
    ( \
      g_CollectionStart_idx[i] + GET_COLLECTIONSIZE(i) == g_CollectionStart_idx[i+1] && \
        0 <= GET_COLLECTIONSIZE(i) <= GET_COLLECTIONMAXSIZE(i) && \
        g_CollectionStart_idx[i] + GET_COLLECTIONMAXSIZE(i) <= TableLength \
      ) \
    ) && \
    \forall integer i; 0 <= i <= g_NextFreeRegister_idx ==> 0 <= g_CollectionStart_idx[i] < TableLength \
  )

/*@
  // The model is valid iff: 
  // - the next register is in the range of the Registry
  // - StartIdex stores the begining of teh current collection at its on-going index
  // - The collections are stuck together
  // - All the colelctions have valid start address
  
  predicate valid_model{L} =
    &Registry[g_NextFreeRegister_idx] == NextFreeRegister &&
    0 <= g_NextFreeRegister_idx <= MaxNumOfCollections &&
    g_CollectionStart_idx[g_NextFreeRegister_idx] == g_CurrentCollectionStart_idx &&
    valid_Registry
  ;

  predicate valid_current_collection{L} =
    &Table[g_CurrentCollectionStart_idx] == CurrentCollectionStart &&
    &Table[g_NextFreeCell_idx] == NextFreeCell &&
    g_CurrentCollectionStart_idx + CurrentCollectionMaxSize <= TableLength &&
    0 <= current_collection_size <= CurrentCollectionMaxSize
  ;
*/

/*#######################################################*/
/*@
  predicate push_stamp_legitimate{L} =
   current_collection_size < CurrentCollectionMaxSize
  ;

  predicate pop_stamp_legitimate{L} =
    0 < current_collection_size
  ;

  predicate push_collection_legitimate{L}(ushort collection_max_size) =
    0 < collection_max_size &&
    (g_NextFreeCell_idx + collection_max_size) <= TableLength
  ;

  predicate push_register_legitimate{L} =
    g_NextFreeRegister_idx < MaxNumOfCollections
  ;

  predicate pop_collection_legitimate{L} = 
    0 < g_NextFreeRegister_idx
  ;

  predicate unchanged_Table_idx{L1,L2}(integer b, integer e) =
    \forall integer i ; b <= i < e ==>
      \at(Table[i],L1) == \at(Table[i],L2)
  ;

  predicate unchanged_Registry_idx{L1,L2}(integer b, integer e) =
    \forall integer i ; b <= i < e ==>
      \at(Registry[i],L1) == \at(Registry[i],L2)
  ;

  predicate unchanged_CollectionStartIndex_idx{L1,L2}(integer b, integer e) =
    \forall integer i ; b <= i < e ==>
      \at(g_CollectionStart_idx[i],L1) == \at(g_CollectionStart_idx[i],L2)
  ;

  predicate unchanged_current_collection{L1,L2} =
    \at(CurrentCollectionStart,L1) == \at(CurrentCollectionStart,L2) &&
    \at(CurrentCollectionMaxSize,L1) == \at(CurrentCollectionMaxSize,L2) &&
    current_collection_size{L1} == current_collection_size{L2}
  ;

  predicate unchanged_Registry{L1,L2} =
    \at(g_NextFreeRegister_idx,L1) == \at(g_NextFreeRegister_idx,L2) &&
    \at(Registry,L1) == \at(Registry,L2) &&
      unchanged_Registry_idx{L1,L2}(0,\at(g_NextFreeRegister_idx,L1))
  ;

  predicate unchanged_Table{L1,L2} =
    \at(g_NextFreeCell_idx,L1) == \at(g_NextFreeCell_idx,L2) &&
    \at(Table,L1) == \at(Table,L2) &&
    unchanged_Table_idx{L1,L2}(0,\at(g_NextFreeCell_idx,L1))
  ;

  lemma lemma_equiv_ptr_idx{L} : \forall integer i, integer j, ushort* a, ushort* p_i, ushort* p_j;
    &a[i] == p_i && &a[j] == p_j ==>
    (
      i < j <==> p_i < p_j
    )
  ;

  lemma l1:
    \forall integer i;
    0 <= i ==>
    (i >> 8) == (i / 256)
  ;

  lemma l2:
    \forall integer i;
    0 <= i ==>
    (i << 8) == (i * 256)
  ;

  lemma l3:
    \forall integer i;
    0 <= i ==>
    (i & 0xff) == (i % 256)
  ;
 */
/*#######################################################*/


/*@
  requires valid_model;
  requires valid_current_collection;
  requires push_stamp_legitimate;

  assigns NextFreeCell, *NextFreeCell, g_NextFreeCell_idx;

  ensures valid_model;
  ensures valid_current_collection;

  ensures unchanged_Registry{Pre,Post};
  ensures unchanged_Table_idx{Pre,Post}(0, \old(g_NextFreeCell_idx));
  ensures *\old(NextFreeCell) == c;
  ensures current_collection_size{Post} == current_collection_size{Pre} + 1;
*/

int push_stamp(ushort c){
  *NextFreeCell = c;
  NextFreeCell+=1;
  //@ ghost g_NextFreeCell_idx +=1;
  return 0;
}


/*@
  requires valid_model;
  requires valid_current_collection;
  requires pop_stamp_legitimate;

  assigns g_NextFreeCell_idx, NextFreeCell;
  
  ensures valid_model;
  ensures valid_current_collection;

  ensures current_collection_size{Post} == current_collection_size{Pre} - 1;
  ensures unchanged_Table_idx{Pre,Post}(0,g_NextFreeCell_idx);
  ensures unchanged_Registry{Pre,Post};
*/

int pop_stamp(){

  NextFreeCell-=1;
  //@ ghost g_NextFreeCell_idx -= 1;
  return 0;
}


/*@
  requires valid_model;
  requires valid_current_collection;

  behavior b_legitimate:
    assumes push_register_legitimate;
    assumes push_collection_legitimate(collection_max_size);

    assigns NextFreeRegister, g_NextFreeRegister_idx;
    assigns *NextFreeRegister;
    assigns CurrentCollectionStart, CurrentCollectionMaxSize, g_CurrentCollectionStart_idx;
    assigns g_CollectionStart_idx[\at(g_NextFreeRegister_idx,Post)];

    ensures \result == 0;
    ensures valid_model;
    ensures valid_current_collection;

    ensures unchanged_Table{Pre,Post};
    ensures g_NextFreeRegister_idx == \old(g_NextFreeRegister_idx) + 1;
    ensures CurrentCollectionStart == \old(NextFreeCell);
    ensures CurrentCollectionMaxSize == collection_max_size;
    ensures O1: GET_COLLECTIONSIZE(\old(g_NextFreeRegister_idx))== current_collection_size{Pre};
    ensures O2: GET_COLLECTIONMAXSIZE(\old(g_NextFreeRegister_idx)) == \old(CurrentCollectionMaxSize);
    ensures unchanged_Registry_idx{Pre,Post}(0,\old(g_NextFreeRegister_idx));
    
  behavior b_illegitimate:
    assumes !push_register_legitimate || !push_collection_legitimate(collection_max_size);
    
    assigns \nothing;
    
    ensures \result == -1;
    ensures valid_model;
    ensures valid_current_collection;

    ensures unchanged_current_collection{Pre,Post};
    ensures unchanged_Registry{Pre,Post};
    ensures unchanged_Table{Pre,Post};

  disjoint behaviors;
  complete behaviors;
*/

int push_collection(uchar collection_max_size){
  // No space in Registry to store a new collection
  if( ! ( ((ushort*) Registry <= NextFreeRegister) && (NextFreeRegister< ((ushort*)Registry + MaxNumOfCollections)) ) ){
    return -1;
  }

  // No space in Table to store a new collection
  if (!( (0<collection_max_size) &&
    ((ushort*) Table <= NextFreeCell) && 
        ((NextFreeCell + collection_max_size) <= ((ushort*) Table + TableLength )))){
    return -1;
  }

  // Save current collection
  *NextFreeRegister = ((NextFreeCell - CurrentCollectionStart)) + (CurrentCollectionMaxSize << 8);
  //@ assert (*NextFreeRegister & 0xff) == current_collection_size; // needed for O1
  //@ assert (*NextFreeRegister >> 8) == CurrentCollectionMaxSize; // needed for O2

  // Update current collection
  NextFreeRegister +=1;
  //@ ghost g_NextFreeRegister_idx +=1;

  CurrentCollectionStart= NextFreeCell;
  //@ ghost g_CurrentCollectionStart_idx = g_NextFreeCell_idx;
  //@ ghost g_CollectionStart_idx[g_NextFreeRegister_idx] = g_CurrentCollectionStart_idx;

  CurrentCollectionMaxSize = collection_max_size;

  return 0;
}


/*@

  requires valid_model;
  requires valid_current_collection;
  
  behavior b_legitimate:
    assumes pop_collection_legitimate;
    
    assigns NextFreeRegister, g_NextFreeRegister_idx;
    assigns NextFreeCell, g_NextFreeCell_idx;
    assigns CurrentCollectionMaxSize;
    assigns CurrentCollectionStart, g_CurrentCollectionStart_idx;

    ensures \result == 0;
    ensures valid_model;
    ensures valid_current_collection;
    
    ensures g_NextFreeRegister_idx == \old(g_NextFreeRegister_idx) -1;
    ensures unchanged_Registry_idx{Pre,Post}(0,(g_NextFreeRegister_idx));

    ensures g_CurrentCollectionStart_idx == g_CollectionStart_idx[\old(g_NextFreeRegister_idx)-1];
    ensures CurrentCollectionMaxSize == GET_COLLECTIONMAXSIZE(\old(g_NextFreeRegister_idx)-1);
    ensures current_collection_size == GET_COLLECTIONSIZE(\old(g_NextFreeRegister_idx)-1);
  
    ensures unchanged_Table_idx{Pre,Post}(0,g_CollectionStart_idx[\old(g_NextFreeRegister_idx)]);

  behavior b_illegitimate:
    assumes !pop_collection_legitimate;
    
    assigns \nothing;

    ensures \result == -1;
    ensures valid_model;
    ensures valid_current_collection;

    ensures unchanged_current_collection{Pre,Post};
    ensures unchanged_Registry{Pre,Post};
    ensures unchanged_Table{Pre,Post};

  disjoint behaviors;
  complete behaviors;
*/

int pop_collection(){

  // No previous collection
  if(!(((ushort*)Registry <= (NextFreeRegister -1)) && 
        ((NextFreeRegister -1) < ((ushort*) Registry + MaxNumOfCollections )))){
    return -1;
  }

  NextFreeRegister-=1;
  //@ ghost g_NextFreeRegister_idx -= 1;
  NextFreeCell = CurrentCollectionStart;
  //@ ghost g_NextFreeCell_idx = g_CurrentCollectionStart_idx;

  CurrentCollectionStart -= *NextFreeRegister & 0xff;
  CurrentCollectionMaxSize = *NextFreeRegister >> 8;
  //@ ghost g_CurrentCollectionStart_idx = g_CollectionStart_idx[g_NextFreeRegister_idx];
 
  return 0;
}