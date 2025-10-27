/* Command to run the proof with Frama-C:
 frama-c-gui -c11 simplified_proved.c -wp -wp-rte -wp-timeout 200 -wp-time-extra 8 -wp-prover altergo,cvc4,cvc4-ce,script -wp-smoke-tests -wp-prop="-@lemma"  -wp-session ./wp_session
*/
#include <stdint.h>       // for uint types definitions
#include <string.h>       // for size_t definition
#include <byteswap.h>     // used in marshal
#define HOST_TO_BE_32(value) __bswap_32 (value) // swap endianness
typedef struct TPM2B_NAME { uint16_t size; uint8_t name[68];} TPM2B_NAME;
typedef struct {
  uint32_t      handle;   // handle used by TPM
  TPM2B_NAME      name;   // TPM name of the object
  uint32_t      rsrcType; // selector for resource type
} RESOURCE;
typedef struct NODE_T {
  uint32_t      handle;   // the handle used as reference
  RESOURCE      rsrc;     // the metadata for this rsrc
  struct NODE_T *   next; // next node in the list
} NODE_T; // linked list of resource
/*@
  predicate zero_tpm2b_name(TPM2B_NAME tpm2b_name) =
    tpm2b_name.size == 0 && \forall int i; 0 <= i  < 68 ==> tpm2b_name.name[i] == 0;
  predicate zero_resource(RESOURCE rsrc) =
    rsrc.handle == 0 && zero_tpm2b_name(rsrc.name) && rsrc.rsrcType == 0;
  predicate zero_rsrc_node_t(NODE_T node) =
    node.handle == 0 && zero_resource(node.rsrc) && node.next == \null;
*/
/************** Logic lists and linked lists definitions *************/
/*@
  predicate ptr_sep_from_list{L}(NODE_T* e, \list<NODE_T*> ll) =
    \forall integer n; 0 <= n < \length(ll) ==> \separated(e, \nth(ll, n));
  predicate dptr_sep_from_list{L}(NODE_T** e, \list<NODE_T*> ll) =
    \forall integer n; 0 <= n < \length(ll) ==> \separated(e, \nth(ll, n));
  predicate in_list{L}(NODE_T* e, \list<NODE_T*> ll) =
    \exists integer n; 0 <= n < \length(ll) && \nth(ll, n) == e;
  predicate in_list_handle{L}(uint32_t out_handle, \list<NODE_T*> ll) =
    \exists integer n; 0 <= n < \length(ll) && \nth(ll, n)->handle == out_handle;
  inductive linked_ll{L}(NODE_T *bl, NODE_T *el, \list<NODE_T*> ll) {
    case linked_ll_nil{L}: \forall NODE_T *el; linked_ll{L}(el, el, \Nil);
    case linked_ll_cons{L}: \forall NODE_T *bl, *el, \list<NODE_T*> tail;
      (\separated(bl, el) && \valid(bl) && linked_ll{L}(bl->next, el, tail) &&
      ptr_sep_from_list(bl, tail)) ==>
        linked_ll{L}(bl, el, \Cons(bl, tail));
  }
  predicate unchanged_ll{L1, L2}(\list<NODE_T*> ll) =
    \forall integer n; 0 <= n < \length(ll) ==>
      \valid{L1}(\nth(ll,n)) && \valid{L2}(\nth(ll,n)) &&
      \at((\nth(ll,n))->next, L1) == \at((\nth(ll,n))->next, L2);
  predicate all_sep_in_list(\list<NODE_T*> ll) =
    \forall integer n1, n2; (0 <= n1 < \length(ll) && 0 <= n2 < \length(ll) && n1 != n2) ==>
        \separated(\nth(ll, n1), \nth(ll, n2));
  axiomatic Node_To_ll {
    logic \list<NODE_T*> to_ll{L}(NODE_T* beg, NODE_T* end) 
      reads {node->next | NODE_T* node; \valid(node) &&
                           in_list(node, to_ll(beg, end))};
    axiom to_ll_nil{L}: \forall NODE_T *node; to_ll{L}(node, node) == \Nil;
    axiom to_ll_cons{L}: \forall NODE_T *beg, *end;
      (\separated(beg, end) && \valid{L}(beg) &&
      ptr_sep_from_list{L}(beg, to_ll{L}(beg->next, end))) ==>
        to_ll{L}(beg, end) == \Cons(beg, to_ll{L}(beg->next, end));
  }
*/

#include "lemmas_node_t.h"

#define _alloc_max 100
static NODE_T _rsrc_bank[_alloc_max];  // bank used by the static allocator
static int _alloc_idx = 0;  // index of the next rsrc node to be allocated 
/*@ 
  predicate valid_rsrc_mem_bank{L} = 0 <= _alloc_idx <= _alloc_max;
  predicate list_sep_from_allocables{L}(\list<NODE_T*> ll) =
    \forall int i; _alloc_idx <= i < _alloc_max ==> 
                        ptr_sep_from_list{L}(&_rsrc_bank[i], ll);
  predicate ptr_sep_from_allocables{L}(NODE_T* node) =
    \forall int i; _alloc_idx <= i < _alloc_max ==> \separated(node, &_rsrc_bank[i]);
  predicate dptr_sep_from_allocables{L}(NODE_T** p_node) =
    \forall int i; _alloc_idx <= i < _alloc_max ==> \separated(p_node, &_rsrc_bank[i]);
*/
/***************************************************************************/
/*@
  requires valid_rsrc_mem_bank;
  assigns _alloc_idx, _rsrc_bank[\old(_alloc_idx)];
  assigns \result \from _rsrc_bank[\old(_alloc_idx)];
  ensures valid_rsrc_mem_bank; 
  
  behavior not_allocable:
    assumes _alloc_idx == _alloc_max;
    
    ensures _alloc_idx == _alloc_max;
    ensures \result == NULL;
    ensures _rsrc_bank == \old(_rsrc_bank);
    ensures \forall int i; 0 <= i < _alloc_max ==> 
              _rsrc_bank[i] == \old(_rsrc_bank[i]); 
  behavior allocable:
    assumes 0 <= _alloc_idx < _alloc_max;
    
    ensures _alloc_idx == \old(_alloc_idx) + 1;
    ensures \result == &(_rsrc_bank[ _alloc_idx - 1]);
    ensures \valid(\result);
    ensures zero_rsrc_node_t( *(\result) );
    ensures \forall int i; 0 <= i < _alloc_max && i != \old(_alloc_idx) ==> 
            _rsrc_bank[i] == \old(_rsrc_bank[i]); 
  disjoint behaviors; complete behaviors;
*/
NODE_T *calloc_NODE_T()
{
  static const RESOURCE empty_RESOURCE;
  if(_alloc_idx < _alloc_max) {
    _rsrc_bank[_alloc_idx].handle = (uint32_t) 0;
    _rsrc_bank[_alloc_idx].rsrc = empty_RESOURCE;
    _rsrc_bank[_alloc_idx].next = NULL;
    _alloc_idx += 1;
    return &_rsrc_bank[_alloc_idx - 1];
  }
  return NULL;
}

typedef struct CONTEXT {
  int placeholder_int;
  NODE_T *rsrc_list;    
} CONTEXT;
/*@
  predicate ctx_sep_from_list(CONTEXT *ctx, \list<NODE_T*> ll) =  
    \forall integer i; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), ctx);
  predicate ctx_sep_from_allocables(CONTEXT *ctx) =
    \forall int i; _alloc_idx <= i < _alloc_max ==> \separated(ctx, &_rsrc_bank[i]);
    
  predicate freshness(CONTEXT * ctx, NODE_T ** node) = 
    ctx_sep_from_allocables(ctx)
    && list_sep_from_allocables(to_ll(ctx->rsrc_list, NULL))
    && ptr_sep_from_allocables(ctx->rsrc_list)
    && ptr_sep_from_allocables(*node)
    && dptr_sep_from_allocables(node);
    
  predicate sep_from_list{L}(CONTEXT * ctx, NODE_T ** node) = 
    ctx_sep_from_list(ctx, to_ll{L}(ctx->rsrc_list, NULL))
    && dptr_sep_from_list(node, to_ll{L}(ctx->rsrc_list, NULL));
*/

/*@
  requires valid_rsrc_mem_bank && freshness(ctx, out_node);
  requires \valid(ctx);
  requires ctx->rsrc_list != NULL ==> \valid(ctx->rsrc_list);
  requires linked_ll(ctx->rsrc_list, NULL, to_ll(ctx->rsrc_list, NULL));
  requires sep_from_list(ctx, out_node);
  requires ptr_sep_from_list(*out_node, to_ll(ctx->rsrc_list, NULL));
  requires !(in_list_handle(esys_handle, to_ll(ctx->rsrc_list, NULL)));
  requires \valid(out_node) && \separated(ctx, out_node);
  requires *out_node != NULL ==> \valid(*out_node) && (*out_node)->next == NULL;
  assigns _alloc_idx, _rsrc_bank[_alloc_idx];
  assigns ctx->rsrc_list \from _rsrc_bank[_alloc_idx];
  assigns *out_node \from _rsrc_bank[_alloc_idx];
  ensures valid_rsrc_mem_bank && freshness(ctx, out_node);  
  ensures sep_from_list(ctx, out_node);  
  ensures unchanged_ll{Pre, Post}(to_ll{Pre}(\old(ctx->rsrc_list), NULL));
  ensures \result \in {1610, 833};
  
  behavior not_allocable:
    assumes _alloc_idx == _alloc_max;
    
    ensures _alloc_idx == _alloc_max;
    ensures \valid(ctx);
    ensures !(in_list_handle(esys_handle, to_ll(ctx->rsrc_list, NULL)));
    ensures ctx->rsrc_list == \old(ctx->rsrc_list);
    ensures *out_node == \old(*out_node);
    ensures unchanged_ll{Pre, Post}(to_ll(ctx->rsrc_list, NULL));
    ensures \result == 833;
  behavior allocated:
    assumes 0 <= _alloc_idx < _alloc_max;
    
    ensures _alloc_idx == \old(_alloc_idx) + 1;
    ensures in_list_handle(esys_handle, to_ll(ctx->rsrc_list, NULL));
    ensures \valid(ctx->rsrc_list) && *out_node == ctx->rsrc_list;
    ensures ctx->rsrc_list == &_rsrc_bank[_alloc_idx - 1]; 
    ensures ctx->rsrc_list->handle == esys_handle;
    ensures ctx->rsrc_list->next == \old(ctx->rsrc_list);
    ensures linked_ll(ctx->rsrc_list, NULL, to_ll(ctx->rsrc_list, NULL));
    ensures unchanged_ll{Pre, Post}(to_ll{Pre}(\old(ctx->rsrc_list), NULL));
    ensures \old(ctx->rsrc_list) != NULL ==>
        \nth(to_ll(ctx->rsrc_list, NULL), 1) == \old(ctx->rsrc_list);
    ensures \result == 1610;    
  disjoint behaviors; complete behaviors;
*/
int createNode(CONTEXT * ctx, uint32_t esys_handle, NODE_T ** out_node){
//@ ghost pre_calloc:;
  //@ghost int if_id = 0;
  /*@ assert \separated(out_node, &_rsrc_bank[_alloc_idx]);*/ 
  /*@ assert \separated(ctx->rsrc_list, &_rsrc_bank[_alloc_idx]); */
  // NODE_T *new_head = calloc(1, sizeof(NODE_T));  /*library version*/
  /*@ assert list_sep_from_allocables(to_ll(ctx->rsrc_list, NULL)); */
  /*@ assert ptr_sep_from_list(&_rsrc_bank[_alloc_idx], to_ll{pre_calloc}(ctx->rsrc_list, NULL)); */
  /*@ assert ptr_sep_from_list(&_rsrc_bank[_alloc_idx], to_ll(ctx->rsrc_list, NULL)); */
  NODE_T *new_head = calloc_NODE_T();
  /*@ assert unchanged_ll{pre_calloc, Here}(
             to_ll{pre_calloc}(ctx->rsrc_list, NULL)); */
//@ ghost post_calloc:;  
  if (new_head == NULL){return 833;}
  /*@ assert \valid(new_head) && new_head->next == NULL; */ 
  /*@ assert ptr_sep_from_list(new_head, to_ll(ctx->rsrc_list, NULL)); */
  /*@ assert unchanged_ll{Pre, Here}(to_ll{Here}(ctx->rsrc_list, NULL));*/
//@ ghost pre_if:;
  if (ctx->rsrc_list == NULL) {
    /* The first object of the list will be added */
    ctx->rsrc_list = new_head;
    /*@ assert unchanged_ll{pre_if, Here}(to_ll(new_head, NULL));*/
    /*@ assert to_ll(new_head, NULL) == [|new_head|]; */  
    /*@ assert \separated(new_head, new_head->next);*/
    new_head->next = NULL;
    /*@ assert to_ll(new_head, NULL) == [|new_head|]; */  
  } 
  else {
    /* The new object will become the first element of the list */
    /*@ assert dptr_sep_from_list(&ctx->rsrc_list, 
                                  to_ll(ctx->rsrc_list, NULL));*/
    new_head->next = ctx->rsrc_list;
//@ ghost post_assign:;
    /*@ assert unchanged_ll{pre_if, Here}(
                            to_ll{pre_if}(ctx->rsrc_list, NULL));*/  
    /*@ assert to_ll(new_head, NULL) == 
        ([|new_head|] ^ to_ll(\at(ctx->rsrc_list, pre_if), NULL));*/
    /*@ assert dptr_sep_from_list(&ctx->rsrc_list, 
                                  to_ll(new_head, NULL));*/
    ctx->rsrc_list = new_head;
    /*@ assert unchanged_ll{post_assign, Here}(
                            to_ll{post_assign}(new_head, NULL));*/
    /*@ assert ctx->rsrc_list->next == \at(ctx->rsrc_list, Pre);*/
    /*@ assert to_ll(ctx->rsrc_list, NULL) == 
        ([|new_head|] ^ to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
    /*@ assert ctx->rsrc_list == \nth(to_ll(ctx->rsrc_list, NULL), 0);*/
  }
  //@ ghost post_add:;
  /*@ assert ctx->rsrc_list == \nth(to_ll(ctx->rsrc_list, NULL), 0);*/
  /*@ assert ctx_sep_from_list(ctx, to_ll(ctx->rsrc_list, NULL));*/
  /*@ assert ctx->rsrc_list == new_head;*/
  /*@ assert unchanged_ll{Pre, Here}(to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/ 
  /*@ assert to_ll(new_head, NULL) == 
             ([|new_head|] ^ to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
  /*@ assert dptr_sep_from_list(out_node, to_ll(new_head, NULL));*/
  *out_node = new_head;
  /*@ assert unchanged_ll{post_add, Here}(to_ll{post_add}(new_head, NULL));*/
  /*@ assert ctx->rsrc_list == \nth(to_ll(ctx->rsrc_list, NULL), 0);*/
  new_head->handle = esys_handle;  
  /*@ assert \nth(to_ll(ctx->rsrc_list, NULL), 0)->handle == esys_handle;*/
  /*@ assert in_list_handle(esys_handle, to_ll(ctx->rsrc_list, NULL));*/
  /*@ assert list_sep_from_allocables(to_ll(ctx->rsrc_list, NULL)); */
  /*@ assert unchanged_ll{Pre, Here}(to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
  return 1610;
}


/*@ 
  requires \valid(out_handle);
  assigns *out_handle;
  ensures \result \in {0, 12};
  ensures *out_handle \in {esys_handle, 0x4000000A, 0x4000000B,
                    0x40000110 + (esys_handle - 0x120U), \old(*out_handle)};
  behavior ok_handle:
    assumes esys_handle <= 31U || 0x120U <= esys_handle <= 0x12FU
         || esys_handle \in {0x10AU, 0x10BU};
    ensures \result == 0;
  behavior wrong_handle:
    assumes esys_handle > 31U && (esys_handle < 0x120U || esys_handle > 0x12FU);
    assumes !(esys_handle \in {0x10AU, 0x10BU});
    ensures *out_handle == \old(*out_handle);
    ensures \result == 12;
  disjoint behaviors; complete behaviors;
*/
int iesys_handle_to_tpm_handle(uint32_t esys_handle,  uint32_t * out_handle)
{
  if (esys_handle <= 31U) {*out_handle = (uint32_t) esys_handle; return 0;}
  if (esys_handle == 0x10AU){*out_handle = 0x4000000A; return 0;}
  if (esys_handle == 0x10BU){*out_handle = 0x4000000B; return 0;}
  if (esys_handle >= 0x120U && esys_handle <= 0x12FU) 
   {*out_handle = 0x40000110 + (esys_handle - 0x120U); return 0;}
  return 12;
}

/*@ 
  requires \valid(src) && \valid(dest + (0 .. sizeof(*src)-1));
  requires \separated(dest+(0..sizeof(*src)-1),src);
  
  assigns dest[0 .. sizeof(*src)-1];
  
  ensures \valid(src);
  ensures \valid(dest + (0 .. sizeof(*src)-1));
*/
void memcpy_custom(uint8_t *dest, uint32_t *src) { 
  dest[3] = (uint8_t)(*src & 0xFF);
  dest[2] = (uint8_t)((*src >> 8) & 0xFF);
  dest[1] = (uint8_t)((*src >> 16) & 0xFF);
  dest[0] = (uint8_t)((*src >> 24) & 0xFF);
}

/*@
  requires \valid(offset) && 0 <= *offset <= UINT8_MAX - sizeof(in);
  requires buff_size > 0 && \valid(&buff[0] + (0 .. buff_size - 1));
  requires *offset <= buff_size && sizeof(in) + *offset <= buff_size;
  requires \separated(offset, buff);
  
  assigns *offset, (&buff[*offset])[0..sizeof(in) - 1];

  ensures *offset ==  \old(*offset) + sizeof(in);    
  ensures \result == 0;
*/
int uint32_Marshal(uint32_t in,uint8_t buff[],size_t buff_size,size_t *offset){ 
  size_t  local_offset = 0; 
  if (offset != NULL){local_offset = *offset;}
  in = HOST_TO_BE_32(in); 
  // memcpy(&buff[local_offset], &in, sizeof (in));
  memcpy_custom(&buff[local_offset], &in);  
  if (offset != NULL){*offset = local_offset + sizeof (in);} 
  return 0; 
}


/*@
  requires valid_rsrc_mem_bank{Pre} && freshness(ctx, node);
  requires \valid(ctx);
  requires ctx->rsrc_list != \null ==> \valid(ctx->rsrc_list);
  requires linked_ll(ctx->rsrc_list, NULL, to_ll(ctx->rsrc_list, NULL));
  requires 0 <= \length(to_ll(ctx->rsrc_list, NULL)) < INT_MAX;
  requires \valid(node);
  requires *node != \null ==>( \valid(*node) && (*node)->next == \null);
  requires sep_from_list(ctx, node) && \separated(node, ctx);
  requires ptr_sep_from_list(*node, to_ll(ctx->rsrc_list, NULL));
  assigns _alloc_idx, _rsrc_bank[_alloc_idx];
  assigns ctx->rsrc_list \from _rsrc_bank[_alloc_idx];
  assigns *node \from _rsrc_bank[_alloc_idx];
  assigns (&ctx->rsrc_list->rsrc.name.name[0])[0];
  ensures valid_rsrc_mem_bank && freshness(ctx, node);
  ensures \separated(node, ctx);
  ensures \result \in {616, 833, 1611, 12};
   
  behavior handle_in_list:
    assumes in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL));
    
    ensures _alloc_idx == \old(_alloc_idx);
    ensures ctx->rsrc_list == \old(ctx->rsrc_list);
    ensures in_list(*node, to_ll(ctx->rsrc_list, NULL)) && *node != NULL;
    ensures (*node)->handle == rsrc_handle && sep_from_list(ctx, node);
    ensures unchanged_ll{Pre, Post}(to_ll(ctx->rsrc_list, NULL));
    ensures \result == 616;
  behavior handle_not_converted:
    assumes !(in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL)));
    assumes rsrc_handle > 31U && ! ( rsrc_handle \in {0x10AU, 0x10BU} );
    assumes rsrc_handle < 0x120U || rsrc_handle > 0x12FU;
    
    ensures unchanged_ll{Pre, Post}(to_ll(ctx->rsrc_list, NULL)); 
    ensures ptr_sep_from_list(*node, to_ll(ctx->rsrc_list, NULL));
    ensures sep_from_list(ctx, node) && *node == \old(*node);
    ensures \result == 12;
  behavior handle_not_in_list_and_node_not_allocable:
    assumes !(in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL)));
    assumes rsrc_handle <= 31U || (rsrc_handle \in {0x10AU, 0x10BU})
            || (0x120U <= rsrc_handle <= 0x12FU);
    assumes _alloc_idx == _alloc_max;
    
    ensures _alloc_idx == _alloc_max;
    ensures unchanged_ll{Pre, Post}(to_ll{Pre}(ctx->rsrc_list, NULL));
    ensures *node == \old(*node) && ctx->rsrc_list == \old(ctx->rsrc_list);
    ensures ptr_sep_from_list(*node, to_ll{Pre}(ctx->rsrc_list, NULL));
    ensures sep_from_list{Pre}(ctx, node); // has to stay in behavior 
    ensures \result == 833;
  behavior handle_not_in_list_and_node_allocated:
    assumes !(in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL)));
    assumes rsrc_handle <= 31U || (rsrc_handle \in {0x10AU, 0x10BU})
            || (0x120U <= rsrc_handle <= 0x12FU);
    assumes 0 <= _alloc_idx < _alloc_max;
    
    ensures in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL));
    ensures (*ctx->rsrc_list).handle == rsrc_handle;
    ensures _alloc_idx == \old(_alloc_idx) + 1;
    ensures \valid(ctx->rsrc_list) && *node == ctx->rsrc_list;
    ensures ctx->rsrc_list != \old(ctx->rsrc_list);
    ensures ctx->rsrc_list->next == \old(ctx->rsrc_list);
    ensures to_ll(ctx->rsrc_list, NULL) 
        == ([|ctx->rsrc_list|] ^ to_ll{Pre}(\old(ctx->rsrc_list), NULL) );
    ensures \old(ctx->rsrc_list) != NULL ==> 
            \nth(to_ll(ctx->rsrc_list, NULL), 1) == \old(ctx->rsrc_list);
    ensures linked_ll(ctx->rsrc_list, NULL, to_ll(ctx->rsrc_list, NULL)); 
    ensures sep_from_list(ctx, node);
    ensures \result == 1611;
  disjoint behaviors; complete behaviors;
*/
int getNode(CONTEXT *ctx, uint32_t rsrc_handle, NODE_T ** node) {
  /*@ assert linked_ll(ctx->rsrc_list, NULL, to_ll(ctx->rsrc_list, NULL));*/
  int r;
  uint32_t tpm_handle;

  NODE_T *tmp_node;
  /*@ ghost int n = 0;*/ 
  /*@ 
    loop invariant unchanged_ll{Pre, Here}(to_ll(ctx->rsrc_list, NULL));
    loop invariant linked_ll(ctx->rsrc_list, NULL, 
                    to_ll(ctx->rsrc_list, NULL));
    loop invariant linked_ll(ctx->rsrc_list, tmp_node, 
                    to_ll(ctx->rsrc_list, tmp_node));
    loop invariant ptr_sep_from_list(tmp_node,
                    to_ll(ctx->rsrc_list, tmp_node));
    loop invariant tmp_node != \null ==> 
                    in_list(tmp_node, to_ll(ctx->rsrc_list, NULL));
    loop invariant !in_list_handle(rsrc_handle, 
                    to_ll(ctx->rsrc_list, tmp_node));
    loop invariant n == \length(to_ll(ctx->rsrc_list, tmp_node));  
    for handle_in_list : loop invariant 
        in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL));
    loop assigns n, tmp_node;
    loop variant \length(to_ll(tmp_node, NULL));
  */
  for (tmp_node = ctx->rsrc_list; tmp_node != NULL;
      tmp_node = tmp_node->next) {
    /*@ assert tmp_node == \nth(to_ll(ctx->rsrc_list, NULL), n);*/
    /*@ assert linked_ll(tmp_node, NULL, to_ll(tmp_node, NULL));*/
    if (tmp_node->handle == rsrc_handle){
      /*@ assert dptr_sep_from_list(node, to_ll(ctx->rsrc_list, NULL));*/
      *node = tmp_node;
      /*@ assert unchanged_ll{Pre, Here}(to_ll{Pre}(ctx->rsrc_list, NULL));*/
      /*@ assert ptr_sep_from_allocables(*node);*/
      return 616;
    }
  /*@ assert to_ll(ctx->rsrc_list, tmp_node->next) 
          == (to_ll(ctx->rsrc_list, tmp_node) ^ [|tmp_node|]);*/
  /*@ghost n++;*/   
  }  

//@ ghost post_loop:;
  /*@ assert !(in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL)));*/  
  /*@ assert unchanged_ll{Pre, Here}(to_ll(ctx->rsrc_list, NULL));*/
  r = iesys_handle_to_tpm_handle(rsrc_handle, &tpm_handle);
  if (r == 12) { return r; };
 
  NODE_T *tmp_node_2 = NULL;
  /*@ assert dptr_sep_from_list(&tmp_node_2, 
                                to_ll{post_loop}(ctx->rsrc_list, NULL));*/
  /*@ assert unchanged_ll{Pre, Here}(to_ll{Pre}(ctx->rsrc_list, NULL));*/
  /*@ assert \separated(node, &tmp_node_2);*/
  r = createNode(ctx, rsrc_handle, &tmp_node_2);
  /*@ assert sep_from_list(ctx, node);*/
  if (r == 833) {/*@ assert sep_from_list(ctx, node);*/ return r;};
//@ ghost post_alloc:;
  /*@ assert to_ll(ctx->rsrc_list, NULL) 
      ==([|ctx->rsrc_list|] ^ to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
  /*@ assert ctx_sep_from_list(ctx, to_ll(ctx->rsrc_list, NULL));*/
  tmp_node_2->rsrc.handle = tpm_handle;
  tmp_node_2->rsrc.rsrcType = 0;  
  size_t offset = 0;
  /*@ assert ptr_sep_from_list(tmp_node_2,
              to_ll(ctx->rsrc_list->next, NULL));*/
  r = uint32_Marshal(tpm_handle, &tmp_node_2->rsrc.name.name[0],
                      sizeof(tmp_node_2->rsrc.name.name),&offset);     
  /*@ assert in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL));*/
  if (r != 0) { return r;};
  tmp_node_2->rsrc.name.size = offset;
  /*@ assert unchanged_ll{post_alloc, Here}(to_ll(ctx->rsrc_list, NULL));*/
  /*@ assert dptr_sep_from_list(node, to_ll(ctx->rsrc_list, NULL));*/
  /*@ assert dptr_sep_from_list(node, 
              to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
  *node = tmp_node_2;
  /*@ assert unchanged_ll{Pre, Here}(
              to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/

  /*@ assert unchanged_ll{Pre, Here}(
             to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
  /*@ assert in_list_handle(rsrc_handle, to_ll(ctx->rsrc_list, NULL));*/
  /*@ assert ctx->rsrc_list->next == \at(ctx->rsrc_list, Pre);*/
  /*@ assert \at(ctx->rsrc_list, Pre) != \null ==> 
      ctx->rsrc_list->next == \nth(to_ll(ctx->rsrc_list, NULL), 1);*/
  /*@ assert ctx->rsrc_list->handle == rsrc_handle;*/
  /*@ assert freshness(ctx, node);*/
  /*@ assert sep_from_list(ctx, node);*/
  return 1611;
}

