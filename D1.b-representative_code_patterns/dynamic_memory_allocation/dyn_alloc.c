/* Command to run the proof with Frama-C:
 frama-c-gui -c11 dyn_alloc.c -wp -wp-rte -wp-timeout 30 -wp-time-extra 8 -wp-prover altergo,cvc4,cvc4-ce -wp-smoke-tests -wp-prop="-@lemma"
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

typedef struct CONTEXT {
  int placeholder_int;
  NODE_T *rsrc_list;    
} CONTEXT;
/*@
  predicate ctx_sep_from_list(CONTEXT *ctx, \list<NODE_T*> ll) =  
    \forall integer i; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), ctx);
        
  predicate sep_from_list{L}(CONTEXT * ctx, NODE_T ** node) = 
    ctx_sep_from_list(ctx, to_ll{L}(ctx->rsrc_list, NULL))
    && dptr_sep_from_list(node, to_ll{L}(ctx->rsrc_list, NULL));
*/

/*@
  requires \valid(ctx);
  requires ctx->rsrc_list != NULL ==> \valid(ctx->rsrc_list);
  requires linked_ll(ctx->rsrc_list, NULL, to_ll(ctx->rsrc_list, NULL));
  requires sep_from_list(ctx, out_node);
  requires ptr_sep_from_list(*out_node, to_ll(ctx->rsrc_list, NULL));
  requires !(in_list_handle(esys_handle, to_ll(ctx->rsrc_list, NULL)));
  requires \valid(out_node) && \separated(ctx, out_node);
  requires *out_node != NULL ==> \valid(*out_node) && (*out_node)->next == NULL;
  
  assigns ctx->rsrc_list, *out_node;
  assigns (\nth(to_ll{Post}(\at(ctx->rsrc_list, Post), NULL), 0) )->handle;
  assigns (\nth(to_ll{Post}(\at(ctx->rsrc_list, Post), NULL), 0))->next;
  
  ensures sep_from_list(ctx, out_node);  
  ensures unchanged_ll{Pre, Post}(to_ll{Pre}(\old(ctx->rsrc_list), NULL));
  ensures \result \in {1610, 833};
  
  ensures \result == 833 ==>  \valid(ctx);
  ensures \result == 833 ==>  !(in_list_handle(esys_handle, to_ll(ctx->rsrc_list, NULL)));
  ensures \result == 833 ==>  ctx->rsrc_list == \old(ctx->rsrc_list);
  ensures \result == 833 ==>  *out_node == \old(*out_node);
  ensures \result == 833 ==>  unchanged_ll{Pre, Post}(to_ll(ctx->rsrc_list, NULL));

  ensures \result == 1610 ==> *\at(*out_node, Post) == *\at(ctx->rsrc_list, Post);
  ensures \result == 1610 ==> in_list_handle(esys_handle, to_ll(ctx->rsrc_list, NULL));
  ensures \result == 1610 ==> \valid(ctx->rsrc_list) && *out_node == ctx->rsrc_list;
  ensures \result == 1610 ==> ctx->rsrc_list->handle == esys_handle;
  ensures \result == 1610 ==> ctx->rsrc_list->next == \old(ctx->rsrc_list);
  ensures \result == 1610 ==> linked_ll(ctx->rsrc_list, NULL, to_ll(ctx->rsrc_list, NULL));
  ensures \result == 1610 ==> unchanged_ll{Pre, Post}(to_ll(\old(ctx->rsrc_list), NULL));
  ensures \result == 1610 ==> \old(ctx->rsrc_list) != NULL ==>
                                \nth(to_ll(ctx->rsrc_list, NULL), 1) == 
                                \old(ctx->rsrc_list);
*/
int createNode(CONTEXT * ctx, uint32_t esys_handle, 
               NODE_T ** out_node){
//@ ghost pre_calloc:;
  //@ghost int if_id = 0;
  NODE_T *new_head = calloc(1, sizeof(NODE_T));
  /*@ assert \valid(new_head) ==> new_head->next == \null;*/
  
  if (new_head == NULL){return 833;}
  /*@ assert unchanged_ll{Pre, Here}(
             to_ll{Here}(ctx->rsrc_list, NULL));*/
  //@ ghost pre_if:;
  if (ctx->rsrc_list == NULL) {
    /* The first object of the list will be added */
    ctx->rsrc_list = new_head;
    /*@ assert unchanged_ll{pre_if, Here}(to_ll(new_head, NULL));*/
    /*@ assert to_ll(new_head, NULL) == [|new_head|];*/  
    /*@ assert \separated(new_head, new_head->next);*/
    new_head->next = NULL;
    /*@ assert to_ll(new_head, NULL) == [|new_head|];*/  
  } 
  else {
    /* The new object will become the first element of the list */
    /*@ assert dptr_sep_from_list(&ctx->rsrc_list, 
                                  to_ll(ctx->rsrc_list, NULL));*/
    new_head->next = ctx->rsrc_list;
    //@ ghost post_assign:;
    /*@ assert unchanged_ll{pre_if, Here}(to_ll{pre_if}(ctx->rsrc_list, NULL));*/  
    /*@ assert to_ll(new_head, NULL) == 
              ([|new_head|] ^ to_ll(\at(ctx->rsrc_list, pre_if), NULL));*/
    /*@ assert dptr_sep_from_list(&ctx->rsrc_list, to_ll(new_head, NULL));*/
    ctx->rsrc_list = new_head;
    /*@ assert unchanged_ll{post_assign, Here}(to_ll{post_assign}(new_head, NULL));*/
    /*@ assert ctx->rsrc_list->next == \at(ctx->rsrc_list, Pre);*/
    /*@ assert to_ll(ctx->rsrc_list, NULL) == 
              ([|new_head|] ^ to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
  }
  //@ ghost post_add:;
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
  /*@ assert unchanged_ll{Pre, Here}(to_ll{Pre}(\at(ctx->rsrc_list, Pre), NULL));*/
  return 1610;
}
