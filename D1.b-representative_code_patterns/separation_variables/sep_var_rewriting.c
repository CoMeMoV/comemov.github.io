#include <stdlib.h>

typedef struct LIST {
    int handle;
    struct LIST * next;
} LIST;

/**** Logic definitions from the "Logic against Ghosts" paper (modulo renaming for node_to_ll) ****/

/*@
  predicate ptr_separated_from_range{L}
    (LIST* e, \list<LIST*> ll, integer beg, integer end) =
    \forall integer n ; 0 <= beg <= n < end <= \length(ll) ==> \separated(\nth(ll, n), e);

  predicate dptr_separated_from_range{L}
    (LIST** e, \list<LIST*> ll, integer beg, integer end) =
    \forall integer n ; 0 <= beg <= n < end <= \length(ll) ==> \separated(\nth(ll, n), e);

  predicate ptr_separated_from_list{L}(LIST* e, \list<LIST*> ll) =
    ptr_separated_from_range(e, ll, 0, \length(ll));

  predicate dptr_separated_from_list{L}(LIST** e, \list<LIST*> ll) =
    dptr_separated_from_range(e, ll, 0, \length(ll));
*/

/*@
  predicate in_list{L}(LIST* e, \list<LIST*> ll) =
    \exists integer n ; 0 <= n < \length(ll) && \nth(ll, n) == e ;
*/

/*@ 
  inductive linked_ll{L}(LIST *bl, LIST *el, \list<LIST*> ll) {
  case linked_ll_nil{L}:
    \forall LIST *el ; linked_ll{L}(el, el, \Nil);
  case linked_ll_cons{L}:
    \forall LIST *bl, *el, \list<LIST*> tail ;
      \separated(bl, el) ==> \valid(bl) ==>
      linked_ll{L}(bl->next, el, tail) ==>
      ptr_separated_from_list(bl, tail) ==>
        linked_ll{L}(bl, el, \Cons(bl, tail)) ;
  }
*/

/*@ 
  axiomatic Node_To_ll {
    logic \list<LIST*> node_to_ll{L}(LIST* beg_node, LIST* end_node) 
      reads { node->next | LIST* node ; \valid(node) && in_list(node, node_to_ll(beg_node, end_node)) } ;
    
    axiom to_ll_nil{L}:
      \forall LIST *node ; node_to_ll{L}(node, node) == \Nil ;
      
    axiom to_ll_cons{L}:
      \forall LIST *beg_node, *end_node ;
        \separated(beg_node, end_node) ==>
        \valid{L}(beg_node) ==>
    ptr_separated_from_list{L}(beg_node, node_to_ll{L}(beg_node->next, end_node)) ==>
          node_to_ll{L}(beg_node, end_node) == (\Cons(beg_node, node_to_ll{L}(beg_node->next, end_node))) ;
  }
*/                   

/*******************************************************************/


/*@
  requires node_separation_to_list : foo(rsrc_list,out_node) ; //dptr_separated_from_list(out_node, node_to_ll(rsrc_list, NULL)); //if uncommented, linked_assert cannot be proved
  assigns \nothing;
  ensures \result == 616;
*/
int dummyCallee(LIST * rsrc_list, LIST ** out_node);

/*@
  requires  linked_ll(rsrc_list, NULL, node_to_ll(rsrc_list, NULL));
  assigns \nothing; 
  ensures \result == 616;
*/
int dummyCaller(LIST * rsrc_list, LIST ** out_node)
{
  /*@ assert linked_assert : linked_ll(rsrc_list, NULL, node_to_ll(rsrc_list, NULL));*/   
    // Proved
   int r;
  {
    LIST *test_node = NULL;
    r = dummyCallee(rsrc_list, &test_node);
  }
  return r ;
} 