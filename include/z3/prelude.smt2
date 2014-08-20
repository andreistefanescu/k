; int extra
(define-fun int_max ((x Int) (y Int)) Int (ite (< x y) y x))
(define-fun int_min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun int_abs ((x Int)) Int (ite (< x 0) (- 0 x) x))

; sets as arrays
(define-sort IntSet () (Array Int Bool))
(define-fun smt_set_mem ((x Int) (s IntSet)) Bool (select s x))
(define-fun smt_set_add ((s IntSet) (x Int)) IntSet  (store s x true))
(define-fun smt_set_emp () IntSet ((as const IntSet) false))
(define-fun smt_set_cup ((s1 IntSet) (s2 IntSet)) IntSet ((_ map or) s1 s2))
(define-fun smt_set_cap ((s1 IntSet) (s2 IntSet)) IntSet ((_ map and) s1 s2))
(define-fun smt_set_com ((s IntSet)) IntSet ((_ map not) s))
(define-fun smt_set_sin ((x Int)) IntSet (smt_set_add smt_set_emp x))
(define-fun smt_set_dif ((s1 IntSet) (s2 IntSet)) IntSet (smt_set_cap s1 (smt_set_com s2)))
(define-fun smt_set_sub ((s1 IntSet) (s2 IntSet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))
(define-fun smt_set_lt  ((s1 IntSet) (s2 IntSet)) Bool (forall ((i Int) (j Int)) (implies (>= i j) (not (and (select s1 i) (select s2 j))))))
(define-fun smt_set_le  ((s1 IntSet) (s2 IntSet)) Bool (forall ((i Int) (j Int)) (implies (>  i j) (not (and (select s1 i) (select s2 j))))))

; data structures (should be generated automatically from K)
(declare-datatypes () ((Tree leaf (node (key Int) (left Tree) (right Tree)))))
(declare-fun smt_tree_keys ((Tree)) IntSet)
(declare-fun smt_tree_height ((Tree)) Int)
(declare-fun smt_bst ((Tree)) Bool)
(declare-fun smt_avl ((Tree)) Bool)

; lemmas as universally quantified formulae
(assert (forall ((t Tree)) (! (>= (smt_tree_height t) 0) :pattern((smt_tree_height t)))))

