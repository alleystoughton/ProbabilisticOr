(* Lower Bound Proof for Adaptive Probabilistic Or *)

require import AllCore Distr DBool DInterval List StdOrder.
import RealOrder.

(* number of arguments to or function *)

op arity : {int | 1 <= arity} as ge1_arity.

(* number of allowed queries *)

op nq  : {int | 0 <= nq} as ge0_nq.   

(* module type of algorithms

   algorithms can have persistent local state and can be probabilistic *)

module type ALG = {
  (* initialization *)

  proc init() : unit

  (* issue a query i, an integer between 0 and n - 1, representing
     the ith (counting from 0) argument to the or function *)

  proc query() : int

  (* give the algorithm the boolean answer to its query *)

  proc answer(a : bool) : unit

  (* ask the algorithm to predict the result of the or function *)

  proc result() : bool
}.

(* relative to a uniformly randomly chosen l in the range 0 to
   arity - 1, and a uniformly random boolean b, answers the query i: *)

op answer (l : int, b : bool, i : int) : bool =
  if i = l then b else false.

(* lower bound game

   parameterized by an algorithm, Alg *)

module GOr(Alg : ALG) = {
  proc main() : bool = {
    var i : int <- 0;
    var qry : int;
    var l : int;
    var b, b', a : bool;
    (* choose the two random parameters, used to answer queries *)
    l <$ [0 .. arity - 1];
    b <$ {0,1};
    (* initialize the algorithm *)
    Alg.init();
    (* let algorithm adaptively issue its nq queries *)
    while (i < nq) {
      (* ask algorithm to issue its next query *)
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {  (* qry is 0, if out of range *)
        qry <- 0;
      }
      (* give algorithm answer to its query *)
      Alg.answer(answer l b qry);
      i <- i + 1;
    }
    (* ask the algorithm to predict result of or function *)
    b' <@ Alg.result();
    (* returns whether the algorithm won, i.e., correctly
       predicated the answer *)
    return b' = b;
  }
}.

(* Below, we prove this lemma

     lemma GOr_bound (Alg <: ALG) &m :
       islossless Alg.query => islossless Alg.answer =>
       islossless Alg.result =>
       Pr[GOr(Alg).main() @ &m : res] <= 1%r / 2%r + nq%r / (arity * 2)%r.

   saying that, for all algorithms Alg whose procedures always
   terminate with probability 1%r, the probability that Alg wins the
   lower bound game is no more than

     1%r / 2%r + nq%r / (arity * 2)%r

   (exp%r means to treat the integer expression exp as a real number)

   E.g., if we set arity = 100 and nq = 79, then

     1%r / 2%r + nq%r / (arity * 2)%r

   is 0.895

   Thus, when arity = 100, any algorithm that wins the lower bound game
   90% of the time needs must ask at least 80 queries

   More generally, we can conclude that any algorithm that returns the
   correct answer at least 90% of the time must ask at least 80
   queries *)

section.

declare module Alg <: ALG.

(* we assume Alg's procedures terminate with probability 1%r
   no matter what their arguments or current states are *)

declare axiom Alg_init_ll : islossless Alg.init.
declare axiom Alg_query_ll : islossless Alg.query.
declare axiom Alg_answer_ll : islossless Alg.answer.
declare axiom Alg_result_ll : islossless Alg.result.

(* G1 is like GOr, except instrumented to detect a bad event:
   at some stage of the loop, when b is true, algorithm queries l *)

local module G1 = {
  var bad : bool

  proc main() : bool = {
    var i : int <- 0;
    var qry : int;
    var l : int;
    var b, b', a : bool;
    l <$ [0 .. arity - 1];
    b <$ {0,1};
    bad <- false;
    Alg.init();
    while (i < nq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      bad <- bad \/ qry = l /\ b;
      Alg.answer(answer l b qry);
      i <- i + 1;
    }
    b' <@ Alg.result();
    return b' = b;
  }
}.

local lemma GOr_G1 &m :
  Pr[GOr(Alg).main() @ &m : res] = Pr[G1.main() @ &m : res].
proof. byequiv => //; sim. qed.

(* like G1, except all query answers are false *)

local module G2 = {
  var bad : bool

  proc main() : bool = {
    var i : int <- 0;
    var qry : int;
    var l : int;
    var b, b', a : bool;
    l <$ [0 .. arity - 1];
    b <$ {0,1};
    bad <- false;
    Alg.init();
    while (i < nq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      bad <- bad \/ qry = l /\ b;
      Alg.answer(false);  (* note *)
      i <- i + 1;
    }
    b' <@ Alg.result();
    return b' = b;
  }
}.

(* we use up to bad reasoning, to connect G1 and G2 *)

local lemma G1_G2_equiv :
  equiv[G1.main ~ G2.main :
        ={glob Alg} ==>
        ={bad}(G1, G2) /\ (! G1.bad{1} => ={res})].
proof.
proc.
seq 5 5 :
  (={i, l, b, glob Alg} /\ ={bad}(G1, G2) /\
   i{1} = 0 /\ ! G1.bad{1}); first call (_ : true); auto.
call
  (_ :
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg}) ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={res})).
proc
  (G2.bad)
  (={bad}(G1, G2))
  (G1.bad{1}); first 2 smt().
apply Alg_result_ll.
while (={i, l, b} /\ ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg})).
seq 2 2 :
  (={i, l, b} /\ ={bad}(G1, G2) /\ (! G1.bad{1} => ={qry, glob Alg})).
wp.
call
  (_ :
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg}) ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={res, glob Alg})).
proc
  (G2.bad)
  (={bad}(G1, G2))
  (G1.bad{1}); first 2 smt().
apply Alg_query_ll.
auto; smt().
sp; elim* => bad_R bad_L; wp.
call
  (_ :
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={a, glob Alg}) ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg})).
proc
  (G2.bad)
  (={bad}(G1, G2))
  (G1.bad{1}); first 2 smt().
apply Alg_answer_ll.
(* smt can prove that the answer is false in G1 when
   the bad event is false *)
auto; smt().
auto; smt().
qed.

(* G2' is like G2 except the while loop simply collects the queries,
   and after the loop, bad is set based on b and the relationship
   between the queries and l *)

local module G2' = {
  var bad : bool

  proc main() : bool = {
    var i : int <- 0;
    var qry : int;
    var l : int;
    var b, b', a : bool;
    var qrys : int list <- [];
    l <$ [0 .. arity - 1];
    b <$ {0,1};
    Alg.init();
    while (i < nq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      qrys <- qrys ++ [qry];
      Alg.answer(false);
      i <- i + 1;
    }
    bad <- l \in qrys /\ b;
    b' <@ Alg.result();
    return b' = b;
  }
}.

(* G2 and G2' are equivalent in terms of whether they set the
   bad event *)

local lemma G2_G2'_bad &m :
  Pr[G2.main() @ &m : G2.bad] = Pr[G2'.main() @ &m : G2'.bad].
proof.
byequiv => //.
proc.
seq 5 5 :
  (={i, l, b, glob Alg} /\ i{1} = 0 /\
   ! G2.bad{1} /\ qrys{2} = []); first call (_ : true); auto.
call (_ : true); first auto.
while
  (={i, l, b, glob Alg} /\ 0 <= i{2} <= nq /\ size qrys{2} = i{2} /\
   (G2.bad{1} <=> l{2} \in qrys{2} /\ b{2})).
wp.
call (_ : true).
wp.
call (_ : true).
auto; smt(size_cat mem_cat).
auto; smt(ge0_nq).
qed.

(* bound the probability of failure in G2' (not clear how to do
   this directly on G2) *)

lemma count_mem_uniq_le_size_of_mem (xs ys : 'a list) :
  uniq ys => count (mem xs) ys <= size xs.
proof.
move => uniq_ys.
have -> : mem xs = mem (undup xs).
  apply fun_ext => y; by rewrite mem_undup.
rewrite count_swap // 1:undup_uniq.
rewrite (lez_trans (size (undup xs))) 1:count_size size_undup.
qed.

local lemma G2'_bad &m :
  Pr[G2'.main() @ &m : G2'.bad] <= nq%r / (arity * 2)%r.
proof.
byphoare => //.
proc.
swap 7 1; wp.
swap [3..4] 3.
seq 5 :
  (size qrys = nq)
  1%r
  (nq%r / (arity * 2)%r)
  0%r
  0%r => //.
seq 1 :
  (l \in qrys)
  (nq%r / arity%r)
  (1%r / 2%r)
  1%r
  0%r => //.
rnd.
auto; progress.
rewrite dinterE /= lez_maxr 1:(lez_trans 1) // 1:ge1_arity ler_pmul2r.
rewrite invr_gt0 lt_fromint ltzE ge1_arity.
rewrite le_fromint -H size_filter count_mem_uniq_le_size_of_mem range_uniq.
rnd (pred1 true).
auto; progress.
rewrite dbool1E /#.
smt().
hoare.
rnd.
auto => />.
smt().
hoare.
call (_ : true).
while (i <= nq /\ size qrys = i).
wp.
call (_ : true).
wp.
call (_ : true).
auto; progress.
smt().
by rewrite cats1 size_rcons.
smt().
by rewrite cats1 size_rcons.
call (_ : true).
auto; progress.
smt(ge0_nq).
smt().
qed.

(* bound the probability of failure in G2 *)

local lemma G2_bad &m :
  Pr[G2.main() @ &m : G2.bad] <= nq%r / (arity * 2)%r.
proof.
rewrite (G2_G2'_bad &m) (G2'_bad &m).
qed.

local lemma G1_G2 &m :
  `|Pr[G1.main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
  nq%r / (arity * 2)%r.
proof.
rewrite (ler_trans Pr[G2.main() @ &m : G2.bad]).
byequiv
  (_ :
   ={glob Alg} ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={res})) :
  G1.bad => //.
apply G1_G2_equiv.
smt().
apply (G2_bad &m).
qed.

local lemma GOr_G2 &m :
  `|Pr[GOr(Alg).main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
  nq%r / (arity * 2)%r.
proof.
rewrite (GOr_G1 &m) (G1_G2 &m).
qed.

(* like G2, except bad event removed *)

local module G3 = {
  proc main() : bool = {
    var i : int <- 0;
    var qry : int;
    var l : int;
    var b, b', a : bool;
    l <$ [0 .. arity - 1];
    b <$ {0,1};
    Alg.init();
    while (i < nq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      Alg.answer(false);
      i <- i + 1;
    }
    b' <@ Alg.result();
    return b' = b;
  }
}.

local lemma G2_G3 &m :
  Pr[G2.main() @ &m : res] = Pr[G3.main() @ &m : res].
proof. byequiv => //; sim. qed.

local lemma GOr_G3 &m :
  `|Pr[GOr(Alg).main() @ &m : res] - Pr[G3.main() @ &m : res]| <=
  nq%r / (arity * 2)%r.
proof.
rewrite -(G2_G3 &m) (GOr_G2 &m).
qed.

(* the algorithm wins G3 exactly half the time *)

local lemma G3_prob &m :
  Pr[G3.main() @ &m : res] = 1%r / 2%r.
proof.
byphoare => //.
proc.
swap 3 3.
swap 2 3.
rnd (pred1 b').
rnd.
call (_ : true).
apply Alg_result_ll.
while (i <= nq) (nq - i).
move => z.
wp.
call (_ : true).
apply Alg_answer_ll.
wp.
call (_ : true).
apply Alg_query_ll.
auto; smt().
call Alg_init_ll.
auto; progress.
smt(ge0_nq).
smt().
rewrite dbool1E /#.
smt().
rewrite weight_dinter.
smt(ge1_arity).
qed.

lemma GOr_close_bound &m :
  `|Pr[GOr(Alg).main() @ &m : res] - 1%r / 2%r| <=
  nq%r / (arity * 2)%r.
proof.
rewrite -(G3_prob &m) (GOr_G3 &m).
qed.

end section.

lemma GOr_close_to_half_bound (Alg <: ALG) &m :
  islossless Alg.init => islossless Alg.query =>
  islossless Alg.answer => islossless Alg.result =>
  `|Pr[GOr(Alg).main() @ &m : res] - 1%r / 2%r| <=
  nq%r / (arity * 2)%r.
proof.
move => Alg_init_ll Alg_query_ll Alg_answer_ll Alg_result_ll.
apply (GOr_close_bound Alg _ _ _ _ &m).
apply Alg_init_ll.
apply Alg_query_ll.
apply Alg_answer_ll.
apply Alg_result_ll.
qed.

lemma GOr_bound (Alg <: ALG) &m :
  islossless Alg.init => islossless Alg.query =>
  islossless Alg.answer => islossless Alg.result =>
  Pr[GOr(Alg).main() @ &m : res] <=
  1%r / 2%r + nq%r / (arity * 2)%r.
proof.
move => Alg_init_ll Alg_query_ll Alg_answer_ll Alg_result_ll.
have close_bnd := GOr_close_to_half_bound Alg &m _ _ _ _.
  apply Alg_init_ll. apply Alg_query_ll.
  apply Alg_answer_ll. apply Alg_result_ll.
have ge0_pr : 0%r <= Pr[GOr(Alg).main() @ &m : res] by rewrite Pr [mu_ge0].
have ge0_half : 0%r <= 1%r / 2%r by rewrite divr_ge0.
smt().
qed.
