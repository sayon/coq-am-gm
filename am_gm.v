Require Import ssreflect ssrnat ssrbool bigop.

(*Require Import ssralg.*)
(*Import GRing.*)
  (* Num.Theory de ssrnum *)
  (* big_cat_nat *)

Lemma next_power_2 n: exists k, 2 ^ k > n.
  exists n.
  elim n => //=.
  move => m H.
  rewrite expnS (@leq_trans (2^m + 1));
    by [ | rewrite -add1n addnC leq_add2r | rewrite mul2n -addnn leq_add2l expn_gt0].
Qed.

Theorem fb_ind  (P: nat -> Prop): P 0 -> P 1 ->
                           (forall (n:nat), P (2^n) -> P(2^(n.+1))) ->
                           (forall (n:nat), P n.+1 -> P n) ->
                           (forall n, P n).
Proof.
  move=> H0 H1 Hdirect Hrev n.  
  have Hpowers: (forall m,  P (2^m)) by move=>m; elim m; [by rewrite expn0| ].
  have Hle: (forall x y i, P x -> y + i = x -> P y).
     move=> x y i.
     elim: i y x.
       + move => ? ? ?. by rewrite addn0 => ->.       
       + move => a H y [|x] Hpsx; rewrite addnS => //=.
         move /eq_add_S =>Hpx.
         by exact (H _ _ (Hrev _ Hpsx) Hpx).
  move : (next_power_2 n) => [p] Hp.
  apply (Hle (2^p) n (2^p-n)) => //=. rewrite addnBA.
       + by rewrite addnC addnK.
  rewrite -ltnS.
  by apply (@ltn_trans (2^p)).
Qed.
  



Definition sq x := x * x.
       
Theorem am_ge_gm' (n:nat): forall (f:nat->nat), sq (\sum_(0 <= i < n ) (f i) ) >= n * n * \prod_(0 <= i < n) (f i) .
Proof.
  move: n.
  apply (fb_ind (fun (n:nat) => (forall (f:nat->nat), n*n*  \prod_(0 <= i < n) f i <= sq (\sum_(0 <= i < n) f i)))).
    + by move=> ?.
    + move=> f. rewrite !mul1n.
      rewrite !big_nat1 /sq.
      by case (f 0); [| by move => ?; rewrite leq_pmulr].

    + move => n  H0 f. 
      rewrite expnS .


      rewrite (@big_cat_nat _  _ _ (2^n)) //=; last by (rewrite mul2n -addnn; apply leq_addr).
      rewrite [X in sq X](@big_cat_nat _  _ _ (2^n)) //=; last by (rewrite mul2n -addnn; apply leq_addr).
      rewrite !mul2n -addnn.



      