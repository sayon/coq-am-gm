From mathcomp.ssreflect Require Import all_ssreflect.

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