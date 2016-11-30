From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool bigop.

Load "fb_ind.v".
       
Theorem am_ge_gm' (n:nat): forall (f:nat->nat),
                             (\sum_(0 <= i < n ) (f i) )^n >= n^n * \prod_(0 <= i < n) (f i) .
Proof.
  move: n.
  
  apply (fb_ind (fun (n:nat) =>(forall (f:nat->nat), (\sum_(0 <= i < n ) (f i) )^n >= n^n * \prod_(0 <= i < n) (f i)))) =>//=.
  + (* P 0 *)
    move=> f.
    by rewrite !big_nil.

  + (* P 1 *)
    move=>f.
    rewrite !expnS expn0 !mul1n expn0 muln1.
    rewrite big_nat_recl //=. rewrite big_nil //=.
    rewrite big_nat_recl //=.
    by rewrite big_nil addn0 muln1.

  + (* P 2^i *)
    move => n Hind f.
    rewrite expnS.         
    rewrite mul2n -addnn.
    


    
    simpl.
    done.
    
    move=> f.
    rewrite mul1n.
    simpl.
    rewrite big_ltn.
    
    rewrite big_nat_recl.


  + (* P 0 *)
    by move=> ?.
  + (* P 1 *)
    move=> f. rewrite !mul1n.
    rewrite !big_nat1.
      by case (f 0); [| by move => ?; rewrite leq_pmulr].

  + (* P (2^n)*)
    move => n  H0 f.
    rewrite !expnS expn0 muln1.
    rewrite [X in _ * X<= _](@big_cat_nat _  _ _ (2^n)) //=.
    rewrite [X in _ <= X * _](@big_cat_nat _  _ _ (2^n)) //=.
    remember (\prod_(0 <= i < 2 ^ n) f i) as p0.
    rewrite [X in _ <= _ * X](@big_cat_nat _  _ _ (2^n)) //=.
    remember (\sum_(0 <= i < 2^n) f i) as s0.

    rewrite mul2n -addnn.
    rewrite -[X in \prod_(X <= _ < _ + _) _ _]add0n.
    rewrite -[X in \sum_(X <= _ < _ + _) _ _]add0n //=.

    rewrite !big_addn -addnBA //=.
    rewrite subnn addn0.

    remember (\prod_(0 <= i < 2 ^ n) f (i + 2 ^ n)) as p1.
    remember (\sum_(0  <= i < 2 ^ n) f (i + 2 ^ n)) as s1.

    rewrite (@leq_trans (s0^2 + s1^2)) //=.
    rewrite (@leq_trans (2^n * 2^n * (p0 + p1)^2)) //=.
    replace ((2^n + 2^n) * (2^n + 2^n)) with (2^n * 2^n * 4).
    rewrite mulnn.
    rewrite -mulnA.
    rewrite leq_mul2l.
    apply /orP. right.
      by apply nat_AGM2.
      
      ring.
      

    rewrite addnn -muln2.
    simpl.
    ring.
    
    rewrite -[X in _ <= X + _]mulnC -[X in _ <= _ + X]mulnC.
    rewrite -mulnDl.
    rewrite mulnCA.
      rewrite leq_mul //=.
      rewrite mulnC.
      by apply nat_AGM2.

      
      rewrite mulnD.
      rewrite leq_add.
      
      Search (_ + _ <= _ + _).
      

      (*Require Import ssralg.*)
(*Import GRing.*)
  (* Num.Theory de ssrnum *)
  (* big_cat_nat *)



