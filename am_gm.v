Require Import ssreflect ssrnat ssrbool.
Require Import bigop.

Definition sq x := x * x.

Theorem am_ge_gm' (f:nat->nat) (n:nat): sq (\sum_(0 <= i < n ) (f i) ) >= n * n * \prod_(0 <= i < n) (f i) .
Proof.

  