Add Rec LoadPath "../src/" as evm_compute.
Add ML Path "../src/". 

Require Import Evm_compute. 

Goal 1 + 2 * 3 = 7.
  evm computed_blacklist [ (Bcons _ mult (Bcons _ plus Bnil)) ].
  match goal with
    | [ |- ?X = ?X ] => fail 100
    | [ |- _ ] => reflexivity
  end.
Qed.