Add Rec LoadPath "../src/" as Exploit.  
Add ML Path "../src/". 

Require Evm_compute. 
Require Import ZArith. 

(* factorisation as an example of non-trivial computation *)

Section fold. 
  Variable A : Type. 
  Variable f : Z -> A -> A. 
  Fixpoint fold n acc:= match n with 
                          | 0 => acc
                          | S k => fold k (f (Z.of_nat k) acc)
                        end. 
End fold. 


Open Scope Z_scope. 

Definition divide x y :=
  Z.modulo x y =? 0 . 

Definition try n z acc :=
  match acc with 
    | None => 
      if z <? 2 then 
        None 
      else if divide n z then 
             Some (z,Z.div n z)
           else None
    | Some x => acc
  end. 


Definition factor n :=
  match fold _ (try (Z.of_nat n)) n None with 
    | Some x => x
    | None => (Z.of_nat n,1)
  end.
   
Eval compute in factor 9. 
  
Remark factorisable :  forall x:nat, (let (a,b) := factor x in (a * b)%Z) = Z.of_nat x.
Admitted. 

Definition k : nat := 1111%nat. Definition ka := 101. Definition kb := 11. 

Require Import String. 

Check ("evm_compute without witnesses")%string. 
Goal exists e1 e2, Z.of_nat k = e1 * e2. 
intros. eexists. eexists.
rewrite <- factorisable. 
Time evm blacklist [Zmult;].   reflexivity.  
Time Qed. 

Check ("vm_compute with witnesses")%string. 
Goal exists e1 e2, Z.of_nat k = e1 * e2. 
intros.  exists ka. exists kb. 
Time vm_compute; reflexivity. 
Time Qed. 

Check ("cbv with witnesses")%string. 
Goal exists e1 e2, Z.of_nat k = e1 * e2. 
intros.  exists ka.  exists kb. 
Time cbv; reflexivity. 
Time Qed. 


(* it works even if there are lets in the hyps *)
Goal exists e1 e2, Z.of_nat k = e1 * e2. 
intros. eexists.   eexists.
 match goal with |- _ = ?x * ?y => 
                 let Hx := fresh in
                 let Hy := fresh in 
                 set (Hx:=x);
                 set (Hy:=y) end.  
(* Fail vm_compute. *)
rewrite <- factorisable. 
evm blacklist [Zmult]. 
unfold H, H0. reflexivity. 
Qed. 



(* An example of a proof that blows up at Qed time, because the proof term does not provide enough information *)
(* 
Check ("cbv without witnesses")%string. 
Goal exists e1 e2, Z.of_nat k = e1 * e2. 
intros. eexists. eexists.
rewrite <- factorisable. 
set (f :=Z.mul).  
Time cbv - [f]; unfold f;  reflexivity. (* 4 s *)
Time Qed.                               (* 154 s !! *)
*)

Fixpoint nexists n P :=
  match n with 
    | 0 => P 
    | S n => exists x, nexists n (P /\ x = 1)
  end%nat. 

Check ("cbv with witnesses")%string. 
Goal exists e1 e2, nexists 10  (Z.of_nat k = e1 * e2).
unfold nexists; do 12 eexists.    
rewrite <- (factorisable). 
evm blacklist [Zmult].
repeat split. 
Time Qed. 

