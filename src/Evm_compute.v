Declare ML Module "evm_compute".

(* Support for dynamic black lists, ie, lists of terms. *)
Inductive Blacklist : Type :=
| Bnil : Blacklist
| Bcons : forall T, T -> Blacklist -> Blacklist.