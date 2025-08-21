From Coq Require Import String.

(** * Concrete Syntax Tree *)
Module Cst.
  Inductive obj : Set :=
  | typ : nat -> obj
  | nat : obj
  | zero : obj
  | succ : obj -> obj
  | natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
  | pi : string -> obj -> obj -> obj
  | fn : string -> obj -> obj -> obj
  | app : obj -> obj -> obj
  | prop_eq : obj -> obj -> obj -> obj
  | refl : obj -> obj -> obj
  | eqrec : obj ->                 (** A : eq domain type *)
            string -> string -> string -> obj -> (** x y (z : Eq A x y). M *)
            string -> obj ->                   (** x. Pf : M[x/x, x/y, refl A x/z] *)
            obj -> obj -> obj -> obj
  | var : string -> obj.
End Cst.
