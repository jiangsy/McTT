From Coq Require Import String.

(** * Concrete Syntax Tree *)
Inductive obj : Set :=
| cst_typ : nat -> obj
| cst_nat : obj
| cst_zero : obj
| cst_succ : obj -> obj
| cst_natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj
| cst_pi : string -> obj -> obj -> obj
| cst_fn : string -> obj -> obj -> obj
| cst_app : obj -> obj -> obj
| cst_prop_eq : obj -> obj -> obj -> obj
| cst_refl : obj -> obj -> obj
| cst_eqrec : obj ->                            (** A : eq domain type *)
              string -> string -> string -> obj -> (** x y (z : Eq A x y). M *)
              string -> obj ->                   (** x. Pf : M[x/x, x/y, refl A x/z] *)
              obj -> obj -> obj -> obj
| cst_var : string -> obj.
