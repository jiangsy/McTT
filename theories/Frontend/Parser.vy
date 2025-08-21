%{

From Coq Require Import List Arith.PeanoNat String.

From Mctt.Frontend Require Export Cst.

Parameter loc : Type.

%}

%token <loc*string> VAR
%token <loc*nat> INT
%token <loc> END LAMBDA NAT PI REC RETURN SUCC TYPE ZERO LET IN REFL AS (* keywords *)
%token <loc> ARROW "->" AT "@" BAR "|" COLON ":" COMMA "," DARROW "=>" LPAREN "(" RPAREN ")" DOT "." DEF ":=" EQ "=" LANGLE "<" RANGLE ">" EOF (* symbols *)

%start <obj * obj> prog
%type <obj> obj eq_obj app_obj atomic_obj
%type <string * obj> param
%type <list (string * obj)> params
%type <string -> obj -> obj -> obj> fnbinder
%type <(string * obj) * obj> let_defn
%type <list ((string * obj) * obj)> let_defns
%type <unit> optional_as_nat

%on_error_reduce obj params eq_obj app_obj atomic_obj

%%

let prog :=
  exp = obj; ":"; typ = obj; EOF; <>

let fnbinder :=
  | PI; { cst_pi }
  | LAMBDA; { cst_fn }

let obj :=
  | ~ = fnbinder; ~ = params; "->"; ~ = obj; { List.fold_left (fun acc arg => fnbinder (fst arg) (snd arg) acc) params obj }
  | ~ = eq_obj; <>

  | REC; escr = obj; optional_as_nat; RETURN; mx = VAR; "."; em = obj;
    "|"; ZERO; "=>"; ez = obj;
    "|"; SUCC; sx = VAR; ","; sr = VAR; "=>"; es = obj;
    END; { cst_natrec escr (snd mx) em ez (snd sx) (snd sr) es }

  | REC; escr = obj; AS; "("; lhs = app_obj; "="; "<"; typ = obj; ">"; rhs = app_obj; ")"; RETURN; mx = VAR; my = VAR; mz = VAR; "."; em = obj;
    "|"; REFL; rx = VAR; "=>"; er = obj;
    END; { cst_eqrec escr (snd mx) (snd my) (snd mz) em (snd rx) er lhs typ rhs }

  | REFL; typ = atomic_obj; e = atomic_obj; { cst_refl typ e }

  | SUCC; ~ = atomic_obj; { cst_succ atomic_obj }
  
  | LET; ds = let_defns; IN; body = obj; { List.fold_left (fun acc arg => cst_app acc (snd arg)) (List.rev ds) (List.fold_left (fun acc arg => cst_fn (fst (fst arg)) (snd (fst arg)) acc) ds body) }

let eq_obj :=
  | lhs = app_obj; "="; "<"; typ = obj; ">"; rhs = app_obj; { cst_prop_eq lhs typ rhs }
  | ~ = app_obj; <>

let app_obj :=
  | ~ = app_obj; ~ = atomic_obj; { cst_app app_obj atomic_obj }
  | ~ = atomic_obj; <>

let atomic_obj :=
  | TYPE; "@"; n = INT; { cst_typ (snd n) }

  | NAT; { cst_nat }
  | ZERO; { cst_zero }
  | n = INT; { nat_rect (fun _ => obj) cst_zero (fun _ => cst_succ) (snd n) }

  | x = VAR; { cst_var (snd x) }

  | "("; ~ = obj; ")"; <>

(* Reversed nonempty list of parameters *)
let params :=
  | ~ = params; ~ = param; { param :: params }
  | ~ = param; { [param] }

(* (x : A) *)
let param :=
  | "("; x = VAR; ":"; ~ = obj; ")"; { (snd x, obj) }

(* Reversed nonempty list of definitions *)
let let_defns :=
  | ~ = let_defns; ~ = let_defn; { let_defn :: let_defns }
  | ~ = let_defn; { [let_defn] }

(* (x : A) := t *)
let let_defn :=
  | "("; ~ = param; ":="; ~ = obj; ")"; { (param, obj) }

let optional_as_nat :=
  | AS; NAT; { tt }
  | { tt }
%%

Extract Constant loc => "Lexing.position * Lexing.position".
