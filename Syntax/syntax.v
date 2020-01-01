From Coq Require Import Strings.String.

Inductive ty : Type :=
  | Bool  : ty
  | Nat   : ty
  | List  : ty -> ty
  | Arrow : ty -> ty -> ty
  | String : ty.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | not : tm -> tm
  | and : tm -> tm
  (* basic STLC *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  (* numbers *)
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm
  (* arithmatic operations *)
  | pls : tm -> tm -> tm
  | mns : tm -> tm -> tm
  | mlt : tm -> tm -> tm
  (* pairs *)
  | pair : tm -> tm -> tm
  | fst : tm -> tm
  | snd : tm -> tm
  (* lists *)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  (* unit *)
  | unit : tm
  (* let *)
  | tlet : string -> tm -> tm -> tm
  (* i.e., [let x = t1 in t2] *).

Check Bool.
Check (tru).
Check (const 5).
Check not tru.
