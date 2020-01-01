From Coq Require Import Strings.String.


Inductive ty : Type :=
  | Bool  : ty
  | Nat   : ty
  | List  : ty -> ty
  | Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test0 : tm -> tm -> tm -> tm
  | test : tm -> tm -> tm -> tm

  (* basic STLC *)
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm

  (* Boolean comparison *)
  | BBool : bool -> tm
  | BEq : tm -> tm -> tm
  | BGe : tm -> tm -> tm
  | BNot : tm -> tm
  | BAnd : tm -> tm -> tm

  (* Chaining comparison *)
  | CBGe : tm -> tm -> tm -> tm
  | Ctest : tm -> tm -> tm -> tm -> tm -> tm

  (* generator *)
  | gen : tm -> tm -> tm
  | genob : tm -> tm
  | next : tm -> tm

  (* numbers *)
  | const : nat -> tm
  | scc : tm -> tm
  | prd : tm -> tm

  (* lists *)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | LHead : tm -> tm

  (* fix *)
  | tfix  : tm -> tm.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Fixpoint beq_nat n m :=
  match n, m  with
    | O, O => true
    | O, _ => false
    | S n', O => false
    | S n', S m' => beq_nat n' m'
  end.

Fixpoint ble_nat n m  :=
  match n, m  with
    | O, _ => true
    | S n', O => false
    | S n', S m' => ble_nat n' m'
  end.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* boolean *)
  | tru => tru
  | fls => fls

  | test0 t1 t2 t3 =>
      test0 (subst x s t1) (subst x s t2) (subst x s t3)
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)

  (* pure STLC *)
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)

  (* boolean operation *)
  | BEq t1 t2 => BEq (subst x s t1) (subst x s t2)
  | BGe t1 t2 => BGe (subst x s t1) (subst x s t2)
  | BNot t1 => BNot (subst x s t1)
  | BAnd t1 t2 => BAnd (subst x s t1) (subst x s t2)

  (* chaining comparison *)
  | CBGe t1 t2 t3 => 
      CBGe (subst x s t1) (subst x s t2) (subst x s t3)
  | Ctest t1 t2 t3 t4 t5 =>
      Ctest (subst x s t1) (subst x s t2) (subst x s t3) (subst x s t4) (subst x s t5)

  (* generator *)
  | gen t1 t2 => gen (subst x s t1) (subst x s t2)
  | genob t1 => genob (subst x s t1)
  | next t1 => next (subst x s t1)

  (* numbers *)
  | const n =>
      const n
  | scc t1 =>
      scc (subst x s t1)
  | prd t1 =>
      prd (subst x s t1)

  (* lists *)
  | tnil T => tnil T
  | tcons t1 t2 => tcons (subst x s t1) (subst x s t2)
  | LHead t1 => LHead (subst x s t1)

  | tfix t1 => tfix (subst x s t1)

  (* unit *)
  | unit => unit
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive value : tm -> Prop :=
  (* basic pure STLC values*)
  | v_abs : forall x T11 t12,
      value (abs x T11 t12)

  (* Numbers are values: *)
  | v_nat : forall n1,
      value (const n1)

  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T, value (tnil T)
  | v_lcons : forall v1 vl,
      value v1 ->
      value vl ->
      value (tcons v1 vl).

Reserved Notation "t1 '-->' t2" (at level 40).
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1 t2')

  (* Test nat and Test bool *)
  | ST_Test1 : forall t1 t1' t2 t3,
       t1 --> t1' ->
       test0 t1 t2 t3 --> test0 t1' t2 t3
  | ST_TestZero : forall t2 t3,
       (test0 (const 0) t2 t3) --> t2
  | ST_TestNonzero : forall n t2 t3,
       (test0 (const (S n)) t2 t3) --> t3

  | ST_TestTru : forall t1 t2,
      test tru t1 t2 --> t1
  | ST_TestFls : forall t1 t2,
      test fls t1 t2 --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      test t1 t2 t3 --> test t1' t2 t3

  (* Boolean operations *)
  | ST_BEq : forall t1 t1' t2,
              t1 --> t1' ->
              BEq t1 t2 --> BEq t1' t2
  | ST_BEqNat : forall n1 n2,
              BEq (const n1) (const n2) --> BBool(beq_nat n1 n2)
  | ST_BEqString : forall s1 s2,
              (BEq (var s1) (var s2)) --> BBool(eqb_string s1 s2)
  | ST_BEqVal: forall v1 t2 t2',
                value v1 ->
                t2 --> t2' ->
                (BEq v1 t2) --> (BEq v1 t2')

  | ST_BGe : forall t1 t1' t2,
              t1 --> t1' ->
              BGe t1 t2 --> BGe t1' t2
  | ST_BGeVal: forall v1 t2 t2',
                value v1 ->
                t2 --> t2' ->
                (BGe v1 t2) --> (BGe v1 t2')
  | ST_BGeConst:  forall n1 n2,
                  BGe (const n1) (const n2) --> BBool(ble_nat n2 n1)


  | ST_BNot : forall t1 t1',
              t1 --> t1' ->
              BNot t1 --> BNot t1'
  | ST_BNotVal: forall b1,
                BNot (BBool b1) --> BBool(negb b1)

  | ST_BAnd : forall t1 t1' t2,
              t1 --> t1' ->
              BAnd t1 t2 --> BAnd t1' t2
  | ST_BAndBool: forall b1 b2,
                BAnd (BBool b1) (BBool b2) --> BBool(andb b1 b2)
  | ST_BAndVal: forall v1 t2 t2',
                value v1 ->
                t2 --> t2' ->
                BAnd v1 t2 --> BAnd v1 t2'


  (* chaining comparison *)
  | ST_CBGe : forall t1 t1' t2 t3,
              t1 --> t1' ->
              CBGe t1 t2 t3 --> CBGe t1' t2 t3
  | ST_CBGeVal1: forall v1 t2 t2' t3,
                value v1 ->
                t2 --> t2' ->
                CBGe v1 t2 t3 --> CBGe v1 t2' t3
  | ST_CBGeVal2: forall v1 v2 t2 t3 t3',
                value v1 ->
                value v2 ->
                t3 --> t3' ->
                CBGe v1 t2 t3 --> CBGe v1 t2 t3'
  | ST_CBGeConst: forall n1 n2 n3,
                  CBGe (const n1) (const n2) (const n3) --> BAnd(BGe (const n1) (const n2)) (BGe (const n2) (const n3))

  | ST_CTest : forall t1 t2 t3 t4 t5,
      Ctest t1 t2 t3 t4 t5 --> test (CBGe t1 t2 t3) t4 t5

  (* numbers *)
  | ST_Succ : forall t1 t1',
       t1 --> t1' ->
       (scc t1) --> (scc t1')
  | ST_SuccNat : forall n1,
       (scc (const n1)) --> (const (S n1))
  | ST_Pred : forall t1 t1',
       t1 --> t1' ->
       (prd t1) --> (prd t1')
  | ST_PredNat : forall n1,
       (prd (const n1)) --> (const (pred n1))


  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       (tcons t1 t2) --> (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (tcons v1 t2) --> (tcons v1 t2')
  | ST_Head : forall t1 t1',
              t1 --> t1'->
              LHead t1 --> LHead t1'
  | ST_HeadVal : forall h1 l1,
              value h1->
              LHead (tcons h1 l1)--> h1


  (* recursive functions *)
  | ST_Fix1 : forall t1 t1',
         t1 --> t1' ->
         (tfix t1) --> (tfix t1')
  | ST_FixAbs : forall y T t1,
         (tfix (abs y T t1)) --> [y:=(tfix (abs y T t1))]t1
  | ST_AppFunc : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12


  (* Generator *)
  | ST_Gen1 : forall t1 t1' t2,
              t1 --> t1' ->
              gen t1 t2 --> gen t1' t2

  | ST_Gen2 : forall v1 t2 t2',
              value v1 ->
              t2 --> t2' ->
              gen v1 t2 --> gen v1 t2'

  | ST_Gen : forall v1 v2 t1 t2 f,
       value v1 -> value v2 ->
       gen (abs t1 Bool v1) (abs t2 Nat v2) -->
       tfix
        (abs f (Arrow (Arrow Bool Nat) (List Nat) )
          (abs t1 Bool
            (abs t2 Nat
              (test (var t1)
                (tcons (var t2)(
                  (test0 (var t2)
                    (app (var f)(app (fls)(const 0)))
                    (app (var f)(app (tru) (prd (var t2)) )) ) ) )
                (tnil Nat) ) ) ) )

  (* Generator Object *)
  | ST_Genob : forall t1 t1',
         t1 --> t1' ->
         genob t1 --> genob t1'
  | ST_GenobVal : forall v1,
         genob v1 --> v1

 (* Next Call to Generator Object *)
  | ST_Next : forall t1 t1',
       t1 --> t1' ->
       next t1 --> next t1'
  | ST_NextVal : forall v1,
       next v1 --> LHead (v1)

where "t1 '-->' t2" := (step t1 t2).
