From Coq Require Import Strings.String.

Inductive ty : Type :=
  | Top   : ty
  | Bool  : ty
  | Nat   : ty
  | List  : ty -> ty
  | Arrow : ty -> ty -> ty
  | IterNil : ty
  | IterCons : ty -> ty -> ty.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test0 : tm -> tm -> tm -> tm
  | test : tm -> tm -> tm -> tm

  (* Basic STLC *)
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

  (* iterator *)
  | iterNil :  tm
  | iterCons : tm -> tm -> tm
  | iterHead : tm -> tm

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
      test0 ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)

  (* Basic STLC *)
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)

  (* boolean operation *)
  | BEq t1 t2 => BEq ([x:=s] t1) ([x:=s] t2)
  | BGe t1 t2 => BGe ([x:=s] t1) ([x:=s] t2)
  | BNot t1 => BNot ([x:=s] t1)
  | BAnd t1 t2 => BAnd ([x:=s] t1) ([x:=s] t2)

  (* chaining comparison *)
  | CBGe t1 t2 t3 =>
      CBGe ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | Ctest t1 t2 t3 t4 t5 =>
      Ctest ([x:=s] t1) ([x:=s] t2) ([x:=s] t3) ([x:=s] t4) ([x:=s] t5)

  (* generator *)
  | gen t1 t2 => gen ([x:=s] t1) ([x:=s] t2)
  | genob t1 => genob ([x:=s] t1)
  | next t1 => next ([x:=s] t1)

  (* numbers *)
  | const n =>
      const n
  | scc t1 =>
      scc ([x:=s] t1)
  | prd t1 =>
      prd ([x:=s] t1)

  (* lists *)
  | tnil T => tnil T
  | tcons t1 t2 => tcons ([x:=s] t1) ([x:=s] t2)
  | LHead t1 => LHead ([x:=s] t1)

  (* iterator *)
  | iterNil => iterNil
  | iterCons t1 t2 => iterCons ([x:=s] t1) ([x:=s] t2)
  | iterHead t1 => iterHead ([x:=s] t1)

  | tfix t1 => tfix ([x:=s] t1)

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
      value (tcons v1 vl)

  (* Iterator values: *)
  | v_iternil : value iterNil
  | v_itercons : forall v vr,
      value v ->
      value vr ->
      value (iterCons v vr).

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

  (* Test nat *)
  | ST_Test1 : forall t1 t1' t2 t3,
       t1 --> t1' ->
       test0 t1 t2 t3 --> test0 t1' t2 t3
  | ST_TestZero : forall t2 t3,
       (test0 (const 0) t2 t3) --> t2
  | ST_TestNonzero : forall n t2 t3,
       (test0 (const (S n)) t2 t3) --> t3
  
  (* Test bool *)
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
  | ST_CBGeVal2: forall v1 v2 t3 t3',
                value v1 ->
                value v2 ->
                t3 --> t3' ->
                CBGe v1 v2 t3 --> CBGe v1 v2 t3'
  | ST_CBGeConst: forall n1 n2 n3,
                  CBGe (const n1) (const n2) (const n3) --> 
                  BAnd(BGe (const n1) (const n2)) (BGe (const n2) (const n3))

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
                (tcons (var t2) (
                  (test0 (var t2)
                    (app (var f)(app (fls)(const 0)))
                    (app (var f)(app (tru) (prd (var t2) ) ) ) ) ) )
                (tnil Nat) ) ) ) )

  (* Generator Object *)
  | ST_Genob : forall t1 t1',
         t1 --> t1' ->
         genob t1 --> genob t1'
  | ST_GenobVal : forall v1,
         genob v1 --> iterCons v1 iterNil

 (* Next Call to Generator Object *)
  | ST_Next : forall t1 t1',
       t1 --> t1' ->
       next t1 --> next t1'
  | ST_NextVal : forall v1,
       next v1 --> iterHead (v1)

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

  (* Iterators *)
  | ST_IterCons1 : forall t1 t1' t2,
       t1 --> t1' ->
       (iterCons t1 t2) --> (iterCons t1' t2)
  | ST_IterCons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (iterCons v1 t2) --> (iterCons v1 t2')
  | ST_IterHead : forall t1 t1',
              t1 --> t1'->
              iterHead t1 --> iterHead t1'
  | ST_IterHeadVal : forall h1 l1,
              value h1->
              iterHead (iterCons h1 l1)--> h1


where "t1 '-->' t2" := (step t1 t2).

Definition total_map (A : Type) := string -> A.

Definition partial_map (A : Type) := total_map (option A).

Definition context := partial_map ty.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: Top
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      (Arrow S1 S2) <: (Arrow T1 T2)

  | S_ItrWidth0 : forall T1 T2,
    (IterCons T1 T2) <: IterNil

  | S_ItrWidth1 : forall S1 S2 T1 T2,
    S1 <: T1 ->
    S2 <: T2 ->
    (IterCons S1 S2) <: (IterCons T1 T2)

where "T '<:' U" := (subtype T U).


Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (var x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (update Gamma x T11) |- t12 \in T12 ->
      Gamma |- (abs x T11 t12) \in (Arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (Arrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (app t1 t2) \in T2

  (* numbers *)
  | T_Nat : forall Gamma n1,
      Gamma |- (const n1) \in Nat
  | T_Succ : forall Gamma t1,
      Gamma |- t1 \in Nat ->
      Gamma |- (scc t1) \in Nat
  | T_Pred : forall Gamma t1,
      Gamma |- t1 \in Nat ->
      Gamma |- (prd t1) \in Nat

  (* Boolean operation types *)
  | T_BBool : forall Gamma b1,
      Gamma |- (BBool b1) \in Bool
  | T_BEq : forall Gamma t1 t2 T,
      Gamma |- t1 \in T ->
      Gamma |- t2 \in T ->
      Gamma |- (BEq t1 t2) \in Bool
  | T_BGe : forall Gamma t1 t2 T,
      Gamma |- t1 \in T ->
      Gamma |- t2 \in T ->
      Gamma |- (BGe t1 t2) \in Bool
  | T_BNot : forall Gamma t1,
      Gamma |- t1 \in Bool ->
      Gamma |- (BNot t1) \in Bool
  | T_BAnd : forall Gamma t1 t2,
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in Bool ->
      Gamma |- (BAnd t1 t2) \in Bool

  | T_Test : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (test t1 t2 t3) \in T1
  | T_Test0 : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (test0 t1 t2 t3) \in T1

  (* chaining comparison *)
  | T_CBGe : forall Gamma t1 t2 t3,
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in Bool ->
      Gamma |- t3 \in Bool ->
      Gamma |- (CBGe t1 t2 t3) \in Bool
  | T_CTest : forall Gamma t1 t2 t3 t4 t5 T1,
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in Bool ->
      Gamma |- t3 \in Bool ->
      Gamma |- t4 \in T1 ->
      Gamma |- t5 \in T1 ->
      Gamma |- (Ctest t1 t2 t3 t4 t5) \in T1

  (* Iterator*)
  | Iter_Nil : forall Gamma,
      Gamma |- iterNil \in IterNil
  | T_IterCons : forall Gamma t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      Gamma |- (iterCons t tr) \in (IterCons T Tr)

  (* Generator Function*)  
  | T_Gen : forall Gamma t1 t2,
      Gamma |- t1 \in Bool ->
      Gamma |- t2 \in Nat ->
      Gamma |- (gen t1 t2) \in List Nat

  (* Generator Object*)
  | T_Genob : forall Gamma t1 T1,
      Gamma |- t1 \in List T1 ->
      Gamma |- genob t1 \in IterCons T1 IterNil

  (* next*)
  | T_Next : forall Gamma t1 T1 T2,
      Gamma |- t1 \in IterCons T1 T2 ->
      Gamma |- next t1 \in T1

  (* fix recursion*)
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 \in (Arrow T1 T1) ->
      Gamma |- tfix t1 \in T1

  (* lists *)
  | T_Nil : forall Gamma T,
      Gamma |- (tnil T) \in (List T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (List T1) ->
      Gamma |- (tcons t1 t2) \in (List T1)

  (* Subsumption Rule*)
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
