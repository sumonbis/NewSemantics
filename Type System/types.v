From Coq Require Import Strings.String.

Inductive ty : Type :=
  | Bool  : ty
  | Nat   : ty
  | String : ty
  | Sum : ty -> ty -> ty
  | List  : ty -> ty
  | Arrow : ty -> ty -> ty
  | Prod : ty -> ty -> ty.

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

  (* let *)
  | tlet : string -> tm -> tm -> tm

  (* fix *)
  | tfix  : tm -> tm

  (* generator *)
  | loop : tm -> tm -> tm -> tm
  | generator : tm -> tm -> tm
  | genob : tm -> tm
  | next : tm -> tm

  (* for-else *)
  | forelse : tm -> tm -> tm

  (* chaining comparison *)
  | chain : tm -> tm -> tm -> tm -> tm.


Check Bool.
Check (tru).
Check (const 5).
Check not tru.
Check forelse.

Definition u_test :=
  test
    (prd
      (scc
        (prd
          (mlt
            (const 2)
            (const 0)))))
    (const 5)
    (const 6).

Definition prod_test :=
  snd
    (fst
      (pair
        (pair
          (const 5)
          (const 6))
        (const 7))).

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)

  (* boolean *)
  | tru => tru
  | fls => fls

  (* numbers *)
  | const n =>
      const n
  | scc t1 =>
      scc (subst x s t1)
  | prd t1 =>
      prd (subst x s t1)
  | mlt t1 t2 =>
      mlt (subst x s t1) (subst x s t2)
  | pls t1 t2 =>
      pls (subst x s t1) (subst x s t2)
  | test t1 t2 t3 =>
      test (subst x s t1) (subst x s t2) (subst x s t3)

  (* chaining comparison *)
  | chain t1 t2 t3 t4 =>
      chain (subst x s t1) (subst x s t2) (subst x s t3) (subst x s t3)

  (* pair *)
  | pair t1 t2 => pair (subst x s t1) (subst x s t2)
  | fst t1 => fst (subst x s t1)
  | snd t1 => snd (subst x s t1)

  (* lists *)
  | tnil T => tnil T
  | tcons t1 t2 =>
      tcons (subst x s t1) (subst x s t2)
  | tfix t1 => tfix (subst x s t1)
  | tlet y t1 t2 =>
      tlet y (subst x s t1) (if eqb_string x y then t2 else (subst x s t2))

  (* generator *)
  | loop t1 t2 t3 => test 
                   (subst x s t1) (subst x s t2) (subst x s t3)
  | generator t1 t2 => generator 
                   (subst x s t1) (subst x s t2)
  | genob t1 => genob (subst x s t1)
  | next t1 => next (subst x s t1)

  (* for-else *)
  | forelse t1 t2 => forelse (subst x s t1) (subst x s t1)

  (* unit *)
  | unit => unit
  end.


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

  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (pair v1 v2).


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
  | ST_Mult1 : forall t1 t1' t2,
       t1 --> t1' ->
       (mlt t1 t2) --> (mlt t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (mlt v1 t2) --> (mlt v1 t2')
  | ST_Mulconsts : forall n1 n2,
       (mlt (const n1) (const n2)) --> (const (mult n1 n2))

  | ST_Test1 : forall t1 t1' t2 t3,
       t1 --> t1' ->
       (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_TestZero : forall t2 t3,
       (test (const 0) t2 t3) --> t2
  | ST_TestNonzero : forall n t2 t3,
       (test (const (S n)) t2 t3) --> t3
  
  (* chaining comparison *)
  | ST_Chain1 : forall t1 t1' t2 t3 t4,
       t1 --> t1' ->
       (chain t1 t2 t3 t4) --> (chain t1' t2 t3 t4)
  | ST_Chain2 : forall t1 t2 t2' t3 t4,
       t2 --> t2' ->
       (chain t1 t2 t3 t4) --> (chain t1 t2' t3 t4)
  | ST_ChainZero1 : forall t2 t3 t4,
       (chain (const 0) t2 t3 t4) --> t3
  | ST_ChainZero2 : forall t1 t3 t4,
       (chain t1 (const 0) t3 t4) --> t3
  | ST_ChainNonzero : forall n t3 t4,
       (chain (const (S n)) (const (S n)) t3 t4) --> t4

  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       (tcons t1 t2) --> (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       (tcons v1 t2) --> (tcons v1 t2')

  (* let *)
  | ST_Let1 : forall y t1 t1' t2,
         t1 --> t1' ->
         (tlet y t1 t2) --> (tlet y t1' t2)
  | ST_LetValue : forall y v1 t2,
         value v1 ->
         (tlet y v1 t2) --> [y:=v1]t2

  (* recursive functions *)
  | ST_Fix1 : forall t1 t1',
         t1 --> t1' ->
         (tfix t1) --> (tfix t1')
  | ST_FixAbs : forall y T t1,
         (tfix (abs y T t1)) --> [y:=(tfix (abs y T t1))]t1
  | ST_AppFunc : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12

  (* loops *)
  | ST_Loop : forall t1 t1' t2 t3,
         t1 --> t1' ->
         (loop t1 t2 t3) --> (loop t1' t2 t3)
  | ST_LoopZero : forall t2 t3,
       (loop (const 0) t2 t3) --> t2
  | ST_LoopNonzero : forall n t2 t3,
       (loop (const (S n)) t2 t3) --> t3

  (* Generator object *)
  | ST_Genob : forall t1 t1',
         t1 --> t1' ->
         (genob t1) --> (genob t1')
  | ST_GenobAbs : forall y T t1,
         (genob (abs y T t1)) --> [y:=(genob (abs y T t1))]t1
  | ST_GenobAppFunc : forall x T11 t12 v2,
         value v2 ->
         (app (abs x T11 t12) v2) --> [x:=v2]t12

  (* next *)
  | ST_Next : forall t1 t1',
       t1 --> t1' ->
       (next t1) --> (next t1')
  
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
         t1 --> t1' ->
         (pair t1 t2) --> (pair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (pair v1 t2) --> (pair v1 t2')
  | ST_Fst1 : forall t1 t1',
         t1 --> t1' ->
         (fst t1) --> (fst t1')
  | ST_FstPair : forall v1 v2,
         value (pair v1 v2) ->
         (fst (pair v1 v2)) --> v1
  | ST_Snd1 : forall t1 t1',
         t1 --> t1' ->
         (snd t1) --> (snd t1')
  | ST_SndPair : forall v1 v2,
         value (pair v1 v2) ->
         (snd (pair v1 v2)) --> v2

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
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in Nat ->
      Gamma |- (mlt t1 t2) \in Nat
  | T_Test : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (test t1 t2 t3) \in T1

  (* chaining comparison *)
  | T_Chain : forall Gamma t1 t2 t3 t4 T1,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in Nat ->
      Gamma |- t3 \in T1 ->
      Gamma |- t4 \in T1 ->
      Gamma |- (chain t1 t2 t3 t4) \in T1

  (* lists *)
  | T_Nil : forall Gamma T,
      Gamma |- (tnil T) \in (List T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (List T1) ->
      Gamma |- (tcons t1 t2) \in (List T1)

  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (pair t1 t2) \in (Prod T1 T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |- t \in (Prod T1 T2) ->
      Gamma |- (fst t) \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |- t \in (Prod T1 T2) ->
      Gamma |- (snd t) \in T2

  (* loops *)
  | T_Loop : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in Nat ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (loop t1 t2 t3) \in T1

  (* let *)
  | T_Let : forall Gamma y t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      (update Gamma y T1) |- t2 \in T2 ->
      Gamma |- (tlet y t1 t2) \in T2

  (* fix recursion*)
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 \in (Arrow T1 T1) ->
      Gamma |- tfix t1 \in T1

  (* Generator Function*)  
  | T_Generator : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (Arrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (generator t1 t2) \in T2

  (* Generator Object*)
  | T_Genob : forall Gamma t1 T1,
      Gamma |- t1 \in (Arrow T1 T1) ->
      Gamma |- genob t1 \in T1

  (* next*)
  | T_Next : forall Gamma t1 T1,
      Gamma |- t1 \in (Arrow T1 T1) ->
      Gamma |- next t1 \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Definition test_Type :=
  test 
    (prd
      (scc
        (prd 
          (mlt
            (const 2)
            (const 0)))))
    (const 5)
    (const 6).

Compute test_Type.

Definition test_Prod :=
  snd
    (fst
      (pair
        (pair
          (const 5) 
          (const 6))
        (const 7))).
