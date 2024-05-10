From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3. TODO: Define the relational semantics (ceval) to support the required constructs.
*)
(*Inductive ceval : state -> list (state * com) -> com -> state -> list (state * com) -> result -> Prop :=*)

Inductive ceval : com -> state -> list (state * com) -> 
          result -> state -> list (state * com) -> Prop :=
| E_Skip : forall st q,
 st / q =[ skip ]=> st / q / Success
| E_Assign : forall st q x a,
    st / q =[ x := a ]=> (st & {x --> aeval st a}) / q / Success
| E_Seq_Skip : forall st q c,
    st / q =[ c ;; skip ]=> st / q / Success
| E_Seq : forall st1 q1 st2 q2 q3 c1 c2,
    st1 / q1 =[ c1 ]=> st2 / q2 / Success ->
    st2 / q2 =[ c2 ]=> st2 / q3 / Success ->
    st1 / q1 =[ c1 ;; c2 ]=> st2 / q3 / Success
| E_IfTrue : forall st1 q1 b c1 c2,
    beval st1 b = true ->
    st1 / q1 =[ c1 ]=> st1 / q1 / Success ->
    st1 / q1 =[ if b then c1 else c2 end ]=> st1 / q1 / Success
| E_IfFalse : forall st1 q1 b c1 c2,
    beval st1 b = false ->
    st1 / q1 =[ c2 ]=> st1 / q1 / Success ->
    st1 / q1 =[ if b then c1 else c2 end ]=> st1 / q1 / Success
| E_WhileEnd : forall st1 q1 b c,
    beval st1 b = false ->
    st1 / q1 =[ while b do c end ]=> st1 / q1 / Success
| E_WhileLoop : forall st1 q1 q2 q3 b c,
    beval st1 b = true ->
    st1 / q1 =[ c ]=> st1 / q2 / Success ->
    st1 / q2 =[ while b do c end ]=> st1 / q3 / Success ->
    st1 / q1 =[ while b do c end ]=> st1 / q3 / Success
(* TODO. Hint: follow the same structure as shown in the chapter Imp *)
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).
(*Esta notação permite-nos escrever expressões como st1 / q1 =[ c ]=> st2 / q2 / r, o que torna mais fácil entender e manipular as relações de avaliação do programa*)

(**
  3.1. TODO: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq; auto.
  - apply E_Assign; auto.
  - apply E_IfFalse; auto.
Qed.


Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  apply E_Assign; auto.
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Assign; auto.
Qed. 

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  exists.
  apply E_Seq; auto.
  - apply E_Seq; eauto.
    + apply E_Assign; auto.
    + apply E_IfTrue; auto.
      * simpl. reflexivity.
      * apply E_Assign; auto.
  - apply E_GuardTrue; auto.
Qed.
    
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  exists.
  apply E_Seq; auto.
  - apply E_Seq; auto.
    + apply E_Assign; auto.
    + apply E_IfFalse; auto.
      * simpl. reflexivity.
      * apply E_Assign; auto.
  - apply E_GuardTrue; auto.
Qed.



(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2. TODO: Prove the properties below.
*)

(*programa composto X := 2; X = 2 -> skip é comportamentalmente equivalente ao programa simples X := 2.*)
Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  (* TODO *)
  unfold cequiv. split.
  - (* Esquerda para Direita -> *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst. inversion H5; subst. exists q1. apply E_Seq with (st2 := st'0); auto.
  - (* Direita para Esquerda <- *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst. inversion H1; subst. exists q1. apply E_Seq with (st2 := st'0); auto.
Qed.

(*Precisamos mostrar que a escolha não determinística entre X := 1 e X := 2*)
Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  (* TODO *)
  unfold cequiv. split.
  - (* -> *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    (*X := 1 é escolhido, então X será 1 e a guarda falhará, levando a skip.*)
    + inversion H1; subst. 
      * (* E_Assign *) exists q1. apply E_Seq with (st2 := st & {X --> aeval st (ANum 1)}); auto.
      * (* E_GuardFalse *) simpl in H5. inversion H5.
    (*X := 2 é escolhido, então X será 2 e a guarda será bem-sucedida, também levando a skip*)
    + inversion H1; subst.
      * (* E_Assign *) exists q1. apply E_Seq with (st2 := st & {X --> aeval st (ANum 2)}); auto.
      * (* E_GuardTrue *) simpl in H5. inversion H5.
  - (* <- *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    inversion H1; subst.
    exists q1. apply E_Seq with (st2 := st & {X --> aeval st (ANum 2)}); auto.
Qed.

(*Afirma que a escolha não determinística entre c e c é equivalente a simplesmente c*)
Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>. (*Prova é Direta*)
Proof.
  (* TODO *)
  unfold cequiv. split.
  - (* -> *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1 c *) exists q1. auto.
    + (* Choice 2 c *) exists q1. auto.
  - (* <- *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    exists q1. apply E_NDChoice1; auto.
Qed.

(*Propriedade afirma que a ordem da escolha não determinística não importa.*)
Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>. (*Prova direta, c1 c2 é a mesma que c2 c1*)
Proof.
  (* TODO *)
  unfold cequiv. split.
  - (* -> *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1: c1 *) exists q1. apply E_NDChoice2; auto.
    + (* Choice 2: c2 *) exists q1. apply E_NDChoice1; auto.
  - (* <- *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1: c2 *) exists q1. apply E_NDChoice2; auto.
    + (* Choice 2: c1 *) exists q1. apply E_NDChoice1; auto.
Qed.

(*Propriedade afirma que a associação de escolhas não determinísticas é irrelevante.*)
Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  (* TODO *)
  unfold cequiv. split.
  - (* -> *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1: c1 *) inversion H3; subst.
      * (* Choice 1.1: c1 *) exists q1. apply E_NDChoice1; auto.
      * (* Choice 1.2: c2 *) exists q1. apply E_NDChoice2; auto.
    + (* Choice 2: c3 *) exists q1. apply E_NDChoice2; auto.
  - (* <- *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1: c1 *) exists q1. apply E_NDChoice1; auto.
    + (* Choice 2: c2 !! c3 *) inversion H3; subst.
      * (* Choice 2.1: c2 *) exists q1. apply E_NDChoice1; auto.
      * (* Choice 2.2: c3 *) exists q1. apply E_NDChoice2; auto.
Qed.

(*Propriedade afirma que a composição sequencial se distribui sobre a escolha não determinística à esquerda. *)
Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
(*c1 ; (c2 !! c3) é equivalente a (c1 ; c2) !! (c1 ; c3).*)
Proof.
  (* TODO *)
  unfold cequiv. split.
  - (* -> *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Sequence 1 *) inversion H5; subst.
      * (* c2 *) exists (q1 ++ [(st'0, c3)]). apply E_NDChoice2; auto.
      * (* c3 *) exists (q1 ++ [(st'0, c4)]). apply E_NDChoice2; auto.
    + (* Sequence 2 *) inversion H5; subst.
      exists q1. apply E_NDChoice1; auto.
  - (* <- *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1: c1;c2 *) inversion H3; subst.
      * (* Sequence 1 *) exists q1. apply E_Seq with (st2 := st'0); auto.
      * (* Sequence 2 *) exists q1. apply E_Seq with (st2 := st'0); auto.
    + (* Choice 2: c1;c3 *) inversion H3; subst.
      exists q1. apply E_Seq with (st2 := st'0); auto.
Qed.

(*Propriedade afirma que a escolha não determinística preserva a equivalência comportamental entre os programas escolhidos. *)
Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  (* TODO *)
  unfold cequiv. split.
  - (* -> *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1: c1 *) destruct (H0 _ _ _ _ _ H2) as [q3 H3].
      exists q3. apply E_NDChoice1; auto.
    + (* Choice 2: c2 *) destruct (H1 _ _ _ _ _ H2) as [q3 H3].
      exists q3. apply E_NDChoice2; auto.
  - (* <- *) unfold cequiv_imp. intros st1 st2 q1 q2 result H.
    inversion H; subst.
    + (* Choice 1: c1' *) destruct (H0 _ _ _ _ _ H2) as [q3 H3].
      exists q3. apply E_NDChoice1; auto.
    + (* Choice 2: c2' *) destruct (H1 _ _ _ _ _ H2) as [q3 H3].
      exists q3. apply E_NDChoice2; auto.
Qed.
