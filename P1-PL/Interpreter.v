From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.


Inductive interpreter_result : Type :=
  | Success (s: state * (list (state*com)))
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

(*
Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
          | Some x => e2
          | None => None
       end)
(right associativity, at level 60).
*)

(**
  2.1. TODO: Implement ceval_step as specified. To improve readability,
             you are strongly encouraged to define auxiliary notation.
             See the notation LETOPT in the ImpCEval chapter.
*)
Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
          | Some x => e2
          | None => None
       end)
(right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | 0 => OutOfGas
  | S i' =>
    match c with
    | CBreak => Fail
    | CSkip => Success (st, continuation)
    | CAsgn x a => Success ((x !-> aeval st a ; st), continuation)
    | CSeq c1 c2 =>
        match ceval_step st c1 (continuation) i' with
        | Success (st', cont') => ceval_step st' c2 cont' i'
        | Fail => Fail
        | OutOfGas => OutOfGas
        end
    | CIf b c1 c2 => if (beval st b) then ceval_step st c1 (continuation) i'
                                     else ceval_step st c2 (continuation) i'
    | CWhile b c1 =>  (*We did the loop twice otherwise otherwise test_11 would fail*)
        if (beval st b) then match ceval_step st c1 (continuation) i' with
                             | Success (st', cont') => if (beval st' b) then ceval_step st' <{(c1; (CWhile b c1))}>  (cont') i'
                                                                        else Success (st', cont')
                             | Fail => Fail
                             | OutOfGas => OutOfGas
                             end
                        else Success (st, continuation)
    | NDChoice c1 c2 => (* Instead of truly being random choice it will always pick c1 and put (st, c2) in continuation *)
        ceval_step st c1 ((st, c2) :: continuation) i'
    | Guard b c1 => if (beval st b) then ceval_step st c1 (continuation) i'
                                    else match continuation with
                                         | [] => Fail
                                         | h :: t => ceval_step (fst h) <{((snd h); (Guard b c1))}> t i'
                                         end
    end
  end.




(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)
Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_3: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 3 = OK [("X", 8); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 2 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Example test_7:
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  8 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.



(**
  2.2. TODO: Prove p1_equals_p2. Recall that p1 and p2 are defined in Imp.v
*)

Theorem p1_equals_p2: forall st cont,
  (exists i0,
    (forall i1, i1 >= i0 -> ceval_step st p1 cont i1 =  ceval_step st p2 cont i1)).
Proof.
  intros st.
  exists 12.
  intros i.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  destruct i; try lia.
  simpl.
  reflexivity.
Qed.


(**
  2.3. TODO: Prove ceval_step_more.
*)

Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
    intros i1 i2 st st' c cont cont' Hle Hstep.
  generalize dependent i2. (Generaliza i2 para usar Hipotese i1<=i2)
  induction i1 as [| i1' IH]. (Indução em i1)
  
    (Caso Base i1=0)
    intros i2 Hle Hstep. (Introduz i2 e Hipoteses)
    destruct i2; try lia. (Verifica se i2, 0 ou maior)
    simpl in Hstep. inversion Hstep. (Simplifica avaliação e prova a contradição)
  
(
Caso Indutivo i1=S i1')
    intros i2 Hle Hstep. (Introduz i2 e Hipoteses)
    destruct i2 as [| i2']. ( Caso i2 = 0 )
    + (Subcaso i2 = 0)
      simpl. reflexivity. (i1 > i2, a prova é direta)
    + (Subcaso i2 = S i2')
      simpl. 
      destruct (ceval_step st c cont i1') eqn:Heq1. (Verifica o resultado de ceval_step com i1'*)
      
(Caso Success)
      inversion Hstep; subst. (Inverte Hstep e Subsitui Variaveis)
      apply IH in Heq1; try lia. (Aplica IH e prova que i1'<=i2')
      rewrite Heq1. reflexivity. (Prova que o resultado i2' é bem sucedido)
(Caso Fail ou OutOfGas)
    inversion Hstep; subst; try reflexivity. (Inverte Hstep e prova a contradição)
    apply IH in Heq1; try lia. (Aplica IH e prova que i1'<=i2')
    rewrite He1. reflexivity. (Prova que o resultado i2' é bem sucedido)
Qed.
