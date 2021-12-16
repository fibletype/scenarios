(*
Давайте выкинем неспецифицированные случаи, потому что с ними очень тяжко осознать что нужно

Идея следующая: нужно взять некоторое множество состояний, задать на них отношение 
(которое как-то должно соответствовать функциям контракта). Потом написать 
рекурсивную функцию, которая будет проходить по состояниям (видимо по коиндуктивному листу)
И проверять заранее написанную лтл формулу 
Возможно эти листы надо как-то хитро строить с предусловиями, но это пока не понятно

Нам не нужен оператор некст, потому что это и есть экзеки и евалы, которые задаются
отношениям. Вероятно нам нужны только файнали, глобали и антил.
Если нам точно нужно следить за одной переменной, то нам нужно будет добавить ее в состояние
Тогда, возможно, нам придется таскать много переменны, что мне не нравится
Надо написать инд проп про корректность состояний


Сейчас надо более явно написать состояния и написать инд проп для лтл.

Нам нужно написать формулу на состояние, которая будет содержать энд импл и ор.
Эта формула над состоянием должна переводиться в формулу над сценарием, в которой содержатся операторы Г Ф У,
то есть выглядеть это должно примерно так:
F (G ((a -> b) or (a -> c)))

Давайте пока начнем с просто G.

*)

Require Import List.
Require Import Lia.
Import ListNotations.

Inductive cond :=
| phi
| psi
| ksi.


Definition state := list cond.

Definition A := [phi ; psi].
Definition B := [psi ; phi].
Definition C := [ksi ; phi].
Definition D := [psi ; ksi].


Inductive rel : state -> state -> Prop := 
| AC : rel A C
| AB : rel A B
| BC : rel B C
| AD : rel A D.

(* G phi /\ F psi /\ phi U psi *)

Inductive rel_prop : list state -> Prop :=
| empty_rel : rel_prop []
| base_rel : forall a, rel_prop [a]
| trans_rel : forall a b l , rel a b -> rel_prop (b :: l) -> rel_prop (a :: b :: l).

Definition state_formula := state -> Prop.

(* 
Inductive state_formula_impl : cond -> state -> Prop :=
| impl : forall c1 c2 s, In c1 s -> In c2 s -> state_formula_impl c1 s.
 *)
Inductive G_formula : list cond -> list state -> Prop :=
| G_empty_form : forall (b : list cond), G_formula b []
| G_hold : forall (a : state) (b : list cond) (c : list state), Forall (fun x => In x a) b -> G_formula b c -> G_formula b (a::c).

Inductive F_formula : cond -> list state -> Prop :=
| F_empty_form : forall (b : cond), F_formula b []
| F_not_hold : forall (a : state) (b: cond) (s : list state), not (In b a) -> F_formula b s -> F_formula b (a::s)
| F_hold_first_time : forall (a : state) (b : cond) (s : list state), In b a -> F_formula b s -> F_formula b (a::s).


Definition scen1 := [ A ; B ; C ].
Definition scen2 := [ A ; D ].

Lemma scen1_correct : rel_prop scen1.
Proof.
    repeat constructor.
Qed.

Lemma scen1_G_phi : G_formula [phi] scen1.
Proof.
    constructor. constructor. simpl. left. auto.
    constructor. constructor. constructor. simpl. right. auto.
    constructor. constructor. constructor. simpl. right. auto.
    constructor. constructor. 
Qed.


Lemma scen1_G_phi_psi : G_formula [phi ; psi] scen1.
Proof.
    constructor.
    simpl. constructor.  left. auto.
    constructor. right. auto. auto.
    constructor. constructor.
    simpl. right. auto.
    constructor.
    simpl. left. auto.
    constructor. constructor.
    constructor. simpl. right. auto.
    constructor.
    simpl.
Admitted.

Lemma scen2_G_phi : G_formula [phi] scen2.
Proof.
    constructor. constructor.
    simpl. left. auto.
    constructor. constructor. constructor.
    simpl.
Admitted.
    
    
Lemma scen1_F_ksi : F_formula ksi scen1.
Proof.
    constructor.
    simpl. unfold not. intros.
    inversion H. discriminate.
    inversion H0. discriminate. assumption.
    constructor. simpl. unfold not. intros.
    inversion H. discriminate.
    inversion H0. discriminate. assumption.
    constructor 3. simpl. left. auto.
    constructor.
Qed.
