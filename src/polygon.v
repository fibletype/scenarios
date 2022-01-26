(* 
Require Import UMLang.UrsusLib.
Local Open Scope ursus_scope.
Print URValueP.
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

Кажется, что формулу над состоянием можно просто заменить на набор условий, что здесь сейчас и описано 

*)

Require Import List.
Import ListNotations.
Local Open Scope list_scope.

Import ListNotations.
Inductive cond :=
| phi
| psi
| ksi.

Definition state := list (URValue XBool false).

(* Условия по которым мы разбиваем систему контрактов на состояния *)

Inductive cond :=
| phi
| psi
| ksi.

(* Состояние это набор условий *)

Definition state := list bool.

(* Несколько состояний *)

Definition A := [true ; false].
Definition B := [false ; true].
Definition C := [true ; true].
Definition D := [false ; false].

(* Переходы между состояниями, которые происходят при обработке сообщений *)

Inductive rel : state -> state -> Prop := 
| AC : rel A C
| AB : rel A B
| BC : rel B C
| AD : rel A D.

(* G phi /\ F psi /\ phi U psi *)

(* Предикат, который гарантирует, что сценарий корректен с точки зрения переходов между состояниями *)
Locate "::".
Locate "[ x ]".
Locate  "_ [ _ ]".

Inductive rel_prop : list state -> Prop :=
| empty_rel : rel_prop nil
| base_rel : forall a, rel_prop (cons a nil)
| trans_rel : forall a b l , rel a b -> rel_prop (b :: l) -> rel_prop (a :: b :: l).



(* Definition state_formula := state -> Prop. *)

(* 
Inductive state_formula_impl : cond -> state -> Prop :=
| impl : forall c1 c2 s, In c1 s -> In c2 s -> state_formula_impl c1 s.
 *)


(* (* Предикаты, которые позволяют нам судить о выполнении каких-то свойств в сценарии *)

Inductive G_formula : list cond -> list state -> Prop :=
| G_empty_form : forall (b : list cond), G_formula b []
| G_hold : forall (a : state) (b : list cond) (c : list state), Forall (fun x => In x a) b -> G_formula b c -> G_formula b (a::c).

(* Некорректный предикат F. Если мы всегда будем использовать второй конструктор, то можем показать выполнимость этого предиката на сценарии, 
    который не удовлетворяет нужным свойствам. Поэтому для этого предиката в доказательствах обязательно должен встретиться 3 конструктор. *)

Inductive F_formula : list cond -> list state -> Prop :=
| F_empty_form : forall (b : list cond), F_formula b []
| F_not_hold : forall (a : state) (b: list cond) (s : list state), not (Forall (fun x => In x a) b) -> F_formula b s -> F_formula b (a::s)
| F_hold_first_time : forall (a : state) (b : list cond) (s : list state), Forall (fun x => In x a) b -> F_formula b s -> F_formula b (a::s).

(* Его можно исправить на предикат, который будет говорить, что наше условие выполняется всегда в последний момент, однако это не будет 
    соответствовать общепринятому значению оператора F *)

(* Inductive FG_formula : list cond -> list state -> Prop :=
| FG_empty_form : forall (b : list cond), FG_formula b []
| FG_not_hold : forall (a : state) (b: list cond) (s : list state), not (Forall (fun x => In x a) b) -> FG_formula b s -> FG_formula b (a::s)
| FG_hold_first_time : forall (a : state) (b : list cond) (s : list state), Forall (fun x => In x a) b -> FG_formula b s -> FG_formula b (a::s).
  *)


(* Определение сценариев *)

Definition scen1 := [ A ; B ; C ].
Definition scen2 := [ A ; D ].

(* Корректность сценария *)

Lemma scen1_correct : rel_prop scen1.
Proof.
    repeat constructor.
Qed.

(* Выполнимость формулы G phi на первом сценарии *)

Lemma scen1_G_phi : G_formula [phi] scen1.
Proof.
    constructor. constructor. simpl. left. auto.
    constructor. constructor. constructor. simpl. right. auto.
    constructor. constructor. constructor. simpl. right. auto.
    constructor. constructor. 
Qed.

(* формула G phi/\psi не выполняется на первом сценарии, хотя непонятно как это реально объяснять*)

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
    
(* Доказательство выполнимости формулы F ksi на первом сценарии *)   

Lemma scen1_F_ksi : F_formula [ksi] scen1.
Proof.
    constructor.
    simpl. unfold not. intros.
    inversion H. inversion H2. discriminate.
    inversion H4. discriminate. assumption.
    constructor. simpl. unfold not. intros.
    inversion H. inversion H2. discriminate.
    inversion H4. discriminate. assumption.

    (* ***************** *)
    constructor 3.
    (* Без этой строчки получается бесполезное доказательство, если я всегда пользовался только первым и вторым конструктором *)

    simpl. constructor. left. auto.
    constructor. constructor.
Qed.
 *)

Module state_formulas.

Variables Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents GlobalParams OutgoingMessageParams: Type.
Context `{ledgerClass: LedgerClass XBool Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents GlobalParams OutgoingMessageParams}.
About URValueL.
Notation URValue := (@URValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents GlobalParams OutgoingMessageParams ledgerClass) .

Import ListNotations.

Inductive Llist (X : Type) : Type :=
| lnil : Llist X
| lcons : X -> Llist X -> Llist X.

Definition state := Llist (URValue XBool false).

Definition a := URValue XBool false.
Definition b := URValue XBool false.
Definition c := URValue XBool false.

Check a : Type.
About Llist.
Arguments lnil {X}.
Arguments lcons {X} a l.
Definition A := lcons a (lcons a lnil).
Definition B := lcons a (lcons b lnil).
Definition C := lcons b (lcons a lnil).
Definition D := lcons a (lcons c lnil).

Definition SFinterpretor := LedgerT (ControlResultP XUInteger XBool false) -> XBool.


(* Inductive state_formula := 
| el (c : URValue XBool false)
| and  (b1 b2 : state_formula)
| or   (b1 b2 : state_formula)
| impl (b1 b2 : state_formula). *)
(* Переписать это как функцию из леджера в бул
    Почему это функция из леджера в бул? 
    state_formula (sRReader (for)) 
    Подумать о том, что сценарий это не последовательность состояний, а 
    начальное состояние и последовательность переходов
*)

Inductive formula :=
| sf   (s : URValue XBool false)
| G    (b : formula)
| F    (b : formula).

Definition eqc c1 c2 := 
    match c1 with
    | phi => match c2 with
            | phi => true
            | _ => false
    end
    | psi => match c2 with
            | psi => true
            | _ => false
    end
    | ksi => match c2 with
            | ksi => true
            | _ => false
    end
    end.

Fixpoint inb'  (b : bool) (a : cond) (l : list cond) : bool := 
    match l with
    | [] => b
    | h :: t => if (eqc a h) 
                then inb' true a t
                else inb' b a t
    end.

Definition inb := inb' false.

(* Compute inb phi A. *)
(* Definition SFInterpretator (sf : URValue XBool false) (s : state) : bool.
induction sf.
refine (inb c s).
refine (andb IHsf1 IHsf2).
refine (orb IHsf1 IHsf2).
refine (implb IHsf1 IHsf2).
Defined. *)

(* 
Compute SFInterpretator (el phi) A .
 *)
(* Fixpoint interpretator (f : formula) (ls : list state) : bool.
induction ls.
refine true.
destruct f.
refine (SFInterpretator s a).
refine (andb (interpretator f [a]) IHls).
refine (orb (interpretator f [a]) IHls).
Defined.
 *)

Fixpoint interpretator (f : formula) (ls : Llist state) : bool.
induction ls.
refine true.
destruct f.
remember ( (sRReader s)). 
apply SFinterpretor in l.

:=
match ls with
| [] => true
| a :: [] => match f with
        | sf s => SFInterpretator s a
        | G s => interpretator s (cons a nil)
        | F s => interpretator s (cons a nil)
end
| a :: t => match f with
            | sf s => SFInterpretator s a
            | G s => andb (interpretator s (cons a nil)) (interpretator s t)
            | F s => orb (interpretator s (cons a nil)) (interpretator s t)
end
end.
(* induction ls.
refine false.
destruct f.
refine (SFInterpretator s a).
refine (andb (interpretator f [a]) IHls).
refine (orb (interpretator f [a]) IHls).
Defined. *)


Definition scen1 := [ A ; B ; C ].


Lemma scen1_F_phi : interpretator (F (sf (el phi))) scen1 = true.
Proof.
    auto.
Qed.

Lemma scen1_G_phi : interpretator (G (sf (el phi))) scen1 = true.
Proof.
    compute. auto.
Qed.

Lemma scen1_F_ksi : interpretator (F (sf (el ksi))) scen1 = false.
Proof.
    compute. auto.
Qed.

Lemma scen1_G_ksi : interpretator (G (sf (el ksi))) scen1 = false.
Proof.
    compute. auto.
Qed.

End state_formulas.
 *)
Require Import List.
Local Open Scope list_scope.
(* Variables (superledger : Type) (a b c: superledger). *)


(* Представляем наше дерево в виде списка деревьев, тогда у нас верхняя вершина будет считаться стволом, а остальные ветками отходящие от 
   этой вершины ствола.
   На некоторые вершины веток у нас задается частичный порядок (пишется руками) 
   При обходе дерева мы должны учитывать этот частичный порядок *)

Inductive Tree (X : Type) : Type :=
| empty : Tree X
| node : X -> Tree X -> Tree X -> Tree X.

Arguments empty {X}.
Arguments node {X} b t.

Definition superledger := nat.


Definition TrunkTree := list (Tree superledger).

(* Inductive PartOrd : superledger -> superledger -> Prop:=
| A : PartOrd a b
| B : PartOrd b c.
 *)

Inductive Order :=
| Nan
| First
| Second.

Definition PartOrd := list (list superledger).

Fixpoint FindList (s : superledger) (l : list (list superledger)) : optional (list superledger) :=
    match l with
    | nil => None
    | cons h t => if (hd h) =? s then h else FindList s t
    end.

Fixpoint CompPartOrd (a b :superledger) (p : PartOrd) := 
    match FindList a p in
    | None => match FindList b p in
                | None => Nan
                | Some k => if (In a k) then Second else Nan
                end
    | Some k => if In b k then First else match FindList b p in
                                            | None => Nan
                                            | Some k => if (In a k) then Second else Nan
                                            end
    end.

Fixpoint MinTime (l : list superledger) : optional superledger :=
    | nil => None
    | cons h t => ???

(* Я могу каждый раз передовать список доступных вершин в аккумуляторе *)


Fixpoint VisitingTree (t : Tree superledger) (acc : list superledger): list superledger :=
    match t with
    | empty => nil
    | node x l r =>  x :: (VisitingTree l) ++ (VisitingTree r)
    end.

Definition scen := node a (node b (node c empty empty) (node a empty empty)) (node b (node c empty empty) empty).

Compute VisitingTree scen.


Fixpoint VisitingTrunkTree (t : TrunkTree) : list superledger := 
    match t with
    | nil => nil
    | cons h t => VisitingTree h ++ VisitingTrunkTree t
    end.

