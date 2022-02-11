Require Import List.
Import ListNotations.
Require Import Nat.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition hd {X} (l : list X) := 
    match l with
    | nil => None
    | cons h t => Some h
    end.

(* Представляем наше дерево в виде списка деревьев, тогда у нас верхняя вершина будет считаться стволом, а остальные ветками отходящие от 
   этой вершины ствола.
   На некоторые вершины веток у нас задается частичный порядок (пишется руками) 
   При обходе дерева мы должны учитывать этот частичный порядок *)

Inductive Tree (X : Type) : Type :=
| empty : Tree X
| node : X -> Tree X -> Tree X -> Tree X.

Arguments empty {X}.
Arguments node {X} b t.


Definition hdT {X} (t : Tree X) := 
    match t with
    | empty => None
    | node x _ _ => Some x
    end.


Definition superledger := nat.

Fixpoint In (a : superledger) (l : list superledger) :=
    match l with
    | nil => false
    | cons h t => if eqb a h then true else In a t
    end.

Definition TrunkTree := list (Tree superledger).

(* Inductive PartOrd : superledger -> superledger -> Prop:=
| A : PartOrd a b
| B : PartOrd b c.
 *)

Inductive Order :=
| Nan
| First
| Second.

(* Способ задания частичного порядка *)
Definition PartOrd := list (list superledger).


Check (eqb 1 2).

(* Функция поиска элемента в частичном порядке *)

Fixpoint FindList (s : superledger) (l : list (list superledger)) : option (list superledger) :=
    match l with
    | nil => None
    | cons h t => match hd h with
                    | None => FindList s t
                    | Some head => if eqb head s then Some h else FindList s t
    end
    end.

(* Функция узнает какой элемент меньше, если их можно сравнить *)

Definition CompPartOrd (a b :superledger) (p : PartOrd) := 
    match FindList a p with
    | None => match FindList b p with                
                | None => Nan
                | Some k => if (In a k) then Second else Nan
                end
    | Some k => if In b k then First else match FindList b p with
                                            | None => Nan
                                            | Some k => if (In a k) then Second else Nan
                                            end
    end.

(* Функция проверяет является ли элемент минимумом для списка *)

Fixpoint IsMin (l : list superledger) (s : superledger) (p : PartOrd) : bool :=
    match l with
    | nil => true
    | cons h t => match CompPartOrd s h p with
                    | Nan => IsMin t s p
                    | First => IsMin t s p
                    | Second => false
    end
    end.

(* Функция находит минимальный элемент в списке *)

Fixpoint MinTime (l : list superledger) (l1 : list superledger) (p : PartOrd) : option superledger :=
    match l with
    | nil => None
    | cons h t => if IsMin l1 h p then Some h else MinTime t l1 p
    end.


Fixpoint TreeToList (t : Tree superledger) : list superledger :=
    match t with
    | empty => nil
    | node x l r => x :: TreeToList l ++ TreeToList r
    end.

Definition scen := node 1 (node 2 (node 3 empty empty) (node 4 empty empty)) (node 5 (node 6 empty empty) empty).

Compute TreeToList scen.


Fixpoint TrunkTreeToList (t : TrunkTree) : list superledger := 
    match t with
    | nil => nil
    | cons h t => TreeToList h ++ TrunkTreeToList t
    end.



Fixpoint delete ( l : list superledger) (s : superledger) :=
    match l with
    | [] => []
    | h :: t => if h =? s then t else h :: delete t s
    end.

Fixpoint ListToScen (p : PartOrd) (s : list superledger) (n : nat): list superledger :=
    match n with
    | 0 => []
    | S n => match MinTime s s p with
            | None => []
            | Some k => k :: ListToScen p (delete s k) n
    end
    end.


(* Функция меняет лист с заданной головой в частичном порядке на другой. Если такой головы нет у листов, то ничего не делает*)
Fixpoint update (p : PartOrd) (l : list superledger) (s : superledger) : PartOrd :=
    match p with
    | [] => []
    | h :: t => match hd h with
                | None => update t l s
                | Some k => if eqb k s then 
                                        l :: update t l s
                                    else
                                        h :: update t l s
                end
    end. 

(* Функция апдейта частичного порядка для дерева *)

Fixpoint TreeToOrd (t : Tree superledger) (p : PartOrd) : PartOrd :=
    match t with
    | empty => p
    | node x l r => match FindList x p with
                    | None => let p1 := ([x] ++ TreeToList l ++ TreeToList r) :: p in
                                let p2 := TreeToOrd l p1 in
                                    TreeToOrd r p2
                    | Some s => match hd s with
                                | None => let p1 := (x :: TreeToList l ++ TreeToList r) :: p in
                                            let p2 := TreeToOrd l p1 in
                                                TreeToOrd r p2
                                | Some h => let p1 := update p (s ++ TreeToList l ++ TreeToList r) h in
                                                let p2 := TreeToOrd l p1 in
                                                    TreeToOrd r p2
                                end
                    end 
    end.
(* Функция делает порядок для головы *)
Definition HeadToOrd (t : Tree superledger) (p : PartOrd) : PartOrd :=
    match t with
    | empty => p
    | node x l r => match FindList x p with
                    | None => ([x] ++ TreeToList l ++ TreeToList r) :: p
                    | Some s => match hd s with
                                | None => (x :: TreeToList l ++ TreeToList r) :: p           
                                | Some h => update p (s ++ TreeToList l ++ TreeToList r) h              
                                end
                    end 
    end.
(* Добавление порядка по дереву без учета ствола *)
Fixpoint TrunkTreeToOrd (t : TrunkTree) (p : PartOrd) : PartOrd :=
    match t with
    | [] => p
    | h :: e => let p1 := TreeToOrd h p in
                    TrunkTreeToOrd e p1
    end.

(* Добавление естественного порядка для вершины по стволу  *)
Fixpoint NodeOrd (n : superledger) (t : TrunkTree) (p : PartOrd) : PartOrd :=
    match t with
    | [] => p
    | h :: e => let p1 := HeadToOrd (node n h empty) p in
                    NodeOrd n e p1
    end.

(* Фкункция по дереву и стволу делает порядок *)
Fixpoint TreeOrd (tree : Tree superledger) (t : TrunkTree) (p : PartOrd) : PartOrd :=
    match tree with
    | empty => p
    | node x l r => let p1 := NodeOrd x t p in
                        let p2 := TreeOrd l t p1 in
                            TreeOrd r t p2
    end.
(* Функция добавление частичного порядка по стволу для дерева *)

Fixpoint TrunkTreeOrd (t : TrunkTree) (p : PartOrd) : PartOrd :=
    match t with
    | [] => p
    | h :: e => let p1 := TreeOrd h e p in
                    TrunkTreeOrd e p1
    end.

Definition FinalizeOrdering (t : TrunkTree) (p : PartOrd) := TrunkTreeToOrd t (TrunkTreeOrd t p).

Unset Guard Checking.

Fixpoint Reachable (n : superledger) (l : list superledger) (p : PartOrd) (vis : list superledger) {struct n} := 
    match l with
    | [] => []
    | h :: t => if In h vis then Reachable n t p vis
    else
        if eqb h n then Reachable n t p vis
                    else 
                        match FindList h p with
                        | None => h :: (Reachable n t p (h :: vis))
                        | Some s =>  let r := Reachable n t p (h :: vis) in 
                                            h :: r ++ (Reachable h s p (h :: vis ++ r)) 
                        end 
    end. 

Set Guard Checking.
(* Построение транзитивного замыкания для вершины *)
Fixpoint Chains (n : nat) (p : PartOrd) : list (list superledger):=
    match n with
    | 0 => []
    | S n => match FindList (S n) p with
            | None => Chains n p
            | Some s => ((S n) :: Reachable (S n) s p []) :: Chains n p
    end
    end.
(* Проверка транзитивного замыкания на отсутствие циклов  *)
Fixpoint IsOrdCorrect (l : list (list superledger)) (a : nat) : nat :=
    match l with
    | [] => a
    | h :: t => match h with
                | [] => IsOrdCorrect t a
                | head :: tail => if In head tail then head
                                else IsOrdCorrect t a
    end
    end. 

(* Testing *)
Definition scenario : PartOrd := [  [4; 3] ;
                                    [6; 5]
                                 ].


Definition sctree := [node 1 (node 5 empty empty) (node 6 empty empty);
                     (node 2 (node 3 empty empty) (node 4 empty empty)) ].
(* Строим частичный порядок *)
Compute FinalizeOrdering sctree scenario.
(* Строим какой-то обход *)
Compute TrunkTreeToList sctree.
(* Строим для каждой вершины список вершин идущих после нее согласно частичному порядку *)
Compute Chains 6 (FinalizeOrdering sctree scenario).
(* Проверяем корректность порядка *)
Compute IsOrdCorrect (Chains 6 (FinalizeOrdering sctree scenario)) 0.
(* Делам финальный обход *)
Compute ListToScen (FinalizeOrdering sctree scenario) (TrunkTreeToList sctree) 6.

(* ******* *)

Definition scenario1 : PartOrd := [ 
                                   ].

Definition sctree1 := [node 1 (node 3 (node 4 (node 9 empty empty) empty) (node 8 empty empty)) (node 5 (node 6 empty empty) (node 7 empty empty));
                     (node 2 (node 10 empty empty) (node 11 empty empty)) ].

(* Строим частичный порядок *)
Compute FinalizeOrdering sctree1 scenario1.
(* Строим какой-то обход *)
Compute TrunkTreeToList sctree1.
(* Строим для каждой вершины список вершин идущих после нее согласно частичному порядку *)
Compute Chains 11 (FinalizeOrdering sctree1 scenario1).
(* Проверяем корректность порядка *)
Compute IsOrdCorrect (Chains 11 (FinalizeOrdering sctree1 scenario1)) 0.
(* Делам финальный обход *)
Compute ListToScen (FinalizeOrdering sctree1 scenario1) (TrunkTreeToList sctree1) 11.

(* ****** *)

Definition scenario2 : PartOrd := [ [4; 7] ;
                                    [7; 3]
                                   ].

Definition sctree2 := [node 1 (node 3 (node 4 (node 9 empty empty) empty) (node 8 empty empty)) (node 5 (node 6 empty empty) (node 7 empty empty));
                     (node 2 (node 10 empty empty) (node 11 empty empty)) ].

(* Строим частичный порядок *)
Compute FinalizeOrdering sctree2 scenario2.
(* Строим какой-то обход *)
Compute TrunkTreeToList sctree2.
(* Строим для каждой вершины список вершин идущих после нее согласно частичному порядку *)
Compute Chains 11 (FinalizeOrdering sctree2 scenario2).
(* Проверяем корректность порядка *)
Compute IsOrdCorrect (Chains 11 (FinalizeOrdering sctree2 scenario2)) 0. (* 7 is imposter (7 < 3 < 4 < 7) *) 
(* Делам финальный обход *)
Compute ListToScen (FinalizeOrdering sctree2 scenario2) (TrunkTreeToList sctree2) 11.

(* End Testing *)

(* Comments *)
(* Возможно мы хотим для большей читаимости убрать из частичного порядка бесполезные элементы Done *)
(* Как доказать, что такое порядок корректен и что означает, что он корректен ? Done *)
(* Функция генерации частичного порядка соответсвует топологии дерева ( и дерева со стволом) *)
(* Для такого сгенерированного списка нужно сказать, что он соответствует корректному частичному порядку 
    Все вершины встретились и никакая не идет раньше чем должна по частичному порядку*)
(* ДОбавление частичного порядка для корректного частичного порядка дает корректный частичный порядок *)
(* Переписать функцию проверки частичного порядка и доказать ее сответствие???? текущей функции проверки *)
(* Доказать лемму, что если в частичном порядке нет проблем, то ветки не выполняются раньше соответствующих нод ствола
    и ствол выполняется "последовательно" *)
(* Если ываыва отправь это сообщение иначе другое???? *)





(* (* Сложение деревьев *)
Fixpoint LeftApp (t1 t2 : Tree superledger) :=
    match t1 with
    | empty => t2
    | node h l r => node h (LeftApp l t2) r
    end.

Compute LeftApp (node 1 (node 5 empty empty) (node 6 empty empty)) (node 2 (node 3 empty empty) (node 4 empty empty)).
(* Сборка дерева из стволового дерева *)
Fixpoint TreeFromTrunk (t : TrunkTree) : Tree superledger :=
    match t with
    | [] => empty
    | h :: e => LeftApp h (TreeFromTrunk e)
    end. *)
(* (* Естественный порядок ствола *)
Fixpoint TrunkOrd (t : TrunkTree) (p : PartOrd) :=
    match t with
    | [] => p
    | h :: e => let p1 := HeadToOrd (TreeFromTrunk (h::e)) p in
                    TrunkOrd e p1
    end. *)