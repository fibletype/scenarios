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

(* Функция поиска элемента в листе *)

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


(* Функция меняет лист с заданной головой на другой. Если такой головы нет у листов, то ничего не делает*)
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

Fixpoint TrunkTreeToOrd (t : TrunkTree) (p : PartOrd) : PartOrd :=
    match t with
    | [] => p
    | h :: e => let p1 := TreeToOrd h p in
                    TrunkTreeToOrd e p1
    end.

Fixpoint LeftApp (t1 t2 : Tree superledger) :=
    match t1 with
    | empty => t2
    | node h l r => node h (LeftApp l t2) r
    end.

Compute LeftApp (node 1 (node 5 empty empty) (node 6 empty empty)) (node 2 (node 3 empty empty) (node 4 empty empty)).

Fixpoint TreeFromTrunk (t : TrunkTree) : Tree superledger :=
    match t with
    | [] => empty
    | h :: e => LeftApp h (TreeFromTrunk e)
    end.

Fixpoint TrunkOrd (t : TrunkTree) (p : PartOrd) :=
    match t with
    | [] => p
    | h :: e => let p1 := TreeToOrd (TreeFromTrunk (h::e)) p in
                    TrunkOrd e p1
    end.

Definition FinalizeOrdering (t : TrunkTree) (p : PartOrd) := (TrunkOrd t p).


(* Testing *)
Definition scenario : PartOrd := [ [2; 4; 5; 6] ;
                                   [4; 5; 6] ;
                                   [6; 5]
                                   ].

Compute TreeToOrd ((node 2 (node 3 empty empty) (node 4 empty empty))) scenario.

Definition sctree := [node 1 (node 5 empty empty) (node 6 empty empty);
                     (node 2 (node 3 empty empty) (node 4 empty empty)) ].
Compute TreeFromTrunk sctree 0.
Compute TreeToOrd (TreeFromTrunk sctree) scenario.
Compute TrunkTreeToOrd sctree (TreeToOrd (TreeFromTrunk sctree) scenario).

Compute TrunkTreeToList sctree.

Compute ListToScen scenario (TrunkTreeToList sctree) 6.

(* ******* *)

Definition scenario1 : PartOrd := [ [3 ; 6]
                                   ].

Definition sctree1 := [node 1 (node 5 empty empty) (node 6 empty empty);
                     (node 2 (node 3 empty empty) (node 4 empty empty)) ].

Compute TrunkTreeToList sctree1.

Compute ListToScen scenario1 (TrunkTreeToList sctree1) 6.

(* ****** *)

Definition scenario2 : PartOrd := [ [7 ; 2 ; 3; 4] ;
                                    [6 ; 5] ;
                                    [5 ; 7]
                                   ].

Definition sctree2 := [node 1 (node 5 (node 7 empty empty) empty) (node 6 empty empty);
                     (node 2 (node 3 empty empty) (node 4 empty empty)) ].

Compute TrunkTreeToList sctree2.

Compute ListToScen scenario2 (TrunkTreeToList sctree2) 7.

(* ****** *)

Definition scenario3 : PartOrd := [ [7 ; 2 ; 3; 4] ;
                                    [6 ; 5]
                                   ].

Definition sctree3 := [node 1 (node 5 (node 7 empty empty) empty) (node 6 empty empty);
                     (node 2 (node 3 empty empty) (node 4 empty empty)) ].
Compute TrunkTreeToOrd sctree3 scenario3.
Compute TrunkTreeToList sctree3.
Compute ListToScen (TrunkTreeToOrd sctree3 scenario3) (TrunkTreeToList sctree3) 7.

(* Compute ListToScen scenario3 (TrunkTreeToList sctree3) 7. 
    Это пример показывает, что частичный порядок нужно дополнять 
    естественным порядком топологии графа *)

(* В связи с этим хочется дополнить частичный порядок естественным порядком графа DONE*)

(* ****** *)

(* Как доказать, что такое порядок корректен и что означает, что он корректен ?*)

(* Для такого сгенерированного списка нужно сказать, что он соответствует корректному частичному порядку *)

(* Доказать лемму, что если в частичном порядке нет проблем, то ветки не выполняются раньше соответствующих нод ствола
    и ствол выполняется "последовательно" *)


(* Кажется, что корректность порядка -- отсутствие противоречий типа 1 < 2 && 2 < 1 
    А также, что в нашем порядке вершина, которая явно идет раньше по графу не идет раньше по порядку *)
