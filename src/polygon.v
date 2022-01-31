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

Fixpoint MinTime (l : list superledger) (p : PartOrd) : option superledger :=
    match l with
    | nil => None
    | cons h t => if IsMin l h p then Some h else MinTime t p
    end.


Fixpoint TreeToList (t : Tree superledger) : list superledger :=
    match t with
    | empty => nil
    | node x l r => x :: TreeToList l ++ TreeToList r
    end.
      
    (* 
    Изначально я хотел обходить просто все дерево, но мне показалось это слишком сложно. Возможно лучше сначала генерировать просто обход,
    а потом из него уже делать православный обход
    if IsMin acc x P then  
                        match hdT l with
                        | None => x :: (VisitingTree r accTree acc)
                        | Some lh => x :: (VisitingTree r (cons l accTree) (cons lh acc) )
                        end
                    else
                        x :: (VisitingTree r (accTree) (acc) )
    end.
 *)
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
    | S n => match MinTime s p with
            | None => []
            | Some k => k :: ListToScen p (delete s k) n
    end
    end.

(* Как доказать, что такое порядок корректен и что означает, что он корректен *)

Definition scenario : PartOrd := [ [2; 4; 5; 6] ;
                                   [4; 2; 5; 6]
                                   ].

Definition sctree := [node 1 (node 5 empty empty) (node 6 empty empty);
                     (node 2 (node 3 empty empty) (node 4 empty empty)) ].

Compute TrunkTreeToList sctree.

Compute ListToScen scenario (TrunkTreeToList sctree) 6.

(* Доказать лемму, что если в частичном порядке нет проблем, то ветки не выполняются раньше соответствующих нод ствола
    и ствол выполняется "последовательно" *)