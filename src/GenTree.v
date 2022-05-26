Require Import Coq.Strings.String List.
Require Import Ascii Printing.
Import ListNotations.
From mathcomp Require Import ssreflect ssrnat ssrbool zify.
Local Open Scope string_scope.

Require Import FinProof.Lib.GenTree.

Set Implicit Arguments.

Section PrintTree.

Context (T : Type) `{Show T}.

Arguments Node {_}.
Arguments Forest /.

Fixpoint unlines (l : list string) : string := 
  match l with 
  | []      => ""
  | l :: ls => l ++ \n ++ unlines ls
  end.

Fixpoint shift (fist : string) (other : string) (ls : list string) : list string := 
  match ls with 
  | []      => []
  | l :: ls => (fist ++ l) :: shift other other ls
  end.

Fixpoint draw (t : Tree T) : list string := 
  let: (Node x ts0) := t in 
  let drawSubTrees := 
    fix foo (ts : Forest T) :=
      match ts with 
      | []      => []
      | [t]     => "|" :: shift "`- " "   " (draw t)
      | t :: ts => "|" :: shift "+- " "|  " (draw t) ++ foo ts
      end in 
  show x :: drawSubTrees ts0.

Definition drawTree : Tree T -> string := 
  fun x => unlines (draw x).

Global Instance ShowString : Show string := {
  show := id
}.

Definition drawForest (f : Forest T) : string := unlines (map drawTree f).

End PrintTree.

#[local] Obligation Tactic := idtac.

#[global, program] Instance ShowTree {T} `{Show T} : 
  Show (Tree T).
Next Obligation.
  intros ??; refine (@drawTree _ _).
Defined.

#[global, program] Instance ShowForest {T} `{Show T} : 
  Show (Forest T).
Next Obligation.
  intros ??; refine (@drawForest _ _).
Defined.


Definition t1 := 
    Node "1"
     [Node "2" [Node "4" []; Node "5" []] ; Node "3" [] ; Node "4" [] ].

(* Compute (\n ++ drawForest [t1;t1;t1]). *)
