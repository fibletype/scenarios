Require Import BinNums List.
Require Import NArith.BinNat.
Require Import Coq.Strings.String.

Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmTypes.



Import ListNotations.

Local Open Scope N_scope.
Local Open Scope string_scope.

Definition linebreak := 
"
".

Notation "\n" := linebreak.


Class Show (T : Type) := {
  show : T -> string
}.

Definition show_small_N (n : N) := 
  match n with 
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | _ => "Not Small"
  end.

Unset Guard Checking.

Fixpoint show_N_aux (n : N) := 
  if n then "" else show_N_aux (n / 10) ++ show_small_N (n mod 10).

Set Guard Checking.

Definition show_N (n : N) := if n then "0" else show_N_aux n.
Definition show_positive (p : positive) := show_N (Npos p).
Definition show_Z (z : Z) := 
  match z with 
  | Z0     => "0"
  | Zpos z => show_positive z 
  | Zneg z => "-" ++ show_positive z
  end.

#[local] Obligation Tactic := idtac.

#[global, program] Instance ShowPosisive : Show positive.
Next Obligation.
refine show_positive.
Defined.

#[global, program] Instance ShowInt : Show Z.
Next Obligation.
refine show_Z.
Defined.

#[global, program] Instance ShowUint : Show N.
Next Obligation.
refine show_N.
Defined.

#[global, program] Instance ShowOption T `{Show T} : Show (option T).
Next Obligation.
intros ?? [ ]; [ refine (show t) | refine "None" ].
Defined.

#[global, program] Instance ShowUintN {n} : Show (XUBInteger n).
Next Obligation.
intros ? [x]; refine (show x).
Defined.

#[global, program] Instance ShowAddress : Show address.
Next Obligation.
intros [x [y] ].
refine ("[" ++ show x ++ ", " ++  show y ++ "]").
Defined.

#[global, program] Instance ShowBool : Show bool.
Next Obligation.
intros [ ].
refine "true".
refine "false".
Defined.

#[global, program] Instance ShowCell : Show cell_.
Next Obligation.
intros.
refine "cell_".
Defined.

Fixpoint pre_print_args (l : list string) : string := 
  match l with 
  | nil => ""
  | l :: nil => l 
  | l :: ls => l ++ ", " ++ pre_print_args ls 
  end.

Definition print_args (l : list string) := "(" ++ pre_print_args l ++ ")".

#[global, program] Instance ShowOutgoingMessage {T} `{Show T} : 
  Show (OutgoingMessage T).
Next Obligation.
intros T ? [| ? t].
{ destruct i. 
 refine ("transfer" ++ _).
 refine ("(" ++ (show x) ++ ")"). }
destruct i.
refine (show t ++ "(" ++ show x ++ ")").
Defined.

#[global, program] Instance ShowOr {T S} `{Show T} `{Show S} : 
  Show (T + S)%type.
Next Obligation.
intros T S ?? [t|t]; refine (show t).
Defined.
