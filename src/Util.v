Require Import BinNums List.
Require Import NArith.BinNat.
Require Import Coq.Strings.String.

Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import FinProof.Common.

Local Obligation Tactic := idtac.
Local Open Scope bool_scope.

#[global, program] 
Instance XBoolEquableOutgoingMessage {I} `{XBoolEquable bool I} : 
  XBoolEquable bool (OutgoingMessage I).
Next Obligation.
intros ?? [ip1|ip1 i1] [ip2|ip2 i2]; [|refine false|refine false|].
{ refine (eqb ip1 ip2). }
refine (eqb ip1 ip2 && eqb i1 i2).
Defined.