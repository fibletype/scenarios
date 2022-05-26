Require Import ssreflect.
From mathcomp Require Import ssrnat.
Require Import BinNums.
Require Import Coq.Strings.String.

Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Lib.GenTree. 
Require Import UMLang.UrsusLib.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.
Require Import UMLang.UrsusLib.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.


Require Import UrsusStdLib.Cpp.stdTypes.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.

Require Import KWproject.Contracts.KWDPool.DKWDPool.Interface.
Require Import KWproject.Contracts.KWDPool.DKWDPool.ClassTypes.
Require Import KWproject.Contracts.KWDPool.DKWDPool.Ledger.
Require Import KWproject.Contracts.KWDPool.DKWDPool.Functions.Funcs.
Require Import KWproject.Contracts.FromGiver.DFromGiver.Interface.
Require Import KWproject.Contracts.FromGiver.DFromGiver.ClassTypes.
Require Import KWproject.Contracts.FromGiver.DFromGiver.Ledger.
Require Import KWproject.Contracts.FromGiver.DFromGiver.Functions.Funcs.
Require Import KWproject.Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import KWproject.Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import KWproject.Contracts.Blank.DBlank.Interface.
Require Import KWproject.Contracts.Blank.DBlank.Ledger.
Require Import KWproject.Contracts.Blank.DBlank.Functions.Funcs.
Require Import KWproject.Project.CommonConsts.
Require Import KWproject.Project.CommonConstSig.
Require Import KWproject.Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import KWproject.Contracts.Blank.DBlank.ClassTypes.


(* Require Import BinNums NArith.BinNat. *)

Require Import BinNums ZArith.

Require Import SuperLedger.
Require Import MessageTree.
Require Import KWInstances.
Require Import Printing GenTree.

Require Import List.

Import ListNotations.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
(* Local Open Scope xlist_scope. *)


Set Implicit Arguments.

Section Scenario.

Notation LedgerClassT lT := 
  (LedgerClass 
    XBool
    (Ledger                  lT)
    (LedgerMainState         lT)
    (LedgerLocalState        lT)
    VMStateLRecord
    (LedgerMessagesAndEvents lT)
    GlobalParamsLRecord
    OutgoingMessageParamsLRecord).
(* 
Context (Interfaces Contracts : Type).
Context `{ContractsUtils Interfaces Contracts}.
 *)
Notation nodeType         := (@nodeType         Interfaces Contracts ).
Notation superLedger      := (@superLedger      Interfaces Contracts ).
Notation messageTree      := (@messageTree      Interfaces Contracts ).
Notation state            := (@state            Interfaces Contracts ).
Notation SuperLedger      := (@SuperLedger      Interfaces Contracts ).
Notation MessagesQueue    := (@MessagesQueue    Interfaces Contracts ).
Notation externalNodeType := (@externalNodeType Interfaces Contracts ).

Notation buildForest := 
  (@buildForest Interfaces Contracts ContractsUtilsKW simpleState _ _).

(* Print buildForest. *)

Definition defBlankLedger := Eval hnf in default : DBlank.Ledger.LedgerLRecord.
Definition defBlankContract := Eval hnf in default : DBlank.Ledger.ContractLRecord.


Definition defVMState := Eval hnf in default : VMStateLRecord.


Definition defKWDPoolLedger   := Eval hnf in default : DKWDPool.Ledger.LedgerLRecord.
Definition defKWDPoolContract := Eval hnf in default : DKWDPool.Ledger.ContractLRecord.

Definition addrKWDPOOL : address. 
split.
refine (210%Z).
refine (Build_XUBInteger 111%N).
Defined.

Definition addrBlank : address. 
split.
refine (210%Z).
refine (Build_XUBInteger 211%N).
Defined.

Definition addrFromGiver : address. 
split.
refine (210%Z).
refine (Build_XUBInteger 311%N).
Defined.

Definition addrGiver : address. 
split.
refine (210%Z).
refine (Build_XUBInteger 411%N).
Defined.

Definition defFromGiverLedger := Eval vm_compute in default : DFromGiver.Ledger.LedgerLRecord.
Definition defFromGiverContract := Eval vm_compute in default : DFromGiver.Ledger.ContractLRecord.

Definition sl1 : superLedger.
refine (cons (addrFromGiver, _) (cons (addrBlank, _ ) (cons (addrKWDPOOL, _) nil))).
{ refine (make_ledg FromGiver _).
  simpl.
  enough (VMStateLRecord).
  enough (DFromGiver.Ledger.ContractLRecord).
  refine  {$$ defFromGiverLedger with 
              (existT _ Ledger_MainState _);
              (existT _ Ledger_VMState _) $$}.
  refine X0.
  refine X.
  refine {$$ defFromGiverContract with
              (existT _ DFromGiver_ι_fund_address__ _); 
              (existT _ DFromGiver_ι_giver_address__ _); 
              (existT _ DFromGiver_ι_nonce__ _) 
  $$}.
  refine addrBlank.
  refine addrGiver.
  refine (Build_XUBInteger 317%N).
  refine {$$ defVMState with 
              (existT _ VMState_ι_pubkey _);
              (existT _ VMState_ι_balance _);
              (existT _ VMState_ι_address _)
  $$}.
  refine (Build_XUBInteger 10%N).
  refine (Build_XUBInteger 1228322%N).
  refine addrFromGiver.
}
{ refine (make_ledg Blank _).
  simpl.
  enough (VMStateLRecord).
  enough (DBlank.Ledger.ContractLRecord).
  refine  {$$ defBlankLedger with 
              (existT _ Ledger_MainState _);
              (existT _ Ledger_VMState _)
  $$}.
  refine X0.
  refine X.
  refine {$$ defBlankContract with
              (existT _ DBlank_ι_lock_time__ _);
              (existT _ DBlank_ι_unlock_time__ _);
              (existT _ DBlank_ι_farm_rate__ _);
              (existT _ DBlank_ι_kwf_lock_time__ _);
              (existT _ DBlank_ι_quant__ _);
              (existT _ DBlank_ι_min_summa__ _);
              (existT _ DBlank_ι_max_summa__ _)
  $$}.
  refine (Build_XUBInteger 420%N).
  refine (Build_XUBInteger 1296000%N).
  refine (Build_XUBInteger 80%N).
  refine (Build_XUBInteger 180%N).
  refine (Build_XUBInteger 10000000000%N).
  refine (Build_XUBInteger 1800000%N).
  refine (Build_XUBInteger 18000000000000000%N).
  refine {$$ defVMState with 
              (existT _ VMState_ι_pubkey _);
              (existT _ VMState_ι_balance _);
              (existT _ VMState_ι_address _)
  $$}.
  refine (Build_XUBInteger 10%N).
  refine (Build_XUBInteger 30000000000%N).
  refine addrBlank.
}
refine (make_ledg KWDPool _).
simpl.
enough (VMStateLRecord).
  enough (DKWDPool.Ledger.ContractLRecord).
  refine  {$$ defKWDPoolLedger with 
              (existT _ Ledger_MainState _);
              (existT _ Ledger_VMState _)
  $$}.
  refine X0.
  refine X.
  refine {$$ defKWDPoolContract with
              (existT _ DKWDPool_ι_fund_address__ _);
              (existT _ DKWDPool_ι_nonce__ _)
  $$}.
  refine (addrBlank).
  refine (Build_XUBInteger 1%N).
  refine {$$ defVMState with 
              (existT _ VMState_ι_pubkey _);
              (existT _ VMState_ι_balance _);
              (existT _ VMState_ι_address _)
  $$}.
  refine (Build_XUBInteger 10%N).
  refine (Build_XUBInteger 400000000000%N).
  refine addrKWDPOOL.
Defined.


Definition step1_deploy : externalNodeType.
refine (make_enode DBlank_ _ _ default _ _ default).
simpl. refine (OutgoingInternalMessage default _) .
refine (Interface._Iconstructor _ _).
refine (Build_XUBInteger 1800000%N).
refine (Build_XUBInteger 18000000000000000%N).
refine addrBlank.
refine (Build_XUBInteger (BinNat.N.of_nat 10)).
refine (Build_errorType None false).
Defined.

Definition step2_setHash : externalNodeType.
refine (make_enode DBlank_ _ _ default _ _ default).
simpl. refine (OutgoingInternalMessage default _) .
refine (Interface.IsetKWDPoolCodeHash _ _).
refine (Build_XUBInteger 137%N).
refine (Build_XUBInteger 1232%N).
refine addrBlank.
refine (Build_XUBInteger (BinNat.N.of_nat 10)).
refine (Build_errorType None false).
Defined.

Definition step3_deployKWD : externalNodeType.
refine (make_enode KWDPool_  _ _ default _ _ default).
simpl. refine (OutgoingInternalMessage default _) .
refine (DKWDPool.Interface._Iconstructor  _).
refine None.
refine addrKWDPOOL.
refine (Build_XUBInteger (BinNat.N.of_nat 10)).
refine (Build_errorType None false).
Defined.

Definition step4_setHash : externalNodeType.
refine (make_enode DBlank_ _ _ default _ _ default).
{ simpl. refine (OutgoingInternalMessage default _).
  refine (Interface.IsetFromGiverCodeHash (Build_XUBInteger 311%N) default). }
{ refine addrBlank. }
{ refine (Build_XUBInteger (BinNat.N.of_nat 10)). }
refine (Build_errorType None false).
Defined.

Definition step5_deployFG : externalNodeType.
refine (make_enode DBlank_ _ _ default _ _ default).
{ simpl. refine (OutgoingInternalMessage default _).
  refine (Interface.IdeployFromGiver (tvmCells.Build_CellSliceBuilder _ _) addrFromGiver _).
  { refine (tvmCells.NormalCell 311%N _ _ _ _); refine tvmCells.EmptyCell. }
  refine (Build_XUBInteger 317%N). }
{ refine addrBlank. }
{ refine (Build_XUBInteger (BinNat.N.of_nat 10)). }
refine (Build_errorType None false).
Defined.

Definition step6_transferKWDP : externalNodeType.
refine (make_enode IDef _ _ addrGiver _ _ default).
{ refine (EmptyMessage _ _).
  split; first refine (Build_XUBInteger 10000000001%N).
  split; first refine false.
  split; first refine default. }
{ refine addrKWDPOOL. }
{ refine (Build_XUBInteger 10%N). }
refine (Build_errorType None false).
Defined.

Definition step7_transferFG (fs : uint128) : externalNodeType.
refine (make_enode IDef _ _ addrGiver _ _ default).
{ refine (EmptyMessage _ _).
  split; first refine fs.
  split; first refine false.
  split; first refine default. }
{ refine addrFromGiver. }
{ refine (Build_XUBInteger 10%N). }
refine (Build_errorType None false).
Defined.

Definition step8_finalizeKWD : externalNodeType.
refine (make_enode DBlank_ _ _ default _ _ _).
{ refine (OutgoingInternalMessage default _).
  refine (Interface.Ifinalize _ _).
  refine false.
  refine addrKWDPOOL. }
{ refine addrBlank. }
{ refine (Build_XUBInteger 10%N). }
{ refine (Build_errorType None false). }
refine (Build_XUBInteger 450%N).
Defined.

Definition step9_finalizeFG : externalNodeType.
refine (make_enode DBlank_ _ _ default _ _ _).
{ refine (OutgoingInternalMessage default _).
  refine (Interface.Ifinalize _ _).
  refine false.
  refine addrFromGiver. }
{ refine addrBlank. }
{ refine (Build_XUBInteger 10%N). }
{ refine (Build_errorType None false). }
refine (Build_XUBInteger 460%N).
Defined.

Definition step10_startVoting : externalNodeType.
refine (make_enode DBlank_ _ _ default _ _ _).
{ refine (OutgoingInternalMessage default _).
  refine (Interface.IstartVoting _ _).
  refine (Build_XUBInteger 690699%N).
  refine default. }
{ refine addrBlank. }
{ refine (Build_XUBInteger 10%N). }
{ refine (Build_errorType None false). }
refine (Build_XUBInteger 500%N).
Defined.

Definition step11_Vote  (b : bool)  : externalNodeType.
refine (make_enode KWDPool_ _ _ default _ _ _).
{ refine (OutgoingInternalMessage default _).
  refine (DKWDPool.Interface.Ivote _ _ _).
  refine b.
  { refine (Build_XUBInteger 0%N). }
  refine default. }
{ refine addrKWDPOOL. }
{ refine (Build_XUBInteger 10%N). }
{ refine (Build_errorType None false). }
refine (Build_XUBInteger 600%N).
Defined.

(* Import KW. *)

Import ListNotations.

(* Definition scen_part1   := Eval vm_compute in [step1_deploy      ; step2_setHash   ; step3_deployKWD].
Definition scen_part2   := Eval vm_compute in [step4_setHash     ; step5_deployFG                   ].
Definition scen_part3   := Eval vm_compute in [step6_transferKWDP; step7_transferFG                 ].
Definition scen_part4   := Eval vm_compute in [step8_finalizeKWD ; step9_finalizeFG                 ].
Definition scen_part5   := Eval vm_compute in [step10_startVoting; step11_Vote                      ].
Definition scen1        := scen_part1 ++ scen_part2 ++ scen_part3 ++ scen_part4 ++ scen_part5 .


(* Definition forest1 := Eval vm_compute in (buildForest 5 scen_part1 superLedgerForScen1). *)

(* Eval vm_compute in checkForest forest1 scen_part1 superLedgerForScen1.  *)

(* Print KWproject.Contracts.Blank.DBlank.Functions.Funcs.deployFromGiver_. *)

Definition forest2 := Eval vm_compute in
  buildForest 50
    (scen_part1 ++ scen_part2 ++ scen_part3 ++ scen_part4 ++ (scen_part5))
    sl1.

Definition sl := Eval vm_compute in 
  buildSLedger 50
    (scen_part1 ++ scen_part2 ++ scen_part3 ++ scen_part4 ++ scen_part5 )
    sl1. 

Compute show forest2. *)

(*

DBlank -> setFromGriverCodeHash(123, default)
DBlank -> deployFromFiver(NormalCell 123 e e e e, [310, 311], 317? )


*)

(* Compute show (buildSLedger (cons step1_deploy (cons step2_setHash (cons step3_deployKWD nil))) superLedgerForScen1). *)

(* Compute (show (inl step3_deployKWD)). *)

(* Compute InterpretNode (inl step1_deploy) superLedgerForScen1. *)


(* Compute show (buildForest (cons step1_deploy (cons step2_setHash nil)) superLedgerForScen1). *)

(* Compute buildSLedger (cons step1_deploy (cons step2_setHash nil)) superLedgerForScen1. *)

(* Eval vm_compute in show (buildSLedger (cons step1_deploy (cons step2_setHash (cons step3_deployKWD nil))) superLedgerForScen1).  *)

(* Eval vm_compute in checkForest (buildForest (cons step1_deploy (cons step2_setHash (cons step3_deployKWD nil))) superLedgerForScen1).  *)

Import ListNotations.

Definition scen_part1    := [step1_deploy      ; step2_setHash   ; step3_deployKWD].
Definition scen_part2    := [step4_setHash     ; step5_deployFG                   ].
Definition scen_part3 fs := [step6_transferKWDP; step7_transferFG  fs           ].
Definition scen_part4    := [step8_finalizeKWD (* ; step9_finalizeFG *)                 ].
Definition scen_part5 b  := [step10_startVoting; step11_Vote b                    ].
(* Definition scen1      b := scen_part1 ++ scen_part2 ++ scen_part3 ++ scen_part4 ++ scen_part5 b. *)
Definition scen2  fs    := scen_part1 ++ scen_part2 ++ scen_part3 fs ++ scen_part4.

(* Definition forest1 := Eval vm_compute in (buildForest 5 scen_part1 superLedgerForScen1). *)

(* Eval vm_compute in checkForest forest1 scen_part1 superLedgerForScen1.  *)

(* Print KWproject.Contracts.Blank.DBlank.Functions.Funcs.deployFromGiver_. *)

(* Definition forest1 b := 
  buildForest 50
    (scen1 b)
    sl1.

Definition slf1 b :=
  buildSLedger 50
    (scen1 b)
    sl1. *)
    
Definition forest2 fs := 
  buildForest 50 (scen2 fs) sl1.

Definition slf2 fs :=
  buildSLedger simpleState 50 (scen2 fs) sl1.

Definition make_internalParams (balance : uint128) (b : boolean) (pub : uint16) : InternalMessageParamsLRecord.
split.
exact balance.
split.
exact b.
exact pub.
Defined.

Coercion XUBInteger2N {n} (a : XUBInteger n) : N.
destruct a.
refine x.
Defined.

Fixpoint Tree_bIn (n : nodeType) (mt : messageTree) : bool :=
  match mt with Node x l => 
    let fix Trees_bIn nod li :=
      match li with 
      | h :: t => orb (Tree_bIn nod h) (Trees_bIn nod t) 
      | _ => false
      end in orb (eqb n x) (Trees_bIn n l)
  end.

(* Set Nested Proofs Allowed. *)

Compute show (forest2 (Build_XUBInteger 100%N)).

From mathcomp Require Import ssrbool.

Definition getFieldKWD (f : DKWDPoolFields) (l : @ledgerWithType _ _ ContractsUtilsKW) : 
  option (field_type f) :=
    match l with
    | make_ledg KWDPool L => Some 
        (f 
          (KWproject.Contracts.KWDPool.DKWDPool.Ledger.LedgerLGetField 
           Ledger_MainState 
           L))
    | _         => None 
    end.

Definition getFieldBlank (f : DBlankFields) (l : @ledgerWithType _ _ ContractsUtilsKW) : 
  option (field_type f) :=
    match l with
    | make_ledg Blank L => Some 
        (f 
          (KWproject.Contracts.Blank.DBlank.Ledger.LedgerLGetField 
           Ledger_MainState 
           L))
    | _         => None 
    end.

Notation getKWD := KWproject.Contracts.KWDPool.DKWDPool.Ledger.LedgerLGetField.

Definition sl_after_deploy := Eval vm_compute in
  buildSLedger simpleState 50 (scen_part1 ++ scen_part2) sl1.

Definition transfer_rest (summa_givers : uint128) : bool := 
  let kwd1      := led sl_after_deploy[addrKWDPOOL]                      in
  let farm_rate := DKWDPool_ι_farm_rate__ (getKWD Ledger_MainState kwd1) in 
  let quant     := DKWDPool_ι_quant__     (getKWD Ledger_MainState kwd1) in 
  (summa_givers <? quant * farm_rate / 100) && (KWMessages_ι_FG_MIN_BALANCE_ <? summa_givers) ==>
    let ms := 
      make_inode 
        IDef 
        (EmptyMessage PhantomType (make_internalParams 
        (Build_XUBInteger ((quant * (quant * farm_rate / 100 - summa_givers)) / ( quant * farm_rate / 100)) )
        true 
        (Build_XUBInteger 1))) 
        addrGiver 
        addrKWDPOOL 
        (Build_errorType None true) in 
    existsb (fun tr => Tree_bIn (inr ms) tr) (forest2 summa_givers).

Arguments sl1                     : simpl never.
Arguments existsb                 : simpl nomatch.
Arguments existsb                 : simpl never.
Arguments N.mul                   : simpl nomatch.
Arguments N.div                   : simpl nomatch.
Arguments N.sub                   : simpl nomatch.
Arguments buildSLedger            : simpl never.
Arguments Tree_bIn                : simpl never.
Arguments InterpretNode           : simpl never.
Arguments Builds                  : simpl never.
Arguments run                     : simpl never.
Arguments xfst                    : simpl never. 
Arguments buildForestT            : simpl never.
Arguments Build                   : simpl never.
Arguments MessageTree.buildForest : simpl never.
Arguments app                     : simpl never.

Definition kwd1      := Eval vm_compute in led sl_after_deploy[addrKWDPOOL].
Definition farm_rate := Eval vm_compute in DKWDPool_ι_farm_rate__ (getKWD Ledger_MainState kwd1).
Definition quant     := Eval vm_compute in DKWDPool_ι_quant__ (getKWD Ledger_MainState kwd1).
Definition fsp1      := Eval vm_compute in buildForest 50 scen_part1 sl1.
Definition slsp1     := Eval vm_compute in buildSLedger simpleState 50 scen_part1 sl1.
Definition fsp2      := Eval vm_compute in buildForest (50 - 3) scen_part2 slsp1.
Definition slsp2     := Eval vm_compute in buildSLedger simpleState (50 - 3) scen_part2 slsp1.
Definition fsp3      := Eval vm_compute in buildForest (50 - 3 - 2) (step6_transferKWDP::nil) slsp2.
Definition slsp3     := Eval vm_compute in buildSLedger simpleState (50 - 3 - 2) (step6_transferKWDP::nil) slsp2.
Definition slsp3'    := Eval vm_compute in setTime (getTime (inl (step7_transferFG default))) slsp3.
Arguments slsp3 : simpl never.

(* Section foo.

Context {T S : Type} (f : T -> list T -> T -> S) (t : T).


Check (f t [t]).


End foo.
Locate "_ [ _ ]". *)

Context (P : superLedger -> Prop) 
  (Q : @InterpretNode_ans _ _ ContractsUtilsKW -> Prop).

Lemma IN7 summa_givers :
  tss_of (InterpretNode (inl (step7_transferFG summa_givers)) slsp3') = nil.
Proof.
rewrite /InterpretNode.
Definition fgiver := Eval vm_compute in slsp3' [getAddrR (inl (step7_transferFG default))].
change (slsp3' [getAddrR (inl (step7_transferFG summa_givers))] ?) with (Some fgiver). 
rewrite /tss_of.
change (slsp3' [getAddrR (inl (step7_transferFG summa_givers))]) with fgiver.
rewrite [in tp fgiver]/fgiver /tp.
Opaque fgiver.
simpl.
rewrite /eq_rect_r /eq_rect /=.
set (ledg := exec_super_state _ _ _ _ _ _ _).
have: 
  (DFromGiver.Ledger.LedgerLGetField Ledger_MessagesState (fst ledg)) = default.
{ rewrite /default /= /ledg /exec_super_state.
  rewrite /interpret_message /interpret_function.
  Arguments Uinterpreter : simpl never.
  simpl.
  rewrite /interpret_params /eq_rect /isoVMState /LedgerClassC /=.
  Transparent fgiver.
  (* rewrite /receive_.
  set (X := Uinterpreter _).
  case E: (run _ _)=> [res r'].
  set (r'' := fst _).
  have->: r'' = r' by rewrite /r''; case: (isError _).
  move/(f_equal xsnd) : E=> /= <-.
  rewrite -[xsnd (run _ _)]/(exec_state _ _).
  Transparent fgiver.
  rewrite /led /=.
  set (inm := interpret_message _ _ _ _ _).
  rewrite /interpret_message in inm.
   }
change (slsp3' [getAddrR (inl (step7_transferFG summa_givers))] ?) with fgiver.
case E: fgiver=> //.
Opaque exec_super_state.
change ()
rewrite /tss_of /eq_rect_r /eq_rect /eq_sym /isoMessages /=.
simpl. *)
Admitted.

Lemma IN_sp summa_givers : 
  P (setTime (getTime (inl step8_finalizeKWD))
     (buildSLedger simpleState (50 - 3 - 2 - 1)
        (step7_transferFG summa_givers :: nil) slsp3)).
Proof.
rewrite /getTime /step8_finalizeKWD /buildSLedger.
rewrite exec_state_buildForest1E.
change (setTime (getTime (inl (step7_transferFG summa_givers))) slsp3) with slsp3'.
rewrite /exec_state run_BuildE.
case E: (InterpretNode _ _)=> [sli tssi erri]. 
simpl.
Admitted.

From mathcomp Require Import fintype ssrnat zify.

Theorem transfer_rest_proof (summa_givers : uint128) : transfer_rest summa_givers.
Proof.
rewrite /transfer_rest.
change (led sl_after_deploy[addrKWDPOOL]) with kwd1.
change (DKWDPool_ι_farm_rate__ (getKWD Ledger_MainState kwd1)) with farm_rate.
change (DKWDPool_ι_quant__ (getKWD Ledger_MainState kwd1)) with quant.
apply/implyP=> /andP-[??].
rewrite /forest2 /scen2 /scen_part3.
change (scen_part1 ++
        scen_part2 ++
      ([step6_transferKWDP; step7_transferFG summa_givers]) ++ scen_part4)
     with (scen_part1 ++
           scen_part2 ++
          [step6_transferKWDP] ++ [step7_transferFG summa_givers] ++ scen_part4).
do ? (rewrite buildForest_cat; last try reflexivity).
rewrite /= 4?existsb_app; apply/or3P/Or33/or3P/Or33.
change (buildForest 50 scen_part1 sl1) with fsp1.
change (buildSLedger simpleState 50 scen_part1 sl1) with slsp1.
change (buildForest (50 - 3) scen_part2 slsp1) with fsp2.
change (buildSLedger simpleState (50 - 3) scen_part2 slsp1) with slsp2.
change (buildForest (50 - 3 - 2) (step6_transferKWDP::nil) slsp2) with fsp3.
change (buildSLedger simpleState (50 - 3 - 2) (step6_transferKWDP::nil) slsp2) with slsp3.
rewrite /buildForest eval_state_buildForest1E /existsb orbF /eval_state run_BuildE.
case E: (InterpretNode _ _)=> [sli tssi erri]. 
simpl.
admit.
(* vm_compute.
reflexivity.
set x := (buildFinished _ _ _ _).
pose proof (y := x).
Definition y := Eval vm_compute in .

vm_compute.
 *)
(* 
simpl. *)

Admitted.


End Scenario.

From QuickChick Require Import QuickChick.

Import QcDefaultNotation.

Open Scope qc_scope.

Import GenLow GenHigh.

Set Warnings "-extraction-opaque-accessed,-extraction".

(* Import KW. *)
(* QuickCheck transfer_rest. *)
(*   
Proof.
  Definition
  sl' := Eval vm_compute in slf2.
  exists (led sl'[addrKWDPOOL]).
  intros kwd.
  exists (led sl'[addrBlank]).
  intros bla.
  Definition 
  forest := Eval vm_compute in forest2.
  exists (hd default (tl (tl (tl (tl (tl (tl (tl forest)))))))).
  intros farm_rate quant summa_givers final_address.
  vm_compute in farm_rate.
  vm_compute in quant.
  vm_compute in summa_givers.
  vm_compute in final_address.
  enough (summa_givers <? quant * farm_rate / 100 = true) as t.
  rewrite t.
  intros ms.
  unfold forest.
  all : reflexivity.
Qed. *)




(* Lemma voting_result1 b : 
  exists2 sled : LedgerLRecord, make_ledg Blank sled = (slf1 b)[addrBlank] &
   DBlank_ι_voting_result__ (KWproject.Contracts.Blank.DBlank.Ledger.LedgerLGetField Ledger_MainState sled) = Some b.
Proof.
  destruct b.
  { Definition
   sl' := Eval vm_compute in (slf1 true).
   reflexivity.  }
  Definition
   sl'' := Eval vm_compute in (slf1 false).
  exists (led sl''[addrBlank]); reflexivity.
Qed. *)


Set Printing Depth 10000.
(* Compute show forest2. *)

(* Compute show sl.  *)

(* Definition tree3 : messageTree.
remember  fr.
refine (hd (Node (inl (make_enode _ _ _ default _)) nil) (tl (tl fr))).
refine default.
refine default.
refine (Build_errorType None false).
Unshelve.
refine KW.DBlank_.
Defined.

Definition ledger3 : superLedger.
refine (buildSLedger (cons step1_deploy (cons step2_setHash nil)) superLedgerForScen1).
Defined. *)

(* Eval vm_compute in show (buildForest (cons step1_deploy (cons step2_setHash (cons step3_deployKWD nil))) superLedgerForScen1).  *)
(* 
Definition scen1 := Eval vm_compute in (cons step1_deploy (cons step2_setHash (cons step3_deployKWD nil))).

Definition fr := Eval vm_compute in (buildForest scen1 default).

Eval vm_compute in checkForest fr scen1 superLedgerForScen1.

Compute eval_state (checkTreeT tree3 (snd fst (InterpretNode (Tree.root tree3) ledger3) )) .

(* Eval vm_compute in checkForest fr scen1 superLedgerForScen1. *)

Compute show (buildForest (cons step1_deploy (cons step2_setHash (cons step3_deployKWD nil))) superLedgerForScen1).
(* Print DKWDPool.Functions.Funcs.check_fund. *)
Compute buildSLedger (cons step1_deploy (cons step2_setHash (cons step3_deployKWD nil))) superLedgerForScen1.
 *)

