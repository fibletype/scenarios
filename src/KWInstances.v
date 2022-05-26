Require Import ssreflect.
Require Import BinNums.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.

Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21.
Require Import FinProof.ProgrammingWith. 
Require Import List.
Require Import FinProof.MonadTransformers21. 
Require Import UMLang.UrsusLib.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.

Require Import SuperLedger GenTree Printing Utils MessageTree.

Require Import KWproject.Contracts.Blank.DBlank.Interface.
Require Import KWproject.Contracts.Blank.DBlank.Ledger.
Require Import KWproject.Contracts.Blank.DBlank.Functions.Funcs.
Require Import KWproject.Contracts.KWDPool.DKWDPool.Interface.
Require Import KWproject.Contracts.KWDPool.DKWDPool.Ledger.
Require Import KWproject.Contracts.KWDPool.DKWDPool.Functions.Funcs.
Require Import KWproject.Contracts.FromGiver.DFromGiver.Interface.
Require Import KWproject.Contracts.FromGiver.DFromGiver.Ledger.
Require Import KWproject.Contracts.FromGiver.DFromGiver.Functions.Funcs.
Require Import KWproject.Contracts.Interfaces.IBlank.IBlank.Interface.
Require Import KWproject.Contracts.Interfaces.IKWFund.IKWFund.Interface.
Require Import KWproject.Contracts.Interfaces.IKWFundParticipant.IKWFundParticipant.Interface.
Require Import KWproject.Project.CommonConsts.
Require Import KWproject.Project.CommonQCEnvironment.
Require Import KWproject.Contracts.Blank.DBlank.ClassTypes.
Require Import KWproject.Contracts.ProofsCommon.

Require Import NArith.BinNat.
Require Import FinProof.Lib.BoolEq.


Import UrsusNotations.
Import CommonConstSig.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Set Typeclasses Depth 100.

(* Module KW. *)

Section Instances.

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

Definition blankLedgerType := 
  Build_ledgerType 
    DBlank.Ledger.LedgerLRecord 
    DBlank.Ledger.ContractLRecord
    DBlank.Ledger.LocalStateLRecord
    DBlank.Ledger.MessagesAndEventsLRecord.

Definition kwdpoolLedgerType := 
  Build_ledgerType 
    DKWDPool.Ledger.LedgerLRecord 
    DKWDPool.Ledger.ContractLRecord
    DKWDPool.Ledger.LocalStateLRecord
    DKWDPool.Ledger.MessagesAndEventsLRecord.

Definition fromgiverLedgerType := 
  Build_ledgerType 
    DFromGiver.Ledger.LedgerLRecord 
    DFromGiver.Ledger.ContractLRecord
    DFromGiver.Ledger.LocalStateLRecord
    DFromGiver.Ledger.MessagesAndEventsLRecord.

Inductive Contracts := 
  | Blank
  | KWDPool
  | FromGiver.

Inductive Interfaces :=
  | DBlank_
  | KWDPool_
  | FromGiver_
  | IBlank_
  | IKWFund_
  | IKWFundParticipant_
  | IDef.

Definition getInterface : Interfaces -> Type := 
  fun I => 
    match I with 
    | DBlank_             => IDBlank
    | KWDPool_            => IDKWDPool
    | FromGiver_          => IDFromGiver
    | IBlank_             => IBlank
    | IKWFund_            => IKWFund
    | IKWFundParticipant_ => IKWFundParticipant
    | IDef                => PhantomType
    end.

(* Coercion getInterface : Contracts >-> Sortclass. *)

Definition getLedger : Contracts -> ledgerType := 
  fun I => 
    match I with 
    | Blank     => blankLedgerType
    | KWDPool   => kwdpoolLedgerType
    | FromGiver => fromgiverLedgerType
    end.

Arguments make_exp _ {_ _ _ _} _.

Definition fallback {rT} `{LedgerClassT rT} : UExpressionWithType rT := 
  @make_exp rT _ PhantomType _ true {{ require_ (FALSE, #{default} ); return_ {} }}.

Definition onbounce {rT} `{LedgerClassT rT} : UExpressionWithType rT := 
  @make_exp rT _ PhantomType _ true {{ require_ (TRUE, #{default} ); return_ {} }}.

Definition receive {rT} `{LedgerClassT rT} : UExpressionWithType rT := 
  @make_exp rT _ PhantomType _ false {{ return_ {} }}.

Definition process_messages (I : Interfaces) :
  XHMap address (XQueue (OutgoingMessage (getInterface I))) -> 
  list (address * list {I & OutgoingMessage (getInterface I)}) := 
  fun ms => (map (fun '(a, q) => (a, map (existT _ I) (xHMapElems q))) ms).

Definition process_message 
  (I : Interfaces) 
  (m : OutgoingMessage (getInterface I)) 
  (a : address) :
  XHMap address (XQueue (OutgoingMessage (getInterface I))) ->
  XHMap address (XQueue (OutgoingMessage (getInterface I))) :=
  fun hm => hm[a] ← (hmapPush m hm[a]).

#[local] Obligation Tactic := idtac.

#[global, program] Instance ContractsUtilsKW : ContractsUtils Interfaces Contracts.
Next Obligation.
now apply getInterface.
Defined.
Next Obligation.
now apply getLedger.
Defined.
Next Obligation.
split.
refine Blank.
Defined.
Next Obligation.
split.
refine default.
Qed.
Next Obligation.
unfold ContractsUtilsKW_obligation_2.
destruct C.
simpl. 
refine DBlank.Ledger.ledgerClass.
refine DKWDPool.Ledger.ledgerClass.
refine DFromGiver.Ledger.ledgerClass.
Defined.
Next Obligation.
unfold ContractsUtilsKW_obligation_1.
unfold ContractsUtilsKW_obligation_2.
split.
destruct I, C; simpl.
{ intros.
  destruct X eqn:blank.
  { refine (make_exp blankLedgerType DBlank.Functions.Funcs.getTimes_). }
  { refine (make_exp blankLedgerType DBlank.Functions.Funcs.getInvestorsNumbers_). }
  { refine (make_exp blankLedgerType DBlank.Functions.Funcs.getGiversSum_). }
  { refine (make_exp blankLedgerType DBlank.Functions.Funcs.getInvestorsSum_). }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.killBlank_ a)). 
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp blankLedgerType  (DBlank.Functions.Funcs.startVoting_ x x0)).
    { refine KWErrors_ι_voting_time_too_long_. }
    { refine KWErrors_ι_voting_time_too_low_. }
    { refine KWMessages_ι_MIN_VOTING_TIME_. }
    { refine KWMessages_ι_TIME_FOR_SETCODE_PREPARE_. }
    refine KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_. }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.vote_ x x0 x1 x2 x3 x4)).
    { refine KWErrors_ι_voting_fee_too_low_. }
    refine KWMessages_ι_VOTING_FEE_. }
  { refine (make_exp blankLedgerType  (DBlank.Functions.Funcs.setFundCode_ c)). 
    { refine KWMessages_ι_TIME_FOR_FUNDS_COLLECTING_. }
    refine KWMessages_ι_RESPAWN_BALANCE_. }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.finalize_ x a)).
    { refine KWMessages_ι_GAS_FOR_PARTICIPANT_MESSAGE_. }
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.acknowledgeFinalizeRight_ a x x0)). }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.acknowledgeFinalizeLeft_ x x0)). }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.notifyRight_ a x x0 x1)).
    { refine KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_. }
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.acknowledgeDeploy_ a x)). }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.deployFromGiver_ c a x)).
  { refine KWMessages_ι_FG_MIN_BALANCE_. } 
  refine KWMessages_ι_EPSILON_BALANCE_.  }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.notifyLeft_ x x0 x1 x2)).
    { refine KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_. }
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp blankLedgerType (Blank.DBlank.Functions.Funcs.isFundReady_ x x0)). 
    refine KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_. }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.setKWDPoolCodeHash_ x x0)). 
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp blankLedgerType (DBlank.Functions.Funcs.setFromGiverCodeHash_ x x0)). 
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp blankLedgerType (Blank.DBlank.Functions.Funcs.constructor_ x x0)).
    refine KWMessages_ι_BLANK_MIN_BALANCE_. }
   }
{ intros; refine fallback. }
{ intros; refine fallback. }
{ intros; refine fallback. }
{ intros. 
  destruct X eqn:kwdpool; simpl.
  { refine (make_exp kwdpoolLedgerType DKWDPool.Functions.Funcs.isFundReady_). }
  { refine (make_exp kwdpoolLedgerType DKWDPool.Functions.Funcs.getBalance_). }
  { refine (make_exp kwdpoolLedgerType DKWDPool.Functions.Funcs.isInitialized_). }
  { refine (make_exp kwdpoolLedgerType DKWDPool.Functions.Funcs.onVoteAccept_). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.onVoteReject_ x)). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.vote_ x x0 x1)).
    { refine KWMessages_ι_VOTING_FEE_. }
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.returnExtraFunds_ a)).
    { refine KWMessages_ι_KWD_MIN_BALANCE_. }
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.returnFunds_ a)).
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.sendFunds_ c)).
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType DKWDPool.Functions.Funcs.acknowledgeFunds_). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.setFinalAddress_ a)).
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.notifyParticipant_ x x0 x1)).
     refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType DKWDPool.Functions.Funcs.receive_).
    { refine KWMessages_ι_DEFAULT_MSG_FLAGS_. }
    { refine KWMessages_ι_GAS_FOR_FUND_MESSAGE_. }
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.initialize_ x x0 x1 x2 x3)). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.constructor_ x)).
    { refine KWMessages_ι_GAS_FOR_FUND_MESSAGE_. }
    refine KWMessages_ι_KWD_MIN_BALANCE_. }
   }
1-3: intros; refine fallback.
{ intros X.
  destruct X eqn:fromgiver.
  { refine (make_exp fromgiverLedgerType DFromGiver.Functions.Funcs.onVoteAccept_). }
  { refine (make_exp fromgiverLedgerType (DFromGiver.Functions.Funcs.onVoteReject_ x)). }
  { refine (make_exp fromgiverLedgerType DFromGiver.Functions.Funcs.returnFunds_).
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp fromgiverLedgerType (DFromGiver.Functions.Funcs.sendFunds_ c)).
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp fromgiverLedgerType DFromGiver.Functions.Funcs.acknowledgeFunds_). }
  { refine (make_exp fromgiverLedgerType (DFromGiver.Functions.Funcs.notifyParticipant_ x x0 x1)).
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp fromgiverLedgerType (DFromGiver.Functions.Funcs.receive_)).
    { refine KWMessages_ι_FG_MIN_BALANCE_. }
    { refine KWMessages_ι_GAS_FOR_FUND_MESSAGE_. }
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp fromgiverLedgerType (DFromGiver.Functions.Funcs.initialize_ x x0 x1 x2 x3)). }
  { refine (make_exp fromgiverLedgerType (DFromGiver.Functions.Funcs.constructor_ x x0)).
    refine KWMessages_ι_GAS_FOR_FUND_MESSAGE_. }
   }

all :intros. (destruct X eqn:blank).
{ refine (make_exp blankLedgerType (DBlank.Functions.Funcs.vote_ x x0 x1 x2 x3 x4)).
  refine KWErrors_ι_voting_fee_too_low_.
  refine KWMessages_ι_VOTING_FEE_.
   }
{ refine (make_exp blankLedgerType (DBlank.Functions.Funcs.acknowledgeDeploy_ a x)). }
{ refine (make_exp blankLedgerType (DBlank.Functions.Funcs.acknowledgeFinalizeRight_ a x x0)). }
{ refine (make_exp blankLedgerType (DBlank.Functions.Funcs.acknowledgeFinalizeLeft_ x x0)). }
{ refine (make_exp blankLedgerType (DBlank.Functions.Funcs.isFundReady_ x x0)).
  refine KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_. }
{ refine (make_exp blankLedgerType (DBlank.Functions.Funcs.notifyRight_ a x x0 x1)).
  refine  KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_.
  refine  KWMessages_ι_EPSILON_BALANCE_. }
{ refine (make_exp blankLedgerType (DBlank.Functions.Funcs.notifyLeft_ x x0 x1 x2)).
  refine KWMessages_ι_MSG_VALUE_BUT_FEE_FLAGS_.
  refine KWMessages_ι_EPSILON_BALANCE_. }

1-6: intros; refine fallback.

{ destruct H eqn:kwdpool.
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.onVoteReject_ x)). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.onVoteAccept_)). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.acknowledgeFunds_)). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.sendFunds_ c)).
    refine KWMessages_ι_EPSILON_BALANCE_. }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.initialize_ x x0 x1 x2 x3)). }
  { refine (make_exp kwdpoolLedgerType (DKWDPool.Functions.Funcs.notifyParticipant_ x x0 x1)).
    refine KWMessages_ι_EPSILON_BALANCE_. }

}
{ destruct H eqn:kwdfund.
{ refine (make_exp fromgiverLedgerType (FromGiver.DFromGiver.Functions.Funcs.onVoteReject_ x)). }
{ refine (make_exp fromgiverLedgerType (FromGiver.DFromGiver.Functions.Funcs.onVoteAccept_)). }
{ refine (make_exp fromgiverLedgerType (FromGiver.DFromGiver.Functions.Funcs.acknowledgeFunds_)). }
{ refine (make_exp fromgiverLedgerType (FromGiver.DFromGiver.Functions.Funcs.sendFunds_ c)).
  refine KWMessages_ι_EPSILON_BALANCE_. }
{ refine (make_exp fromgiverLedgerType (FromGiver.DFromGiver.Functions.Funcs.initialize_ x x0 x1 x2 x3)). }
{ refine (make_exp fromgiverLedgerType (FromGiver.DFromGiver.Functions.Funcs.notifyParticipant_ x x0 x1)).
  refine KWMessages_ι_EPSILON_BALANCE_. }

}
1-3: refine onbounce.
{ destruct I, C; simpl.
  { refine None. }
  { refine None. }
  { refine None. }
  { refine (Some _).
    refine (DBlank.Ledger.MessagesAndEventsLEmbeddedType _OutgoingMessages_IDKWDPool). }
  { refine None. }
  { refine None. }
  { refine (Some _).
    refine (DBlank.Ledger.MessagesAndEventsLEmbeddedType _OutgoingMessages_IDFromGiver). }
  { refine None. }
  { refine None. }
  { refine (Some _).
    refine (DBlank.Ledger.MessagesAndEventsLEmbeddedType DBlank.Ledger._OutgoingMessages_IBlank). }
  { refine (Some _).
    refine (DKWDPool.Ledger.MessagesAndEventsLEmbeddedType DKWDPool.Ledger._OutgoingMessages_IBlank). }
  { refine (Some _).
    refine (DKWDPool.Ledger.MessagesAndEventsLEmbeddedType DKWDPool.Ledger._OutgoingMessages_IBlank). }
  { refine None. }
  { refine (Some _).
    refine (DKWDPool.Ledger.MessagesAndEventsLEmbeddedType DKWDPool.Ledger._OutgoingMessages_IKWFund). }
  { refine (Some _).
    refine (DFromGiver.Ledger.MessagesAndEventsLEmbeddedType DFromGiver.Ledger._OutgoingMessages_IKWFund). }
  { refine (Some _).
    refine (DBlank.Ledger.MessagesAndEventsLEmbeddedType DBlank.Ledger._OutgoingMessages_IKWFundParticipant). }
  { refine (Some _).
    refine (DKWDPool.Ledger.MessagesAndEventsLEmbeddedType DKWDPool.Ledger._OutgoingMessages_IKWFundParticipant). }
  { refine (Some _).
    refine (DFromGiver.Ledger.MessagesAndEventsLEmbeddedType DFromGiver.Ledger._OutgoingMessages_IKWFundParticipant). }
  { refine (Some _).
    refine (DBlank.Ledger.MessagesAndEventsLEmbeddedType DBlank.Ledger._OutgoingMessages_Default). }
  { refine (Some _).
    refine (DKWDPool.Ledger.MessagesAndEventsLEmbeddedType DKWDPool.Ledger._OutgoingMessages_Default). }
  refine (Some _).
  refine (DFromGiver.Ledger.MessagesAndEventsLEmbeddedType DFromGiver.Ledger._OutgoingMessages_Default). }
Defined.
Next Obligation.
unfold ContractsUtilsKW_obligation_2.
intros.
destruct C eqn:contract; simpl; split.
Print receive.
{ refine receive. }

{ unshelve refine (make_exp kwdpoolLedgerType (@DKWDPool.Functions.Funcs.receive_ commonErrors _ _ _)).
  { refine KWMessages_ι_DEFAULT_MSG_FLAGS_.    }
  { refine KWMessages_ι_GAS_FOR_FUND_MESSAGE_. }
  { refine KWMessages_ι_EPSILON_BALANCE_.      } 
}
{   refine (make_exp fromgiverLedgerType (@DFromGiver.Functions.Funcs.receive_ commonErrors _ _ _)).
  { refine KWMessages_ι_FG_MIN_BALANCE_.       }
  { refine KWMessages_ι_GAS_FOR_FUND_MESSAGE_. }
  { refine KWMessages_ι_EPSILON_BALANCE_.      }     
}
Defined.
Next Obligation.
(* intros.
unfold ContractsUtilsKW_obligation_1.
split. destruct I eqn:contract; simpl.
{ refine DBlank.Interface.IonBounce.             }
{ refine KWDPool.DKWDPool.Interface.IonBounce.   }
{ refine DFromGiver.Interface.IonBounce.         }
{ refine IBlank.Interface.IonBounce.             }
{ refine IKWFund.Interface.IonBounce.            }
{ refine IKWFundParticipant.Interface.IonBounce. } *)
esplit; unfold ContractsUtilsKW_obligation_1.
refine (PhantomPoint : getInterface IDef).
Defined.
Next Obligation.
intros I. unfold ContractsUtilsKW_obligation_2.
destruct I eqn: contract.
{ refine (Some (existT _ Blank default)). }
{ refine (Some (existT _ KWDPool default)). }
{ refine (Some (existT _ FromGiver default)). }
all: refine None.
Defined.
Next Obligation.
unfold ContractsUtilsKW_obligation_2, ContractsUtilsKW_obligation_1.
intros ?.
destruct C eqn:contr; simpl; intros mess.
{ refine (_ ++ _ ++ _ ++ _ ++ _).
  { refine (process_messages IDef (DBlank.Ledger._OutgoingMessages_Default mess)). }
  { refine (process_messages IKWFundParticipant_ (DBlank.Ledger._OutgoingMessages_IKWFundParticipant mess)). }
  { refine (process_messages FromGiver_ (DBlank.Ledger._OutgoingMessages_IDFromGiver mess)). }
  { refine (process_messages IBlank_ (DBlank.Ledger._OutgoingMessages_IBlank mess)). }
  refine (process_messages KWDPool_ (DBlank.Ledger._OutgoingMessages_IDKWDPool mess)). }
{ refine (_ ++ _ ++ _ ++ _).
  { refine (process_messages IDef (DKWDPool.Ledger._OutgoingMessages_Default mess)). }
  { refine (process_messages IKWFundParticipant_ (DKWDPool.Ledger._OutgoingMessages_IKWFundParticipant mess)). }
  { refine (process_messages IBlank_ (DKWDPool.Ledger._OutgoingMessages_IBlank mess)). }
  refine (process_messages IKWFund_ (DKWDPool.Ledger._OutgoingMessages_IKWFund mess)). }
refine (_ ++ _ ++ _ ++ _).
{ refine (process_messages IDef (DFromGiver.Ledger._OutgoingMessages_Default mess)). }
{ refine (process_messages IKWFundParticipant_ (DFromGiver.Ledger._OutgoingMessages_IKWFundParticipant mess)). }
{ refine (process_messages IBlank_ (DFromGiver.Ledger._OutgoingMessages_IBlank mess)). }
refine (process_messages IKWFund_ (DFromGiver.Ledger._OutgoingMessages_IKWFund mess)).
Defined.
Next Obligation.
unfold ContractsUtilsKW_obligation_2.
intros ?.
destruct C eqn:contr; simpl.
{ refine default. } (* ??? *)
{ refine default. } (* ??? *)
refine default.     (* ??? *)
Defined.

Require Import FinProof.Lib.HMapList.
Require Import FinProof.Lib.Lists.

Next Obligation.

destruct C eqn:contr; simpl; intros mr a m.
{ assert (q := DBlank.Ledger._OutgoingMessages_Default mr).
  refine 
  {$$ mr with DBlank.Ledger._OutgoingMessages_Default := 
              process_message IDef m a q $$}%record. }
{ assert (q := DKWDPool.Ledger._OutgoingMessages_Default mr).
  refine 
  {$$ mr with DKWDPool.Ledger._OutgoingMessages_Default := 
              process_message IDef m a q $$}%record. }
assert (q := DFromGiver.Ledger._OutgoingMessages_Default mr).
refine 
{$$ mr with DFromGiver.Ledger._OutgoingMessages_Default := 
            process_message IDef m a q $$}%record.
Defined.
Next Obligation.
intros C; destruct C eqn:CE; intros; simpl.
{ rewrite {1}/process_message; eexists; split.
  { apply/in_app_iff; left.
    apply/in_map_iff. 
    rewrite DBlank.Ledger.MessagesAndEventsFields_eq.
    exists (a, (hmapPush (defaulM PhantomPoint v)
      (DBlank.Ledger.MessagesAndEventsLGetField
      DBlank.Ledger._OutgoingMessages_Default lm) [a])); split.
    { reflexivity. }
    apply/lookup_in/lookup_insert. }
rewrite /snd /fst; split=> //.
apply/in_map_iff; eexists; split.
{ reflexivity. }
move: (defaulM PhantomPoint v)=> x.
exact/bIn_in/lookup_bIn_elems/lookup_insert. }
{ rewrite {1}/process_message; eexists; split.
  { apply/in_app_iff; left.
    apply/in_map_iff. 
    rewrite DKWDPool.Ledger.MessagesAndEventsFields_eq.
    exists (a, (hmapPush (defaulM PhantomPoint v)
      (DKWDPool.Ledger.MessagesAndEventsLGetField
      DKWDPool.Ledger._OutgoingMessages_Default lm) [a])); split.
    { reflexivity. }
    exact/lookup_in/lookup_insert. }
rewrite /snd /fst; split=> //.
apply/in_map_iff; eexists; split.
{ reflexivity. }
exact/bIn_in/lookup_bIn_elems/lookup_insert. }
rewrite {1}/process_message; eexists; split.
{ apply/in_app_iff; left.
  apply/in_map_iff. 
  rewrite DFromGiver.Ledger.MessagesAndEventsFields_eq.
  exists (a, (hmapPush (defaulM PhantomPoint v)
    (DFromGiver.Ledger.MessagesAndEventsLGetField
    DFromGiver.Ledger._OutgoingMessages_Default lm) [a])); split.
  { reflexivity. }
  exact/lookup_in/lookup_insert. }
rewrite /snd /fst; split=> //.
apply/in_map_iff; eexists; split.
{ reflexivity. }
exact/bIn_in/lookup_bIn_elems/lookup_insert.
Qed.
Next Obligation.
intros [ ]; simpl; esplit; simpl.
{ refine DBlank.Ledger.LedgerFields_eq. }
{ refine DKWDPool.Ledger.LedgerFields_eq. }
refine DFromGiver.Ledger.LedgerFields_eq.
Defined.
Next Obligation.
intros [ ]; simpl.
{ refine (DBlank.Ledger.MessagesAndEventsLEmbeddedType DBlank.Ledger._OutgoingMessages_Default). } 
{ refine (DKWDPool.Ledger.MessagesAndEventsLEmbeddedType DKWDPool.Ledger._OutgoingMessages_Default). } 
refine (DFromGiver.Ledger.MessagesAndEventsLEmbeddedType DFromGiver.Ledger._OutgoingMessages_Default).
Qed.
Local Open Scope string_scope.

Notation "'[[' x , y , .. , z ']]'" :=
  (print_args (cons (show x) (cons (show y) .. (cons (show z) nil) ..))).

Notation "'[[' x ']]'" :=
  (print_args (cons (show x) nil)).

#[global, program] Instance ShowGetInterfaces {I} : Show (GetInterface I).
Next Obligation.
intros I.
destruct I eqn:E.
{ intros i.
  destruct i eqn:e.
  { refine "getTimes". }
  { refine "getInvestorsNumbers". }
  { refine "getGiversSum". }
  { refine "getInvestorsSum". }
  { refine ("killBlank(" ++ show a ++ ")"). }
  { refine ("startVoting(" ++ show x ++ ", " ++ show x0 ++ ")"). } 
  { refine ("vote(" ++ show x ++ ", " ++ show x0 ++ ", " ++ show x1 ++ ", " ++ show x2 ++ ", " ++ show x3 ++ ", " ++ show x4 ++ ")"). }
  { refine ("setFundCode(" ++ show c ++ ")"). }
  { refine ("finalize(" ++ show x ++ ", " ++ show a ++ ")"). }
  { refine ("acknowledgeFinalizeRight(" ++ show a ++ ", " ++ show x ++ ", " ++ show x0 ++ ")"). }
  { refine ("acknowledgeFinalizeLeft(" ++ show x ++ ", " ++ show x0 ++ ")"). }
  { refine ("notifyRight(" ++ show a ++ ", " ++ show x ++ ", " ++ show x0 ++ ", " ++ show x1 ++ ")"). }
  { refine ("acknowledgeDeploy(" ++ show a ++ ", " ++ show x ++ ")"). }
  { refine ("deployFromGiver(" ++ show c ++ ", " ++ show a ++ ", " ++ show x ++ ")"). }
  { refine ("notifyLeft(" ++ show x ++ ", " ++ show x0 ++ ", " ++ show x1 ++ ", " ++ show x2 ++ ")"). }
  { refine ("isFundReady(" ++ show x ++ ", " ++ show x0 ++ ")"). }
  { refine ("setKWDPoolCodeHash(" ++ show x ++ ", " ++ show x0 ++ ")"). }
  { refine ("setFromGiverCodeHash(" ++ show x ++ ", " ++ show x0 ++ ")"). }
  { refine ("constructor(" ++ show x ++ ", " ++ show x0 ++ ")"). }
}
{ intros i.
  destruct i eqn:e.
  { refine "isFundReady". }
  { refine "getBalance". }
  { refine "isInitialized". }
  { refine "onVoteAccept". }
  { refine ("onVoteReject(" ++ show x ++ ")"). }
  { refine ("vote(" ++ show x ++ ", " ++ show x0 ++ ", " ++ show x1 ++ ")"). }
  { refine ("returnExtraFunds(" ++ show a ++ ")"). }
  { refine ("returnFunds(" ++ show a ++ ")"). }
  { refine ("sendFunds(" ++ show c ++ ")"). }
  { refine "acknowledgeFunds". }
  { refine ("setFinalAddress(" ++ show a ++ ")"). }
  { refine ("notifyParticipant(" ++ show x ++ ", " ++ show x0 ++ ", " ++ show x1 ++ ")"). }
  { refine "receive". }
  { refine ("initialize(" ++ show x ++ ", " ++ show x0 ++ ", " ++ show x1 ++ ", " ++ show x2 ++ "," ++ show x3 ++ ")"). }
  { refine ("constructor" ++ [[ x ]]). }
   }
{ intros i.
  destruct i eqn:e.
  { refine "onVoteAccept". }
  { refine ("onVoteReject" ++ [[ x ]]). }
  { refine "returnFunds". }
  { refine ("sendFunds" ++ [[c]]). }
  { refine "acknowledgeFunds". }
  { refine ("notifyParticipant" ++ [[x, x0, x1]]). }
  { refine "receive". }
  { refine ("initialize" ++ [[x, x0, x1, x2, x3]]). }
  { refine ("constructor" ++ [[x, x0]]). }
   }
{ intros i.
  destruct i eqn:e.
  { refine ("vote" ++ [[ x, x0, x1, x2, x3, x4]]). }
  { refine ("acknowledgeDeploy" ++ [[a, x]]). }
  { refine ("acknowledgeFinalizeRight" ++ [[a, x, x0]]). }
  { refine ("acknowledgeFinalizeLeft" ++ [[x, x0]]). }
  { refine ("isFundReady" ++ [[x, x0]]). }
  { refine ("notifyRight" ++ [[a, x, x0, x1]]). }
  { refine ("notifyLeft" ++ [[x, x0, x1, x2]]). }
   }
{ intros i.
  destruct i eqn:e.
  { refine ("sendKWDPoolParams" ++ [[x, x0, c]]). }
  { refine ("sendFromGiverParams" ++ [[a, x, c]]). }
   }
{
  intros i; destruct i eqn: e.
  { refine ("onVoteReject" ++ [[ x ]] ). }
  { refine ("onVoteAccept"). }
  { refine ("acknowledgeFunds"). }
  { refine ("sendFunds" ++ [[ c ]] ). }
  { refine ("initialize" ++ [[ x , x0 , x1 , x2 , x3 ]] ). }
  { refine ("notifyParticipant" ++ [[ x , x0 , x1 ]] ). }
  
}
{
  intros i; destruct i eqn: e.
  refine "onBounce".
}

Defined.
Fail Next Obligation.

#[global, program] Instance ShowInterfaces : Show Interfaces.
Next Obligation.
intros I; destruct I eqn:E.
{ refine "DBlank". }
{ refine "KWDPool". }
{ refine "FromGiver". }
{ refine "Blank". }
{ refine "KWFund". }
{ refine "KWFundParticipant". }
refine "".
Defined.

#[global, program] Instance ShowLedgerBlank : Show (Ledger blankLedgerType) .
Next Obligation.
intros.
destruct X.
destruct c.
repeat (destruct l).
refine ("Blank Ledger " ++ \n ++ _).
refine ("kwdpool_code_hash         := "         ++ show x  ++ \n ++ _ ).
refine ("kwdpool_code_depth        := "        ++ show x  ++ \n ++ _ ).
refine ("fromgiver_code_hash       := "       ++ show x1  ++ \n ++ _ ).
refine ("fromgiver_code_depth      := "      ++ show x2  ++ \n ++ _ ).
refine ("givers_summa              := "              ++ show x3  ++ \n ++ _ ).
refine ("investors_adj_summa       := "       ++ show x4  ++ \n ++ _ ).
refine ("investors_summa           := "           ++ show x5  ++ \n ++ _ ).
refine ("min_summa                 := "                 ++ show x6  ++ \n ++ _ ).
refine ("max_summa                 := "                 ++ show x7  ++ \n ++ _ ).
refine ("lock_time                 := "                 ++ show x8  ++ \n ++ _ ).
refine ("unlock_time               := "               ++ show x9  ++ \n ++ _ ).
refine ("farm_rate                 := "                 ++ show x10  ++ \n ++ _ ).
refine ("kwf_lock_time             := "             ++ show x11  ++ \n ++ _ ).
refine ("quant                     := "                     ++ show x12  ++ \n ++ _ ).
refine ("nonce                     := "                     ++ show x13  ++ \n ++ _ ).
refine ("num_investors_sent        := "        ++ show x14  ++ \n ++ _ ).
refine ("num_investors_received    := "    ++ show x15  ++ \n ++ _ ).
refine ("can_change_kwdpool_code   := "   ++ show x16  ++ \n ++ _ ).
refine ("can_change_fromgiver_code := " ++ show x17  ++ \n ++ _ ).
refine ("num_from_givers           := "           ++ show x18  ++ \n ++ _ ).
refine ("voted_for                 := "                 ++ show x19  ++ \n ++ _ ).
refine ("voted_against             := "             ++ show x20  ++ \n ++ _ ).
refine ("voting_start_time         := "         ++ show x21  ++ \n ++ _ ).
refine ("voting_time               := "               ++ show x22  ++ \n ++ _ ).
refine ("voting_result             := "             ++ show x23  ++ \n ++ _ ).
refine ("voting_code_hash          := "          ++ show x24  ++ \n ++ _ ).
refine ("voting_id                 := "                 ++ show x25  ++ \n ++ _ ).
refine ("code_updated              := "              ++ show x26  ++ \n ++ _).
revert p.
clear.
intros.
repeat (destruct p).
revert v.
clear.
intros.
destruct v.
repeat (destruct p).
refine ("VMState Blank" ++ \n ++ _).
refine ("pubkey      := "      ++ show x ++ \n ++ _). 
refine ("msg_pubkey  := "  ++ show x0 ++ \n ++ _).     
refine ("now         := "         ++ show x1 ++ \n ++ _).
refine ("msg_sender  := "  ++ show a ++ \n ++ _).     
refine ("msg_value   := "   ++ show x2 ++ \n ++ _).   
refine ("balance     := "     ++ show x3 ++ \n ++ _). 
refine ("address     := "     ++ show a0 ++ \n ++ _). 
refine ("code        := "        ++ show c ++ \n ++ _).
refine ("msg_data    := "    ++ show c0 ++ \n ++ _).  
refine ("accepted    := "    ++ show x4 ++ \n ++ _).  
refine ("reserved    := "    ++ show x5 ++ \n ++ _).  
refine ("currentCode := " ++ show c1 ++ \n ++ _).     
refine ("IsCommitted := " ++ show x6 ++ \n ++ _).     
refine ("isTVMExited := " ++ show x7).     
Defined.

#[global, program] Instance ShowLedgerKWD : Show (Ledger kwdpoolLedgerType ) .
Next Obligation.
intros.
destruct X.
destruct c.
repeat (destruct l).
refine ("KWDPool Ledger " ++ \n ++ _).
refine ("balance         := "         ++ show x ++ \n ++ _).
refine ("fund_address    := "    ++ show a ++ \n ++ _).
refine ("lock_time       := "       ++ show x0 ++ \n ++ _).
refine ("unlock_time     := "     ++ show x1 ++ \n ++ _).
refine ("nonce           := "           ++ show x2 ++ \n ++ _).
refine ("final_address   := "   ++ show x3 ++ \n ++ _).
refine ("quant           := "           ++ show x4 ++ \n ++ _).
refine ("voting_flag     := "     ++ show x5 ++ \n ++ _).
refine ("fund_ready_flag := " ++ show x6 ++ \n ++ _).
refine ("init_time       := "       ++ show x7 ++ \n ++ _).
refine ("deposit_time    := "    ++ show x8 ++ \n ++ _).
refine ("farm_rate       := "       ++ show x9 ++ \n ++ _).
refine ("kwf_lock_time   := "   ++ show x10 ++ \n ++ _).
refine ("initialized     := "     ++ show x11 ++ \n ++ _).
refine ("voting_bitmap   := "   ++ show x12 ++ \n ++ _).
revert p.
clear. intros.
repeat (destruct p).
revert v.
clear. intros.
destruct v.
repeat (destruct p).
refine ("VMState KWDPool" ++ \n ++ _).
refine ("pubkey      := "      ++ show x ++ \n ++ _). 
refine ("msg_pubkey  := "  ++ show x0 ++ \n ++ _).     
refine ("now         := "         ++ show x1 ++ \n ++ _).
refine ("msg_sender  := "  ++ show a ++ \n ++ _).     
refine ("msg_value   := "   ++ show x2 ++ \n ++ _).   
refine ("balance     := "     ++ show x3 ++ \n ++ _). 
refine ("address     := "     ++ show a0 ++ \n ++ _). 
refine ("code        := "        ++ show c ++ \n ++ _).
refine ("msg_data    := "    ++ show c0 ++ \n ++ _).  
refine ("accepted    := "    ++ show x4 ++ \n ++ _).  
refine ("reserved    := "    ++ show x5 ++ \n ++ _).  
refine ("currentCode := " ++ show c1 ++ \n ++ _).     
refine ("IsCommitted := " ++ show x6 ++ \n ++ _).     
refine ("isTVMExited := " ++ show x7).     
Defined.

#[global, program] Instance ShowLedgerFromGiver : Show (Ledger fromgiverLedgerType ) .
Next Obligation.
intros.
destruct X.
destruct c.
repeat (destruct l).
refine ("From Giver Ledger " ++ \n ++ _).
refine ("balance         := " ++ show x ++ \n ++ _).
refine ("fund_address    := " ++ show a ++ \n ++ _).
refine ("lock_time       := " ++ show x0 ++ \n ++ _).
refine ("unlock_time     := " ++ show x1 ++ \n ++ _).
refine ("giver_address   := " ++ show a0 ++ \n ++ _).
refine ("fund_ready_flag := " ++ show x2 ++ \n ++ _).
refine ("nonce           := " ++ show x3 ++ \n ++ _).
revert p.
clear. intros.
repeat (destruct p).
revert v.
clear. intros.
destruct v.
repeat (destruct p).
refine ("VMState FromGiver" ++ \n ++ _).
refine ("pubkey      := " ++ show x ++ \n ++ _). 
refine ("msg_pubkey  := " ++ show x0 ++ \n ++ _).     
refine ("now         := " ++ show x1 ++ \n ++ _).
refine ("msg_sender  := " ++ show a ++ \n ++ _).     
refine ("msg_value   := " ++ show x2 ++ \n ++ _).   
refine ("balance     := " ++ show x3 ++ \n ++ _). 
refine ("address     := " ++ show a0 ++ \n ++ _). 
refine ("code        := " ++ show c ++ \n ++ _).
refine ("msg_data    := " ++ show c0 ++ \n ++ _).  
refine ("accepted    := " ++ show x4 ++ \n ++ _).  
refine ("reserved    := " ++ show x5 ++ \n ++ _).  
refine ("currentCode := " ++ show c1 ++ \n ++ _).     
refine ("IsCommitted := " ++ show x6 ++ \n ++ _).     
refine ("isTVMExited := " ++ show x7).     
Defined.

#[global, program] Instance ShowGetLedger {C} : Show (GetLedger C) .
Next Obligation.
intros.
destruct C eqn:contra.
all : simpl in X;
refine (show X).
Defined.

Local Open Scope bool_scope.

#[global, program] Instance XBoolEquableInterfaces :  XBoolEquable bool Interfaces.
Next Obligation.
refine (fun i1 i2 => 
  match i1, i2 with 
  | DBlank_, DBlank_ => true
  | KWDPool_, KWDPool_ => true
  | FromGiver_, FromGiver_ => true
  | IBlank_, IBlank_ => true
  | IKWFund_, IKWFund_ => true
  | IKWFundParticipant_, IKWFundParticipant_ => true
  | IDef, IDef => true
  | _, _ => false 
  end).
Defined.

#[global, program] Instance XBoolEquableIDBlank :  XBoolEquable bool IDBlank.
Next Obligation.
  refine (fun x y => 
  match x, y with 
    | IgetTimes                                   ,
      IgetTimes                                    => true
    | IgetInvestorsNumbers                        ,
      IgetInvestorsNumbers                         => true 
    | IgetInvestorsSum                            ,
      IgetInvestorsSum                             => true 
    | IgetGiversSum                               ,
      IgetGiversSum                                => true
    | IkillBlank a1                               ,
      IkillBlank a2                                => eqb a1 a2
    | IstartVoting x1 x2                          ,
      IstartVoting y1 y2                           => eqb x1 y1 && eqb x2 y2
    | Interface.Ivote x1 x2 x3 x4 x5 x6           ,
      Interface.Ivote y1 y2 y3 y4 y5 y6            => 
        eqb x1 y1 && eqb x2 y2 && eqb x3 y3 && eqb x4 y4 && eqb x5 y5 && eqb x6 y6
    | IsetFundCode c1                             ,
      IsetFundCode c2                              => eqb c1 c2
    | Ifinalize x1 a1                             ,
      Ifinalize y1 b1                              => eqb x1 y1 && eqb a1 b1
    | Interface.IacknowledgeFinalizeRight a1 x1 x2,
      Interface.IacknowledgeFinalizeRight b1 y1 y2 => eqb a1 b1 && eqb x1 y1 && eqb x2 y2
    | Interface.IacknowledgeFinalizeLeft x1 x2    , 
      Interface.IacknowledgeFinalizeLeft y1 y2     => eqb x1 y1 && eqb x2 y2
    | Interface.InotifyRight a1 x1 x2 x3          ,
      Interface.InotifyRight b1 y1 y2 y3           => 
        eqb a1 b1 && eqb x1 y1 && eqb x2           y2 && eqb x3 y3
    | Interface.InotifyLeft a1 x1 x2 x3           ,
      Interface.InotifyLeft b1 y1 y2 y3            => 
        eqb a1 b1 && eqb x1 y1 && eqb x2           y2 && eqb x3 y3
    | Interface.IisFundReady x1 x2                , 
      Interface.IisFundReady y1 y2                 => eqb x1 y1 && eqb x2 y2
    | IsetKWDPoolCodeHash x1 x2                   ,
      IsetKWDPoolCodeHash y1 y2                    => eqb x1 y1 && eqb x2 y2
    | IsetFromGiverCodeHash x1 x2                 ,
      IsetFromGiverCodeHash y1 y2                  => eqb x1 y1 && eqb x2 y2
    | Interface._Iconstructor x1 x2               ,
      Interface._Iconstructor y1 y2                => eqb x1 y1 && eqb x2 y2
    | Interface.IacknowledgeDeploy a1 x1          ,
      Interface.IacknowledgeDeploy b1 y1           => eqb a1 b1 && eqb x1 y1
    | IdeployFromGiver c1 a1 x1                   ,
      IdeployFromGiver d1 b1 y1                    => eqb c1 d1 && eqb a1 b1 && eqb x1 y1
    | _, _                                         => false
    end).
Defined.

#[global, program] Instance XBoolEquableIDKWDPool :  XBoolEquable bool IDKWDPool.
Next Obligation.
refine (fun x y => 
  match x, y with 
  | DKWDPool.Interface.IisFundReady      ,
      DKWDPool.Interface.IisFundReady        => true
    | IgetBalance                          ,
      IgetBalance                            => true 
    | IisInitialized                       , 
      IisInitialized                         => true 
    | Interface.IonVoteAccept              , 
      Interface.IonVoteAccept                => true 
    | Interface.IonVoteReject x1           , 
      Interface.IonVoteReject y1             => eqb x1 y1
    | DKWDPool.Interface.Ivote x1 x2 x3    ,
      DKWDPool.Interface.Ivote y1 y2 y3      => eqb x1 y1 && eqb x2 y2 && eqb x3 y3
    | IreturnExtraFunds a1                 ,
      IreturnExtraFunds a2                   => eqb a1 a2
    | Interface.IreturnFunds a1            ,
      Interface.IreturnFunds a2              => eqb a1 a2
    | Interface.IsendFunds c1              ,
      Interface.IsendFunds c2                => eqb c1 c2
    | Interface.IacknowledgeFunds          , 
      Interface.IacknowledgeFunds            => true
    | IsetFinalAddress a1                  ,
      IsetFinalAddress a2                    => eqb a1 a2
    | Interface.InotifyParticipant x1 x2 x3,
      Interface.InotifyParticipant y1 y2 y3  => eqb x1 y1 && eqb x2 y2 && eqb x3 y3
    | Interface.Ireceive                   ,
      Interface.Ireceive                     => true 
    | Interface.Iinitialize x1 x2 x3 x4 x5 ,
      Interface.Iinitialize y1 y2 y3 y4 y5   =>
        eqb x1 y1 && eqb x2 y2 && eqb x3 y3 && eqb x4 y4 && eqb x5 y5
    | DKWDPool.Interface._Iconstructor x   ,
      DKWDPool.Interface._Iconstructor y     => eqb x y
    | _, _                                   => false
    end).
Defined.

Arguments eqb : simpl never.

From mathcomp Require Import ssreflect ssrbool.

Hint Resolve eqbxx : core.
Remove Hints  intFunBool : typeclass_instances.
Remove Hints  maybeFunBool : typeclass_instances.

Set Typeclasses Depth 200. 
#[global, program] Instance eqb_spec_IDBlank :  eqb_spec IDBlank.
Next Obligation.
move=> a b; case: a=>>; case: b=>>; split=> //.
all: try by rewrite /eqb; move=> /= /eqb_spec_intro->.
all: try by case; do ? move->; rewrite /Common.eqb /= ?eqbxx.
all: try by rewrite /eqb /=; do ? case/andP; do ? move=> /eqb_spec_intro->.
{ by rewrite /eqb /=; do 2? case/andP; do ? move=> /eqb_spec_intro->. }
{ by rewrite /eqb /=; do 3? case/andP; do ? move=> /eqb_spec_intro->. }
by rewrite /eqb /=; do 1? case/andP; do ? move=> /eqb_spec_intro->.
Qed.

#[global, program] Instance eqb_spec_IDKWDPool :  eqb_spec IDKWDPool.
Next Obligation.
move=> a b; case: a=>>; case: b=>>; split=> //.
all: try by rewrite /eqb; move=> /= /eqb_spec_intro->.
all: try by case; do ? move->; rewrite /eqb /= ?eqbxx.
all: try by rewrite /eqb /=; do ? case/andP; do ? move=> /eqb_spec_intro->.
Qed.

#[global, program] Instance eqb_spec_IKWFund :  eqb_spec IKWFund.
Next Obligation.
move=> a b; case: a=>>; case: b=>>; split=> //.
all: try by rewrite /eqb; move=> /= /eqb_spec_intro->.
all: try by case; do ? move->; rewrite /eqb /= ?eqbxx.
all: try by rewrite /eqb /=; do ? case/andP; do ? move=> /eqb_spec_intro->.
by rewrite /eqb /=; do 2? case/andP; do ? move=> /eqb_spec_intro->.
Qed.

#[global, program] Instance XBoolEquableGetInterfaces {I} :  XBoolEquable bool (GetInterface I).
Next Obligation.
refine (fun i x y => 
  match i, x, y with
  | DBlank_            , x, y
  | KWDPool_           , x, y
  | FromGiver_         , x, y
  | IBlank_            , x, y
  | IKWFund_           , x, y 
  | IKWFundParticipant_, x, y 
  | IDef               , x, y => eqb x y
  end).
Defined.

#[global, program] Instance XBoolEquableNodeType : 
  XBoolEquable bool (@nodeType Interfaces Contracts ContractsUtilsKW).
Next Obligation.
refine (fun n1 n2 => 
  match n1, n2 with
  | inl n1, inl n2 => 
    match n1, n2 with 
    | make_enode DBlank_             m1 r1 s1 p1 e1 t1,
      make_enode DBlank_             m2 r2 s2 p2 e2 t2
    | make_enode KWDPool_            m1 r1 s1 p1 e1 t1,
      make_enode KWDPool_            m2 r2 s2 p2 e2 t2
    | make_enode FromGiver_          m1 r1 s1 p1 e1 t1,
      make_enode FromGiver_          m2 r2 s2 p2 e2 t2
    | make_enode IBlank_             m1 r1 s1 p1 e1 t1,
      make_enode IBlank_             m2 r2 s2 p2 e2 t2
    | make_enode IKWFund_            m1 r1 s1 p1 e1 t1,
      make_enode IKWFund_            m2 r2 s2 p2 e2 t2
    | make_enode IKWFundParticipant_ m1 r1 s1 p1 e1 t1,
      make_enode IKWFundParticipant_ m2 r2 s2 p2 e2 t2
    | make_enode IDef                m1 r1 s1 p1 e1 t1,
      make_enode IDef                m2 r2 s2 p2 e2 t2 =>
      eqb m1 m2 && eqb r1 r2 && eqb s1 s2 &&eqb p1 p2 && eqb e1 e2 && eqb t1 t2
    | _, _ => false
    end
  | inr n1, inr n2 => 
    match n1, n2 with 
    | make_inode DBlank_             m1 r1 p1 e1,
      make_inode DBlank_             m2 r2 p2 e2
    | make_inode KWDPool_            m1 r1 p1 e1,
      make_inode KWDPool_            m2 r2 p2 e2
    | make_inode FromGiver_          m1 r1 p1 e1,
      make_inode FromGiver_          m2 r2 p2 e2
    | make_inode IBlank_             m1 r1 p1 e1,
      make_inode IBlank_             m2 r2 p2 e2
    | make_inode IKWFund_            m1 r1 p1 e1,
      make_inode IKWFund_            m2 r2 p2 e2
    | make_inode IKWFundParticipant_ m1 r1 p1 e1,
      make_inode IKWFundParticipant_ m2 r2 p2 e2
    | make_inode IDef                m1 r1 p1 e1,
      make_inode IDef                m2 r2 p2 e2 =>
      eqb m1 m2 && eqb r1 r2 && eqb p1 p2 && eqb e1 e2
    | _, _ => false
    end
  | _, _ => false
  end).
Defined.

#[global, program] Instance eqb_spec_prod {T S} `{eqb_spec T} `{eqb_spec S} : 
  eqb_spec (T * S).
Next Obligation. 
move=> ?????? [??][??]; split=> [|[->->] ]; rewrite /eqb /= ?eqbxx //.
by case: ifP=> [/eqb_spec_reflect->/eqb_spec_reflect->|].
Defined.

#[global, program] Instance eqb_spec_InternalMessageParamsLRecord : 
  eqb_spec (InternalMessageParamsLRecord).
Next Obligation.
case=> ? [?? [? [>] ] ]; by apply eqb_spec_prod.
Qed.

#[global, program] Instance eqb_spec_OutgoingMessage {T} `{eqb_spec T} : 
  eqb_spec (OutgoingMessage T).
Next Obligation.
move=> ??? [?|??] [?|??]; split=> //; rewrite /eqb /=; [| |case/andP|].
2,4: by case; do ? move->; rewrite ?eqbxx.
all: by do ? move/eqb_spec_reflect=>->.
Defined.

#[global, program] Instance eqb_spec_Interfaces : eqb_spec Interfaces.
Next Obligation.
by case=> -[ ]; rewrite /eqb /=; split=> //.
Qed.

#[global, program] Instance eqb_spec_nodeType : eqb_spec (@nodeType Interfaces Contracts ContractsUtilsKW).
Next Obligation.
move=> [ [I1 m1 ?????]|[I1 m1 ???] ] [ [I2 m2 ?????]|[I2 m2 ???] ]; split=> //.
all: try by rewrite /eqb //=.
all: destruct I1; destruct I2=> //=; rewrite /eqb //=.
all: try by do ? case/andP; do ? move/eqb_spec_reflect=>-> //.
all: try by (do ? case)=> /(ex_projT2_eq eq_refl) /=; rewrite /eq_rect_r /=; (do ? move=> ->); rewrite ?eqbxx.
Qed.

#[global, program] Instance XDefault_messageTree : XDefault (@messageTree Interfaces Contracts ContractsUtilsKW). 
Next Obligation.
split.
{ refine (inr (make_inode _ _ _ _ _)).
  { refine default. }
  { refine default. }
  { refine default. }
  split; refine default. 
}
refine nil.
Unshelve.
refine IDef.
Defined.

End Instances.

(* End KW. *)
