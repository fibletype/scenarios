Require Import ssreflect.
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
Require Import Printing.

Require Import FinProof.Lib.BoolEq.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
(* Local Open Scope xlist_scope. *)

(************* delete after a new coq-finproof verion ***************)
#[local] Obligation Tactic := idtac.
Lemma eqbxx {T} `{eqb_spec T} (x : T) : eqb x x = true.
Proof. exact/eqb_spec_intro. Qed.
#[global, program] Instance eqb_spec_option {T} `{eqb_spec T} :  eqb_spec (option T).
Next Obligation.
move=> ??? [?[?|]|[ ] ]; rewrite /eqb //=; split=> [/eqb_spec_intro->|[->] ] //.
exact: eqbxx.
Qed.
(********************************************************************)

Set Typeclasses Depth 100.

Section Def.

Set Implicit Arguments.

Notation "m [ i ]"     := (hmapFindWithDefault default  i m) (at level 5, left associativity).
Notation "m [ i ] ← v" := (xHMapInsert  i v m) (at level 5, left associativity).
Notation "m [ i ] ?"   := (hmapLookup  i m) (at level 5, left associativity): ursus_scope.

Structure ledgerType  := {
  Ledger                  :> Type;
  LedgerMainState         :  Type;
  LedgerLocalState        :  Type;
  LedgerMessagesAndEvents :  Type;
}.

Instance XDefault_ledgerType : XDefault ledgerType.
do ? split; refine PhantomType.
Defined.

Implicit Type (sT : ledgerType) (rT : ledgerType) (addr : address).

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

Definition UExpression (l : ledgerType) `{lC : LedgerClassT l} :=
  (@UExpressionL
    l
    (LedgerMainState         l)
    (LedgerLocalState        l)
    VMStateLRecord
    (LedgerMessagesAndEvents l)
    GlobalParamsLRecord
    OutgoingMessageParamsLRecord
    lC).

Definition ULValue (l : ledgerType) `{lC : LedgerClassT l} :=
  (@ULValueL
    l
    (LedgerMainState         l)
    (LedgerLocalState        l)
    VMStateLRecord
    (LedgerMessagesAndEvents l)
    GlobalParamsLRecord
    OutgoingMessageParamsLRecord
    lC).


Record UExpressionWithType l `{lC : LedgerClassT l} := make_exp {
  X_of    :  Type;
  _       :  XDefault X_of;
  b_of    :  bool;
  Uexp_of :> UExpression l X_of b_of
}.



Instance X_of_Default (l : ledgerType) `{lC : LedgerClassT l}
 (uexp : UExpressionWithType l) : XDefault (X_of uexp).
Proof. now destruct uexp. Qed.

Context (Interfaces : Type) (Contracts : Type).

Class Signature (Interface : Type) (rT : ledgerType)
  `{rC : LedgerClassT rT} := {
  InterpretInterface : Interface -> UExpressionWithType rT;
  Queue              : option
    (EmbeddedType (LedgerMessagesAndEvents rT) 
                  (XHMap address (XQueue (OutgoingMessage Interface))))
}. 

Class HasReceive (rT : ledgerType) `{rC : LedgerClassT rT} := {
  Receive : UExpressionWithType rT
}.

(* Class DefaultExpressions (Interface : Type) := {
  OnBounce : Interface;
}. *)

Class DefaultExpressions
  (Interfaces : Type) (get : Interfaces -> Type)  := {
  IforBounce : Interfaces;
  OnBounce   : get IforBounce
}.

(* Require Import KWproject.Contracts.KWDPool.DKWDPool.Ledger. *)
(* Search setPruvendoRecord. *)
(* Print DeployInitLGetField. *)
(* Check DeployInitLFieldType. *)
(* Check @field_type. *)

Class FieldUtils (rT : ledgerType) `{rC : LedgerClassT rT} := {
  LedgerGetField : forall f : LedgerFields, rT -> field_type f;

  GetSet         : forall (f : LedgerFields) (v : field_type f) (r : rT),
    LedgerGetField f {$$r with f := v $$}%record = v
}.

Definition defaulM {I : Type} (i : I) (v : uint) : OutgoingMessage I.
constructor 2; last refine i.
do ? split.
{ refine v. }
{ refine false. }
refine default.
Defined.

(* TODO: refactor Ledger *)

Class ContractsUtils := {
  GetInterface          :  Interfaces -> Type;
  GetLedger             :  Contracts -> ledgerType;
  DefaultContract       :> XDefault Contracts;
  DefaultLedger         :> XDefault (GetLedger default);
  LedgerClassC          :> forall {C}, LedgerClassT (GetLedger C);
  SignatureC            :> forall {I C}, Signature (GetInterface I) (GetLedger C);
  HasRecieveC           :> forall {C}, HasReceive (GetLedger C);
  DefaultExpressionsC   :> DefaultExpressions GetInterface;
  Constructor           :  Interfaces -> option {C & GetLedger C};
  GetOutgoingMessage    :  forall {C},
    LedgerMessagesAndEvents (GetLedger C) ->
    list (address * list {I & OutgoingMessage (GetInterface I)});
  DeleteOutgoingMessage :  forall C,
    LedgerMessagesAndEvents (GetLedger C);
  PutOnBounce    :  forall {C},
    LedgerMessagesAndEvents (GetLedger C) ->
    address ->
    OutgoingMessage (GetInterface IforBounce) ->
    LedgerMessagesAndEvents (GetLedger C);
  GetPutOM              :  forall C a lm v,
    exists l, 
      In l (@GetOutgoingMessage C (PutOnBounce lm a (defaulM OnBounce v))) /\
      In (existT _ IforBounce (defaulM OnBounce v)) (snd l) /\ 
      fst l = a;
  FieldUtilsC           :> forall {C}, FieldUtils (GetLedger C);
  EmbOB                 :> forall {C}, 
    EmbeddedType (LedgerMessagesAndEvents (GetLedger C))
      (mapping address (queue (OutgoingMessage (GetInterface IforBounce))))
}.

Context `{ContractsUtils}.

Record ledgerWithType := make_ledg {
  tp  : Contracts;
  led : GetLedger tp;
}.

#[global] Instance DefaultledgerWithType : XDefault ledgerWithType.
split; refine (make_ledg default default).
Qed.

Definition superLedger := XHMap address ledgerWithType.

Definition getInternalMessageParams {I} :
  OutgoingMessage I -> InternalMessageParamsLRecord := 
  fun mess =>
  match mess with 
  | EmptyMessage            _ im => im
  | OutgoingInternalMessage im _ => im 
  end.

Definition interpret_params (C : Contracts) (I : Interfaces)
  X (pubkey : XUInteger256):
  address -> OutgoingMessage (GetInterface I) -> UExpression (GetLedger C) X false.
intros addrS mess.
set im := getInternalMessageParams mess.
destruct im as [value _].
change false with (orb false false).
refine {{ {_} := #{addrS}; 
          {_} := #{value};
          {_} += #{value};
          {_} := #{pubkey} }}.
{ refine (@ULState _ _ _ _ _ _ _ _ _ _ _ _ _ address Ledger_VMState _).
  rewrite <- isoVMState.
  refine (VMStateLEmbeddedType VMState_ι_msg_sender). }
{ refine (@ULState _ _ _ _ _ _ _ _ _ _ _ _ _ XUInteger128 Ledger_VMState _).
  rewrite <- isoVMState.
  refine (VMStateLEmbeddedType VMState_ι_msg_value). }
{ refine (ULState Ledger_VMState _).
  rewrite <- isoVMState.
  refine (VMStateLEmbeddedType VMState_ι_balance). }
refine (@ULState _ _ _ _ _ _ _ _ _ _ _ _ _ XUInteger256 Ledger_VMState _).
rewrite <- isoVMState.
refine (VMStateLEmbeddedType VMState_ι_msg_pubkey).
Defined.

Definition interpret_function (C : Contracts) (I : Interfaces):
  OutgoingMessage (GetInterface I) -> UExpressionWithType (GetLedger C) :=
fun mess =>
  match mess with 
  | EmptyMessage            _ _ => Receive
  | OutgoingInternalMessage _ i => @InterpretInterface (GetInterface I) (GetLedger C) _ _ i
  end.

Definition interpret_message  
  (C : Contracts) (I : Interfaces) (pubkey : XUInteger256) :
  address -> OutgoingMessage (GetInterface I) -> UExpressionWithType (GetLedger C) :=
  fun addrS mess => 
  let: make_exp x uexp2 := interpret_function C I mess in 
  make_exp x {{ {interpret_params C I _ pubkey addrS mess}; {uexp2} }}. 

Definition isError {R b t} (cr : ControlResultP t R b) : option (ErrorType t) :=
  match cr with
  | ControlValue _ _ => None
  | ControlError e   => Some e
  | _                => None 
  end.

Definition getBounce {I} (mess : OutgoingMessage I) : bool :=
  Messsage_ι_bounce (match mess with 
  | EmptyMessage            _ i => i 
  | OutgoingInternalMessage i _ => i
  end). 

Definition ULState (l : ledgerType) `{lC : LedgerClassT l}:= (@ULState _ XUInteger XMaybe XProd XHMap
    l
    (LedgerMainState         l)
    (LedgerLocalState        l)
    VMStateLRecord
    (LedgerMessagesAndEvents l)
    GlobalParamsLRecord
    OutgoingMessageParamsLRecord
    lC 
    ).

Structure errorType := {
  err_of : option (ErrorType uint);
  has_money_for_on_bounce : bool;
}.

#[global]
Instance XBoolEquableErrorType : XBoolEquable bool errorType := 
  { eqb := fun '(Build_errorType e b) '(Build_errorType e' b') => 
      andb (eqb e e') (eqb b b') }.

Arguments eqb : simpl never.

#[global]
Instance eqb_spec_errorType : eqb_spec errorType.
Proof.
split=> -[??][??]; rewrite /eqb; split.
{ by case/andb_prop=> /eqb_spec_intro->/eqb_spec_intro->. }
by move=>-> /=; rewrite ?boolEqRefl.
Qed.

Definition exec_super_state (C : Contracts) (I : Interfaces)
  (pubkey : XUInteger256) (r : GetLedger C) (addrS : address)
  (mess : OutgoingMessage (GetInterface I)) (IsInternal : bool)
  : GetLedger C * errorType.
refine (match interpret_message C I pubkey addrS mess with
| @make_exp _ _ T x b Uexp_of0 => 
  let L := Uinterpreter (R := T) Uexp_of0 in
  let: xpair res r' := run L r in 
  match 
    isError res,
    IsInternal, 
    @Queue (GetInterface I) (GetLedger C) LedgerClassC SignatureC,
    getBounce mess
  with 
  | Some er, true , Some emb, true => _
  | Some er, false, _       , _    => (r', Build_errorType (Some er) true)
  | _, _, _, _ => (r', Build_errorType None true) 
  end
end).
assert uint as mess_balance.
{ assert XUInteger128 as X.
  { apply (@projEmbed _ _ (VMStateLEmbeddedType VMState_ι_msg_value)).
    assert (@field_type (GetLedger C) _ _ Ledger_VMState) as LV.
    { refine (LedgerGetField _ r'). }
    rewrite -isoVMState in LV; exact LV. }
  destruct X as [X]; refine X. }
assert uint as balance.
{ assert XUInteger128 as X.
  { apply (@projEmbed _ _ (VMStateLEmbeddedType VMState_ι_balance)).
    assert (@field_type (GetLedger C) _ _ Ledger_VMState) as LV.
    { refine (LedgerGetField _ r'). }
    rewrite -isoVMState in LV; exact LV. }
  destruct X as [X]; refine X. }
destruct (BinNat.N.leb mess_balance balance) eqn:M.
{ refine (_, Build_errorType (Some er) true).
  assert (LedgerMessagesAndEvents (GetLedger C)) as LM.
  { rewrite [LedgerMessagesAndEvents _]isoMessages.
    refine (LedgerGetField _ r'). }
  assert (@field_type (GetLedger C) _ _ Ledger_MessagesState) as LM'.
  { rewrite -isoMessages; 
    refine (PutOnBounce LM addrS (defaulM OnBounce mess_balance)). }
  refine (setPruvendoRecord _ LM' _).
  refine (exec_state (Uinterpreter ({{ {_} -= β #{mess_balance} }}) ) r').
  refine (ULState _ _ _).
  rewrite <- isoVMState.
  refine (VMStateLEmbeddedType VMState_ι_balance). }
exact (r', Build_errorType (Some er) false).
(* 
assert (GetLedger C) as r''.
{ refine (exec_state 
(Uinterpreter
  (send_internal_message_left 
    {{ {ULState (GetLedger C) Ledger_MessagesState _} [[# {addrS}]] }}
    || [$ {tvm_msg_value} ⇒ {Messsage_ι_value }; FALSE ⇒ {Messsage_ι_bounce} $] || 
    || #{ OnBounce } ||))
 r').
{ rewrite <-isoMessages. refine EmbOB. }
split; refine nil. }
refine (setPruvendoRecord _ LM' r''). *)
Defined.
(* pose proof (Ledger_MessagesState).
refine ((exec_state 
  (Uinterpreter
    (send_internal_message_left 
      {{ {ULState (GetLedger C) Ledger_MessagesState _} [[# {addrS}]] }}
      || [$ {tvm_msg_value} ⇒ {Messsage_ι_value }; FALSE ⇒ {Messsage_ι_bounce} $] || 
      || #{ OnBounce } ||))
   r') , Some er).
rewrite <-isoMessages; refine emb.
{ split; refine nil. }
refine DefaultExpressionsC.
Defined. *)

Record internalNodeType := make_inode {
  Ii_of     : Interfaces;
  messi_of  : OutgoingMessage (GetInterface Ii_of);
  addriR_of : address;
  addriS_of : address;
  errori    : errorType
}.

Record externalNodeType := make_enode {
  Ie_of     : Interfaces;
  messe_of  : OutgoingMessage (GetInterface Ie_of);
  addreR_of : address;
  addreS_of : address;
  pubkey_of : XUInteger256;
  errore    : errorType;
  time_of   : XUInteger32
}.

Definition nodeType := (externalNodeType + internalNodeType)%type.

Definition Deploy (I : Interfaces)
  addr (sl : superLedger) : superLedger :=
  match @Constructor _ I, sl[addr]? with 
  | Some (existT _ c l) , None => sl[addr] ← (make_ledg c l)
  | _                   , _    => sl
  end.

Definition getAddrR (n : nodeType) : address :=
  match n with
  | inl e => addreR_of e
  | inr i => addriR_of i
  end.


Definition getAddrS (n : nodeType) : address :=
  match n with
  | inl e => addreS_of e
  | inr i => addriS_of i
  end.
  

Definition getI (n : nodeType) : Interfaces :=
  match n with
  | inl e => Ie_of e
  | inr i => Ii_of i
  end.

Definition getMess (n : nodeType) : (OutgoingMessage (GetInterface (getI n))) :=
  match n with
  | inl e => messe_of e
  | inr i => messi_of i
  end.

Definition getPubkey (n : nodeType) : XUInteger256 :=
  match n with
  | inl e => pubkey_of e
  | inr i => default
  end.

Definition isInternal (n : nodeType) := 
  match n with
  | inl a => false
  | inr b => true
  end.

Definition isExternal (n : nodeType) := 
  match n with
  | inl a => true
  | inr b => false
  end.

Definition getError n := 
  match n with
  | inl e => errore e
  | inr i => errori i
  end.


Definition putError (n : nodeType) (e : errorType) : nodeType :=
  match n with
  | inl (make_enode Ie_of messe_of addreR_of addreS_of pubkey_of _ time_of) =>
          inl (make_enode Ie_of messe_of addreR_of addreS_of pubkey_of e time_of)
  | inr (make_inode Ii_of messi_of addriR_of addriS_of _ ) =>
          inr (make_inode Ii_of messi_of addriR_of addriS_of e)
  end.

Definition getTime (n : nodeType) : XUInteger32 := 
  match n with 
  | inl (make_enode _ _ _ _ _ _ time_of) => time_of
  | _                                  => default
  end.

Definition setTime (t : XUInteger32) (sl : superLedger) : superLedger.
refine (
  map
  (fun '(a, l) =>
   (a,
   make_ledg (tp l)
       {$$led l with Ledger_VMState
       := eq_rect VMStateLRecord
             (fun x: Type => x) _
             (field_type Ledger_VMState) isoVMState
             $$}%record)) sl).
refine (let VMS :=
  unkeyed (eq_rect_r (fun T : Type => T) (LedgerGetField Ledger_VMState (led l)) isoVMState) in
  {$$VMS with VMState_ι_now := t $$}%record).
Defined.

Lemma get_putError n err : getError (putError n err) = err.
Proof. by case: n=> -[ ]. Qed.

Lemma isExternal_putError n err :
  isExternal n = isExternal (putError n err).
Proof. by case: n=> -[ ]. Qed.

Lemma put_putError err1 err2 n : 
  putError (putError n err1) err2 = putError n err2.
Proof. by case: n=> -[ ]. Qed.

Lemma put_getError n : 
  putError n (getError n) = n.
Proof. by case: n=> -[ ]. Qed.

Lemma getTime_putError n err : 
  getTime (putError n err) = getTime n.
Proof. by case: n=> -[ ]. Qed.

Lemma addrS_putError q err : getAddrS (putError q err) = getAddrS q.
Proof. by case: q=> -[ ]. Qed.


Structure InterpretNode_ans := mk_IN {
  sl_of    : superLedger;
  tss_of   : list (list nodeType);
  errTp_of : errorType
}.

#[global]
Coercion errTp_of : InterpretNode_ans >-> errorType.

Definition InterpretNode 
  (n : nodeType) (sl : superLedger) : InterpretNode_ans.
set addrR  := getAddrR   n.
set addrS  := getAddrS   n.
set mess   := getMess    n.
set I      := getI       n.
set pubkey := getPubkey  n.
set isI    := isInternal n.
refine (if sl[addrR]? is None then mk_IN sl nil (Build_errorType None true) else _).
set rT     := tp sl[addrR].
set r      := led sl[addrR].
set lt     := exec_super_state rT I pubkey r addrS mess isI.
set r'     := fst lt.
set er     := snd lt.
set mT     := LedgerGetField Ledger_MessagesState r'.
rewrite <-isoMessages in mT.
set nodes  := GetOutgoingMessage    mT.
set mT'    := DeleteOutgoingMessage (tp sl[addrR]).
split. 
{ refine (sl[addrR] ← _). 
  refine (make_ledg rT _).
  refine (setPruvendoRecord Ledger_MessagesState _ r').
  rewrite <-isoMessages.
  refine mT'. }
{ refine (map (fun x => _) nodes).
  destruct x as [addr ms].
  refine (map (fun x => _) ms).
  destruct x as [i om].
  refine (inr (make_inode _ om addr addrR (Build_errorType None false))). }
refine er.
Defined.

Lemma IN_putError n err sl : 
  InterpretNode (putError n err) sl = 
  InterpretNode n sl.
Proof. by case: n=> /==> -[ ]. Qed.

Definition errorE := 
  ((get_putError, 
    put_putError),
   (put_getError, 
    getTime_putError),
   (addrS_putError, 
    IN_putError))%type.

From mathcomp Require Import ssrbool.

Lemma eqb_spec_reflect {A} `{eqb_spec A} a b : 
  reflect (a = b) (Common.eqb a b).
Proof. by apply/(iffP idP)=> /eqb_spec_intro. Qed.

Definition isOnBounceI `{eqb_spec Interfaces} {I} : GetInterface I -> Prop :=
  match (eqb_spec_reflect IforBounce I) with
  | ReflectT pf => 
    match pf in (_ = y) return (GetInterface y -> Prop) with 
    | eq_refl => eq OnBounce
    end
  | ReflectF pf => fun _ => False
  end.

Definition isOnBounce `{eqb_spec Interfaces} (n : nodeType) : Prop.
pose proof getMess n as om.
destruct om.
refine False.
refine (isOnBounceI g).
Defined.

Definition onBounce_spec_aux `{eqb_spec Interfaces}
  (mes : {I : Interfaces & OutgoingMessage (GetInterface I)}) := 
  let: existT _ m := mes in 
  getBounce m = false /\
    match m with 
    | EmptyMessage _ => False
    | OutgoingInternalMessage _ i => isOnBounceI i
    end.

(* Require Import UMLang.SML_NG32. *)
(* Require Import UMLang.LocalClassGenerator.ClassGenerator. *)

(* Search setPruvendoRecord. *)
(* Print LedgerLGetField. *)


(* Lemma getPruvendoRecord' *)
  (* (r : LedgerLRecord) v: *)
    (* Ledger_MessagesState  *)
    (* {$$r with Ledger_MessagesState := v $$}%record = v. *)
(* Proof. *)
  (* Search "LedgerLGetField". *)
(* Admitted. *)

Lemma super_exec_error `{eqb_spec Interfaces} C I pubkey r addrS mess isI
  (ex := exec_super_state C I pubkey r addrS mess isI) : 
  isI                              = true ->
  isSome (err_of (snd ex))         = true ->
  has_money_for_on_bounce (snd ex) = true ->
  Exists (fun '(a, ms) => Exists onBounce_spec_aux ms /\ a = addrS) 
      ((GetOutgoingMessage
            (eq_rect_r (fun T : Type => T)
               (LedgerGetField Ledger_MessagesState (fst ex)) isoMessages))).
Proof.
rewrite /ex /exec_super_state.
case E1: (interpret_message _ _ _ _ _).
case E2: (run _ _).
case E3: (isError _)=> //.
case E4: isI=> //.
case E5: Queue=> //.
case E6: (getBounce _)=> //.
case E7: (BinNat.N.leb _ _)=> //.
rewrite /fst GetSet /snd {1}/eq_rect_r.
(* set m := (existT _ _ _). *)
move: (eq_rect_r _ _ _)=> lm.
move: isoMessages.
case: _ / => /= ?.
move: (match VMStateLProjEmbed VMState_ι_msg_value _ with | Build_XUBInteger x => x end).
move=> v.
case: (GetPutOM C addrS lm v)=> [ [a l ] ] [ ]? [ ]IN ???; apply/Exists_exists.
exists (a, l); do ? split=> //.
apply/Exists_exists. eexists; split; first exact/IN.
do ? split=> //.
rewrite /defaulM /isOnBounceI.
case: (eqb_spec_reflect _)=> //.
move=> p. 
suff-> : p = eq_refl.
{ reflexivity. }
exact/eq_irrelevance.
Qed.


Definition onBounce_spec `{eqb_spec Interfaces} (addrS : address) (n : nodeType) := 
  isOnBounce n                   /\ 
  getAddrS   n           = addrS /\
  getBounce  (getMess n) = false.

Lemma onBounce_spec_putError `{eqb_spec Interfaces} a err n : 
  onBounce_spec a (putError n err) <->
  onBounce_spec a n.
Proof. by case: n=> -[ ]. Qed.

Context `{eqb_spec Interfaces}.

Lemma IN_error n sl (Int := (InterpretNode n sl)) :
    isInternal n                = true ->
    isSome (err_of Int)         = true -> 
    has_money_for_on_bounce Int = true ->
    getBounce (getMess n)       = true ->
    exists2 l,  In l (tss_of Int) & Exists (onBounce_spec (getAddrR n))  l. 
Proof.
rewrite /Int /InterpretNode /err_of /tss_of.
case: (sl[_]?)=> // ?.
move/super_exec_error/[apply]/[apply]/Exists_exists => -[ ] -[a l [IN [obs ads gb] ] ].
set addrR  := getAddrR   n.
exists 
  (map (fun '(existT i om) => (inr (make_inode _ om a addrR (Build_errorType None false)))) l).
{ by apply/in_map_iff; exists (a, l). }
case/Exists_exists: obs=> -[I m] [? [*] ]; apply/Exists_exists.
exists (inr (make_inode _ m a addrR (Build_errorType None false))); do ? split=> //=.
by apply/in_map_iff; exists (existT _ I m).
Qed.


Lemma IN_addrS n sl sl' qss err:
  InterpretNode n sl = mk_IN sl' qss err -> 
  Forall (Forall (fun n' => getAddrS n' = getAddrR n)) qss.
Proof.
  rewrite -{2}[qss]/(tss_of (mk_IN sl' qss err)) /InterpretNode=><-.
  case: sl [_] ? => [?|]; last by constructor.
  by do ? rewrite /tss_of Forall_map Forall_forall=> -[*].
Qed.

Lemma IN_internal n sl sl' qss err :
  InterpretNode n sl = mk_IN sl' qss err -> 
  Forall (Forall (fun n => isInternal n = true)) qss.
Proof.
  rewrite -{2}[qss]/(tss_of (mk_IN sl' qss err)) /InterpretNode=><-.
  case: sl [_] ? => [?|]; last by constructor.
  by do ? rewrite /tss_of Forall_map Forall_forall=> -[*].
Qed.

Context `{Show Interfaces} `{forall {I}, Show (GetInterface I)}.
Context `{forall {C}, Show (GetLedger C)}.


#[local] Obligation Tactic := idtac.

Local Open Scope string_scope.

#[global, program] Instance ShowErrorType : Show errorType.
Next Obligation.
refine (fun '(Build_errorType er b) => 
  if b then show er else show er ++ " not enough money for onBounce ¯\_(ツ)_/¯").
Defined.

#[global, program] Instance ShowInternalNodeType : Show internalNodeType.
Next Obligation.
intros [I mess addrR addrS er].
destruct (err_of er) as [e|] eqn:errr.
{ refine ("error = " ++ show e ++ show addrS ++ "- " ++ show I ++ "." ++ show mess ++ " ->" ++ show addrR). }
refine (show addrS ++ "- " ++ show I ++ "." ++ show mess ++ " ->" ++ show addrR).
Defined.

#[global, program] Instance ShowExternalNodeType : Show externalNodeType.
Next Obligation.
intros [I mess addrR ?? er].
destruct (err_of er) as [e|] eqn:errr.
{ refine ("error = " ++ show e ++ "|| "  ++ show I ++ "." ++ show mess ++ " ->" ++ show addrR ). }
refine (show I ++ "." ++ show mess ++ " ->" ++  show addrR ).
Defined.


#[global, program] Instance ShowSl : Show superLedger.
Next Obligation.
intros.
induction X.
refine "".
destruct a.
destruct l.
refine (\n ++ show a ++ " -> " ++ _).
refine (show led0 ++ _).
refine (\n ++ IHX).
Defined.

   
(*
  1) Добавить Дефолтные сообщения +
    1.1) Сделать дефолтную интерпретацию сообщения +
    1.2) Сделать дефолтный ledgerWithType, интрепретировать все сообщения ему как 1)
  2) Научиться деплоить контракты * +
  3) Работать со сценариями
    3.1) Определить сценарии +
    3.2) Определить listT
    3.3) Интерпретировать одно сообщение в lisT LedgerT ***
    3.4) Интерпретировать сценарий в lisT LedgerT 
    3.5) Построить дерево
  4) Добавить время
*)

End Def.
