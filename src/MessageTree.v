Require Import ssreflect.
From mathcomp Require Import ssrnat zify.
Require Import BinNums.

Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21.
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.MonadTransformers21. 
Require Import FinProof.StateMonad21Instances.
Require Import UMLang.UrsusLib.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.
Require Import KWproject.Contracts.ProofsCommon.

Require Import SuperLedger GenTree.

Require Import List.

Require Import FinProof.Lib.BoolEq.
Require Import FinProof.Lib.GenTree.

Import ListNotations.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
(* Local Open Scope xlist_scope. *)

Set Typeclasses Depth 100.


Set Implicit Arguments.

Section MessageTree.

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

Context (Interfaces Contracts : Type).
Context `{ContractsUtils Interfaces Contracts}.

Notation nodeType         := (@nodeType         Interfaces Contracts).
Notation superLedger      := (@superLedger      Interfaces Contracts).
Notation externalNodeType := (@externalNodeType Interfaces Contracts).

Definition messageTree := Tree nodeType.

Implicit Type t : messageTree.

Record state := {
  MessagesQueue : list nodeType;
  SuperLedger   : superLedger;
  RunOutOfFuel  : bool;
}.

(*  *)
(* Notation StateT := (simpleState superLedger). *)

Check MonadState.

Context (StateTG : Type -> Type -> Type).
Context `{Mo : forall S, Monad (StateTG S)} `{forall S, @MonadState (StateTG S) S (Mo S)}.

Notation StateT' := (StateTG state).
Notation StateT  := (StateTG superLedger).

Definition putMessageQueue (n : list nodeType) : state -> state := 
  fun '(Build_state ms sl r) => Build_state n sl r.

Definition putSuperLedger (s : superLedger) : state -> state := 
  fun '(Build_state ms sl r) => Build_state ms s r.

Definition runOut : state -> state := 
  fun '(Build_state ms sl r) => Build_state ms sl true.

Local Obligation Tactic := idtac.

Local Open Scope bool_scope.

Context `{nodeEqType: eqb_spec nodeType}.

Fixpoint takeheads {T} (l : list (list T)) := 
  match l with 
  | (h :: t) :: ls => h :: takeheads ls
  | [ ] :: ls => takeheads ls
  | [ ] => [ ]
  end.

Fixpoint checkRoots (R : nodeType -> nodeType -> Prop) ts qss: Prop := 
  match ts, qss with 
  | [ ]    , [ ]             => True
  | t :: ts, (q :: _) :: qss => R (Tree.root t) q /\ checkRoots R ts qss
  | _      , _               => False
  end.

#[global, program] 
Instance XBoolEquableList {T} `{XBoolEquable bool T} : XBoolEquable bool (list T).
Next Obligation.
intros ??.
refine (fix foo (l1 l2 : list _) :=
  match l1, l2 with 
  | h1 :: t1, h2 :: t2 => eqb h1 h2 && foo t1 t2
  | nil     , nil      => true
  | _       , _        => false
  end).
Defined.

Fixpoint checkTreeT (mt : messageTree) (qss : list (list nodeType)) :
  StateT bool :=
  let fix Checks mts qss : StateT bool := 
    match mts, qss with 
    | [ ]    , [ ]               => $true
    | t :: ts, (q :: qs) :: qss  =>
      do sl ← get;
      let sl'  := sl_of  (InterpretNode (Tree.root t) sl) in
      let tss  := tss_of (InterpretNode (Tree.root t) sl) in
      let err  := errTp_of (InterpretNode (Tree.root t) sl) in
      let qss' := if qs is nil then tss else qs :: tss    in
      (put sl' >>
      do b  ← checkTreeT t qss';
      do bs ← Checks ts qss;
      $ (eqb (Tree.root t) (putError q err) && b && bs))
    | _      , _                 => $ false
    end in
  Checks (Tree.nodes mt) qss.

Fixpoint checkTreesT mts qss : StateT bool := 
  match mts, qss with 
  | [ ]    , [ ]               => $true
  | t :: ts, (q :: qs) :: qss  =>
    do sl ← get;
    let sl'  := sl_of  (InterpretNode (Tree.root t) sl) in
    let tss  := tss_of (InterpretNode (Tree.root t) sl) in
    let err  := errTp_of (InterpretNode (Tree.root t) sl) in
    let qss' := if qs is nil then tss else qs :: tss    in
   (put sl' >>
    do b  ← checkTreeT t qss';
    do bs ← checkTreesT ts qss;
    $ (eqb (Tree.root t) (putError q err) && b && bs))
  | _      , _                 => $ false
  end.

Lemma checkTreeE (n : nodeType)  : 
  (forall t q qs qss ts, checkTreeT (Node n (t :: ts)) ((q :: qs) :: qss) = 
    do sl ← get;
    let sl'  := sl_of  (InterpretNode (Tree.root t) sl) in
    let tss  := tss_of (InterpretNode (Tree.root t) sl) in
    let err  := errTp_of (InterpretNode (Tree.root t) sl) in
    let qss' := if qs is nil then tss else qs :: tss    in
    (put sl' >>
    do b  ← checkTreeT t qss';
    do bs ← checkTreeT (Node n ts) qss ;
    $ (eqb (Tree.root t) (putError q err) && b && bs))) *
  (checkTreeT (Node n nil) nil = $true).
Proof. by [ ].  Qed.

Lemma checkTreeE2 (n : nodeType) ts qss : 
  checkTreeT (Node n ts) qss = checkTreesT ts qss.
Proof. by [ ]. Qed.

Fixpoint checkForestT (l : list messageTree) : (StateT bool) :=
  match l with
  | [ ]     => $ true
  | t :: ts => 
    modify (setTime (getTime (Tree.root t))) >>
    do sl ← get;
    let: mk_IN sl' qss err := InterpretNode (Tree.root t) sl in
    put sl' >>
    do b  ← checkTreeT   t qss;
    do bs ← checkForestT ts;
    $ (b && bs && eqb (getError (Tree.root t)) err)
  end.

Lemma checkForestE t ts :
  checkForestT (t :: ts) =
    modify (setTime (getTime (Tree.root t))) >>
    do sl ← get;
    let: mk_IN sl' qss err := InterpretNode (Tree.root t) sl in
    put sl' >>
    do b  ← checkTreeT   t qss;
    do bs ← checkForestT ts;
    $ (b && bs && eqb (getError (Tree.root t)) err).
Proof. by [ ]. Qed.

Definition mapNode (l : list externalNodeType) : list nodeType := map inl l.

Definition checkForest (l : list messageTree) (ems : list externalNodeType) (sl : superLedger) := 
  eval_state (checkForestT l) sl && 
  eqb 
    (map (fun t => putError (Tree.root t) (Build_errorType None false)) l) 
    (map (fun m => putError m (Build_errorType None false)) (mapNode ems)).

Definition execForest (l : list messageTree) (sl : superLedger) := 
  exec_state (checkForestT l) sl.

#[global] Arguments checkTreeT : simpl never.


Lemma checkTreesE t ts q qs qss: 
  checkTreesT (t :: ts) ((q :: qs) :: qss) = 
  do sl ← get;
  let sl'  := sl_of  (InterpretNode (Tree.root t) sl) in
  let tss  := tss_of (InterpretNode (Tree.root t) sl) in
  let err  := errTp_of (InterpretNode (Tree.root t) sl) in
  let qss' := if qs is nil then tss else qs :: tss    in
  (put sl' >>
  do b  ← checkTreeT t qss';
  do bs ← checkTreesT ts qss;
  $ (eqb (Tree.root t) (putError q err) && b && bs)).
Proof. by [ ]. Qed.

(* 
  1) addrR parent = addrS children +
  2) все кроме root -- internalNodeType +
  3) bounce onBounce = false
  4) messge queue is empty for intermediate ledgers +
  .) balance = const 
  .) add new field option ErrorType +
  .) if ↑ = Some error ==> exists message onBounce somewhere (come up with spec) 
  
  
  1) InterpretNode n sl = (sl', qss) -> 
  Forall (Forall (fun n' => addrS_of n' = addrR_of n)) qss.
  2) InterpretNode n sl = (sl', qss) -> 
  sum_balance sl = sum_balance sl'.
  3) InterpretNode n sl = (sl', qss) -> 
  Forall (Forall (fun n' => isOnBoune n' -> bouncce n' = false))) qss.
 *)

Fixpoint Builds (Build : nodeType -> StateT' messageTree) 
  (nss : list (list nodeType)) : StateT' (list messageTree) :=
  match nss with
  | (n :: ns) :: nss => 
    modify (putMessageQueue ns) >>
    do mt  ← Build n;
    do mts ← Builds Build nss;
    $ (mt :: mts)
  | _ :: nss => modify runOut >> $ nil
  | _        => $ nil
  end.

Fixpoint Build (fuel : nat) (n : nodeType) : StateT' messageTree :=
  if fuel is S fuel then
    do sl ← embed_fun SuperLedger;
    do ms ← embed_fun MessagesQueue;
    let Int := (InterpretNode n sl)                  in
    let sl' := sl_of  Int                            in
    let nss := tss_of Int                            in
    let err := errTp_of Int                          in
    let qss' := if ms is nil then nss else ms :: nss in
    modify (putSuperLedger sl') >> 
    if qss' is nil then $ (Node (putError n err) nil) else
    do mts ← Builds (Build fuel) qss';
    $ (Node (putError n err) mts)
  else modify runOut >> $ (Node n nil).

Fixpoint buildForestT fuel (l : list nodeType) : (StateT' (list messageTree)) :=
  match l with
  | [ ] => $ [ ]
  | n :: tln => modify (fun '(Build_state ms sl r) => Build_state ms (setTime (getTime n) sl) r) >>
                do tree ← Build fuel n;
                do forest ← buildForestT (fuel - 1) tln;
                $ (tree :: forest)
  end.

Definition buildForest fuel (l : list externalNodeType) (sl : superLedger) := 
  eval_state (buildForestT fuel (mapNode l)) (Build_state nil sl false).

Definition buildSLedger fuel (l : list externalNodeType) (sl : superLedger) := 
  SuperLedger (exec_state (buildForestT fuel (mapNode l)) (Build_state nil sl false)).

Definition buildFinished fuel (l : list externalNodeType) (sl : superLedger) := 
  negb (RunOutOfFuel (exec_state (buildForestT fuel (mapNode l)) (Build_state nil sl false))).

(* Context `{nodeEqType : eqb_spec nodeType}. *)

Arguments run : simpl never.


Lemma runmodify {M : Type -> Type} {S : Type} `{Monad M}
  {MonadState : MonadState S} (f : S -> S) 
  (s : S) : run (modify f) s = (f s, f s)%xprod.
Proof. by rewrite /modify runbind runget /Basics.compose runput. Qed.

Lemma runmodifybind {M : Type -> Type} {S : Type} `{Monad M}
  {MonadState : MonadState S} (f : S -> S) X (m : M X)
  (s : S) : run (modify f >> m) s = run m (f s).
Proof. 
  rewrite runbind'.
  case E: (run _); rewrite runmodify in E.
  by case: E=>?->. 
Qed.

Lemma runputbind {M : Type -> Type} {S : Type} `{Monad M}
  {MonadState : MonadState S} (f : S) X (m : M X)
  (s : S) : run (put f >> m) s = run m f.
Proof. 
  rewrite runbind'.
  case E: (run _); rewrite runput in E.
  by case: E=>?->. 
Qed.

From mathcomp Require Import ssreflect ssrbool zify.

Inductive run_chekTree_spec tr que stat stat' : Prop := 
  | Run_step t sl' tss st  q qs qss qss' sl ts x err
    (trE   : tr   = Node x (t :: ts))
    (queE  : que = (q :: qs) :: qss) 
    (statE : stat = sl)
    (tE    : Tree.root t = putError q err)
    (INt   : InterpretNode (Tree.root t) sl = mk_IN sl' tss err)
    (qss'E : qss' = if qs is nil then tss else qs :: tss)
    (runE1 : run (checkTreeT t qss') sl' = (true, st)%xprod)
    (runE2 : run (checkTreeT (Node x ts) qss) st = (true, stat')%xprod)
    (runE3 : 
      run 
        (checkTreeT (Node x (t :: ts)) ((q :: qs) :: qss)) 
        sl = 
        (true, stat')%xprod)  :
      run_chekTree_spec tr que stat stat'
  | Run_empty x sl
    (runE : run (checkTreeT (Node x nil) nil) sl = 
      (true, sl)%xprod)
    (trE    : tr    = Node x nil)
    (queE   : que   = nil)
    (statE  : stat  = sl)
    (stat'E : stat' = sl) : 
      run_chekTree_spec tr que stat stat' .

Arguments eqb : simpl never. 

Lemma run_checkTreeE x ts sl qss :  
  run (checkTreeT (Node x ts) qss) sl = 
  match ts, qss with 
  | t :: ts, (q :: qs) :: qss =>
    let: mk_IN sl' tss err      := InterpretNode (Tree.root t) sl in
    let: (b , st)%xprod  := run 
      (checkTreeT t (if qs is nil then tss else qs :: tss))
      sl' in 
    let: (b', st')%xprod := run (checkTreeT (Node x ts) qss) st in
      (eqb (Tree.root t) (putError q err) && b && b', st')%xprod
  | [ ]    , [ ]              => (true, sl)%xprod
  | _      , _                => (false, sl)%xprod
  end.
Proof. 
case: ts qss=> [|t ts] [|[>|q qs qss] ].
{ by rewrite checkTreeE rununit. }
1-4: by rewrite /checkTreeT /= rununit.
rewrite checkTreeE runbind runget /SuperLedger.
rewrite runputbind /putSuperLedger.
destruct (InterpretNode (Tree.root t) sl) as [sl' tss err] eqn:E.
set qss' := match qs with
            | [ ] => snd (fst (sl', tss, err))
            | _ :: _ => qs :: snd (fst (sl', tss, err))
            end.
rewrite runbind /fst.
destruct (run (checkTreeT t qss') _) as [b st] eqn:E1.
rewrite runbind.
destruct (run (checkTreeT (Node x ts) qss) _) as [b1 st'] eqn:E2.
by rewrite rununit.
Qed.

(* Arguments Builds : simpl never. *)

Lemma run_BuildE n fuel ms sl r:
  run (Build fuel n) (Build_state ms sl r) = 
  if fuel is fuel.+1 then 
    let: mk_IN sl' tss err := InterpretNode n sl in
    let: qss               := if ms is nil then tss else ms :: tss in
      match qss with 
      | nil      => ([putError n err | [ ] ], (Build_state ms sl' r))%xprod
      | nil :: _ => ([putError n err | [ ] ], (Build_state ms sl' true))%xprod
      | ((q :: qs) :: qss) =>
        let: (trh, st)%xprod := 
          run (Build fuel q) (Build_state qs sl' r) in 
        let: (trt, st')%xprod :=
          run (Builds (Build fuel) qss) st in 
          ([putError n err | trh :: trt], st')%xprod 
      end
  else ([n | [ ] ], (Build_state ms sl true))%xprod.
Proof.
case: fuel=> [|fuel].
{ by rewrite /= @runmodifybind rununit. }
do ? rewrite /= runbind runembed /=.
case E: (InterpretNode n sl)=> [sl' tss err] /=.
set qss := if ms is nil then tss else ms :: tss.
case: qss=> [|[|q qs] qss].
{ by rewrite runmodifybind rununit. }
{ by rewrite runmodifybind /= runbind /Builds runmodifybind ?rununit. }
rewrite runmodifybind /= runbind runmodifybind runbind.
case: (run _ _)=> [trh st].
rewrite runbind.
case: (run _ _)=> [trt st'].
by rewrite ?rununit.
Qed.

Arguments Builds : simpl nomatch.

Lemma run_BuildsE Build st nss:
  run (Builds Build nss) st = 
  match nss with
  | (n :: ns) :: nss => 
    let: (trh, st1)%xprod :=
      run (Build n) (putMessageQueue ns st) in 
    let: (trt, st2)%xprod := 
      run (Builds (Build) nss) st1 in 
      (trh :: trt, st2)%xprod
  | _ :: nss => (nil, runOut st)%xprod
  | _        => (nil, st)%xprod
  end.
Proof.
case: nss=> [|[|]>].
1-2: by rewrite /= ?runmodifybind rununit.
rewrite /= runbind runmodify runbind.
case: (run _ _)=>>.
rewrite runbind.
case: (run _ _)=>>.
by rewrite rununit.
Qed.

Inductive run_Build_spec n ms1 sl1 ms2 sl2 t : nat -> list (list nodeType) -> Prop := 
  | Runb_step err tss sl sl' q qs qss fuel trh trt ms'
    (INt   : InterpretNode n sl1 = mk_IN sl tss err)
    (qssE  : (q :: qs) :: qss = if ms1 is nil then tss else ms1 :: tss)
    (runE1 : 
      run (Build fuel q) (Build_state qs sl false) = 
      (trh, Build_state ms' sl' false)%xprod)
    (runE2 : 
      run (Builds (Build fuel) qss) (Build_state ms' sl' false) = 
      (trt, Build_state ms2 sl2 false)%xprod)
    (runE4 : 
      run (Build fuel.+1 n) (Build_state ms1 sl1 false) = 
      ([putError n err | trh :: trt], Build_state ms2 sl2 false)%xprod)
    (tE : [putError n err | trh :: trt] = t)
    (* (nE : n = putError n err) *)
      : run_Build_spec n ms1 sl1 ms2 sl2 t (fuel.+1) ((q :: qs) :: qss)
  | Runb_empty err tss sl fuel
    (INt  : InterpretNode n sl1 = mk_IN sl tss err)
    (qssE : nil = if ms1 is nil then tss else ms1 :: tss)
    (runE : run (Build fuel.+1 n) (Build_state ms1 sl1 false) = 
      ([putError n err | [ ] ], (Build_state ms1 sl false))%xprod)
    (* (nE   : t = putError n err) *)
    (msE  : ms1 = ms2)
    (sl2E : sl2 = sl)
    (tE : [putError n err | [ ] ] = t)
      : run_Build_spec n ms1 sl1 ms2 sl2 t (fuel.+1) nil.

Lemma Build_RunOutOfFuel_aux ts nss n t sl sl' ms ms' fuel r: 
  (run (Build fuel n) (Build_state ms sl r) = (t, (Build_state ms' sl' false))%xprod ->
  r = false) * 
  (run (Builds (Build fuel) nss) (Build_state ms sl r) = (ts, (Build_state ms' sl' false))%xprod ->
  r = false).
Proof.
elim: fuel nss n t sl sl' ms ms' r ts. 
{ move=> nss ? ? sl sl' ms ms' r ts; rewrite run_BuildE; split=> //.
  elim: nss sl sl' r ms ms' ts=> [>|[|n ns] ? IHnss >]; rewrite run_BuildsE //.
  { by case. }
  case E1: (run _ _)=> [t1 st1].
  case E2: (run _ _)=> [t2 [ ] ]; move: E2.
  rewrite run_BuildE in E1.
  move=> /[swap]=> -[???->].
  by case: E1=> ? <- /IHnss. }
move=> fuel IHfuel.
have HB: forall n t sl sl' ms ms' r,
  run (Build fuel.+1 n) (Build_state ms sl r) = (t, Build_state ms' sl' false)%xprod ->
  r = false.
{ move=> n t sl sl' ms ms' r.
  rewrite run_BuildE.
  case: (InterpretNode _ _)=> [? tss ?].
  set (qss := if ms is nil then tss else ms :: tss).
  case E: qss=> [|[|q qs] qss']=> //.
  { by case. }
  case E1: (run _ _)=> [t1 [ ] ].
  case E2: (run _ _)=> [t2 [ ] ]; move: E2.
  move=> /[swap] -[???->].
  edestruct IHfuel as [_ IH2].
  move: E1=> /[swap] /IH2 ->.
  edestruct IHfuel as [IH1 _].
  by move/IH1. }
move=> nss n t sl sl' ms ms' r ts; split.
{ exact/HB. }
elim: nss ms ms' sl sl' r ts=> [>|[|n' ns] nss IHnss >]; rewrite run_BuildsE //.
{ by case. }
case E1: (run _ _)=> [t1 [ ] ].
case E2: (run _ _)=> [t2 [ ] ]; move: E2.
move=> /[swap] -[???->] /IHnss.
by move: E1=> /[swap]-> /HB.
Unshelve. all: done.
Qed.

Lemma Build_RunOutOfFuel n t sl sl' ms ms' fuel r: 
  run (Build fuel n) (Build_state ms sl r) = (t, (Build_state ms' sl' false))%xprod ->
  r = false.
Proof.
edestruct Build_RunOutOfFuel_aux as [IH1]; exact/IH1.
Unshelve. all: exact/nil.
Qed.

Lemma Builds_RunOutOfFuel (n : nodeType) nss ts t sl sl' ms ms' fuel r: 
  run (Builds (Build fuel) nss) (Build_state ms sl r) = (ts, (Build_state ms' sl' false))%xprod ->
  r = false.
Proof.
edestruct Build_RunOutOfFuel_aux as [_ IH1]; exact/IH1.
Unshelve. 
{ exact/n. }
exact/[n | nil].
Qed.


Lemma run_BuildP n t sl sl' ms ms' fuel :
  run (Build fuel n) (Build_state ms sl false) = (t, (Build_state ms' sl' false))%xprod ->
  let: mk_IN _ tss _ := InterpretNode n sl in 
  run_Build_spec n ms sl ms' sl' t fuel (if ms is nil then tss else ms :: tss).
Proof.
move=> /[dup] rE.
rewrite run_BuildE.
case E1: (InterpretNode _ _) => [s tss err].
case E2: fuel=> //.
set qss := (if ms is nil then tss else ms :: tss).
case E3: qss=> [|[|q qs] qss']=> // [ [<-<-<-]|].
{ econstructor=> //.
  { exact/E1. }
  { exact/eq_sym/E3. }
  by rewrite -E2 run_BuildE /= E1 -/qss E3 E2. }
case E4: (run _ _)=> [trh [ ] ].
case E5: (run _ _)=> [trt st2].
case=> /[dup] tE <- st2E.
econstructor=> //.
{ exact/E1. }
{ exact/eq_sym/E3. }
{ move: st2E E5 E4=> {1}-> /Builds_RunOutOfFuel-/(_ n t)->; exact. }
{ move: st2E E5 (E5)=> {1 2}-> /Builds_RunOutOfFuel-/(_ n t)->; exact. }
by rewrite -E2 rE tE.
Qed.

Lemma run_checkTreeP x ts qss sl sl' :  
    (run_chekTree_spec (Node x ts) qss sl sl') <->
    (run (checkTreeT (Node x ts) qss) sl = (true, sl')%xprod).
Proof.
  split.
  { case=> [>[->->->->qE]*|?>? [->->->->->] ] //. }
  case: ts qss=> [|t ts] [|[>|q qs qss] ].
  2-5: by rewrite /checkTreeT /= rununit.
  { rewrite /checkTreeT /= rununit=> -[->]. 
    apply/(@Run_empty _ _ _ _ x sl')=> //.
    by rewrite /checkTreeT /= rununit. }
  move=> /[dup] r.
  rewrite run_checkTreeE.
  destruct (InterpretNode (Tree.root t) sl) as [sl'' tss err] eqn:E.
  set qss' := match qs with
              | [ ] => snd (sl'', tss)
              | _ :: _ => qs :: snd (sl'', tss)
              end.
  destruct (run (checkTreeT t qss') _) as [b st] eqn:E1.
  destruct (run (checkTreeT (Node x ts) qss) st) as [b1 ?] eqn:E2.
  move=> -[/andP ] [/andP ] [/eqb_spec_reflect] tE bE b1E sE.
  rewrite bE in E1; rewrite b1E sE in E2.
  exact/(Run_step _ _ _ _ E (eq_refl qss') E1 E2).
Qed.


Lemma eval_state_checkTreeP x ts qss st :
  reflect 
    (run_chekTree_spec (Node x ts) qss st (xsnd (run (checkTreeT (Node x ts) qss) st)))
    (eval_state (checkTreeT (Node x ts) qss) st).
Proof.
  apply: (iffP idP); rewrite /eval_state.
  { move=> RE; apply/run_checkTreeP; move: RE.
    by case: (run _ _)=> /= ??->. }
  by move/run_checkTreeP=>->.
Qed.

Lemma putError_internal q err : isInternal q = true -> isInternal (putError q err).
Proof.
  intros.
  unfold putError;
  destruct q.
  destruct e.
  { simpl in H1; auto. }
  destruct i; simpl in *; auto.
Qed. 

Lemma checkTree_intrenalN (t : messageTree) (qss : list (list nodeType)) sl : 
  Forall (Forall (fun n => isInternal n = true)) qss ->
  eval_state (checkTreeT t qss) sl = true -> 
  Forall (Tree.Forall (fun n => isInternal n = true)) (Tree.nodes t).
Proof.
  revert qss sl.
  induction t as [|t ts].
  { intros; constructor. }
  intros qss sl qsI; simpl.
  move=> /eval_state_checkTreeP runC.
  destruct runC; subst; try done.
  injection (eq_sym trE); intros; subst.
  destruct t as [n ts'].
  do ? constructor.
  { inversion qsI as [|?? X]; inversion X as [|?? Y].
    apply putError_internal with (err:=err) in Y;
    by rewrite <- tE in Y. }
  { apply (f_equal xfst) in runE1.
    eapply (IHt _ _ _ runE1); auto.
    Unshelve.
    apply IN_internal in INt.
    inversion qsI as [|?? X]; inversion X.
    by destruct qs; auto; constructor. }
  apply (f_equal xfst) in runE2.
  eapply IHt0 with (qss := qss0) (sl := st); auto.
  by inversion qsI.
Qed.

Lemma checkTree_checkRoots t qss sl : 
  eval_state (checkTreeT t qss) sl = true -> 
  checkRoots (fun n1 n2 => getAddrS n1 = getAddrS n2) (Tree.nodes t) qss.
Proof.
elim/Tree_ind: t qss sl=> [|t ts].
{ move=> ? [? /eval_state_checkTreeP-[|] //|>].
  by rewrite /eval_state /checkTreeT /= rununit. }
move=> n IHt1 IHt2 [>|[>|q qs qss] ].
1-2: by rewrite /eval_state /checkTreeT /= rununit.
move=> ? /eval_state_checkTreeP-[ ]//.
move=> ??? > [<-<-<-] [<-<-<-] <- qE.
move=> ??? /(f_equal xfst) r /= *.
split; last exact/IHt2/r.
by rewrite qE errorE.
Qed. 

Arguments InterpretNode : simpl never.

Inductive addr_spec : messageTree -> Prop := 
  | Addr_spec1 n (t : messageTree) ts
    (addrRt       : getAddrS n = getAddrS (Tree.root t))
    (addrSts      : Forall (fun n' => getAddrS (Tree.root n') = getAddrR n) ts)
    (addr_spec_tr : Forall addr_spec (t :: ts)) :
      addr_spec (Node n (t :: ts))
  | Addr_spec2 n ts
    (addrSts      : Forall (fun n' => getAddrS (Tree.root n') = getAddrR n) ts)
    (addr_spec_tr : Forall addr_spec ts) :
      addr_spec (Node n ts).

Definition addr_spec_nodes n qss := 
  match qss with 
  | q :: qs => 
    Forall (Forall (fun n' => getAddrS n' = getAddrR n)) qss \/
    Forall (Forall (fun n' => getAddrS n' = getAddrR n)) qs /\ 
    Forall (fun n' => getAddrS n' = getAddrS n) q
  | nil => True
  end.

Lemma add_spec_nodesF n qss :
  Forall (Forall (fun n' => getAddrS n' = getAddrR n)) qss ->
  addr_spec_nodes n qss.
Proof. by case: qss=> //=; left. Qed.

Lemma checkRoots_Forall ts qss (P : nodeType -> Prop) 
  (R : nodeType -> nodeType -> Prop) :
  (forall x y, P y -> R x y -> P x) ->
  Forall (Forall P) qss ->
  checkRoots R ts qss ->
  Forall P (map (@Tree.root _) ts).
Proof.
  elim: ts qss=> /=; first by constructor.
  move=>> IHts -[ ] // [ ] //> RP X.
  inversion X as [|?? Y]; inversion Y.
  move=> [/RP] PP { }/IHts IHts.
  constructor=> //; last exact/IHts.
  exact/PP.
Qed.

Hint Resolve Tree.size_lt_cons Tree.size_lt_add_root : core.

Lemma checkTree_addr_spec t qss sl : 
  addr_spec_nodes (Tree.root t) qss ->
  eval_state (checkTreeT t qss) sl = true ->
  addr_spec t.
Proof.
have AH: (forall n x y,
  getAddrS y = getAddrR n -> getAddrS x = getAddrS y -> getAddrS x = getAddrR n).
{ by move=>> ->. }
elim/Tree.ind_size: t qss sl=> -[n ts] IHt qss sl.
case: qss=> [|[|q qs] qss].
1-2: case: (ts)=> [|>]; rewrite /checkTreeT /= /eval_state rununit //.
{ by do ? constructor. }
case: ts IHt=> [|t ts] IHt.
{ by rewrite /checkTreeT /= /eval_state rununit. }
move=> ads.
case/eval_state_checkTreeP=> // ?? tss > [<-<-<-] [<-<-<-] <-.
move=> qE IN qss'E r1 r2 r3.
have adsts: (addr_spec (Node n ts)).
{ apply/IHt=> //; last exact/(f_equal xfst r2).
  move: ads=> /= -[|[ ] ] X *; apply/add_spec_nodesF=> //.
  by inversion X. }
have adstss: addr_spec_nodes (Tree.root t) tss.
{ exact/add_spec_nodesF/IN_addrS/IN. }
move: ads.
rewrite /addr_spec_nodes=> /[dup] ? -[ads|[ads1 ads2] ].
{ constructor 2.
  { move/(f_equal xfst)/checkTree_checkRoots: r3.
    by move=> /checkRoots_Forall-/(_ _ (AH _) ads) /Forall_map. }
  constructor.
  { apply/IHt=> //; last exact/(f_equal xfst r1).
    case: (qs) qss'E ads=> [|a l]-> // /Forall_forall f.
    right; split.
    { exact/IN_addrS/IN. }
    rewrite qE; apply/Forall_forall=> x In.
    move: (f (q :: a :: l))=> /(_ (or_introl eq_refl))/Forall_forall.
    move=> /[dup]/(_ x)/(_ (or_intror In))->.
    move=> /(_ q)/(_ (or_introl eq_refl)).
    by rewrite errorE=>->. }
  by inversion adsts. }
constructor 1.
{ rewrite qE. 
  move/Forall_forall/(_ q (or_introl eq_refl)): ads2.
  by rewrite errorE=>->. } 
{ move/(f_equal xfst)/checkTree_checkRoots: r2=> /=.
  by move=> /checkRoots_Forall-/(_ _ (AH _) ads1) /Forall_map. }
constructor; last by inversion adsts.
apply/IHt=> //; last exact/(f_equal xfst r1).
case: (qs) qss'E ads2=> [|a l]-> // /Forall_forall f.
right; split=> //.
{ exact/IN_addrS/IN. }
rewrite qE; apply/Forall_forall=> x In.
move: (f x)=> /(_ (or_intror In)).
move: (f q)=> /(_ (or_introl eq_refl)).
by rewrite errorE=>->.
Qed.

Definition error_spec `{eqb_spec Interfaces} (t : messageTree) := 
  forall t', 
    let rt' := Tree.root t' in
    Tree.sub t' t ->
    isInternal rt' ->
    isSome (err_of (getError rt'))  ->
    has_money_for_on_bounce (getError rt') ->
    getBounce (getMess rt') ->
    exists2 n, 
      Tree.In n t' &
      onBounce_spec (getAddrR rt') n.

Lemma checkTree_qss t sl qss : 
  eval_state (checkTreeT t qss) sl = true ->
  forall x q, In q qss -> In x q -> exists err, Tree.In (putError x err) t.
Proof.
elim/Tree.ind_size: t sl qss=> -[t [|tsh tst] ] IHt sl qss.
all: case/eval_state_checkTreeP=> //.
{ by move=>> ?? ->. }
move=> ??????????? err [<-<-<-].
destruct qss as [|[|q qs] qss]=> //.
case=><-<-<-<- qE IN qss'E /(f_equal xfst) r1 /(f_equal xfst) r2 r3.
move=> ?? /= [<-/=[<-|] |].
{ by exists err; constructor 2; do ? constructor 1. }
{ case: (qs) r1 qss'E=> // ?? /IHt/[swap]->/[apply]-[ ] //.
  { by left. }
  by move=> err'; exists err'; constructor 2; constructor 1. }
move: r2=> /IHt/[apply]/[apply]-[//|] err'.
exists err'; exact/Tree.In_cons.
Qed.

Lemma checkTree_error_hyps {sl qs qss n tsh tst q qss'} :
  eval_state (checkTreeT (Node n (tsh :: tst)) qss) sl = true -> 
  qss = (q :: qs) :: qss' ->
  let IntN := InterpretNode (Tree.root tsh) sl in
  [/\ getError (Tree.root tsh) = errTp_of IntN                                    ,
  incl (tss_of IntN) (if qs is nil then (tss_of IntN) else qs :: (tss_of IntN)) &
  eval_state 
    (checkTreeT tsh (if qs is nil then (tss_of IntN) else qs :: (tss_of IntN))) 
    (sl_of IntN) = true].
Proof.
  case/eval_state_checkTreeP=>> //.
  case=> <-<-<--><- qE IN qss'E r1 r2 r3 [? qsE ?] IntN.
  rewrite -qsE /IntN IN /= qE errorE -qss'E; split=>//.
  { move: qss'E; rewrite qsE; case: (qs)=>[|??]-> //; by right. }
  by move/(f_equal xfst): r1.
Qed.


Lemma checkTree_error_spec `{eqb_spec Interfaces} sl qss tr: 
  (let IntN := InterpretNode (Tree.root tr) sl in
  getError (Tree.root tr) = errTp_of IntN ->
  incl (tss_of IntN) qss -> 
  eval_state (checkTreeT tr qss) (sl_of IntN) = true -> 
    error_spec tr) /\ 
  (eval_state (checkTreeT tr qss) sl = true ->
    Forall error_spec (Tree.nodes tr)).
Proof.
elim/Tree.ind_size: tr sl qss=> -[n ts] IHtr sl qss.
split.
{ move=> IntN err inc.
  destruct ts as [|tsh tst]=> /eval_state_checkTreeP-[ ] //.
  { move=> ? sl' ? [xE] qssE; move: inc err; rewrite /IntN qssE xE /Tree.root.
    move=> inc err <- r; rewrite /error_spec=> ?. 
    rewrite Tree.subE=> -[ ]; last by move=> X; inversion X.
    move->=> /=; by rewrite err=> /IN_error/[apply]/[apply]/[apply]-[?/inc]. }
  move=> ? sl' ? sl'' ? qs qss1 qss'>; move: inc err => inc err.
  case=> <-<-<- /[dup] qssE <-<- qE IN qss'E.
  move=> r1 /(f_equal xfst) r2 /(f_equal xfst) r3.
  move=> t' /=; rewrite Tree.subE=> -[->|].
  { rewrite err => /IN_error/[apply]/[apply]/[apply]-[ ]; rewrite /Tree.root.
    move/checkTree_qss: r3=> qss_sub.
    move=> x /inc/qss_sub x_sub /Exists_exists .
    case=> n' -[/x_sub-[err' ] ]; exists (putError n' err')=> //.
    exact/onBounce_spec_putError. }
  move=> /= /Exists_cons-[ ].
    { have s: (Tree.size tsh < Tree.size (Node n (tsh :: tst)))%coq_nat by [ ].
    case: (IHtr _ s (sl_of IntN) qss')=> +_.
    case: (checkTree_error_hyps r3 qssE).
    rewrite IN -qss'E=> ???; exact. }
  have s: (Tree.size (Node n tst) < Tree.size (Node n (tsh :: tst)))%coq_nat by [ ].
  case: (IHtr _ s sl'' qss1)=> _.
  move: r2=> /[swap]/[apply] /=.
  move=> /Forall_forall f /Exists_exists-[n' [/f] ]; exact. }
destruct ts as [|tsh tst].
{ by constructor. }
case/eval_state_checkTreeP=> // ? sl' ? sl'' ? qs qss1 qss'>.
case=> <-<-<- /[dup] qssE <-<- qE IN qss'E.
move=> r1 /(f_equal xfst) r2 /(f_equal xfst) r3.
constructor.
{ have s: (Tree.size tsh < Tree.size (Node n (tsh :: tst)))%coq_nat by [ ].
  case: (IHtr _ s sl qss')=> +_.
  case: (checkTree_error_hyps r3 qssE).
  rewrite IN -qss'E=> ???; exact. }
have s: (Tree.size (Node n tst) < Tree.size (Node n (tsh :: tst)))%coq_nat by [ ].
case: (IHtr _ s sl'' qss1)=> _.
by move: r2=> /[swap]/[apply] /=.
Qed.

Lemma checkForest_IN 
  (P : list (list nodeType) -> nodeType -> Prop) 
  (Q : messageTree -> Prop)
  sl trs :
  (forall n sl qss err sl', 
    InterpretNode n sl = mk_IN sl' qss err -> 
    P qss n) ->
  (forall qss sl tr, 
    P qss (Tree.root tr) -> 
    eval_state (checkTreeT tr qss) sl = true -> Q tr) ->
  eval_state (checkForestT trs) sl = true -> Forall Q trs.
Proof.
move=> PP QP.
elim: trs sl; first by constructor.
move=> trh trt IHtrs sl.
rewrite checkForestE /eval_state runmodifybind runbind runget.
case E1: (InterpretNode _ _).
rewrite runputbind runbind.
case E2: (run _ _); move/(f_equal xfst): E2=> E2.
rewrite runbind.
case E3: (run _ _); move/(f_equal xfst): E3=> E3.
rewrite rununit /==> /andP-[/andP-[ ] ]; rewrite /is_true=>*; subst.
constructor.
{ exact/QP/E2/PP/E1. }
exact/IHtrs/E3.
Qed.

Arguments Tree.root {_}.
Arguments Tree.nodes {_}.

Theorem checkForest_messages_type trs ems sl :
  checkForest trs ems sl ->
  (forall tr, In tr trs -> isExternal (Tree.root tr)) /\ 
  (forall tr, In tr trs ->
    Forall (Tree.Forall (fun x => isInternal x)) (Tree.nodes tr)).
Proof.
move=> /andP-[/checkForest_IN] IN Eq; split.
{ elim: (trs) ems Eq=> // trh trt IHtrs [ ] // e ?.
  rewrite /= /eqb /==> /andP-[/eqb_spec_intro] tE { }/IHtrs IHtrs.
  move=> tr -[<-|/IHtrs] //.
  rewrite (isExternal_putError _ (Build_errorType None false)) tE.
  by case: (e). }
apply/Forall_forall/IN=>>.
{ exact/IN_internal. }
exact/checkTree_intrenalN.
Qed.

Theorem checkForest_addr_spec trs ems sl :
  checkForest trs ems sl ->
  Forall addr_spec trs.
Proof.
move=> /andP-[/checkForest_IN] + _; apply=>>.
{ apply IN_addrS. }
by move=> ?; apply/checkTree_addr_spec/add_spec_nodesF.
Qed.

Theorem checkForest_error_spec `{eqb_spec Interfaces} trs ems sl :
  checkForest trs ems sl ->
  Forall error_spec trs.
Proof.
move=> /andP-[+_].
elim: trs sl; first by constructor.
move=> trh trt IHtrs sl.
rewrite checkForestE /eval_state runmodifybind runbind runget.
case E1: (InterpretNode _ _)=> [sl' tss' err'].
rewrite runputbind runbind.
case E2: (run _ _); move/(f_equal xfst): E2=> E2.
rewrite runbind.
case E3: (run _ _); move/(f_equal xfst): E3=> E3.
rewrite rununit /==> /andP-[/andP-[ ] ]; rewrite /is_true=>??; subst.
move/eqb_spec_intro=> ?.
constructor.
{ case: (checkTree_error_spec (setTime (getTime (Tree.root trh)) sl) tss' trh)=> +_. 
  by apply; rewrite E1. }
exact/IHtrs/E3.
Qed.

Arguments Tree.size : simpl never.

Lemma checkTreeT_inj t1 t2 tss sl :
  Tree.root t1 = Tree.root t2 ->
  eval_state (checkTreeT t1 tss) sl = true ->
  eval_state (checkTreeT t2 tss) sl = true ->
  ((t1 = t2) * 
  (run (checkTreeT t2 tss) sl = 
   run (checkTreeT t2 tss) sl))%type.
Proof.
move=> rE e1 e2; suff->: (t1 = t2) by [ ].
move: rE e1 e2.
elim/Tree.ind_size: t1=> -[x ts] IHt1 in t2 tss sl *.
move=> /= rE /eval_state_checkTreeP rP.
inversion rP; subst; destruct t2 as [x' ts']=> //=; first last.
all: move=> /eval_state_checkTreeP rP'.
all: inversion rP'; subst=> //.
all: case: trE=> ??; subst.
all: case: trE0=> ??; subst=> //.
case/(@eq_sym _ _ _): queE=> *; subst.
move: INt INt0 (tE) (tE0). 
rewrite {1}tE {1}tE0 ?errorE=> -> -[??->/[swap]<-].
move/IHt1=> /= IH; subst.
move: (f_equal xfst runE1) (f_equal xfst runE0).
move=> { }/IH/[apply]/(_ (@Tree.size_lt_add_root _ _ _ _)).
move=> ?; subst.
move: runE1 runE0=>-> [?]; subst.
move/IHt1: (f_equal xfst runE2) (f_equal xfst runE4)=> /[apply].
by move/(_ (@Tree.size_lt_cons _ _ _ _))/(_ eq_refl)=> [->].
Qed.

Lemma MessagesQueue_run_BuildE {n fuel sl ms} :
  RunOutOfFuel (exec_state (Build fuel n) (Build_state ms sl false)) = false ->
  MessagesQueue (exec_state (Build fuel n) (Build_state ms sl false)) = [ ].
Proof.
set eq := (@eq_refl _ (run (Build fuel n) (Build_state ms sl false))).
move: {2}(run _ _) eq=> -[t [ms' sl' ?] ]=> /[dup]+/[swap].
rewrite /exec_state=>{1}->/=-> /[dup]{2}-> /=.
elim: fuel=> [|fuel IHfuel] in t n ms ms' sl sl' *.
{ by rewrite run_BuildE. }
move/run_BuildP.
case E: (InterpretNode _ _)=> [? tss ?].
set qss := if ms is nil then tss else ms :: tss.
move=> rP.
inversion rP; subst; first last.
{ by case: (ms')=> [|??] in qssE *. }
move/IHfuel: runE1=> ?; subst.
move: IHfuel runE2; clear=> IHfuel.
elim: qss0=> [|[|q qs] qss IHqss] in trt sl'0 ms' sl' *; rewrite run_BuildsE //=.
{ by case. }
case E: (run _ _)=> [?[?? r] ].
case E1: (run _ _)=> [?[ ] ]; move: E1=> /[swap].
case=> ? ->->-> E1.
have rE: r = false by exact/Builds_RunOutOfFuel/E1.
subst.
move/IHfuel: E=> ?; subst.
exact/IHqss/E1.
Qed.

Lemma run_Build_eq_root fuel n  ms sl ms1 sl1 t :
  run (Build fuel n) (Build_state ms sl false) = 
  (t, Build_state ms1 sl1 false)%xprod -> 
    Tree.root t = putError n (InterpretNode (Tree.root t) sl).
Proof.
move/run_BuildP.
case E: (InterpretNode _ _)=> [>] rP.
by inversion rP; rewrite -tE /= errorE INt.
Qed.

Lemma run_Build_eq_root2 fuel n  ms sl ms1 sl1 t :
  run (Build fuel n) (Build_state ms sl false) = 
  (t, Build_state ms1 sl1 false)%xprod -> 
    Tree.root t = putError n (InterpretNode n sl).
Proof.
move/run_BuildP.
case E: (InterpretNode _ _)=> [>] rP.
by inversion rP; rewrite -tE -E /= INt.
Qed.

Lemma checkTreeBuildE n t fuel sl sl' ms : 
  let: tss  := tss_of (InterpretNode n sl) in
  let: sl'' := sl_of (InterpretNode n sl) in
  let: qss  := (if ms is nil then tss else ms :: tss)  in
  run (Build fuel n) (Build_state ms sl false) = 
  (t, (Build_state nil sl' false))%xprod ->
  run (checkTreeT t qss) sl'' = (true, sl')%xprod.
Proof.
elim: fuel t ms n sl sl'=>[>|].
{ by rewrite run_BuildE. }
move=> fuel IHfuel [x ts] ms n sl sl'.
case E: (InterpretNode n sl)=> [sl'' tss err].
rewrite /tss_of /sl_of.
set qss  := (if ms is nil then tss else ms :: tss).
move/run_BuildP; rewrite {1}E -/qss=> rP.
inversion rP=> //; have slE: sl'' = sl0 by rewrite INt in E; case: E=> slE.
all: subst; rewrite -tE.
2: { by rewrite run_checkTreeE. }
rewrite run_checkTreeE.
case E6: (InterpretNode _ _)=> [sl'' tss'' err''].
case E7: (run _ _)=> [b1 s1].
case E8: (run _ _)=> [b2 s2].
move/run_Build_eq_root: (runE1) (E6)=> /[swap] -> /= /[dup] rE->.
rewrite eqbxx /=.
move: (@MessagesQueue_run_BuildE q fuel sl0 qs) (runE1).
rewrite /exec_state {1 2}runE1 /= => -> // /IHfuel.
rewrite rE errorE in E6; rewrite E6 /=.
rewrite E7=> -[-> sE] /=; subst.
elim: (qss0) (ms') (sl') (sl'0) (b2) (s2) (trt) runE2 E8.
{ clear=>>; rewrite run_BuildsE run_checkTreeE.
  by case=><-?<- [->->]. }
move: IHfuel nodeEqType; clear=> IHfuel nodeEqType.
move=> [|q qs] qss IHqss ?? sl' >; rewrite run_BuildsE //=.
case E1: (run _ _)=> [trt [?? r] ].
case E2: (run _ _)=> [trt1 st1].
case=> <- st1E; subst.
rewrite run_checkTreeE.
case E6: (InterpretNode _ _)=> [sl'' tss'' err''].
case E7: (run _ _)=> [b3 s3].
case E8: (run _ _)=> [b4 s4].
have rE: r = false by exact/Builds_RunOutOfFuel/E2.
subst.
move/run_Build_eq_root: (E1) (E6)=> /[swap] -> /= /[dup] rE->.
rewrite eqbxx /= .
move: (@MessagesQueue_run_BuildE q fuel sl' qs) (E1).
rewrite /exec_state {1 2}E1 /= => -> // /IHfuel.
rewrite rE errorE in E6; rewrite E6 /=.
rewrite E7=> -[-> sE] /=; subst.
by move/IHqss: E2=> /(_ _ _ E8)=> -[->->][->->].
Qed.

Lemma checkTreeP n t fuel sl sl' ms : 
  let: tss  := tss_of (InterpretNode n sl) in
  let: sl'' := sl_of (InterpretNode n sl) in
  let: qss  := if ms is nil then tss else ms :: tss  in
  RunOutOfFuel (exec_state (Build fuel n) (Build_state ms sl false)) = false ->
  run (Build fuel n) (Build_state ms sl false) = 
  (t, (Build_state nil sl' false))%xprod <->
  putError n (InterpretNode n sl) = Tree.root t /\ 
  run (checkTreeT t qss) sl'' = (true, sl')%xprod.
Proof.
move=> rofE; split.
{ by move=> /[dup] /run_Build_eq_root2-> /checkTreeBuildE->. }
case=> tE.
set rb := run (Build fuel n) (Build_state ms sl false).
set st := xsnd rb.
move: (@checkTreeBuildE n (xfst rb) fuel sl (SuperLedger st) ms).
move: (rofE) (MessagesQueue_run_BuildE rofE).
rewrite /exec_state /st /rb; case E: (run _ _)=> [? [ ] ].
move=> /= ->-> /(_ eq_refl).
rewrite /exec_state E /= in rofE; rewrite rofE in E.
move/run_Build_eq_root2: E=> rootE.
do 2? move=> /[dup] /(f_equal xsnd) /= {-1}<- /[swap].
move=> /(f_equal xfst)/[swap] /(f_equal xfst) /=.
by move/checkTreeT_inj/[apply]; rewrite rootE -tE=> /(_ eq_refl)-[->].
Qed.

Lemma run_buildForestE fuel ls ms sl r : 
  run (buildForestT fuel ls) (Build_state ms sl r) = 
  match ls with 
  | [ ] => ([ ], Build_state ms sl r)%xprod
  | n :: tln => 
    let: (tree, st)%xprod := 
      run 
        (Build fuel n) 
        (Build_state ms (setTime (getTime n) sl) r) in 
    let: (forest, st')%xprod := run (buildForestT (fuel - 1) tln) st in 
      (tree :: forest, st')%xprod
  end.
Proof.
case: ls=> //= *; rewrite (rununit, runmodifybind) //.
do ? (rewrite runbind; case: (run _ _)=> * ).
by rewrite rununit.
Qed.

Lemma eval_state_buildForest1E fuel l sl ms r : 
  eval_state (buildForestT fuel (l :: nil)) (Build_state ms sl r) = 
  [eval_state (Build fuel l) (Build_state ms (setTime (getTime l) sl) r)].
Proof.
rewrite /eval_state run_buildForestE.
by case: (run _ _)=> [?[ ] ] *; rewrite run_buildForestE.
Qed.

Lemma exec_state_buildForest1E fuel l sl ms r : 
  exec_state (buildForestT fuel (l :: nil)) (Build_state ms sl r) = 
  exec_state (Build fuel l) (Build_state ms (setTime (getTime l) sl) r).
Proof.
rewrite /exec_state run_buildForestE.
by case: (run _ _)=> [?[ ] ] *; rewrite run_buildForestE.
Qed.

Lemma buildForest_RunOutOfFuel ls sl fuel ms r: 
  RunOutOfFuel 
    (exec_state (buildForestT fuel ls) (Build_state ms sl r)) = false ->
  r = false.
Proof.
elim: ls=> [|l ls IHl] in fuel ms sl r *; rewrite /exec_state /=.
{ by rewrite rununit. }
rewrite runmodifybind runbind.
case E1: (run _ _)=> [? [ ] ]; rewrite runbind.
case E2: (run _ _)=> [? [ ] ]; rewrite rununit.
move: E2=> /[swap] /=-> /(f_equal xsnd)/(f_equal RunOutOfFuel)/IHl.
move=> ?; subst.
exact/Build_RunOutOfFuel/E1.
Qed.

Lemma MessageQueue_run_buildForestE {ls fuel sl}: 
  RunOutOfFuel 
    (exec_state (buildForestT fuel ls) (Build_state nil sl false)) = false ->
  MessagesQueue
    (exec_state (buildForestT fuel ls) (Build_state nil sl false)) = nil.
Proof.
elim: ls=> [|l ls IHl] in fuel sl *; rewrite /exec_state /=.
{ by rewrite rununit. }
rewrite runmodifybind runbind.
case E1: (run _ _)=> [? [ ] ]; rewrite runbind.
case E2: (run _ _)=> [? [ ] ]; rewrite rununit.
move: (E2)=> /[swap] /= ?; subst.
move/[dup]/(f_equal xsnd)/(f_equal RunOutOfFuel).
move/buildForest_RunOutOfFuel=> ?; subst.
move/[dup]/(f_equal xsnd)/(f_equal RunOutOfFuel).
move/(f_equal xsnd)/(f_equal RunOutOfFuel)/MessagesQueue_run_BuildE: (E1).
rewrite /= /exec_state E1 /= => ?; subst=>/IHl.
by rewrite /exec_state E2.
Qed.


Lemma rof_buildForest_cons {l ls fuel sl tr tr' ms1 sl1 ms2 sl2 r1 r2} : 
  let: st1 := Build_state ms1 sl1 r1 in 
  let: st2 := Build_state ms2 sl2 r2 in 
  RunOutOfFuel 
  (exec_state (buildForestT fuel (l :: ls)) (Build_state nil sl false)) = false ->
  run (Build fuel l) (Build_state nil (setTime (getTime l) sl) false) =
     (tr, st1)%xprod -> 
  run (buildForestT (fuel - 1) ls) st1 = (tr', st2)%xprod -> 
  (r1  = false) *
  (r2  = false) *
  (ms1 = nil)   *
  (ms2 = nil).
Proof.
rewrite /exec_state /= runmodifybind runbind.
case E1: (run _ _)=> [? [ ] ]; rewrite runbind.
case E2: (run _ _)=> [? [ ] ]; rewrite rununit.
move=> /= ?; subst.
move/(f_equal xsnd)/(f_equal RunOutOfFuel)/buildForest_RunOutOfFuel: (E2)=> /= ?.
subst.
move/(f_equal xsnd)/(f_equal RunOutOfFuel)/MessagesQueue_run_BuildE: (E1)=> /= E.
rewrite /exec_state E1 /= in E; subst.
move/(f_equal xsnd)/(f_equal RunOutOfFuel)/MessageQueue_run_buildForestE: (E2).
by rewrite /exec_state E2=> /= ?; subst=> -[? <-<-<-]; rewrite E2=> -[?<-?<-].
Qed.


Lemma checkForestTP fr ls fuel sl sl' : 
  RunOutOfFuel 
    (exec_state (buildForestT fuel ls) (Build_state nil sl false)) = false ->
  (map (fun t => putError (Tree.root t) (Build_errorType None false)) fr) =
  (map (fun m => putError m (Build_errorType None false)) ls) /\
  run (checkForestT fr) sl = (true, sl')%xprod <->
  run (buildForestT fuel ls) (Build_state nil sl false) = 
  (fr, Build_state nil sl' false)%xprod.
Proof.
elim: ls=> [/=|l ls IHl] in fr fuel sl sl' *.
{ rewrite /exec_state ?rununit /==> ?.
  case: fr=> [/=|]; last split=> [ [ ]|] //.
  by rewrite rununit; split=> [ [? [ ] ]|[ ] ]->. }
move=> rofE /=.
rewrite runmodifybind runbind.
case E1: (run (Build _ _) _)=> [a [? sl'' ?] ].
rewrite runbind.
case E2: (run (buildForestT _ _) _)=> [b [? sl0 ?] ].
rewrite rununit. 
have runE1 := E1; have runE2 := E2.
rewrite ?(rof_buildForest_cons rofE E1 E2) {E1 E2} in runE1 runE2 *.
split.
{ case=> lsE ct.
  destruct fr as [|tr fr]=> //.
  move: ct; rewrite /=.
  rewrite runmodifybind runbind runget.
  case E3: (InterpretNode _ _)=> [sl1 tss1 err1].
  rewrite runputbind runbind.
  case E4: (run _ _)=> [? sl'''].
  rewrite runbind.
  case E5: (run _ _)=> [ ].
  rewrite rununit=> -[/andP-[/andP-[ ] ] ]; rewrite /is_true=> ??+?; subst.
  move=> /eqb_spec_reflect.
  move: (@checkTreeP l tr fuel (setTime (getTime l) sl) sl''' nil).
  move: lsE=> /= [ ] /(f_equal (fun x => putError x (getError l))).
  rewrite ?errorE=> {5 6 7 8 9 10 11}<- lsE.
  rewrite ?errorE ?E3 /= => -[ ].
  { by rewrite /exec_state runE1. }
  move=> _ /[swap]<-; rewrite ?errorE E4=> /(_ (conj eq_refl eq_refl)).
  rewrite runE1=> -[??]; subst.
  case: (IHl fr (fuel - 1) sl''' sl').
  { by rewrite /exec_state runE2. }
  rewrite lsE E5=> /(_ (conj eq_refl eq_refl)).
  by rewrite runE2=> -[->->]. }
case=> <-<- /=.
rewrite runmodifybind runbind runget.
case E3: (InterpretNode _ _)=> [sl1 tss1 err1].
rewrite runputbind runbind.
case E4: (run _ _)=> [? sl'''].
rewrite runbind.
case E5: (run _ _)=> [ ].
rewrite rununit.
move: (@checkTreeP l a fuel (setTime (getTime l) sl) sl'' nil).
case.
{ by rewrite /exec_state runE1. }
move=> /(_ runE1) -[ ] ++ _.
move=> aE; move: E3; rewrite -aE ?errorE=>-> /=.
rewrite ?errorE eqbxx E4=> -[??]; subst.
case: (IHl b (fuel - 1) sl'' sl0).
{ by rewrite /exec_state runE2. }
by move=> _ /(_ runE2) -[-> ]; rewrite E5=> -[->->].
Qed.

Lemma checkForestP fr scen fuel sl : 
  buildFinished fuel scen sl ->
  reflect (fr = buildForest fuel scen sl) (checkForest fr scen sl).
Proof.
rewrite /buildFinished=> /negbTE /[dup] rofE /checkForestTP cE.
rewrite /checkForest /buildForest /eval_state.
apply/(iffP andP).
{ case=> fE /eqb_spec_reflect ?.
  rewrite (proj1 (cE fr (xsnd (run (checkForestT fr) sl)))); split=> //.
  by case: (run _ _) fE=> //= ??->. }
move=> frE.
destruct 
  (cE 
    fr 
    (SuperLedger 
      (xsnd 
        (run 
          (buildForestT fuel (mapNode scen)) 
          (Build_state nil sl false))))) as [_ bE].
case: bE=> [|-> ->] //=; last by rewrite eqbxx.
move/MessageQueue_run_buildForestE: rofE (rofE).
by rewrite frE /exec_state; case: (run _ _)=> /= ? [/=> ->->].
Qed.

Lemma execForestE fr scen fuel sl : 
  buildFinished fuel scen sl ->
  checkForest fr scen sl ->
  execForest fr sl = buildSLedger fuel scen sl.
Proof.
move=> /[dup] + /checkForestP/[apply]+->.
rewrite /buildFinished=> /negbTE /[dup] rofE /checkForestTP cE.
rewrite /execForest /buildSLedger /exec_state /=.
case: (cE (buildForest fuel scen sl) 
  (SuperLedger 
    (xsnd 
      (run 
        (buildForestT fuel (mapNode scen))
        (Build_state nil sl false)))))=> _ [|?->] //.
move/MessageQueue_run_buildForestE: rofE (rofE).
rewrite /exec_state; case E: (run _ _)=> [? [/=> ] ].
by move=>->->; rewrite /buildForest /eval_state E.
Qed.

Arguments buildForestT : simpl never.

Lemma buildForest_cat fuel ems1 ems2 sl : 
  buildFinished fuel ems1 sl ->
  buildForest fuel (ems1 ++ ems2) sl = 
  buildForest fuel ems1 sl ++
  buildForest (fuel - length ems1) ems2 (buildSLedger fuel ems1 sl).
Proof.
elim: ems1=> [/=|em ems1 IHems1 /=] in fuel ems2 sl *.
{ rewrite /buildForest /eval_state rununit /= subn0.
  by rewrite /buildSLedger /exec_state /= rununit. }
rewrite /buildFinished=> /negbTE rofE.
rewrite /buildForest /buildSLedger /eval_state /exec_state /=.
rewrite 2?run_buildForestE.
case E1: (run (Build _ _) _)=> [a [? sl' ?] ].
case E2: (run (buildForestT _ _) _)=> [b [ ] ].
case E3: (run (buildForestT _ _) _)=> [c [ ] ].
case E4: (run (buildForestT _ _) _)=> [d [ ] ].
move=> /=; apply/f_equal.
move: (IHems1 (fuel - 1) ems2 sl').
rewrite /buildForest /eval_state.
have runE1 := E1; have runE3 := E3.
rewrite !(rof_buildForest_cons rofE E1 E3) {E1 E3} in runE1 runE3 E4 E2 *.
have->: fuel - 1 - length ems1 = fuel - (length ems1).+1 by lia.
rewrite /buildFinished /buildSLedger /exec_state ?runE3 E2 /= E4.
exact.
Qed.

Section LedgerInvariants.

Variable (P : superLedger -> Prop).

Hypothesis P_inv_IN : forall n sl sl', 
  P sl -> 
  sl' = sl_of (InterpretNode n sl) -> 
  P sl'.

(* Lemma P_inv_CT tr qss st : 
  P st ->
  P (exec_state (checkTreeT tr qss) st).
Proof.
  rewrite /exec_state.
  case: st qss; elim/Tree.ind: tr=> /=.
  { move=> x ms sl qss ?; case: qss.
    { by rewrite run_checkTreeE. }
    by rewrite /checkTreeT /= rununit. }
  move=> t ts x ++++ qss.
  case: qss=> [*|[*|q qs qss IHtr1 IHtr2 ms sl Psl] ].
  1-2: by rewrite /checkTreeT /= rununit.
  rewrite run_checkTreeE.
  case E1: (InterpretNode _ _)=> [sl' tss].
  set qss' := if ms is nil then tss else ms :: tss.
  case E2: (run (checkTreeT _ _) _)=> [b [ms1 sl1] ].
  case E3: (run _ _) => [b' st' /=].
  move/(f_equal xsnd): E3=> /=<-.
  apply/IHtr2.
  move/(f_equal xsnd)/(f_equal SuperLedger): E2=> /=<-.
  apply/IHtr1/(P_inv_IN (Tree.root t) Psl).
  by rewrite E1.
Qed. *)

End LedgerInvariants.

End MessageTree.

