From HB Require Import structures.
From mathcomp Require Import boot boolp functions ssrnum ssralg.
From mathcomp Require Import interval_inference.
From mathcomp Require Import unstable reals Rstruct classical_sets.
From infotheo Require Import realType_ext.
From monae Require Import preamble hierarchy monad_lib proba_lib state_lib.
From monae Require Import monad_transformer proba_model.
From FreerDPS Require Import all_freerdps ping_common ping_components.
From FreerDPS Require Import prob_state.
From FreerDPS Require prob_monad_ping.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Abbreviation R := Rdefinitions.R.

Local Open Scope monae_scope.
Local Open Scope proba_monad_scope.
Local Open Scope contract_scope.
Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.

(******************************************************************************)
(* The lossy ping as components, on the Hoare side (quality) and on the       *)
(* probabilistic side (quantity).                                             *)
(******************************************************************************)

Import NetworkChannelMod ccm scm.

Definition flip_promise (ns : net_state) :
    forall X, @FlipEff R X -> X -> Prop :=
  fun X cmd => match cmd in FlipEff X return X -> Prop with
  | flipe q => fun b => ((q == 1%:i01) ==> b) /\ ((q == 0%:i01) ==> ~~ b)
  end.

Definition flip_c : contract (@FlipEff R) net_state :=
  make_contract const_witness no_requirement flip_promise.

Inductive queue := ToServer | ToClient.
Inductive NETWORK : effect :=
| DROP : queue -> NETWORK unit.

Definition drop_queue (q : queue) (ns : net_state) : net_state :=
  match q with
  | ToServer => consume_serverQ ns
  | ToClient => consume_clientQ ns
  end.

Definition network_step (ns : net_state) :
    forall X, NETWORK X -> X -> net_state :=
  fun X cmd _ => match cmd with DROP q => drop_queue q ns end.

(** A queue may only lose the packet that was just put in it. *)
Definition holds_packet (q : queue) (ns : net_state) : bool :=
  match q with
  | ToServer => serverQ ns == Some Ping
  | ToClient => clientQ ns == Some Pong
  end.

Definition network_req (ns : net_state) : forall X, NETWORK X -> Prop :=
  fun X cmd => match cmd with DROP q => holds_packet q ns end.

Definition network_c : contract NETWORK net_state :=
  make_contract network_step network_req no_promise.

Lemma chan_inv_drop q ns : chan_inv ns -> chan_inv (drop_queue q ns).
Proof. by case: q; case; split=> //; apply/eqP. Qed.

Definition link_c {LinkF : effect} `{NETWORK ;; @FlipEff R -<< LinkF} :
    contract LinkF net_state :=
  network_c -^- flip_c.

Lemma network_handler_preserves_inv X (cmd : NETWORK X) :
  preserves_invariant chan_inv (hoare_of_contract network_c cmd).
Proof.
by move=> s x s' _ [-> _]; case: cmd x=> q x /=; exact: chan_inv_drop.
Qed.

Lemma flip_handler_preserves_inv X (cmd : @FlipEff R X) :
  preserves_invariant chan_inv (hoare_of_contract flip_c cmd).
Proof. by move=> s x s' _ [-> _] /= inv. Qed.

Lemma link_handler_preserves_inv {LinkF : effect}
    `{NETWORK ;; @FlipEff R -<< LinkF} X (cmd : LinkF X) :
  preserves_invariant chan_inv (hoare_of_contract link_c cmd).
Proof.
apply: (shared_preserves_invariant (cf := network_c) (ce := flip_c)).
  exact: network_handler_preserves_inv.
exact: flip_handler_preserves_inv.
Qed.

Section transmit.
Context {Fx : effect} `{NETWORK ;; @FlipEff R -<< Fx} {M : freerMonad Fx}.
Context (p : {prob R}).

Definition drop_packet (q : queue) : M unit := ptrigger (DROP q).

(** The packet in [q] is lost with probability [p], kept with [1 - p]. *)
Definition transmit (q : queue) : M unit :=
  flip p >>= fun lost => when lost (drop_packet q).
End transmit.

Section link_syntax.
Context {Fx : effect} `{NETWORK ;; @FlipEff R -<< Fx} {M : freerMonad Fx}.
Context (p : {prob R}).

Lemma syn_flip : providesOnlyF (F := @FlipEff R) (flip p : M bool).
Proof. by exists (frTrigger (flipe p)). Qed.

Lemma syn_drop_packet q :
  providesOnlyF (F := NETWORK) (drop_packet q : M unit).
Proof. by exists (frTrigger (DROP q)). Qed.

End link_syntax.

(* We split because of the provideT we will go through *)
Section link_syntax.
Context {LinkF Fx : effect} `{Hlink : NETWORK ;; @FlipEff R -<< LinkF}.
Context `{HL : LinkF -< Fx} {M : freerMonad Fx} (p : {prob R}).
Lemma syn_transmit q :
  providesOnlyF (F := LinkF)
    (@transmit _ (@strictProvideT _ _ _ _ Hlink HL) M p q).
Proof.
exists (frBind (frTrigger (inj (flipe p))) (fun lost =>
  if lost then frBind (frTrigger (inj (DROP q))) (fun=> frRet tt)
  else frRet tt)).
rewrite /= /transmit; congr (_ >>= _).
by apply: funext=> -[].
Qed.
End link_syntax.

#[local] Hint Extern 0 (providesOnlyF (flip _)) =>
  solve [exact: syn_flip] : core.
#[local] Hint Extern 0 (providesOnlyF (drop_packet _)) =>
  solve [exact: syn_drop_packet] : core.
#[local] Hint Extern 0 (providesOnlyF (transmit _ _)) =>
  solve [exact: syn_transmit] : core.

Section transmit_s.
Context {Fx : effect} `{NETWORK ;; @FlipEff R -<< Fx} {M : freerMonad Fx}.
Context (p : {prob R}) (q : queue).

Lemma pre_transmit ns :
  holds_packet q ns -> pre (link_c |~ (transmit p q : M unit)) ns.
Proof.
move=> queued; rewrite freer_to_hoare_bindE freer_contract_right //.
split; first by rewrite pre_to_hoare_triggerP.
move=> lost ? /post_to_hoare_triggerP [-> _]; rewrite pre_to_hoare_whenP.
case: lost=> //=; rewrite freer_contract_left //.
by rewrite pre_to_hoare_triggerP.
Qed.

End transmit_s.

Section lossy_client.
Context {LinkF Fx : effect} `{Hlink : NETWORK ;; @FlipEff R -<< LinkF}.
Context `{Hcl : client_api ;; LinkF -<< Fx}.
Context {M : inductiveFreerMonad Fx} (p : {prob R}).

Let link_side : NETWORK ;; @FlipEff R -<< Fx :=
  @strictProvideT _ _ _ _ Hlink Hcl.(p2).

Definition lossy_client : component (M := M) CLIENT Fx :=
  fun _ cmd => match cmd with
  | ASK => send >> @transmit _ link_side M p ToServer
  | ANSWER => answer
  end.

Definition lossy_client_c : contract Fx net_state :=
  client_c -^- @link_c LinkF Hlink.

Lemma pre_lossy_client T (cmd : CLIENT T) ns :
  chan_inv ns -> pre (lossy_client_c |~ lossy_client cmd) ns.
Proof.
move=> inv; case: cmd=> /=; last first.
  by rewrite freer_contract_left //; exact: (pre_client ANSWER inv).
rewrite freer_to_hoare_bindE freer_contract_left //; split.
  exact: (pre_client ASK inv).
move=> _ ns1 /send_run [_ sQ].
rewrite freer_contract_right // freer_contract_prodT.
by apply: pre_transmit; rewrite /= sQ serverQ_fill_serverQ.
Qed.

(** Each primitive of [lossy_client_c] preserves the channel invariant. *)
Lemma lossy_client_handler_preserves_inv X (cmd : Fx X) :
  preserves_invariant chan_inv (hoare_of_contract lossy_client_c cmd).
Proof.
apply: (shared_preserves_invariant (cf := client_c) (ce := link_c)).
  exact: (@client_handler_preserves_inv _ (refl_Provide client_api)).
exact: link_handler_preserves_inv.
Qed.

Lemma lossy_client_run_preserves_inv A (prog : M A) :
  preserves_invariant chan_inv (lossy_client_c |~ prog).
Proof.
apply: to_hoare_preserves_invariant=> *.
exact: lossy_client_handler_preserves_inv.
Qed.

Lemma lossy_client_correct :
  correct_component lossy_client (no_contract CLIENT) lossy_client_c
    (fun=> chan_inv).
Proof.
move=> ? ns inv ? cmd _; split; first exact: pre_lossy_client.
move=> t ns' run; split=> //.
by apply: (lossy_client_run_preserves_inv _ run inv); exact: pre_lossy_client.
Qed.

End lossy_client.

Section lossy_server.
Context {LinkF Fx : effect} `{Hlink : NETWORK ;; @FlipEff R -<< LinkF}.
Context `{Hsv : server_api ;; LinkF -<< Fx}.
Context {M : inductiveFreerMonad Fx} (p : {prob R}).

Let link_side : NETWORK ;; @FlipEff R -<< Fx :=
  @strictProvideT _ _ _ _ Hlink Hsv.(p2).

Definition lossy_serve : M (option unit) :=
  serve_of (fun=> recv) (reply >> @transmit _ link_side M p ToClient) tt.

Definition lossy_server : component (M := M) SERVER Fx :=
  fun _ cmd => match cmd with
  | SERVE => lossy_serve
  end.

Definition lossy_server_c : contract Fx net_state :=
  server_c -^- @link_c LinkF Hlink.

Lemma pre_lossy_server T (cmd : SERVER T) ns :
  chan_inv ns -> pre (lossy_server_c |~ lossy_server cmd) ns.
Proof.
case: cmd=> -[sQ_ok _] /=; rewrite /lossy_serve /serve_of freer_to_hoare_bindE.
rewrite freer_contract_left //; split; first by rewrite recv_respect.
move=> [[]|] * /=; last 2 first.
- by rewrite pre_ret.
- by rewrite pre_ret.
rewrite freer_to_hoare_bindE; split; last by move=> *; rewrite pre_ret.
rewrite freer_to_hoare_bindE freer_contract_left //.
split; first by rewrite reply_respect.
move=> _ ns2 /reply_run [cQ _].
rewrite freer_contract_right // freer_contract_prodT.
by apply: pre_transmit; rewrite /= cQ clientQ_fill_clientQ.
Qed.

(** Each primitive of [lossy_server_c] preserves the channel invariant. *)
Lemma lossy_server_handler_preserves_inv X (cmd : Fx X) :
  preserves_invariant chan_inv (hoare_of_contract lossy_server_c cmd).
Proof.
apply: (shared_preserves_invariant (cf := server_c) (ce := link_c)).
  exact: (@server_handler_preserves_inv _ (refl_Provide server_api)).
exact: link_handler_preserves_inv.
Qed.

Lemma lossy_server_run_preserves_inv A (prog : M A) :
  preserves_invariant chan_inv (lossy_server_c |~ prog).
Proof.
apply: to_hoare_preserves_invariant=> *.
exact: lossy_server_handler_preserves_inv.
Qed.

Lemma lossy_server_correct :
  correct_component lossy_server (no_contract SERVER) lossy_server_c
    (fun=> chan_inv).
Proof.
move=> ? ns inv ? cmd _; split; first exact: pre_lossy_server.
move=> t ns' run; split=> //.
by apply: (lossy_server_run_preserves_inv _ run inv); exact: pre_lossy_server.
Qed.

End lossy_server.

Section lossy_protocol.
Context {Link Apis ProtoF : effect}.
Context `{Hlink : NETWORK ;; @FlipEff R -<< Link}.
Context `{Happ : client_api ;; server_api -<< Apis}.
Context `{Hproto : Apis ;; Link -<< ProtoF}.
Context {M : inductiveFreerMonad ProtoF} (p : {prob R}).

Definition client_side : client_api ;; Link -<< ProtoF :=
  strict_inner_left Happ Hproto.
Definition server_side : server_api ;; Link -<< ProtoF :=
  strict_inner_right Happ Hproto.

Definition lossy_contract : contract ProtoF net_state :=
  (client_c -^- server_c : contract Apis net_state) -^- @link_c Link Hlink.

Definition lossy_ping : component (M := M) ping_round ProtoF :=
  ping_with (@lossy_client _ _ Hlink client_side M p)
    (@lossy_server _ _ Hlink server_side M p).

Lemma lossy_contract_client {U} (m : M U) :
  providesOnlyF (F := client_api) m -> (lossy_contract |~ m) = (client_c |~ m).
Proof.
by move=> *;
  rewrite freer_contract_left // freer_contract_prodT freer_contract_left.
Qed.

Lemma lossy_contract_server {U} (m : M U) :
  providesOnlyF (F := server_api) m -> (lossy_contract |~ m) = (server_c |~ m).
Proof.
by move=>*;
  rewrite freer_contract_left // freer_contract_prodT freer_contract_right.
Qed.

Lemma lossy_contract_link {U} (m : M U) :
  providesOnlyF (F := Link) m -> (lossy_contract |~ m) = (link_c |~ m).
Proof.
by move=> syn; rewrite freer_contract_right.
Qed.

Lemma lossy_client_contractE T (cmd : CLIENT T) :
  (lossy_contract |~ @lossy_client _ _ Hlink client_side M p T cmd) =
  (@lossy_client_c _ _ Hlink client_side |~
    @lossy_client _ _ Hlink client_side M p T cmd).
Proof.
case: cmd=> /=; last first.
  by rewrite lossy_contract_client // freer_contract_left.
rewrite [LHS]freer_to_hoare_bindE [RHS]freer_to_hoare_bindE.
rewrite lossy_contract_client // [in RHS]freer_contract_left //.
congr (_ >>= _); apply: funext=> _.
by rewrite lossy_contract_link // freer_contract_right.
Qed.

Lemma lossy_server_contractE T (cmd : SERVER T) :
  (lossy_contract |~ @lossy_server _ _ Hlink server_side M p T cmd) =
  (@lossy_server_c _ _ Hlink server_side |~
    @lossy_server _ _ Hlink server_side M p T cmd).
Proof.
case: cmd=> /=; rewrite /lossy_serve /serve_of.
rewrite [LHS]freer_to_hoare_bindE [RHS]freer_to_hoare_bindE.
rewrite lossy_contract_server // [in RHS]freer_contract_left //.
congr (_ >>= _); apply: funext=> -[[]|] /=; last 2 first.
- by rewrite /freer_to_hoare !denote_ret.
- by rewrite /freer_to_hoare !denote_ret.
rewrite [LHS]freer_to_hoare_bindE [RHS]freer_to_hoare_bindE.
congr (_ >>= _); last first.
  by apply: funext=> c; rewrite /freer_to_hoare !denote_ret.
rewrite [LHS]freer_to_hoare_bindE [RHS]freer_to_hoare_bindE.
rewrite lossy_contract_server // [in RHS]freer_contract_left //.
congr (_ >>= _); apply: funext=> _.
by rewrite lossy_contract_link // freer_contract_right.
Qed.

Lemma lossy_client_shared_correct :
  correct_component (@lossy_client _ _ Hlink client_side M p)
    (no_contract CLIENT) lossy_contract (fun=> chan_inv).
Proof.
by move=> *; rewrite lossy_client_contractE; exact: lossy_client_correct.
Qed.

Lemma lossy_server_shared_correct :
  correct_component (@lossy_server _ _ Hlink server_side M p)
    (no_contract SERVER) lossy_contract (fun=> chan_inv).
Proof.
by move=> *; rewrite lossy_server_contractE; exact: lossy_server_correct.
Qed.

Lemma lossy_ping_correct :
  correct_component lossy_ping (no_contract ping_round)
    lossy_contract (fun=> chan_inv).
Proof.
exact/ping_with_correct/lossy_server_shared_correct/lossy_client_shared_correct.
Qed.
End lossy_protocol.

Section denote_retry.
Context {Fx : effect} {M : freerMonad Fx} {N : monad}.
Lemma denote_retry (h : Fx ~~> N) (run : M outcome) fuel :
  denote _ h _ (retry_ping_pong run fuel) =
  retry_ping_pong (denote _ h _ run) fuel.
Proof.
elim: fuel=> [//|fuel IH] /=; rewrite denote_bind.
by congr (_ >>= _); apply: funext=> -[]; rewrite compE /= ?denote_ret.
Qed.
End denote_retry.

(* -- PROBABILITIES START HERE -- *)

Module LossySpecs.
Section specs.
Context {N : probDrStateMonad R net_state} (p : {prob R}).

Definition spec_client : CLIENT ~~> N :=
  fun _ cmd => match cmd in CLIENT T return N T with
  | ASK => get >>= fun s =>
      let s1 := fill_serverQ Ping s in
      put (drop_queue ToServer s1) <| p |> put s1
  | ANSWER => get >>= fun s =>
      let answer := if clientQ s is Some Pong then GotPong else LostPong in
      put (consume_clientQ s) >> Ret answer
  end.

Definition spec_server : SERVER ~~> N :=
  fun _ cmd => match cmd in SERVER T return N T with
  | SERVE => get >>= fun s =>
      let s0 := consume_serverQ s in
      if serverQ s is Some Ping then
        let s1 := fill_clientQ Pong s0 in
        (put (drop_queue ToClient s1) <| p |> put s1) >> Ret (Some tt)
      else put s0 >> Ret None
  end.

(** A transmission succeeds with probability [1 - p]. *)
Definition ref_ping_pong : ping_round ~~> N :=
  fun _ cmd => match cmd in ping_round T return N T with
  | one_round =>
      ping_pong (transmit := prob_monad_ping.transmit) p%:num.~%:i01
  | retry_round fuel =>
      ping_pongs (transmit := prob_monad_ping.transmit) p%:num.~%:i01 fuel
  end.

End specs.
End LossySpecs.

Module SharedLink.
Import LossySpecs.

Section shared_link.
Context {Link Apis ProtoF : effect}.
Context `{Hlink : NETWORK ;; @FlipEff R -<< Link}.
Context `{Happ : client_api ;; server_api -<< Apis}.
Context `{Hproto : Apis ;; Link -<< ProtoF}.
Context {N : probDrStateMonad R net_state}.

Local Abbreviation client_side := (@client_side _ _ _ Happ Hproto).
Local Abbreviation server_side := (@server_side _ _ _ Happ Hproto).

Definition link_side : NETWORK ;; @FlipEff R -<< ProtoF :=
  @strictProvideT _ _ _ _ Hlink Hproto.(p2).

Local Abbreviation proto_c := (@lossy_contract _ _ _ Hlink Happ Hproto).

Variable res : net_state -> forall X, ProtoF X -> X.
Hypothesis res_compliant : @compliant R _ link_side.(p2) _ proto_c res.

Local Abbreviation h := (@prob_handler R _ link_side.(p2) _ N proto_c res).

Lemma h_send m :
  h (@inj _ _ client_side.(p1) _ (SEND m)) =
  get >>= fun s => put (fill_serverQ m s) >> Ret tt.
Proof.
rewrite prob_handler_store; first exact: injK_None.
rewrite /store_op; bind_ext=> s.
rewrite /= /effect.injT !injK_Some /=.
by case: (res s _).
Qed.

Lemma h_wait :
  h (@inj _ _ client_side.(p1) _ WAIT) =
  get >>= fun s => put (consume_clientQ s) >> Ret (clientQ s).
Proof.
have flip0 :
    @prj _ _ (@may_prov _ _ link_side.(p2)) _
      (@inj _ _ client_side.(p1) _ WAIT) = None.
  exact: injK_None.
rewrite prob_handler_store // /store_op; bind_ext=> s.
move: (res_compliant s flip0).
rewrite /= /gen_promise /effect.injT !injK_Some /=.
by case=> -[+ _] _; rewrite /gen_promise injK_Some /= => /eqP ->.
Qed.

Lemma h_reply m :
  h (@inj _ _ server_side.(p1) _ (RPLY m)) =
  get >>= fun s => put (fill_clientQ m s) >> Ret tt.
Proof.
rewrite prob_handler_store; first exact: injK_None.
rewrite /store_op; bind_ext=> s.
rewrite /= /effect.injT !injK_Some /= (@injK_None _ _ _ _ _ Happ.(d2)).
by case: (res s _).
Qed.

Lemma h_recv :
  h (@inj _ _ server_side.(p1) _ RECV) =
  get >>= fun s => put (consume_serverQ s) >> Ret (serverQ s).
Proof.
have flip0 :
    @prj _ _ (@may_prov _ _ link_side.(p2)) _
      (@inj _ _ server_side.(p1) _ RECV) = None.
  exact: injK_None.
rewrite prob_handler_store // /store_op; bind_ext=> s.
move: (res_compliant s flip0).
rewrite /= /gen_promise /effect.injT !injK_Some /=.
case=> -[_ +] _; rewrite /gen_promise injK_Some /= => /eqP ->.
by rewrite (@injK_None _ _ _ _ _ Happ.(d2)).
Qed.

Lemma h_drop q :
  h (@inj _ _ link_side.(p1) _ (DROP q)) =
  get >>= fun s => put (drop_queue q s) >> Ret tt.
Proof.
rewrite prob_handler_store; first exact: injK_None.
rewrite /store_op; bind_ext=> s.
rewrite /= /effect.injT (@injK_None _ _ _ _ _ Hproto.(d2)) !injK_Some /=.
by case: (res s _).
Qed.

Lemma h_flip q : h (@inj _ _ link_side.(p2) _ (flipe q)) = bcoin q.
Proof. exact: prob_handler_flip. Qed.

Context (M : inductiveFreerMonad ProtoF) (p : {prob R}).

Lemma put_transmit s q :
  put s >> denote _ h _ (@transmit _ link_side M p q) =
  put (drop_queue q s) <| p |> put s.
Proof.
rewrite /transmit denote_bind /flip /ptrigger denote_trigger h_flip /bcoin.
rewrite choice_bindDl !bindretf !compE /when /= denote_ret choice_bindDr.
rewrite !bindmskip /drop_packet /ptrigger denote_trigger h_drop.
by rewrite -bindA putgetput bindmskip putput.
Qed.

Lemma lossy_client_prob_correct :
  forall T (cmd : CLIENT T),
    denote _ h _ (@lossy_client _ _ Hlink client_side M p _ cmd) =
    spec_client p cmd.
Proof.
move=> _ [] /=.
  rewrite denote_bind /send /ptrigger denote_trigger h_send bindA.
  bind_ext=> s; rewrite bindA bindretf compE.
  exact: put_transmit.
rewrite /answer /answer_of denote_bind /wait /ptrigger denote_trigger h_wait.
rewrite bindA.
bind_ext=> s; rewrite bindA bindretf compE.
by case: (clientQ s)=> [[]|]; rewrite denote_ret.
Qed.

Lemma lossy_server_prob_correct :
  forall T (cmd : SERVER T),
    denote _ h _ (@lossy_server _ _ Hlink server_side M p _ cmd) =
    spec_server p cmd.
Proof.
move=> _ [] /=; rewrite /lossy_serve /serve_of denote_bind /recv /ptrigger.
rewrite denote_trigger h_recv bindA; bind_ext=> s; rewrite bindA bindretf.
rewrite compE; case: (serverQ s)=> [[]|] /=; [| by rewrite denote_ret ..].
rewrite !denote_bind /reply /ptrigger denote_trigger h_reply !bindA.
rewrite -bindA putgetput !bindA bindretf compE.
rewrite -bindA putput -bindA put_transmit.
by congr (_ >>= _); apply: funext; case; rewrite compE denote_ret.
Qed.

Local Abbreviation lossy_ping := (@lossy_ping _ _ _ Hlink Happ Hproto M p).

Lemma lossy_round_denote :
  denote _ h _
    (round_with (@lossy_client _ _ Hlink client_side M p)
      (@lossy_server _ _ Hlink server_side M p)) =
  round_of (spec_client p ASK) (fun=> spec_server p SERVE)
    (fun=> spec_client p ANSWER).
Proof.
rewrite /round_with /round_of 2!denote_bind lossy_client_prob_correct.
congr (_ >>= _).
- by congr (_ >>= _); apply: funext; case; exact: lossy_server_prob_correct.
- apply: funext; case; [case|]; rewrite compE.
  + exact: lossy_client_prob_correct.
  + by rewrite denote_ret.
Qed.

Remark consume_serverQ_twice s : consume_serverQ (consume_serverQ s) = consume_serverQ s.
Proof. done. Qed.
Remark consume_clientQ_twice s : consume_clientQ (consume_clientQ s) = consume_clientQ s.
Proof. done. Qed.
Remark consume_fill_serverQ m s : consume_serverQ (fill_serverQ m s) =  {| serverQ := None; clientQ := clientQ s |}.
Proof. done. Qed.
Remark consume_fill_clientQ m s : consume_clientQ (fill_clientQ m s) =  {| serverQ := serverQ s; clientQ := None |}.
Proof. done. Qed.
Remark consume_fill_serverQ_empty m : consume_serverQ (fill_serverQ m empty_net) = empty_net.
Proof. done. Qed.
Remark consume_fill_clientQ_empty m : consume_clientQ (fill_clientQ m empty_net) =  empty_net.
Proof. done. Qed.

Lemma lossy_ping_distribution :
  put empty_net >> denote _ h _ (lossy_ping one_round) =
  put empty_net >> exchange_once (M := N) (choose := choice) p%:num.~%:i01.
Proof.
rewrite lossy_round_denote /round_of /exchange_once /exchange !bindA.
rewrite -bindA putgetput /= choiceC !choice_bindDl !choice_bindDr.
rewrite -!bindA putput putgetput /= putput.
rewrite !bindA !bindretf !choice_bindDl !choice_bindDr.
do 2 rewrite -!bindA putput putgetput /= !putput 1?putgetput /=.
rewrite !bindA !bindretf -bindA putput.
by congr (_ <| _ |> _); exact: choiceC.
Qed.

Lemma lossy_pings_exchanges fuel :
  put empty_net >> denote _ h _ (lossy_ping (retry_round fuel)) =
  put empty_net >> exchanges (M := N) (choose := choice) p%:num.~%:i01 fuel.
Proof.
have := lossy_ping_distribution; rewrite lossy_round_denote.
rewrite denote_retry lossy_round_denote; set round := round_of _ _ _.
elim: fuel=> [|fuel IH] /= one; first exact: one.
rewrite -bindA one bindA /exchange_once /exchange !choice_bindDl !bindretf /=.
by rewrite !choice_bindDr IH.
Qed.

Lemma denote_lossy_ping :
  put empty_net >> denote _ h _ (lossy_ping one_round) =
  put empty_net >>
    ping_pong (transmit := prob_monad_ping.transmit) p%:num.~%:i01.
Proof.
by rewrite lossy_ping_distribution prob_monad_ping.ping_pong_distribution.
Qed.

Lemma denote_lossy_pings fuel :
  put empty_net >> denote _ h _ (lossy_ping (retry_round fuel)) =
  put empty_net >>
    ping_pongs (transmit := prob_monad_ping.transmit) p%:num.~%:i01 fuel.
Proof.
by rewrite lossy_pings_exchanges prob_monad_ping.ping_pongs_exchanges.
Qed.

(** Without loss, the exchange always succeeds. *)
Lemma lossy_ping0 :
  p = 0%:i01 ->
  put empty_net >> denote _ h _ (lossy_ping one_round) =
  put empty_net >> Ret GotPong.
Proof.
move=> p0; have onem_p1 : p%:num.~%:i01 = 1%:i01.
  by apply: val_inj; rewrite /= p0 onem0.
by rewrite denote_lossy_ping onem_p1 prob_monad_ping.ping_pong1.
Qed.

Lemma lossy_pings0 fuel :
  p = 0%:i01 ->
  put empty_net >> denote _ h _ (lossy_ping (retry_round fuel)) =
  put empty_net >> Ret GotPong.
Proof.
move=> p0; have onem_p1 : p%:num.~%:i01 = 1%:i01.
  by apply: val_inj; rewrite /= p0 onem0.
by rewrite denote_lossy_pings onem_p1 prob_monad_ping.ping_pongs1.
Qed.

Lemma lossy_ping_success_probability :
  put empty_net >> success_of (denote _ h _ (lossy_ping one_round)) =
  put empty_net >> bcoin (p_exchange_once p%:num.~%:i01).
Proof.
rewrite success_ofE -bindA denote_lossy_ping bindA -success_ofE.
by rewrite -ping_pong_successE prob_monad_ping.ping_pong_success_probability.
Qed.

Lemma lossy_ping_retry_success_probability fuel :
  put empty_net >> success_of (denote _ h _ (lossy_ping (retry_round fuel))) =
  put empty_net >> bcoin (p_exchanges p%:num.~%:i01 fuel).
Proof.
rewrite success_ofE -bindA denote_lossy_pings bindA -success_ofE.
rewrite -ping_pongs_successE.
by rewrite prob_monad_ping.ping_pong_retry_success_probability.
Qed.

Theorem lossy_ping_hoare_and_prob :
  correct_component lossy_ping (no_contract ping_round) proto_c
    (fun=> chan_inv) /\
  prob_correct_component (HF := link_side.(p2)) (N := N) lossy_ping proto_c res
    empty_net (ref_ping_pong p).
Proof.
split; first exact: lossy_ping_correct.
by move=> _ [|fuel]; [exact: denote_lossy_ping | exact: denote_lossy_pings].
Qed.

End shared_link.
End SharedLink.
