From monae Require Import preamble hierarchy.
From mathcomp Require Import boot boolp classical_sets.
From FreerDPS Require Import all_freerdps ping_common.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope contract_scope.
Local Open Scope classical_set_scope.
Close Scope nat_scope.
(** * Specifying the Ping-Pong Protocol *)

Module Export PingPongM.
(** ** Client *)

Inductive client_api : effect :=
| SEND : msg -> client_api unit
| WAIT : client_api (option msg).

Section client_program.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.
Definition send : M unit := ptrigger $ SEND Ping.
Definition wait : M (option msg) := ptrigger WAIT.
Definition C : M (option msg) :=
  send >>= fun=> wait.
End client_program.

(** ** Server *)

Inductive server_api : effect :=
| RPLY : msg -> server_api unit
| RECV : server_api (option msg).

Section server_program.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.
Definition reply : M unit := ptrigger $ RPLY Pong.
Definition recv : M (option msg) := ptrigger RECV.
Definition S_p : M (option unit) := serve_of (fun=> recv) reply tt.
End server_program.
End PingPongM.

Module Export PingSyntax.
Section syntax.
Context {ProtoF : effect} {Hc: client_api -< ProtoF} {Hs: server_api -< ProtoF}.
Context {M : freerMonad ProtoF}.

Lemma syn_send : providesOnlyF (H:=Hc) (M := M) send.
Proof. by exists (frTrigger (SEND Ping)). Qed.

Lemma syn_wait : providesOnlyF (H:=Hc) (M := M) wait.
Proof. by exists (frTrigger (inj $ WAIT)). Qed.

Lemma syn_c : providesOnlyF (F:=client_api) (M := M) C.
Proof.
by exists (frBind (frTrigger (SEND Ping)) (fun=> frTrigger WAIT)).
Qed.

Lemma syn_reply : providesOnlyF (F:=server_api) (M := M) reply.
Proof. by exists (frTrigger (RPLY Pong)). Qed.

Lemma syn_recv : providesOnlyF (F:=server_api) (M := M) recv.
Proof. by exists (frTrigger RECV). Qed.

Lemma syn_s_p : providesOnlyF (F:=server_api) (M := M) S_p.
Proof.
exists
  (frBind (frTrigger RECV)
    (fun incoming =>
      if incoming is Some Ping then
        frBind (frTrigger (RPLY Pong)) (fun c => frRet (Some c))
      else frRet None)).
rewrite /= /S_p /serve_of.
congr (recv >>= _).
by apply: boolp.funext=> -[[] |].
Qed.
End syntax.

#[export] Hint Extern 0 (providesOnlyF send) =>
  solve [exact: syn_send] : core.
#[export] Hint Extern 0 (providesOnlyF wait) =>
  solve [exact: syn_wait] : core.
#[export] Hint Extern 0 (providesOnlyF C) =>
  solve [exact: syn_c] : core.
#[export] Hint Extern 0 (providesOnlyF reply) =>
  solve [exact: syn_reply] : core.
#[export] Hint Extern 0 (providesOnlyF recv) =>
  solve [exact: syn_recv] : core.
#[export] Hint Extern 0 (providesOnlyF S_p) =>
  solve [exact: syn_s_p] : core.

End PingSyntax.

Module NetworkChannelMod.
Definition packet := option msg.

HB.instance Definition _ := gen_eqMixin packet.
HB.instance Definition _ := gen_choiceMixin packet.

Record net_state := mk_chan {
  serverQ : packet;
  clientQ : packet;
}.

HB.instance Definition _ := gen_eqMixin net_state.
HB.instance Definition _ := gen_choiceMixin net_state.

Implicit Type p : packet.
Implicit Type ns : net_state.
Implicit Type m : msg.

Definition fill_serverQ m ns := {| serverQ := Some m; clientQ := clientQ ns |}.
Definition fill_clientQ m ns := {| serverQ := serverQ ns; clientQ := Some m |}.
Definition consume_clientQ ns := {| serverQ := serverQ ns; clientQ := None |}.
Definition consume_serverQ ns := {| serverQ := None; clientQ := clientQ ns |}.

Fact serverQ_fill_serverQ m ns : serverQ (fill_serverQ m ns) = Some m.
Proof. done. Qed.

Fact clientQ_fill_serverQ m ns : clientQ (fill_serverQ m ns) = clientQ ns.
Proof. done. Qed.

Fact clientQ_fill_clientQ m ns : clientQ (fill_clientQ m ns) = Some m.
Proof. done. Qed.

Fact serverQ_fill_clientQ m ns : serverQ (fill_clientQ m ns) = serverQ ns.
Proof. done. Qed.

Fact clientQ_consume_clientQ ns : clientQ (consume_clientQ ns) = None.
Proof. done. Qed.

Fact serverQ_consume_clientQ ns : serverQ (consume_clientQ ns) = serverQ ns.
Proof. done. Qed.

Fact serverQ_consume_serverQ ns : serverQ (consume_serverQ ns) = None.
Proof. done. Qed.

Fact clientQ_consume_serverQ ns : clientQ (consume_serverQ ns) = clientQ ns.
Proof. done. Qed.

Opaque fill_serverQ fill_clientQ consume_clientQ consume_serverQ.

Definition chan_inv ns := serverQ ns != Some Pong /\ clientQ ns != Some Ping.

Lemma chan_inv_empty : chan_inv {| serverQ := None; clientQ := None |}.
Proof. by split; apply/eqP. Qed.

End NetworkChannelMod.

Import NetworkChannelMod.
Local Open Scope nat_scope.

(** ** Client Specification *)
Module ccm.

Definition c_step ns : forall X, client_api X -> X -> net_state
  := fun X cmd result => match cmd with
| SEND p => fill_serverQ p ns
| WAIT => consume_clientQ ns
end.

Definition client_req ns : forall X, client_api X -> bool
  := fun X cmd => match cmd with
| SEND m => m == Ping
| WAIT => clientQ ns != Some Ping
end.

Definition client_promise (ns : net_state) : forall X, client_api X -> X -> bool
  := fun X cmd => match cmd with
| SEND _ => fun _ => true
| WAIT => fun result => result == clientQ ns
end.

Definition client_c : contract client_api net_state :=
  make_contract c_step client_req client_promise.

Section client_respectful_and_run_lemmas.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.

Lemma send_respect :
  pre (client_c |~ (send : M _)) = [set: _].
Proof. by rewrite -subTset=>? _; exact/pre_to_hoare_triggerP/eqxx. Qed.

Lemma send_run (s s' : net_state) (u:unit)
  (run : post (client_c |~ (send : M _)) s u s') :
clientQ s' = clientQ s /\ serverQ s' = serverQ (fill_serverQ Ping s).
Proof. by move: run=> /post_to_hoare_triggerP=> -[] ->. Qed.

Lemma wait_respect :
  pre (client_c |~ (wait : M _)) = [set n | clientQ n != Some Ping].
Proof. by apply/seteqP; split=>ns; rewrite pre_to_hoare_triggerP. Qed.

Lemma wait_run (s s' : net_state) p
  (run : post (client_c |~ (wait : M _)) s p s') :
clientQ s' = None /\ serverQ s' = serverQ s.
Proof. by move: run=> /post_to_hoare_triggerP=> -[] ->. Qed.

Lemma c_respect :
pre (client_c |~ (C : M _)) = [set n | clientQ n != Some Ping].
Proof.
apply/seteqP; rewrite freer_to_hoare_bindE; split=>[ ns [] | ns /= Hy].
- rewrite send_respect wait_respect=> /= ? /(_ tt (fill_serverQ Ping ns)) -> //.
  exact/post_to_hoare_triggerP.
- split; first by rewrite send_respect.
  move=> [] s=> /send_run=> -[Hc _].
  by rewrite wait_respect /= Hc.
Qed.

Lemma c_run (s s' : net_state) (p : option msg)
  (run : post (client_c |~ (C : M _)) s p s') :
clientQ s' = None /\ serverQ s' = serverQ (fill_serverQ Ping s).
Proof.
move: run; rewrite freer_to_hoare_bindE.
case=> [[]] [[sQ cQ]] [] /send_run; case=>/= -> ->.
by move/wait_run.
Qed.

End client_respectful_and_run_lemmas.

End ccm.

(** ** Server Specification *)

Module scm.

Definition server_step ns : forall X, server_api X -> X -> net_state
  := fun X cmd result => match cmd with
| RPLY p => fill_clientQ p ns
| RECV => consume_serverQ ns
end.

Definition server_req ns : forall X, server_api X -> bool
  := fun X cmd => match cmd with
| RPLY m => m == Pong
| RECV => serverQ ns != Some Pong
end.

Definition server_promise (ns : net_state) : forall X, server_api X -> X -> bool
  := fun X cmd => match cmd with
| RECV => fun result => result == serverQ ns
| RPLY m => fun _ => true
end.

Definition server_c : contract server_api net_state :=
  make_contract server_step server_req server_promise.

Section server_respectful_and_run_lemmas.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.

Lemma reply_respect :
  pre (server_c |~ (reply : M _)) = [set: _].
Proof. by rewrite -subTset=>??; exact/pre_to_hoare_triggerP/eqxx. Qed.

Lemma reply_run (s s' : net_state) u
  (run : post (server_c |~ (reply : M _)) s u s') :
clientQ s' = clientQ (fill_clientQ Pong s) /\ serverQ s' = serverQ s.
Proof. by move: run; rewrite post_to_hoare_triggerP /= => -[->]. Qed.

Lemma recv_respect :
  pre (server_c |~ (recv : M _)) = [set ns | serverQ ns != Some Pong].
Proof. by apply/seteqP; split=> ?; rewrite pre_to_hoare_triggerP. Qed.

Lemma recv_run (s s' : net_state) (p : option msg)
  (run : post (server_c |~ (recv : M _)) s p s') :
clientQ s' = clientQ s /\ serverQ s' = None.
Proof. by move: run=> /post_to_hoare_triggerP=> -[] ->. Qed.

Lemma s_p_respect :
  pre (server_c |~ (S_p : M _)) = [set n | serverQ n != Some Pong].
Proof.
apply/seteqP; rewrite /S_p /serve_of freer_to_hoare_bindE; split=> s /=;
  first by case; rewrite recv_respect.
split; first by rewrite recv_respect.
move=> [[]|] [sQ cQ] /recv_run /=; case=> -> ->.
- rewrite freer_to_hoare_bindE; split=> *.
all: by rewrite ?reply_respect // pre_ret.
Qed.

Lemma s_p_run (s s' : net_state) (p : option unit)
  (run : post (server_c |~ (S_p : M _)) s p s') :
(if p is Some _
then clientQ s' = Some Pong
else clientQ s' = clientQ s)
  /\ serverQ s' = None.
Proof.
move: run; rewrite freer_to_hoare_bindE;
  case=>[[[]|]] [[s1 c1]] [] /recv_run /= [] -> ->.
- rewrite freer_to_hoare_bindE; case=>[[]] [[s2 c2]] [] /reply_run /= [] -> ->.
all: by rewrite post_ret; case=> <- <-.
Qed.

End server_respectful_and_run_lemmas.
End scm.

Import ccm scm.

(** * Protocol Description :
       +---+  == send Ping ==>  +-----------+  == delvr Ping ==>  +---+
       | C |                    | net_state |                     | S |
       +---+  <== get Pong ==   +-----------+  <== reply Pong ==  +---+
*)
Section retry.
Context {Fx Fout : effect} `{Fout -<? Fx} {M : freerMonad Fx}.
Context (c : contract Fout net_state) (run : M outcome).

Lemma pre_retry_ping_pong fuel :
  pre (c |~ run) = [set: _] ->
  pre (c |~ retry_until success_event run fuel) = [set: _].
Proof.
rewrite -!subTset=> Hpre; elim: fuel=> [|fuel IH] *; first exact: Hpre.
rewrite freer_to_hoare_bindE; split=> [|result s _]; first exact: Hpre.
by case: result; [by rewrite pre_ret | have ? := Hpre s; exact: IH ..].
Qed.

End retry.

Module ProtocolM.
Section proto_s.

Inductive ping_round : effect :=
| one_round : ping_round outcome
| retry_round : nat -> ping_round outcome.

Context {ProtoF : effect}.
Context `{client_api ;; server_api -<< ProtoF}.
Context {M : freerMonad ProtoF}.

(** One round, built from the non-probabilistic skeleton. *)
Definition ping_pong : M outcome :=
  round_of send (fun=> S_p) (answer_of (fun=> wait)).

Definition ping_pongs (fuel : nat) : M outcome :=
  retry_until success_event ping_pong fuel.

Definition ping_protocol : component (M:=M) ping_round ProtoF :=
  fun _ cmd => match cmd with
    | one_round => ping_pong
    | retry_round fuel => ping_pongs fuel
    end.

Definition ping_contract : contract ProtoF net_state := client_c -^- server_c.

Lemma pre_ping_pong : pre (ping_contract |~ ping_pong) = [set: _].
Proof.
rewrite /ping_pong /round_of /answer_of bindA -subTset=>??.
rewrite freer_to_hoare_bindE freer_contract_left //=; split;
  first by rewrite send_respect.
case=> [] [s1 c1] /send_run /= [-> ->].
rewrite freer_to_hoare_bindE freer_contract_right //; split;
  first by rewrite s_p_respect; exact/eqP.
move=> [[]|] [s2 c2] /s_p_run /= [-> ->]; last by rewrite pre_ret.
+ rewrite freer_to_hoare_bindE freer_contract_left //=; split;
    first by rewrite wait_respect; exact/eqP.
  by move=> [[]|] [s3 c3] /wait_run /= [-> ->]; rewrite pre_ret.
Qed.

Lemma pre_ping_any_cmd T (cmd : ping_round T) :
  pre (ping_contract |~ ping_protocol cmd) = [set: _].
Proof.
by case: cmd=> [|?];
  last apply: pre_retry_ping_pong;
  exact: pre_ping_pong.
Qed.

Lemma ping_handler_preserves_inv X (cmd : ProtoF X) :
  preserves_invariant chan_inv (hoare_of_contract ping_contract cmd).
Proof.
move=> s r s' /=.
do 2 rewrite /gen_requirement /gen_state_update /gen_promise /=.
case: (prj (F:=client_api) cmd)=> [c_cmd|].
- move=> [+ _] [-> _] [sQ_ok cQ_ok]; clear cmd.
  by case: c_cmd r=> [m|] r /= => [/eqP ->|]; split=>//; exact/eqP.
case: (prj (F:=server_api) cmd)=> [s_cmd| _]/=; last by case=> ->.
move=> [_ +] [-> _] [sQ_ok cQ_ok]; clear cmd.
by case: s_cmd r=> [m|] r /= => [/eqP ->|]; split=> //; exact/eqP.
Qed.


Definition ping_inv ns := ns = {| serverQ := None; clientQ := None|}.

Lemma post_ping_pong n r n' :
  ping_inv n -> post (ping_contract |~ ping_pong) n r n' -> ping_inv n'.
Proof.
move=> ->; rewrite /ping_pong /round_of  bindA.
rewrite freer_to_hoare_bindE freer_contract_left //.
case=> -[] [[s1 c1]] [] /send_run /= [-> ->].
rewrite freer_to_hoare_bindE freer_contract_right //.
case=> [[[]|]] [[s2 c2]] [] /s_p_run /= [-> ->];
  last by rewrite post_ret=> -[_ <-].
rewrite freer_to_hoare_bindE freer_contract_left //.
case=> o [[s3 c3]] [] /wait_run /= [-> ->].
by case: o=> [[]|]; rewrite post_ret=> -[_ <-].
Qed.

Lemma post_ping_pongs n r n' fuel :
  ping_inv n -> post (ping_contract |~ ping_pongs fuel) n r n' -> ping_inv n'.
Proof.
elim: fuel n=> [|fuel IH] n n_inv; first exact: post_ping_pong.
rewrite freer_to_hoare_bindE.
case=> r1 [s1] [].
move=>/(post_ping_pong n_inv) -> /=.
by case: (success_event r1); [rewrite post_ret=> -[_ <-] | exact: IH].
Qed.

Lemma post_ping_proto T n r n' (cmd : ping_round T) :
  ping_inv n -> post (ping_contract |~ ping_protocol cmd) n r n' -> ping_inv n'.
Proof.
case: cmd r=>[| fuel] r.
- exact: post_ping_pong.
- exact: post_ping_pongs.
Qed.
End proto_s.

Section proto_inv.
Context {ProtoF : effect}.
Context `{client_api ;; server_api -<< ProtoF}.
Context {M : inductiveFreerMonad ProtoF}.

Lemma ping_run_preserves_inv A (p : M A) :
  preserves_invariant chan_inv (ping_contract |~ p).
Proof.
by apply: to_hoare_preserves_invariant=> *; exact: ping_handler_preserves_inv.
Qed.

Theorem ping_correct :
  correct_component (ping_protocol (M := M)) (no_contract ping_round)
    ping_contract (fun _ ns => chan_inv ns /\ ping_inv ns).
Proof.
move=> [] n [cinv pinv] X cmd []; split=> [| x n' run].
  by rewrite pre_ping_any_cmd.
split=> //; split.
- by move: run cinv; apply: ping_run_preserves_inv; rewrite pre_ping_any_cmd.
- exact/post_ping_proto/run/pinv.
Qed.

End proto_inv.
End ProtocolM.

(** * Probability of Success *)

(**
A ns transmission succeeds with probability [1 - p]. Packet losses are
independent. For one round trip:

<<
P(Pong received) = P(Ping delivered) * P(Pong delivered)
                 = (1 - p) * (1 - p)
                 = (1 - p)^2.
>>

For at most [n] attempts, with [q = (1 - p)^2]:

<<
P(n) = 1 - (1 - q)^n.
>>
*)
