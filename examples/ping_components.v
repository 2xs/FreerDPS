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

(******************************************************************************)
(* Interfaces :                                                               *)
(*   client_api / server_api := describe what a socket does                   *)
(*   CLIENT := interface of the client component.                             *)
(*   SERVER := interface of the server component.                             *)
(* Components :                                                               *)
(*   client := client component, CLIENT on top of client_api                  *)
(*   server := server component, SERVER on top of server_api                  *)
(*   ping_with cl sv := the protocol built from a client and a server.        *)
(*                      builds from the generic provided in ping_common.v.    *)
(******************************************************************************)


Module Export PingPongM.
Inductive client_api : effect :=
| SEND : msg -> client_api unit
| WAIT : client_api (option msg).

Section client_program.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.
Definition send : M unit := ptrigger $ SEND Ping.
Definition wait : M (option msg) := ptrigger WAIT.
End client_program.

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

Fact syn_send : providesOnlyF (H:=Hc) (M := M) send.
Proof. by exists (frTrigger (SEND Ping)). Qed.
Fact syn_wait : providesOnlyF (H:=Hc) (M := M) wait.
Proof. by exists (frTrigger (inj $ WAIT)). Qed.
Fact syn_reply : providesOnlyF (F:=server_api) (M := M) reply.
Proof. by exists (frTrigger (RPLY Pong)). Qed.
Fact syn_recv : providesOnlyF (F:=server_api) (M := M) recv.
Proof. by exists (frTrigger RECV). Qed.
Fact syn_s_p : providesOnlyF (F:=server_api) (M := M) S_p.
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

Remark serverQ_fill_serverQ m ns : serverQ (fill_serverQ m ns) = Some m.
Proof. done. Qed.
Remark clientQ_fill_serverQ m ns : clientQ (fill_serverQ m ns) = clientQ ns.
Proof. done. Qed.
Remark clientQ_fill_clientQ m ns : clientQ (fill_clientQ m ns) = Some m.
Proof. done. Qed.
Remark serverQ_fill_clientQ m ns : serverQ (fill_clientQ m ns) = serverQ ns.
Proof. done. Qed.
Remark clientQ_consume_clientQ ns : clientQ (consume_clientQ ns) = None.
Proof. done. Qed.
Remark serverQ_consume_clientQ ns : serverQ (consume_clientQ ns) = serverQ ns.
Proof. done. Qed.
Remark serverQ_consume_serverQ ns : serverQ (consume_serverQ ns) = None.
Proof. done. Qed.
Remark clientQ_consume_serverQ ns : clientQ (consume_serverQ ns) = clientQ ns.
Proof. done. Qed.
Opaque fill_serverQ fill_clientQ consume_clientQ consume_serverQ.

Definition chan_inv ns := serverQ ns != Some Pong /\ clientQ ns != Some Ping.
Lemma chan_inv_empty : chan_inv {| serverQ := None; clientQ := None |}.
Proof. by split; apply/eqP. Qed.
End NetworkChannelMod.

Import NetworkChannelMod.
Local Open Scope nat_scope.

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

End client_respectful_and_run_lemmas.
End ccm.

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
move=> [[]|] [sQ cQ] /recv_run /=; case=> -> ->;
 first (rewrite freer_to_hoare_bindE; split=> [|*]).
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
  case=>[[[]|]] [[s1 c1]] [] /recv_run /= [] -> ->;
    first (rewrite freer_to_hoare_bindE;
      case=>[[]] [[s2 c2]] [] /reply_run /= [] -> ->).
all: by rewrite post_ret; case=> <- <-.
Qed.

End server_respectful_and_run_lemmas.
End scm.

Import ccm scm.

(** * Protocol Description :
      +---+  === (1) send Ping ==> +-----------+  === delvr Ping ==>  +---+
      | C |                        | net_state |                      | S | (2)
      +---+  <== (3) get Pong ===  +-----------+  <== reply Pong ===  +---+
*)

Inductive ping_round : effect :=
| one_round : ping_round outcome
| retry_round : nat -> ping_round outcome.

Definition ping_contract {ProtoF : effect}
    `{client_api ;; server_api -<< ProtoF} : contract ProtoF net_state :=
  client_c -^- server_c.

Inductive CLIENT : effect :=
| ASK : CLIENT unit
| ANSWER : CLIENT outcome.

Inductive SERVER : effect :=
| SERVE : SERVER (option unit).

Section c_s.
Context {Fx : effect} `{client_api -< Fx} {M : freerMonad Fx}.

Definition answer : M outcome := answer_of (fun=> wait) tt.

Definition client : component (M := M) CLIENT Fx :=
  fun _ cmd => match cmd with
  | ASK => send
  | ANSWER => answer
  end.

Lemma syn_client T (cmd : CLIENT T) :
  providesOnlyF (F := client_api) (client cmd).
Proof.
case: cmd; first exact: syn_send.
exists (frBind (frTrigger WAIT) (fun reply =>
  if reply is Some Pong then frRet GotPong else frRet LostPong)).
rewrite /= /answer /answer_of; congr (wait >>= _).
by apply: funext=> -[[]|].
Qed.

Lemma pre_client T (cmd : CLIENT T) ns :
  chan_inv ns -> pre (client_c |~ client cmd) ns.
Proof.
case: cmd=> [_ /=|[_ cQ_ok] /=]; first by rewrite send_respect.
rewrite /answer /answer_of freer_to_hoare_bindE; split.
- by rewrite wait_respect.
- by case=>[[]|]; rewrite pre_ret.
Qed.

Lemma client_handler_preserves_inv X (cmd : Fx X) :
  preserves_invariant chan_inv (hoare_of_contract client_c cmd).
Proof.
move=> s r s' /=; rewrite /gen_requirement /gen_state_update /gen_promise.
case: (prj cmd)=> [c_cmd|]; last by move=> _ [->].
move=> + [-> _] [??]; clear cmd.
by case: c_cmd r => [m|] r=> [/eqP -> |]; split=>//; exact/eqP.
Qed.
End c_s.

Section c_inv_s.
Context {Fx : effect} `{client_api -< Fx} {M : inductiveFreerMonad Fx}.

Lemma client_run_preserves_inv A (p : M A) :
  preserves_invariant chan_inv (client_c |~ p).
Proof.
by apply: to_hoare_preserves_invariant=> *; exact: client_handler_preserves_inv.
Qed.

Theorem client_correct :
  correct_component (client (M := M)) (no_contract CLIENT) client_c
    (fun=> chan_inv).
Proof.
move=> ? ns inv ? cmd _; split; first exact: pre_client.
move=> t ns' run; split=> //.
by apply: (client_run_preserves_inv _ run inv); exact: pre_client.
Qed.

End c_inv_s.

#[local] Hint Extern 0 (providesOnlyF answer) =>
  solve [exact: (syn_client ANSWER)] : core.

Section s_s.
Context {Fx : effect} `{server_api -< Fx} {M : freerMonad Fx}.

Definition server : component (M := M) SERVER Fx :=
  fun _ cmd => match cmd with
  | SERVE => S_p
  end.

Lemma syn_server T (cmd : SERVER T) :
  providesOnlyF (F := server_api) (server cmd).
Proof. by case: cmd; exact: syn_s_p. Qed.

Lemma pre_server T (cmd : SERVER T) ns :
  chan_inv ns -> pre (server_c |~ server cmd) ns.
Proof. by case: cmd; case; rewrite s_p_respect. Qed.

Lemma server_handler_preserves_inv X (cmd : Fx X) :
  preserves_invariant chan_inv (hoare_of_contract server_c cmd).
Proof.
move=> s r s' /=; rewrite /gen_requirement /gen_state_update /gen_promise.
case: (prj cmd)=> [s_cmd|]; last by move=> _ [->].
move=> + [-> _] [??]; clear cmd.
by case: s_cmd r=> [m|] r /= => [/eqP ->|]; split=> //; exact/eqP.
Qed.
End s_s.

Section s_inv_s.
Context {Fx : effect} `{server_api -< Fx} {M : inductiveFreerMonad Fx}.

Lemma server_run_preserves_inv A (p : M A) :
  preserves_invariant chan_inv (server_c |~ p).
Proof.
by apply: to_hoare_preserves_invariant=> *; exact: server_handler_preserves_inv.
Qed.

Theorem server_correct :
  correct_component (server (M := M)) (no_contract SERVER) server_c
    (fun=> chan_inv).
Proof.
move=> ? ns inv ? cmd _; split; first exact: pre_server.
move=> t ns' run; split=> //.
by apply: (server_run_preserves_inv _ run inv); exact: pre_server.
Qed.
End s_inv_s.

Section proto_s.
Context {Fx Fout : effect} `{Fout -<? Fx} {M : freerMonad Fx}.

(* here we use `round_of` because we don't have `transmit`. *)
Definition round_with (cl : component (M := M) CLIENT Fx)
    (sv : component (M := M) SERVER Fx) : M outcome :=
  round_of (cl _ ASK) (fun=> sv _ SERVE) (fun=> cl _ ANSWER).

(* as this is a loop, we prove it over any program *)
Lemma retry_ping_pong_ok (c : contract Fout net_state) (run : M outcome) :
  (forall ns, chan_inv ns -> pre (c |~ run) ns
    /\ forall t ns', post (c |~ run) ns t ns' -> chan_inv ns') ->
  forall fuel ns, chan_inv ns ->
    pre (c |~ retry_until success_event run fuel) ns
    /\ forall t ns', post (c |~ retry_until success_event run fuel) ns t ns' ->
  chan_inv ns'.
Proof.
move=> run_ok; elim=> [|fuel IH] ns inv /=; first exact: run_ok.
have [run_pre run_post] := run_ok ns inv.
rewrite freer_to_hoare_bindE; split.
- split=> // result ns1 /run_post inv1.
  by case: result; [rewrite pre_ret | exact: (IH ns1 inv1).1 ..].
- move=> t ns' [result [ns1 [/run_post inv1]]].
  by case: result; [rewrite post_ret=> -[_ <-] | exact: (IH ns1 inv1).2 ..].
Qed.

Definition ping_with (cl : component (M := M) CLIENT Fx)
    (sv : component (M := M) SERVER Fx) :
  component (M := M) ping_round Fx :=
  fun _ cmd => match cmd with
  | one_round => round_with cl sv
  | retry_round fuel => retry_until success_event (round_with cl sv) fuel
  end.

(** One round keeps the channel invariant as soon as both components do. *)
Lemma round_with_ok (cl : component (M := M) CLIENT Fx)
    (sv : component (M := M) SERVER Fx) (c : contract Fout net_state) :
  correct_component cl (no_contract CLIENT) c (fun=> chan_inv) ->
  correct_component sv (no_contract SERVER) c (fun=> chan_inv) ->
  forall ns, chan_inv ns ->
    pre (c |~ round_with cl sv) ns /\
    forall t ns', post (c |~ round_with cl sv) ns t ns' -> chan_inv ns'.
Proof.
move=> cl_ok sv_ok ns inv; rewrite /round_with /round_of bindA; split.
- rewrite freer_to_hoare_bindE; split;
    first by exact: (correct_pre cl_ok).
  move=> _ ns1 /(correct_post (sin := tt) cl_ok inv I) [_ inv1].
  rewrite freer_to_hoare_bindE; split;
    first by exact: (correct_pre sv_ok).
  move=> served ns2 /(correct_post (sin := tt) sv_ok inv1 I) [_ inv2].
  case: served=> [[]|]; last by rewrite pre_ret.
  exact: (correct_pre cl_ok).
move=> result ns'; rewrite freer_to_hoare_bindE.
case=> _ [ns1] [/(correct_post (sin := tt) cl_ok inv I) [_ inv1]].
rewrite freer_to_hoare_bindE.
case=> served [ns2] [/(correct_post (sin := tt) sv_ok inv1 I) [_ inv2]].
case: served=> [[]|]; last by rewrite post_ret=> -[_ <-].
by case/(correct_post (sin := tt) cl_ok inv2 I).
Unshelve.
all: done.
Qed.

Theorem ping_with_correct (cl : component (M := M) CLIENT Fx)
    (sv : component (M := M) SERVER Fx) (c : contract Fout net_state) :
  correct_component cl (no_contract CLIENT) c (fun=> chan_inv) ->
  correct_component sv (no_contract SERVER) c (fun=> chan_inv) ->
  correct_component (ping_with cl sv) (no_contract ping_round) c
    (fun=> chan_inv).
Proof.
move=> cl_ok sv_ok ?? inv _ [|fuel] _ /=.
  have [round_pre round_post] := round_with_ok cl_ok sv_ok inv.
  by split=> // t ns' /round_post.
have [retry_pre retry_post] :=
  retry_ping_pong_ok (round_with_ok cl_ok sv_ok) fuel inv.
by split=> // t ns' /retry_post.
Qed.

End proto_s.

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
