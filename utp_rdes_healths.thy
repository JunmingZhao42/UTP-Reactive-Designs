section \<open> Reactive Designs Healthiness Conditions \<close>

theory utp_rdes_healths
  imports "UTP-Reactive.utp_reactive"
begin

subsection \<open> Preliminaries \<close>

named_theorems rdes and rdes_def and RD_elim

type_synonym ('s,'t) rdes = "('s,'t,unit) rsp_hrel"
  
translations
  (type) "('s,'t) rdes" <= (type) "('s, 't, unit) rsp_hrel"

(* FIXME: Nasty Hack. Can we automate this? *)

declare des_vars.splits [alpha_splits del]
declare rea_vars.splits [alpha_splits del]
declare rea_vars.splits [alpha_splits]
declare des_vars.splits [alpha_splits]

lemma R2_st_ex: "R2 (\<exists> st\<^sup>< \<Zspot> P) = (\<exists> st\<^sup>< \<Zspot> R2(P))"
  by (pred_auto)

lemma R2s_st'_eq_st:
  "R2s($st\<^sup>> = $st\<^sup><)\<^sub>e = ($st\<^sup>> = $st\<^sup><)\<^sub>e"
  by (pred_auto)

lemma R2c_st'_eq_st:
  "R2c($st\<^sup>> = $st\<^sup><)\<^sub>e = ($st\<^sup>> = $st\<^sup><)\<^sub>e"
  by (pred_auto)

lemma R1_des_lift_skip: "R1(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  by (pred_auto)

lemma R2_des_lift_skip:
  "R2(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  apply (pred_auto) using minus_zero_eq by blast

lemma R1_R2c_ex_st: "R1 (R2c (\<exists> st\<^sup>> \<Zspot> Q\<^sub>1)) = (\<exists> st\<^sup>> \<Zspot> R1 (R2c Q\<^sub>1))"
  by (pred_auto)

subsection \<open> Identities \<close>

text \<open> We define two identities fro reactive designs, which correspond to the regular and 
  state-sensitive versions of reactive designs, respectively. The former is the one used in
  the UTP book and related publications for CSP. \<close>

definition skip_rea :: "('t::trace, '\<alpha>) rp_hrel" ("II\<^sub>C") where
skip_rea_def [pred]: "II\<^sub>C = (II \<or> (\<not> $ok\<^sup>< \<and> $tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)"

definition skip_srea :: "('s, 't::trace, '\<alpha>) rsp_hrel" ("II\<^sub>R") where
skip_srea_def [pred]: "II\<^sub>R = ((\<exists> st\<^sup>< \<Zspot> II\<^sub>C) \<triangleleft> $wait\<^sup>< \<triangleright> II\<^sub>C)"

lemma skip_rea_R1_lemma: "II\<^sub>C = R1(ok\<^sup>< \<longrightarrow> II)"
  by (pred_auto)

lemma skip_rea_form: "II\<^sub>C = (II \<triangleleft> $ok\<^sup>< \<triangleright> R1(true))"
  by (pred_auto)

lemma skip_srea_form: "II\<^sub>R = ((\<exists> st\<^sup>< \<Zspot> II) \<triangleleft> $wait\<^sup>< \<triangleright> II) \<triangleleft> $ok\<^sup>< \<triangleright> R1(true)"
  by (pred_auto)

lemma R1_skip_rea: "R1(II\<^sub>C) = II\<^sub>C"
  by (pred_auto)

lemma R2c_skip_rea: "R2c II\<^sub>C = II\<^sub>C"
  by (pred_auto, metis add.right_neutral diff_add_cancel_left')

lemma R2_skip_rea: "R2(II\<^sub>C) = II\<^sub>C"
  by (metis R1_R2c_is_R2 R1_skip_rea R2c_skip_rea)

lemma R2c_skip_srea: "R2c(II\<^sub>R) = II\<^sub>R"
  apply (pred_auto) using minus_zero_eq by blast+

lemma skip_srea_R1 [closure]: "II\<^sub>R is R1"
  by (pred_auto)

lemma skip_srea_R2c [closure]: "II\<^sub>R is R2c"
  by (simp add: Healthy_def R2c_skip_srea)

lemma skip_srea_R2 [closure]: "II\<^sub>R is R2"
  by (metis Healthy_def' R1_R2c_is_R2 R2c_skip_srea skip_srea_R1)

subsection \<open> RD1: Divergence yields arbitrary traces \<close>

definition RD1 :: "('t::trace,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel" where
[pred]: "RD1(P) = (P \<or> (\<not> $ok\<^sup>< \<and> $tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)"

text \<open> $RD1$ is essentially $H1$ from the theory of designs, but viewed through the prism of
  reactive processes. \<close>

lemma RD1_idem: "RD1(RD1(P)) = RD1(P)"
  by (pred_auto)

lemma RD1_Idempotent: "Idempotent RD1"
  by (simp add: Idempotent_def RD1_idem)

lemma RD1_mono: "P \<sqsubseteq> Q \<Longrightarrow> RD1(P) \<sqsubseteq> RD1(Q)"
  by (pred_auto)

lemma RD1_Monotonic: "Monotonic RD1"
  using Monotonic_refine RD1_mono by blast

lemma RD1_Continuous: "Continuous RD1"
  by (pred_auto)

lemma R1_true_RD1_closed [closure]: "R1(true) is RD1"
  by (pred_auto)

lemma RD1_wait_false [closure]: "P is RD1 \<Longrightarrow> P\<lbrakk>False/wait\<^sup><\<rbrakk> is RD1"
  by (pred_auto)

lemma RD1_wait'_false [closure]: "P is RD1 \<Longrightarrow> P\<lbrakk>False/wait\<^sup>>\<rbrakk> is RD1"
  by (pred_auto)
    
lemma RD1_seq: "RD1(RD1(P) ;; RD1(Q)) = RD1(P) ;; RD1(Q)"
  by (pred_auto)

lemma RD1_seq_closure [closure]: "\<lbrakk> P is RD1; Q is RD1 \<rbrakk> \<Longrightarrow> P ;; Q is RD1"
  by (metis Healthy_def' RD1_seq)

lemma RD1_R1_commute: "RD1(R1(P)) = R1(RD1(P))"
  by (pred_auto)

lemma RD1_R2c_commute: "RD1(R2c(P)) = R2c(RD1(P))"
  by (pred_auto)

lemma RD1_via_R1: "R1(H1(P)) = RD1(R1(P))"
  by (pred_auto)

lemma RD1_R1_cases: "RD1(R1(P)) = (R1(P) \<triangleleft> $ok\<^sup>< \<triangleright> R1(true))"
  by (pred_auto)

lemma skip_rea_RD1_skip: "II\<^sub>C = RD1(II)"
  by (pred_auto)

lemma skip_srea_RD1 [closure]: "II\<^sub>R is RD1"
  by (pred_auto)

lemma RD1_algebraic_intro:
  assumes
    "P is R1" "(R1(true\<^sub>h) ;; P) = R1(true\<^sub>h)" "(II\<^sub>C ;; P) = P"
  shows "P is RD1"
proof -
  have "P = (II\<^sub>C ;; P)"
    by (simp add: assms(3))
  also have "... = (R1(ok\<^sup>< \<longrightarrow> II) ;; P)"
    by (simp add: skip_rea_R1_lemma)
  also have "... = (((\<not> ok\<^sup>< \<and> R1(true)) ;; P) \<or> P)"
    by (metis (no_types, opaque_lifting) R1_disj R1_extend_conj R1_skip impl_neg_disj pred_ba.inf.commute pred_ba.inf_top_left seqr_left_unit seqr_or_distl)
  also have "... = ((R1(\<not> ok\<^sup><) ;; (R1(true\<^sub>h) ;; P)) \<or> P)"
    using dual_order.trans by (pred_simp, blast)
  also have "... = ((R1(\<not> ok\<^sup><) ;; R1(true\<^sub>h)) \<or> P)"
    by (simp add: assms(2))
  also have "... = (R1(\<not> ok\<^sup><) \<or> P)"
    by (pred_auto)
  also have "... = RD1(P)"
    by (pred_auto)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

theorem RD1_left_zero:
  assumes "P is R1" "P is RD1"
  shows "(R1(true) ;; P) = R1(true)"
proof -
  have "(R1(true) ;; R1(RD1(P))) = R1(true)"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

theorem RD1_left_unit:
  assumes "P is R1" "P is RD1"
  shows "(II\<^sub>C ;; P) = P"
proof -
  have "(II\<^sub>C ;; R1(RD1(P))) = R1(RD1(P))"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

lemma RD1_alt_def:
  assumes "P is R1"
  shows "RD1(P) = (P \<triangleleft> $ok\<^sup>< \<triangleright> R1(true))"
proof -
  have "RD1(R1(P)) = (R1(P) \<triangleleft> $ok\<^sup>< \<triangleright> R1(true))"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

theorem RD1_algebraic:
  assumes "P is R1"
  shows "P is RD1 \<longleftrightarrow> (R1(true\<^sub>h) ;; P) = R1(true\<^sub>h) \<and> (II\<^sub>C ;; P) = P"
  using RD1_algebraic_intro RD1_left_unit RD1_left_zero assms by blast

subsection \<open> R3c and R3h: Reactive design versions of R3 \<close>

definition R3c :: "('t::trace, '\<alpha>) rp_hrel \<Rightarrow> ('t, '\<alpha>) rp_hrel" where
[pred]: "R3c(P) = (II\<^sub>C \<triangleleft> $wait\<^sup>< \<triangleright> P)"

definition R3h :: "('s, 't::trace, '\<alpha>) rsp_hrel \<Rightarrow> ('s, 't, '\<alpha>) rsp_hrel" where
 R3h_def [pred]: "R3h(P) = ((\<exists> st\<^sup>< \<Zspot> II\<^sub>C) \<triangleleft> $wait\<^sup>< \<triangleright> P)"

lemma R3c_idem: "R3c(R3c(P)) = R3c(P)"
  by (pred_auto)

lemma R3c_Idempotent: "Idempotent R3c"
  by (simp add: Idempotent_def R3c_idem)

lemma R3c_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3c(P) \<sqsubseteq> R3c(Q)"
  by (pred_auto)

lemma R3c_Monotonic: "Monotonic R3c"
  using Monotonic_refine R3c_mono by blast

lemma R3c_Continuous: "Continuous R3c"
  by (pred_auto)

lemma R3c_rcond_def: "R3c(P) = (II\<^sub>C \<lhd> $wait \<rhd> P)"
  by (simp add:R3c_def rcond_def aext_var)

lemma R3h_idem: "R3h(R3h(P)) = R3h(P)"
  by (pred_auto)

lemma R3h_Idempotent: "Idempotent R3h"
  by (simp add: Idempotent_def R3h_idem)

lemma R3h_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3h(P) \<sqsubseteq> R3h(Q)"
  by (pred_auto)

lemma R3h_Monotonic: "Monotonic R3h"
  using Monotonic_refine R3h_mono by blast

lemma R3h_Continuous: "Continuous R3h"
  by (pred_auto)

lemma R3h_inf: "R3h(P \<sqinter> Q) = R3h(P) \<sqinter> R3h(Q)"
  by (pred_auto)

lemma R3h_UINF:
  "A \<noteq> {} \<Longrightarrow> R3h(\<Sqinter> i \<in> A. P(i)) = (\<Sqinter> i \<in> A. R3h(P(i)))"
  by (pred_auto)

lemma R3h_cond: "R3h(P \<triangleleft> b \<triangleright> Q) = (R3h(P) \<triangleleft> b \<triangleright> R3h(Q))"
  by (pred_auto)

lemma R3c_via_RD1_R3: "RD1(R3(P)) = R3c(RD1(P))"
  by (pred_auto)

lemma R3c_RD1_def: "P is RD1 \<Longrightarrow> R3c(P) = RD1(R3(P))"
  by (simp add: Healthy_if R3c_via_RD1_R3)

lemma RD1_R3c_commute: "RD1(R3c(P)) = R3c(RD1(P))"
  by (pred_auto)

lemma R1_R3c_commute: "R1(R3c(P)) = R3c(R1(P))"
  by (pred_auto)

lemma R2c_R3c_commute: "R2c(R3c(P)) = R3c(R2c(P))"
  apply (pred_auto) using minus_zero_eq by blast+

lemma R1_R3h_commute: "R1(R3h(P)) = R3h(R1(P))"
  by (pred_auto)

lemma R2c_R3h_commute: "R2c(R3h(P)) = R3h(R2c(P))"
  apply (pred_auto) using minus_zero_eq by blast+

lemma RD1_R3h_commute: "RD1(R3h(P)) = R3h(RD1(P))"
  by (pred_auto)

lemma R3c_cancels_R3: "R3c(R3(P)) = R3c(P)"
  by (pred_auto)

lemma R3_cancels_R3c: "R3(R3c(P)) = R3(P)"
  by (pred_auto)

lemma R3h_cancels_R3c: "R3h(R3c(P)) = R3h(P)"
  by (pred_auto)

lemma in_unrest_get_post [unrest]: "in\<alpha> \<sharp> get\<^bsub>ns_alpha snd\<^sub>L x\<^esub>"
  by (expr_simp)

lemma out_unrest_get_pre [unrest]: "out\<alpha> \<sharp> get\<^bsub>ns_alpha fst\<^sub>L x\<^esub>"
  by (expr_simp)

lemma R3c_semir_form:
  "(R3c(P) ;; R3c(R1(Q))) = R3c(P ;; R3c(R1(Q)))"
  by (simp add: R3c_def rcond_seq_left_distr unrest, pred_auto)

lemma R3h_semir_form:
  "(R3h(P) ;; R3h(R1(Q))) = R3h(P ;; R3h(R1(Q)))"
  by (simp add: R3h_def rcond_seq_left_distr unrest)
     (pred_simp, blast intro:order_trans)

lemma R3c_seq_closure:
  assumes "P is R3c" "Q is R3c" "Q is R1"
  shows "(P ;; Q) is R3c"
  by (metis Healthy_def' R3c_semir_form assms)

lemma R3h_seq_closure [closure]:
  assumes "P is R3h" "Q is R3h" "Q is R1"
  shows "(P ;; Q) is R3h"
  by (metis Healthy_def' R3h_semir_form assms)

lemma R3c_R3_left_seq_closure:
  assumes "P is R3" "Q is R3c"
  shows "(P ;; Q) is R3c"
proof -
  have "(P ;; Q) = ((P ;; Q)\<lbrakk>True/wait\<^sup><\<rbrakk> \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by (simp add: expr_if_bool_var_left)
  also have "... = (((II \<triangleleft> $wait\<^sup>< \<triangleright> P) ;; Q)\<lbrakk>True/wait\<^sup><\<rbrakk> \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by (metis Healthy_if R3_def SEXP_def aext_var assms(1))
  also have "... = ((II\<lbrakk>True/wait\<^sup><\<rbrakk> ;; Q) \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by (subst_eval)
  also have "... = (((II \<and> wait\<^sup><) ;; Q) \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by pred_auto
  also have "... = ((II\<lbrakk>True/wait\<^sup><\<rbrakk> ;; Q\<lbrakk>True/wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by pred_auto
  also have "... = ((II\<lbrakk>True/wait\<^sup><\<rbrakk> ;; (II\<^sub>C \<triangleleft> $wait\<^sup>< \<triangleright> Q)\<lbrakk>True/wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by (metis Healthy_def' R3c_def assms(2))
  also have "... = ((II\<lbrakk>True/wait\<^sup><\<rbrakk> ;; II\<^sub>C\<lbrakk>True/wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by (subst_eval)
  also have "... = (((II \<and> wait\<^sup><) ;; II\<^sub>C) \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by pred_auto
  also have "... = ((II ;; II\<^sub>C) \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by pred_auto
  also have "... = (II\<^sub>C \<triangleleft> $wait\<^sup>< \<triangleright> (P ;; Q))"
    by simp
  also have "... = R3c(P ;; Q)"
    by (simp add: R3c_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma R3c_cases: "R3c(P) = ((II \<triangleleft> $ok\<^sup>< \<triangleright> R1(true)) \<triangleleft> $wait\<^sup>< \<triangleright> P)"
  by (pred_auto, (metis (full_types))+)

lemma R3h_cases: "R3h(P) = (((\<exists> st\<^sup>< \<Zspot> II) \<triangleleft> $ok\<^sup>< \<triangleright> R1(true)) \<triangleleft> $wait\<^sup>< \<triangleright> P)"
  by (pred_auto, (metis (full_types))+)

lemma R3h_form: "R3h(P) = II\<^sub>R \<triangleleft> $wait\<^sup>< \<triangleright> P"
  by (pred_auto)

lemma R3c_subst_wait: "R3c(P) = R3c(P \<^sub>f)"
  by pred_auto

lemma R3h_subst_wait: "R3h(P) = R3h(P \<^sub>f)"
  by pred_auto

lemma skip_srea_R3h [closure]: "II\<^sub>R is R3h"
  by (pred_auto)

lemma R3h_wait_true:
  assumes "P is R3h"
  shows "P \<^sub>t = II\<^sub>R \<^sub>t"
proof -
  have "P \<^sub>t = (II\<^sub>R \<triangleleft> $wait\<^sup>< \<triangleright> P) \<^sub>t"
    by (metis Healthy_if R3h_form assms)
  also have "... = II\<^sub>R \<^sub>t"
    by (simp add: usubst)
  finally show ?thesis .
qed

lemma R3c_refines_R3h: "R3h(P) \<sqsubseteq> R3c(P)"
  by (pred_auto)

subsection \<open> RD2: A reactive specification cannot require non-termination \<close>

definition RD2 where
[pred]: "RD2(P) = H2(P)"
  
text \<open> $RD2$ is just $H2$ since the type system will automatically have J identifying 
  the reactive variables as required. \<close>

lemma RD2_ok_up:
  assumes "M is RD2"
    and "merge_eval M x p q (\<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>)"
  shows "merge_eval M x p q (\<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>)"
proof -
  have "merge_eval M x p q \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr> =
    merge_eval (H2 M) x p q \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>"
    using assms(1) by (simp add: Healthy_def' RD2_def)
  also have "... = (merge_eval M x p q \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr> \<or>
      merge_eval M x p q \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>)"
    by (simp add: H2_merge_eval)
  finally show ?thesis using assms(2) by blast
qed

lemma RD2_idem: "RD2(RD2(P)) = RD2(P)"
  by (simp add: H2_idem RD2_def)

lemma RD2_Idempotent: "Idempotent RD2"
  by (simp add: Idempotent_def RD2_idem)

lemma RD2_mono: "P \<sqsubseteq> Q \<Longrightarrow> RD2(P) \<sqsubseteq> RD2(Q)"
  by (simp add: H2_def RD2_def seqr_mono)

lemma RD2_Monotonic: "Monotonic RD2"
  using Monotonic_refine RD2_mono by blast

lemma RD2_Continuous: "Continuous RD2"
  by (pred_auto)

lemma RD1_RD2_commute: "RD1(RD2(P)) = RD2(RD1(P))"
  by (pred_auto)

lemma RD2_R3c_commute: "RD2(R3c(P)) = R3c(RD2(P))"
  by (simp add: R3c_def RD2_def H2_def rcond_seq_left_distr unrest, pred_auto)

lemma RD2_R3h_commute: "RD2(R3h(P)) = R3h(RD2(P))"
  by (simp add: R3h_def RD2_def H2_def rcond_seq_left_distr unrest, pred_auto)

subsection \<open> Major healthiness conditions \<close>

definition RH :: "('t::trace,'\<alpha>) rp_hrel \<Rightarrow> ('t,'\<alpha>) rp_hrel" ("\<^bold>R")
where [pred]: "RH(P) = R1(R2c(R3c(P)))"

definition RHS :: "('s,'t::trace,'\<alpha>) rsp_hrel \<Rightarrow> ('s,'t,'\<alpha>) rsp_hrel" ("\<^bold>R\<^sub>s")
where [pred]: "RHS(P) = R1(R2c(R3h(P)))"

definition RD :: "('t::trace,'\<alpha>) rp_hrel \<Rightarrow> ('t,'\<alpha>) rp_hrel"
where [pred]: "RD(P) = RD1(RD2(RP(P)))"

definition SRD :: "('s,'t::trace,'\<alpha>) rsp_hrel \<Rightarrow> ('s,'t,'\<alpha>) rsp_hrel"
where [pred]: "SRD(P) = RD1(RD2(RHS(P)))"

lemma RH_comp: "RH = R1 \<circ> R2c \<circ> R3c"
  by (auto simp add: RH_def)

lemma RHS_comp: "RHS = R1 \<circ> R2c \<circ> R3h"
  by (auto simp add: RHS_def)

lemma RD_comp: "RD = RD1 \<circ> RD2 \<circ> RP"
  by (auto simp add: RD_def)

lemma SRD_comp: "SRD = RD1 \<circ> RD2 \<circ> RHS"
  by (auto simp add: SRD_def)

lemma RH_idem: "\<^bold>R(\<^bold>R(P)) = \<^bold>R(P)"
  by (simp add: R1_R2c_commute R1_R3c_commute R1_idem R2c_R3c_commute R2c_idem R3c_idem RH_def)

lemma RH_Idempotent: "Idempotent \<^bold>R"
  by (simp add: Idempotent_def RH_idem)

lemma RH_Monotonic: "Monotonic \<^bold>R"
  by (simp add: Monotonic_comp R1_Monotonic R2c_Monotonic R3c_Monotonic RH_comp)

lemma RH_mono: "P \<sqsubseteq> Q \<Longrightarrow> \<^bold>R(P) \<sqsubseteq> \<^bold>R(Q)"
  by (metis Monotonic_refine RH_Monotonic)

lemma RH_Continuous: "Continuous \<^bold>R"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3c_Continuous RH_comp)

lemma RHS_idem: "\<^bold>R\<^sub>s(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(P)"
  by (simp add: R1_R2c_is_R2 R1_R3h_commute R2_idem R2c_R3h_commute R3h_idem RHS_def)

lemma RHS_Idempotent [closure]: "Idempotent \<^bold>R\<^sub>s"
  by (simp add: Idempotent_def RHS_idem)

lemma RHS_Monotonic: "Monotonic \<^bold>R\<^sub>s"
  by (simp add: Monotonic_comp R1_Monotonic R2c_Monotonic R3h_Monotonic RHS_comp)

lemma RHS_mono: "P \<sqsubseteq> Q \<Longrightarrow> \<^bold>R\<^sub>s(P) \<sqsubseteq> \<^bold>R\<^sub>s(Q)"
  by (metis Monotonic_refine RHS_Monotonic)

lemma RHS_Continuous [closure]: "Continuous \<^bold>R\<^sub>s"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3h_Continuous RHS_comp)

lemma RHS_inf: "\<^bold>R\<^sub>s(P \<sqinter> Q) = \<^bold>R\<^sub>s(P) \<sqinter> \<^bold>R\<^sub>s(Q)"
  by (meson Continuous_choice_dist RHS_Continuous)

lemma RHS_INF:
  "A \<noteq> {} \<Longrightarrow> \<^bold>R\<^sub>s(\<Sqinter> i \<in> A. P(i)) = (\<Sqinter> i \<in> A. \<^bold>R\<^sub>s(P(i)))"
  by (simp add: RHS_def R3h_UINF R2c_USUP R1_USUP)

lemma RHS_sup: "\<^bold>R\<^sub>s(P \<squnion> Q) = \<^bold>R\<^sub>s(P) \<squnion> \<^bold>R\<^sub>s(Q)"
  by (pred_auto)

lemma RHS_SUP: 
  "A \<noteq> {} \<Longrightarrow> \<^bold>R\<^sub>s(\<Squnion> i \<in> A. P(i)) = (\<Squnion> i \<in> A. \<^bold>R\<^sub>s(P(i)))"
  by (pred_auto)
    
lemma RHS_cond: "\<^bold>R\<^sub>s(P \<triangleleft> b \<triangleright> Q) = (\<^bold>R\<^sub>s(P) \<triangleleft> R2c b \<triangleright> \<^bold>R\<^sub>s(Q))"
  by (simp add: RHS_def R3h_cond R2c_condr R1_cond)

lemma RD_alt_def: "RD(P) = RD1(RD2(\<^bold>R(P)))"
  by (simp add: R3c_via_RD1_R3 RD1_R1_commute RD1_R2c_commute RD1_R3c_commute RD1_RD2_commute RH_def RD_def RP_def)

lemma RD1_RH_commute: "RD1(\<^bold>R(P)) = \<^bold>R(RD1(P))"
  by (simp add: RD1_R1_commute RD1_R2c_commute RD1_R3c_commute RH_def)

lemma RD2_RH_commute: "RD2(\<^bold>R(P)) = \<^bold>R(RD2(P))"
  by (metis R1_H2_commute R2c_H2_commute RD2_R3c_commute RD2_def RH_def)

lemma RD_idem: "RD(RD(P)) = RD(P)"
  by (simp add: RD_alt_def RD1_RH_commute RD2_RH_commute RD1_RD2_commute RD2_idem RD1_idem RH_idem)

lemma RD_Idempotent: "Idempotent RD"
  using Idempotent_def RD_idem by blast

lemma RD_Monotonic: "Monotonic RD"
  by (simp add: Monotonic_comp RD1_Monotonic RD2_Monotonic RD_comp RP_Monotonic)

lemma RD_Continuous: "Continuous RD"
  by (simp add: Continuous_comp RD1_Continuous RD2_Continuous RD_comp RP_Continuous)

lemma R3_RD_RP: "R3(RD(P)) = RP(RD1(RD2(P)))"
  by (metis (no_types, lifting) R1_R2c_is_R2 R2_R3_commute R3_cancels_R3c RD1_RH_commute RD2_RH_commute RD_alt_def RH_def RP_def)

lemma RD_healths [closure]:
  assumes "P is RD"
  shows "P is R1" "P is R2" "P is R3c" "P is RD1" "P is RD2"
  apply (metis Healthy_def R1_idem RD1_RH_commute RD2_RH_commute RH_def RD_alt_def assms)
  apply (metis Healthy_def R1_R2c_is_R2 R2_idem RD1_RH_commute RD2_RH_commute RH_def RD_alt_def assms)
  apply (metis Healthy_def R3_RD_RP R3c_via_RD1_R3 RD1_RD2_commute RD1_RH_commute RD2_R3c_commute RD2_RH_commute RD_alt_def RD_def assms)
  apply (metis Healthy_Idempotent Healthy_def RD1_Idempotent RD_alt_def assms)
  apply (metis H2_idem Healthy_def RD1_RD2_commute RD2_def RD_def assms)
  done

lemma RD1_RHS_commute: "RD1(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(RD1(P))"
  by (simp add: RD1_R1_commute RD1_R2c_commute RD1_R3h_commute RHS_def)

lemma RD2_RHS_commute: "RD2(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(RD2(P))"
  by (metis R1_H2_commute R2c_H2_commute RD2_R3h_commute RD2_def RHS_def)

lemma SRD_idem: "SRD(SRD(P)) = SRD(P)"
  by (simp add: RD1_RD2_commute RD1_RHS_commute RD1_idem RD2_RHS_commute RD2_idem RHS_idem SRD_def)

lemma SRD_Idempotent [closure]: "Idempotent SRD"
  by (simp add: Idempotent_def SRD_idem)

lemma SRD_Monotonic: "Monotonic SRD"
  by (simp add: Monotonic_comp RD1_Monotonic RD2_Monotonic RHS_Monotonic SRD_comp)

lemma SRD_Continuous [closure]: "Continuous SRD"
  by (simp add: Continuous_comp RD1_Continuous RD2_Continuous RHS_Continuous SRD_comp)

lemma SRD_RHS_H1_H2: "SRD(P) = \<^bold>R\<^sub>s(\<^bold>H(P))"
  by (metis (mono_tags, lifting) R1_R2c_commute R1_R3h_commute RD1_R1_commute RD1_RHS_commute RD1_via_R1 RD2_RHS_commute RD2_def RHS_def SRD_def)

lemma SRD_healths [closure]:
  assumes "P is SRD"
  shows "P is R1" "P is R2" "P is R3h" "P is RD1" "P is RD2"
  apply (metis Healthy_def R1_idem RD1_RHS_commute RD2_RHS_commute RHS_def SRD_def assms)
  apply (metis Healthy_def R1_R2c_is_R2 R2_idem RD1_RHS_commute RD2_RHS_commute RHS_def SRD_def assms)
  apply (metis Healthy_def R1_R3h_commute R2c_R3h_commute R3h_idem RD1_R3h_commute RD2_R3h_commute RHS_def SRD_def assms)
  apply (metis Healthy_def' RD1_idem SRD_def assms)
  apply (metis Healthy_def' RD1_RD2_commute RD2_idem SRD_def assms)
done

lemma SRD_intro:
  assumes "P is R1" "P is R2" "P is R3h" "P is RD1" "P is RD2"
  shows "P is SRD"
  by (metis Healthy_def R1_R2c_is_R2 RHS_def SRD_def assms(2) assms(3) assms(4) assms(5))

lemma SRD_ok_false [usubst]: "P is SRD \<Longrightarrow> P\<lbrakk>False/ok\<^sup><\<rbrakk> = R1(true)"
  by (metis H1_H2_eq_design Healthy_if R1_ok_false RD1_via_R1 RD2_def SRD_healths(1) SRD_healths(4) SRD_healths(5) design_ok_false)
 
lemma SRD_ok_true_wait_true [usubst]:
  assumes "P is SRD"
  shows "P\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> = (\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
proof -
  have "P = (\<exists> st\<^sup>< \<Zspot> II) \<triangleleft> $ok\<^sup>< \<triangleright> R1 true \<triangleleft> $wait\<^sup>< \<triangleright> P"
    by (metis Healthy_def R3h_cases SRD_healths(3) assms)
  moreover have "((\<exists> st\<^sup>< \<Zspot> II) \<triangleleft> $ok\<^sup>< \<triangleright> R1 true \<triangleleft> $wait\<^sup>< \<triangleright> P)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> = (\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
    by (simp add: usubst)
  ultimately show ?thesis
    by (simp)
qed

lemma SRD_left_zero_1: "P is SRD \<Longrightarrow> R1(true) ;; P = R1(true)"
  by (simp add: RD1_left_zero SRD_healths(1) SRD_healths(4))

lemma SRD_left_zero_2:
  assumes "P is SRD"
  shows "(\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> ;; P = (\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
proof -
  have "(\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> ;; R3h(P) = (\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if SRD_healths(3) assms)
qed

subsection \<open> UTP theories \<close>

text \<open> We create two theory objects: one for reactive designs and one for stateful reactive
        designs. \<close>

interpretation rdes_theory: utp_theory_continuous RD
  rewrites "P \<in> carrier rdes_theory.thy_order \<longleftrightarrow> P is RD"
  and "carrier rdes_theory.thy_order \<rightarrow> carrier rdes_theory.thy_order \<equiv> \<lbrakk>RD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>RD\<rbrakk>\<^sub>H"
  and "le rdes_theory.thy_order = (\<sqsubseteq>)"
  and "eq rdes_theory.thy_order = (=)"  
proof -
  show "utp_theory_continuous RD"
    by (unfold_locales, simp_all add: RD_Idempotent RD_Continuous)
qed (simp_all)

interpretation srdes_theory: utp_theory_continuous SRD
  rewrites "P \<in> carrier srdes_theory.thy_order \<longleftrightarrow> P is SRD"
  and "carrier srdes_theory.thy_order \<rightarrow> carrier srdes_theory.thy_order \<equiv> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  and "le srdes_theory.thy_order = (\<sqsubseteq>)"
  and "eq srdes_theory.thy_order = (=)"  
proof -
  show "utp_theory_continuous SRD"
    by (unfold_locales, simp_all add: SRD_Idempotent SRD_Continuous)
qed (simp_all)

interpretation rdes_rea_galois:
  galois_connection "(RD \<Leftarrow>\<langle>RD1 \<circ> RD2,R3\<rangle>\<Rightarrow> RP)"
proof (simp add: mk_conn_def, rule galois_connectionI', simp_all add: utp_partial_order)
  show "R3 \<in> \<lbrakk>RD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>RP\<rbrakk>\<^sub>H"
    by (metis (no_types, lifting) Healthy_def' Pi_I R3_RD_RP RP_idem mem_Collect_eq)
  show "RD1 \<circ> RD2 \<in> \<lbrakk>RP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>RD\<rbrakk>\<^sub>H"
    by (simp add: Pi_iff Healthy_def, metis RD_def RD_idem)
  show "isotone (utp_order RD) (utp_order RP) R3"
    by (simp add: R3_Monotonic isotone_utp_orderI)
  show "isotone (utp_order RP) (utp_order RD) (RD1 \<circ> RD2)"
    by (simp add: Monotonic_comp RD1_Monotonic RD2_Monotonic isotone_utp_orderI)
  fix P :: "('a, 'b) rp_hrel"
  assume "P is RD"
  thus "P \<sqsubseteq> RD1 (RD2 (R3 P))"
    by (simp add: Healthy_if R3c_via_RD1_R3 RD1_RD2_commute RD_healths)
    
next
  fix P :: "('a, 'b) rp_hrel"
  assume a: "P is RP"
  thus "R3 (RD1 (RD2 P)) \<sqsubseteq> P"
  proof -
    have "R3 (RD1 (RD2 P)) = RP (RD1 (RD2(P)))"
      by (metis Healthy_if R3_RD_RP RD_def a)
    moreover have "RD1(RD2(P)) \<sqsubseteq> P"
      by (pred_auto)
    ultimately show ?thesis
      by (metis Healthy_if RP_mono a)
  qed
qed

interpretation rdes_rea_retract:
  retract "(RD \<Leftarrow>\<langle>RD1 \<circ> RD2,R3\<rangle>\<Rightarrow> RP)"
  by (unfold_locales, simp_all add: mk_conn_def utp_partial_order)
     (simp add: Healthy_if R3c_via_RD1_R3 RD1_RD2_commute RD_healths)
     
abbreviation Chaos :: "('s,'t::trace,'\<alpha>) rsp_hrel" where
"Chaos \<equiv> srdes_theory.utp_bottom"

abbreviation Miracle :: "('s,'t::trace,'\<alpha>) rsp_hrel" where
"Miracle \<equiv> srdes_theory.utp_top"

thm srdes_theory.weak.bottom_lower
thm srdes_theory.weak.top_higher
thm srdes_theory.meet_bottom
thm srdes_theory.meet_top

abbreviation srd_lfp ("\<mu>\<^sub>R") where "\<mu>\<^sub>R F \<equiv> srdes_theory.utp_lfp F"

abbreviation srd_gfp ("\<nu>\<^sub>R") where "\<nu>\<^sub>R F \<equiv> srdes_theory.utp_gfp F"

syntax
  "_srd_mu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>R _./ _" [0, 10] 10)
  "_srd_nu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>R _./ _" [0, 10] 10)

translations
  "\<mu>\<^sub>R X. P" == "\<mu>\<^sub>R (\<lambda> X. P)"
  "\<nu>\<^sub>R X. P" == "\<mu>\<^sub>R (\<lambda> X. P)"

syntax_consts
  "_srd_mu" \<rightleftharpoons> "srd_lfp" and
  "_srd_nu" \<rightleftharpoons> "srd_gfp"

text \<open> The reactive design weakest fixed-point can be defined in terms of relational calculus one. \<close>

lemma srd_mu_equiv:
  assumes "Monotonic F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<mu>\<^sub>R X. F(X)) = (\<mu> X. F(SRD(X)))"
  by (metis assms srdes_theory.utp_lfp_def)

end