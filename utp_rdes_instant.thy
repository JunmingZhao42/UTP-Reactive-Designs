section \<open> Instantaneous Reactive Designs \<close>

theory utp_rdes_instant
  imports utp_rdes_prog
begin

definition ISRD1 :: "('s,'t::trace,'\<alpha>) rsp_hrel \<Rightarrow> ('s,'t,'\<alpha>) rsp_hrel" where
[pred]: "ISRD1(P) = P \<parallel>\<^sub>R \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> ($tr\<^sup>< = $tr\<^sup>>)\<^sub>e)"

definition ISRD :: "('s,'t::trace,'\<alpha>) rsp_hrel \<Rightarrow> ('s,'t,'\<alpha>) rsp_hrel" where
[pred]: "ISRD = ISRD1 \<circ> NSRD"

lemma ISRD1_idem_lemma: "\<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> ($tr\<^sup>< = $tr\<^sup>>)\<^sub>e) \<parallel>\<^sub>R \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> ($tr\<^sup>< = $tr\<^sup>>)\<^sub>e) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> ($tr\<^sup>< = $tr\<^sup>>)\<^sub>e)"
proof -
  have [closure]: "($tr\<^sup>< = $tr\<^sup>>)\<^sub>e is RR" 
    by (pred_simp, metis dual_order.refl minus_zero_eq trace_class.diff_cancel)
  show ?thesis 
    by (simp add: rea_design_par_def rdes closure rpred)
qed

lemma ISRD1_idem: "ISRD1(ISRD1(P)) = ISRD1(P)"
  by (simp add: ISRD1_def ISRD1_idem_lemma RHS_comp_assoc)

lemma ISRD1_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> ISRD1(P) \<sqsubseteq> ISRD1(Q)"
  by (simp add: ISRD1_def rea_design_par_mono)
  
lemma ISRD1_RHS_design_form:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>> \<sharp> R"
  shows "ISRD1(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> false \<diamondop> R5(R))"
  using assms 
    by (simp add: ISRD1_def choose_srd_def RHS_tri_design_par unrest R5_def)
       (metis (no_types, lifting) R1_design_R1_pre R1_extend_conj' pred_ba.boolean_algebra.conj_one_right)

lemma ISRD1_form:
  "ISRD1(SRD(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> false \<diamondop> (R5(post\<^sub>R(P))))"
  by (simp add: ISRD1_RHS_design_form SRD_as_reactive_tri_design unrest)

lemma ISRD1_rdes_def [rdes_def]: 
  "\<lbrakk> P is RR; R is RR \<rbrakk> \<Longrightarrow> ISRD1(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> false \<diamondop> R5(R))"
  by (simp add: ISRD1_def R5_def rdes_def closure rpred)

lemma ISRD_intro: 
  assumes "P is NSRD" "peri\<^sub>R(P) = (\<not>\<^sub>r pre\<^sub>R(P))" "($tr\<^sup>< = $tr\<^sup>>)\<^sub>e \<sqsubseteq> post\<^sub>R(P)"
  shows "P is ISRD"
proof -
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) is ISRD1"
    by (metis (mono_tags, lifting) Healthy_intro ISRD1_RHS_design_form R5_def assms(2) assms(3) ok'_peri_unrest ok'_post_unrest ok'_pre_unrest pred_ba.inf.absorb_iff1 rea_impl_false rea_impl_mp srdes_tri_eq_intro)
  hence "P is ISRD1"
    by (simp add: SRD_reactive_tri_design closure assms(1))
  thus ?thesis
    by (simp add: ISRD_def Healthy_comp assms(1))
qed

lemma ISRD1_rdes_intro:
  assumes "P is RR" "Q is RR" "($tr\<^sup>< = $tr\<^sup>>)\<^sub>e \<sqsubseteq> Q"
  shows "\<^bold>R\<^sub>s(P \<turnstile> false \<diamondop> Q) is ISRD1"
  unfolding Healthy_def
  by (metis (mono_tags, lifting) ISRD1_rdes_def R5_def assms(1) assms(2) assms(3) pred_ba.le_iff_inf)

lemma ISRD_rdes_intro [closure]:
  assumes "P is RC" "Q is RR" "($tr\<^sup>< = $tr\<^sup>>)\<^sub>e \<sqsubseteq> Q"
  shows "\<^bold>R\<^sub>s(P \<turnstile> false \<diamondop> Q) is ISRD"
  unfolding Healthy_def
  by (simp add: Healthy_if ISRD1_rdes_intro ISRD_def NSRD_rdes_intro RC_implies_RR assms rrel_theory.top_closed unrest)

lemma ISRD_implies_ISRD1:
  assumes "P is ISRD"
  shows "P is ISRD1"
proof -
  have "ISRD(P) is ISRD1"
    by (simp add: ISRD_def Healthy_def ISRD1_idem)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

find_theorems sset
  
lemma ISRD_implies_SRD: 
  assumes "P is ISRD"
  shows "P is SRD"
proof -
  have 1:"ISRD(P) = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true \<and> R1 true) \<turnstile> false \<diamondop> (post\<^sub>R P \<and> ($tr\<^sup>< = $tr\<^sup>>)\<^sub>e))"
    by (simp add: NSRD_form ISRD1_def R5_def ISRD_def RHS_tri_design_par rdes_def unrest closure)
  moreover have "... is SRD"
    by (simp add: unrest_ssubst_expr unrest usubst_eval usubst closure assms)
  ultimately have "ISRD(P) is SRD"
    by (simp)
  with assms show ?thesis
    by (simp add: Healthy_def)
qed

lemma tr'_eq_tr_RR [closure]: "($tr\<^sup>< = $tr\<^sup>>)\<^sub>e is RR"
  using minus_zero_eq by pred_auto

lemma wpR_property [wp]: "(\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false\<^sub>h) wp\<^sub>r false\<^sub>h = (\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false\<^sub>h"
  using dual_order.trans by (pred_simp, blast)

thm wp_rea_false_RC

lemma ISRD_implies_NSRD [closure]: 
  assumes "P is ISRD"
  shows "P is NSRD"
proof -
  have 1:"ISRD(P) = ISRD1(RD3(SRD(P)))"
    by (simp add: ISRD_def NSRD_def SRD_def, metis RD1_RD3_commute RD3_left_subsumes_RD2)
  also have "... = ISRD1(RD3(P))"
    by (simp add: assms ISRD_implies_SRD Healthy_if)
  also have "... = ISRD1 (\<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false\<^sub>h) \<turnstile> (\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> post\<^sub>R P))"
    by (simp add: RD3_def, subst SRD_right_unit_tri_lemma, simp_all add: assms ISRD_implies_SRD)
  also have "... = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false\<^sub>h) \<turnstile> false \<diamondop> (post\<^sub>R P \<and> ($tr\<^sup>< = $tr\<^sup>>)\<^sub>e))"
    by (simp add: RHS_tri_design_par ISRD1_def unrest choose_srd_def rpred closure ISRD_implies_SRD assms)
  finally have 1: "ISRD(P) = ..." .
  hence "... = (... ;; II\<^sub>R)"
    by (rdes_simp, simp_all add: RHS_tri_design_composition_wp closure unrest_ssubst_expr unrest rpred usubst_eval wp assms ISRD_implies_SRD)

  thus ?thesis
    by (metis (no_types, lifting) "1" Healthy_if Healthy_intro ISRD_implies_SRD RD3_def SRD_RD3_implies_NSRD assms)
qed
  
lemma ISRD_form:
  assumes "P is ISRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> false \<diamondop> R5(post\<^sub>R(P))) = P"
proof -
  have "P = ISRD1(P)"
    by (simp add: ISRD_implies_ISRD1 assms Healthy_if)
  also have "... = ISRD1(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_reactive_tri_design ISRD_implies_SRD assms)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> false \<diamondop> R5(post\<^sub>R(P)))"
    by (simp add: ISRD1_rdes_def R5_def closure assms)
  finally show ?thesis ..
qed
    
lemma ISRD_elim [RD_elim]: 
  "\<lbrakk> P is ISRD; Q(\<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> false \<diamondop> R5(post\<^sub>R(P)))) \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: ISRD_form)
  
lemma skip_srd_ISRD [closure]: "II\<^sub>R is ISRD"
  by (rule ISRD_intro, simp_all add: rdes closure, pred_auto)
    
lemma assigns_srd_ISRD [closure]: "\<langle>\<sigma>\<rangle>\<^sub>R is ISRD"
  by (rule ISRD_intro, simp_all add: rdes closure, pred_auto)

lemma seq_ISRD_closed:
  assumes "P is ISRD" "Q is ISRD"
  shows "P ;; Q is ISRD"
  apply (insert assms)
  apply (erule ISRD_elim)+
  apply (simp add: rdes_def closure assms unrest)
  apply (rule ISRD_rdes_intro)
    apply (simp_all add: rdes_def closure assms unrest)
  apply (pred_auto)
  done

lemma ISRD_Miracle_right_zero:
  assumes "P is ISRD" "pre\<^sub>R(P) = true\<^sub>r"
  shows "P ;; Miracle = Miracle"
  by (rdes_simp cls: assms)

text \<open> A recursion whose body does not extend the trace results in divergence \<close>

lemma ISRD_recurse_Chaos:
  assumes "P is ISRD" "post\<^sub>R P ;; true\<^sub>r = true\<^sub>r"
  shows "(\<mu>\<^sub>R X. P ;; X) = Chaos"
proof -
  have 1: "(\<mu>\<^sub>R X. P ;; X) = (\<mu> X. P ;; SRD(X))"
    by (auto simp add: srdes_theory.utp_lfp_def closure mono assms)
  have "(\<mu> X. P ;; SRD(X)) \<sqsubseteq> Chaos"
  proof -
    have "P ;; Chaos \<sqsubseteq> Chaos"
      apply (rdes_refine_split cls: assms)
      using assms(2) apply (pred_auto, metis (no_types, lifting) dual_order.antisym order_refl)
       apply (pred_auto)+
      done
    hence "P ;; SRD Chaos \<sqsubseteq> Chaos"
      by (simp add: Healthy_if srdes_theory.bottom_closed)
    thus ?thesis
      by (metis "1" \<open>P ;; Chaos \<sqsubseteq> Chaos\<close> srdes_theory.LFP_lowerbound srdes_theory.bottom_closed)
  qed
  thus ?thesis
    by (metis "1" pred_ba.order.eq_iff srdes_theory.LFP_closed srdes_theory.bottom_lower)
qed

lemma recursive_assign_Chaos:
  "(\<mu>\<^sub>R X. \<langle>\<sigma>\<rangle>\<^sub>R ;; X) = Chaos"
  by (rule ISRD_recurse_Chaos, simp_all add: closure rdes, pred_auto)  

lemma unproductive_form:
  assumes "P\<^sub>2 is RR" "P\<^sub>3 is RR" "P\<^sub>3 is R5" "P\<^sub>3 \<noteq> false"
  shows "\<not> (\<^bold>R\<^sub>s(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) is Productive)"
proof -
  have 1:"Productive(\<^bold>R\<^sub>s(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> R4(P\<^sub>3))"
    by (simp add: Productive_RHS_R4_design_form closure assms)
  have 2:"... = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> false)"
    by (metis Healthy_if R4_R5 assms(3))
  have 3:"... \<noteq> \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)"
    by (simp add: R5_implies_R1 assms rea_true_conj(1) rrel_theory.bottom_closed rrel_theory.top_closed srdes_tri_eq_iff)
  thus ?thesis
    by (metis "1" "2" Healthy_if)
qed

lemma unproductive_assigns: "\<not> (\<langle>\<sigma>\<rangle>\<^sub>R is Productive)"
  unfolding rdes_def by (rule unproductive_form, simp_all add: closure, pred_auto+)

end