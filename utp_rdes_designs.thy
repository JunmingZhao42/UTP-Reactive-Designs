section \<open> Reactive Design Specifications \<close>

theory utp_rdes_designs
  imports utp_rdes_healths
begin

subsection \<open> Reactive design forms \<close>

lemma rdes_skip_def: "II\<^sub>C = \<^bold>R(true \<turnstile> (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<not>wait\<^sup>> \<and> \<lceil>II\<rceil>\<^sub>R))"
  apply (pred_auto) using minus_zero_eq by blast+

lemma srdes_skip_def: "II\<^sub>R = \<^bold>R\<^sub>s(true \<turnstile> (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<not>wait\<^sup>> \<and> \<lceil>II\<rceil>\<^sub>R))"
  apply (pred_auto) using minus_zero_eq by blast+

lemma Chaos_def: "Chaos = \<^bold>R\<^sub>s(false \<turnstile> true)"
proof -
  have "Chaos = SRD(true)"
    by (metis srdes_theory.healthy_bottom)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(true))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(false \<turnstile> true)"
    by (metis H1_design H2_true design_false_pre)
  finally show ?thesis .
qed

lemma Miracle_def: "Miracle = \<^bold>R\<^sub>s(true \<turnstile> false)"
proof -
  have "Miracle = SRD(false)"
    by (metis srdes_theory.healthy_top)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(false))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (simp add: H1_H2_false top_d_def)
  finally show ?thesis .
qed

lemma RD1_reactive_design: "RD1(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by (pred_auto)

lemma RD2_reactive_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "RD2(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RH_commute RD2_def)

lemma RD1_st_reactive_design: "RD1(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (pred_auto)

lemma RD2_st_reactive_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "RD2(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RHS_commute RD2_def)

lemma wait_false_design:
  "(P \<turnstile> Q) \<^sub>f = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by (pred_auto)

lemma RD_RH_design_form:
  "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "RD(P) = RD1(RD2(R1(R2c(R3c(P)))))"
    by (simp add: RD_alt_def RH_def)
  also have "... = RD1(H2(R1(R2s(R3c(P)))))"
    by (simp add: R1_R2s_R2c RD2_def)
  also have "... = RD1(R1(H2(R2s(R3c(P)))))"
    by (simp add: R1_H2_commute)
  also have "... = R1(H1(R1(H2(R2s(R3c(P))))))"
    by (simp add: R1_idem RD1_via_R1)
  also have "... = R1(H1(H2(R2s(R3c(R1(P))))))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R2s_R2c R1_R3c_commute RD1_via_R1)
  also have "... = R1(R2s(H1(H2(R3c(R1(P))))))"
    by (simp add: R2s_H1_commute R2s_H2_commute)
  also have "... = R1(R2s(H1(R3c(H2(R1(P))))))"
    by (metis RD2_R3c_commute RD2_def)
  also have "... = R2(R1(H1(R3c(H2(R1(P))))))"
    by (metis R1_R2_commute R1_idem R2_def)
  also have "... = R2(R3c(R1(\<^bold>H(R1(P)))))"
    by (simp add: R1_R3c_commute RD1_R3c_commute RD1_via_R1)
  also have "... = RH(\<^bold>H(R1(P)))"
    by (metis R1_R2s_R2c R1_R3c_commute R2_R1_form RH_def)
  also have "... = RH(\<^bold>H(P))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R3c_commute R1_idem RD1_via_R1 RH_def)
  also have "... = RH((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: subst_pred[THEN sym], metis R3c_subst_wait RH_def wait_false_design)
  finally show ?thesis .
qed

lemma RD_reactive_design:
  assumes "P is RD"
  shows "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis RD_RH_design_form Healthy_def' assms)

lemma RD_RH_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "RD(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by (simp add: RD1_reactive_design RD2_reactive_design RD_alt_def RH_idem assms(1) assms(2))

lemma RH_design_is_RD:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "\<^bold>R(P \<turnstile> Q) is RD"
  by (simp add: RD_RH_design Healthy_def' assms(1) assms(2))

lemma SRD_RH_design_form:
  "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "SRD(P) = R1(R2c(R3h(RD1(RD2(R1(P))))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_commute R1_R3h_commute R1_idem R2c_H2_commute RD1_R1_commute RD1_R2c_commute RD1_R3h_commute RD2_R3h_commute RD2_def RHS_def SRD_def)
  also have "... = R1(R2s(R3h(\<^bold>H(P))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_is_R2 R1_R3h_commute R2_R1_form RD1_via_R1 RD2_def)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(P))"
    by (simp add: R1_R2s_R2c RHS_def)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: subst_pred[THEN sym], metis R3h_subst_wait RHS_def wait_false_design)
  finally show ?thesis .
qed

lemma SRD_reactive_design:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis SRD_RH_design_form Healthy_def' assms)

lemma SRD_RH_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "SRD(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (simp add: RD1_st_reactive_design RD2_st_reactive_design RHS_idem SRD_def assms(1) assms(2))

lemma RHS_design_is_SRD:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q) is SRD"
  by (simp add: Healthy_def' SRD_RH_design assms(1) assms(2))

lemma SRD_RHS_H1_H2: "SRD(P) = \<^bold>R\<^sub>s(\<^bold>H(P))"
  by (simp add: SRD_RHS_H1_H2)

subsection \<open> Auxiliary healthiness conditions \<close>

definition [pred]: "R3c_pre(P) = (true \<triangleleft> $wait\<^sup>< \<triangleright> P)"

definition [pred]: "R3c_post(P) = (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> P)"

definition [pred]: "R3h_post(P) = ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> P)"

lemma R3c_pre_conj: "R3c_pre(P \<and> Q) = (R3c_pre(P) \<and> R3c_pre(Q))"
  by (pred_auto)

lemma R3c_pre_seq:
  "(true ;; Q) = true \<Longrightarrow> R3c_pre(P ;; Q) = (R3c_pre(P) ;; Q)"
  by (pred_auto)

lemma unrest_ok_R3c_pre [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R3c_pre(P)"
  by pred_auto

lemma unrest_ok'_R3c_pre [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R3c_pre(P)"
  by pred_auto

lemma unrest_ok_R3c_post [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R3c_post(P)"
  by pred_auto

lemma unrest_ok_R3c_post' [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R3c_post(P)"
  by pred_auto

lemma unrest_ok_R3h_post [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R3h_post(P)"
  by pred_auto

lemma unrest_ok_R3h_post' [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R3h_post(P)"
  by pred_auto

subsection \<open> Composition laws \<close>

theorem R1_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) =
   R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
proof -
  have "(R1((\<exists> ok\<^sup>> \<Zspot> P) \<turnstile> (\<exists> ok\<^sup>> \<Zspot> Q)) ;; R1((\<exists> ok\<^sup>< \<Zspot> R) \<turnstile> (\<exists> ok\<^sup>< \<Zspot> S))) =
   R1((\<not> (R1(\<not> (\<exists> ok\<^sup>> \<Zspot> P)) ;; R1(true)) \<and> \<not> (R1(\<exists> ok\<^sup>> \<Zspot> Q) ;; R1(\<not> (\<exists> ok\<^sup>< \<Zspot> R)))) \<turnstile> (R1(\<exists> ok\<^sup>> \<Zspot> Q) ;; R1(\<exists> ok\<^sup>< \<Zspot> S)))"
    using order_refl by (pred_auto; metis (full_types))
  thus ?thesis
    by (simp add: assms ex_unrest)
qed

theorem R1_design_composition':
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) =
    R1(((\<not>\<^sub>r P) wp\<^sub>r false \<and> R1(Q) wp\<^sub>r R) \<turnstile> (R1(Q) ;; R1(S)))"
  by (simp add: R1_design_composition assms, (pred_auto; blast))

theorem R1_design_composition_RR:
  assumes "P is RR" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  by (simp_all add: R1_design_composition' assms unrest Healthy_if closure wp)

theorem R1_design_composition_RC:
  assumes "P is RC" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1((P \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  by (simp add: R1_design_composition_RR assms unrest Healthy_if closure wp)

lemma R2s_design: "R2s(P \<turnstile> Q) = (R2s(P) \<turnstile> R2s(Q))"
  by (simp add: R2s_def design_def usubst subst_apply_SEXP)

lemma R2c_design: "R2c(P \<turnstile> Q) = (R2c(P) \<turnstile> R2c(Q))"
  by pred_auto

lemma R1_R3c_design:
  "R1(R3c(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by (pred_auto)

lemma R1_R3h_design:
  "R1(R3h(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3h_post(Q))"
  by (pred_auto)

lemma R3c_R1_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(R3c(R1(P \<turnstile> Q)) ;; R3c(R1(R \<turnstile> S))) =
       R3c(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> wait\<^sup>>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
    by (pred_auto; blast)
  have 2:"(\<not> (R1 (R3c_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R)))"
    by (pred_auto, blast, metis (full_types), blast)
  have 3:"(R1 (R3c_post Q) ;; R1 (R3c_post S)) = R3c_post (R1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 S))"
    by (pred_auto, blast)
  show ?thesis
    apply (simp add: R3c_semir_form R1_R3c_commute[THEN sym] R1_R3c_design unrest )
    apply (subst R1_design_composition)
        apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
    done
qed

lemma R3h_R1_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(R3h(R1(P \<turnstile> Q)) ;; R3h(R1(R \<turnstile> S))) =
       R3h(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> wait\<^sup>>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
   by (pred_auto; blast)
  have 2:"(\<not> (R1 (R3h_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R)))"
    by (pred_auto, blast, metis (full_types), blast)
  have 3:"(R1 (R3h_post Q) ;; R1 (R3h_post S)) = R3h_post (R1 Q ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 S))"
    by (pred_auto; metis Orderings.order_eq_iff)
    
  show ?thesis
    apply (simp add: R3h_semir_form R1_R3h_commute[THEN sym] R1_R3h_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma R2_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(R2(P \<turnstile> Q) ;; R2(R \<turnstile> S)) =
       R2((\<not> (R1 (\<not> R2c P) ;; R1 true) \<and> \<not> (R1 (R2c Q) ;; R1 (\<not> R2c R))) \<turnstile> (R1 (R2c Q) ;; R1 (R2c S)))"
  apply (simp add: R2_R2c_def R2c_design R1_design_composition assms unrest R2c_not R2c_and R2c_disj R1_R2c_commute[THEN sym] R2c_idem R2c_R1_seq)
  apply (metis (no_types, lifting) R2c_R1_seq R2c_not R2c_true)
done

lemma RH_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(RH(P \<turnstile> Q) ;; RH(R \<turnstile> S)) =
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> wait\<^sup>>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (pred_auto)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))"
  proof -
    have "((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> wait\<^sup>>) ;; R2 (\<not> R))"
      by (pred_auto)
    hence "R2c ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> wait\<^sup>>) ;; R2 (\<not> R))"
      by (metis (no_types) R1_R2c_is_R2 R2_seqr_distribute R2c_seq)
    also have "... = ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))"
      by (pred_auto)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S)))) = (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S)))"
    apply (pred_auto)
    apply (metis diff_add_cancel_left' le_add trace_class.add_diff_cancel_left trace_class.add_left_mono)
    apply (metis diff_add_cancel_left' minus_cancel_le)
    done

  have "(R1(R2s(R3c(P \<turnstile> Q))) ;; R1(R2s(R3c(R \<turnstile> S)))) =
        ((R3c(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3c(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, opaque_lifting) R1_R2s_R2c R1_R3c_commute R2c_R3c_commute R2s_design)
  also have "... = R3c (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S)))))"
    by (simp add: R3c_R1_design_composition assms unrest)
  also have "... = R3c(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3c_commute R2c_R3c_commute RH_def)
qed

lemma RHS_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> wait\<^sup>>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (pred_auto, blast)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))"
    apply pred_auto
    apply (metis diff_add_cancel_left' le_add trace_class.add_diff_cancel_left trace_class.add_left_mono)
    apply (metis diff_add_cancel_left' minus_cancel_le)
    done

  have 3:"R2c((R1 (R2s Q) ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S)))) =
          (R1 (R2s Q) ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))\<lbrakk>True/wait\<^sup><\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))\<lbrakk>True/wait\<^sup><\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))\<lbrakk>True/wait\<^sup><\<rbrakk>)) =
            R2c(R1 (R2s (Q\<lbrakk>True/wait\<^sup>>\<rbrakk>)) ;; (\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>True/wait\<^sup><\<rbrakk>)"
        by (pred_auto)
      also have "... = R2c(R2(Q\<lbrakk>True/wait\<^sup>>\<rbrakk>) ;; R2((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>True/wait\<^sup><\<rbrakk>))"
        by (metis (no_types) R2_def R2_des_lift_skip R2_st_ex R2_subst_wait_true)
      also have "... = (R2(Q\<lbrakk>True/wait\<^sup>>\<rbrakk>) ;; R2((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>True/wait\<^sup><\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))\<lbrakk>True/wait\<^sup><\<rbrakk>)"
        apply (simp add: usubst R2_des_lift_skip)
        apply (metis (no_types) R2_def R2_des_lift_skip R2_st_ex R2_subst_wait_true subst_apply_twice)
      done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))\<lbrakk>False/wait\<^sup><\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))\<lbrakk>False/wait\<^sup><\<rbrakk>)"
      by (simp add: usubst)
         (metis (no_types) R1_wait'_false R1_wait_false R2_R1_form R2_subst_wait'_false R2_subst_wait_false R2c_seq)
       
    ultimately show ?thesis
      by (metis (no_types, lifting) R2_R1_form R2_condr' R2_des_lift_skip R2_st_ex R2c_seq R2s_wait SEXP_def aext_var)
  qed

  have "(R1(R2s(R3h(P \<turnstile> Q))) ;; R1(R2s(R3h(R \<turnstile> S)))) =
        ((R3h(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3h(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, opaque_lifting) R1_R2s_R2c R1_R3h_commute R2c_R3h_commute R2s_design)
  also have "... = R3h (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S)))))"
    by (simp add: R3h_R1_design_composition assms unrest)
  also have "... = R3h(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3h_commute R2c_R3h_commute RHS_def)
qed

lemma RHS_R2s_design_composition:
  assumes
    "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    "P is R2s" "Q is R2s" "R is R2s" "S is R2s"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> P) ;; R1 true) \<and> \<not> ((R1 Q \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R))) \<turnstile>
                       (R1 Q ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 S)))"
proof -
  have f1: "R2s P = P"
    by (meson Healthy_def assms(5))
  have f2: "R2s Q = Q"
    by (meson Healthy_def assms(6))
  have f3: "R2s R = R"
    by (meson Healthy_def assms(7))
  have "R2s S = S"
    by (meson Healthy_def assms(8))
  then show ?thesis
    using f3 f2 f1 by (simp add: RHS_design_composition assms(1) assms(2) assms(3) assms(4))
qed

lemma RH_design_export_R1: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R1(Q))"
  by (pred_auto)

lemma RH_design_export_R2s: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2s(Q))"
  by (pred_auto)

lemma RH_design_export_R2c: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2c(Q))"
  by (pred_auto)

lemma RHS_design_export_R1: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R1(Q))"
  by (pred_auto)

lemma RHS_design_export_R2s: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2s(Q))"
  by (pred_auto)

lemma RHS_design_export_R2c: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2c(Q))"
  by (pred_auto)

lemma RHS_design_export_R2: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2(Q))"
  by (pred_auto)

lemma R1_design_R1_pre: 
  "\<^bold>R\<^sub>s(R1(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (pred_auto)

lemma RHS_design_ok_wait: "\<^bold>R\<^sub>s(P\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<turnstile> Q\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (pred_auto)

lemma RH_design_neg_R1_pre:
  "\<^bold>R ((\<not> R1 P) \<turnstile> R) = \<^bold>R ((\<not> P) \<turnstile> R)"
  by (pred_auto)

lemma RHS_design_neg_R1_pre:
  "\<^bold>R\<^sub>s ((\<not> R1 P) \<turnstile> R) = \<^bold>R\<^sub>s ((\<not> P) \<turnstile> R)"
  by (pred_auto)

lemma RHS_design_conj_neg_R1_pre:
  "\<^bold>R\<^sub>s (((\<not> R1 P) \<and> Q) \<turnstile> R) = \<^bold>R\<^sub>s (((\<not> P) \<and> Q) \<turnstile> R)"
  by (pred_auto)

lemma RHS_pre_lemma: "(\<^bold>R\<^sub>s P)\<^sup>f\<^sub>f = R1(R2c(P\<^sup>f\<^sub>f))"
  by (pred_auto)

lemma RH_design_R2c_pre:
  "\<^bold>R(R2c(P) \<turnstile> Q) = \<^bold>R(P \<turnstile> Q)"
  by (pred_auto)

lemma RHS_design_R2c_pre:
  "\<^bold>R\<^sub>s(R2c(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (pred_auto)

subsection \<open> Refinement introduction laws \<close>

lemma R1_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "$ok\<^sup>< \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>< \<sharp> P\<^sub>2" "$ok\<^sup>> \<sharp> P\<^sub>2"
    "$ok\<^sup>< \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>< \<sharp> Q\<^sub>2" "$ok\<^sup>> \<sharp> Q\<^sub>2"    
  shows "R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
proof -
  have "R1((\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> P\<^sub>1) \<turnstile> (\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> P\<^sub>2)) \<sqsubseteq> R1((\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> Q\<^sub>1) \<turnstile> (\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> Q\<^sub>2)) 
       \<longleftrightarrow> `R1(\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> P\<^sub>1) \<longrightarrow> R1(\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> Q\<^sub>1)` \<and> `R1(\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> P\<^sub>1) \<and> R1(\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> Q\<^sub>2) \<longrightarrow> R1(\<exists> (ok\<^sup><,ok\<^sup>>) \<Zspot> P\<^sub>2)`"
    by (pred_auto; meson)
  thus ?thesis
    by (simp_all add: ex_unrest ex_plus Healthy_if assms)
qed

lemma R1_design_refine_RR:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR"
  shows "R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
  by (simp add: R1_design_refine assms unrest closure)

lemma RH_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "P\<^sub>1 is R2c" "P\<^sub>2 is R2c" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R2c"
    "$ok\<^sup>< \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>< \<sharp> P\<^sub>2" "$ok\<^sup>> \<sharp> P\<^sub>2"
    "$ok\<^sup>< \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>< \<sharp> Q\<^sub>2" "$ok\<^sup>> \<sharp> Q\<^sub>2"    
    "$wait\<^sup>< \<sharp> P\<^sub>1" "$wait\<^sup>< \<sharp> P\<^sub>2" "$wait\<^sup>< \<sharp> Q\<^sub>1" "$wait\<^sup>< \<sharp> Q\<^sub>2"    
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
proof -
  have "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> R1(R3c(R2c(P\<^sub>1 \<turnstile> P\<^sub>2))) \<sqsubseteq> R1(R3c(R2c(Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp add: R2c_R3c_commute RH_def)
  also have "... \<longleftrightarrow> R1(R3c(P\<^sub>1 \<turnstile> P\<^sub>2)) \<sqsubseteq> R1(R3c(Q\<^sub>1 \<turnstile> Q\<^sub>2))"
    by (simp add: Healthy_if R2c_design assms)
  also have "... \<longleftrightarrow> R1(R3c(P\<^sub>1 \<turnstile> P\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(R3c(Q\<^sub>1 \<turnstile> Q\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk>"
    by (metis (no_types) R1_R3c_commute R3c_idem R3c_mono R3c_subst_wait pred_ba.le_iff_inf subst_pred(4))
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk>"      
    by (pred_auto)
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)"      
    by (simp add: usubst assms closure unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
    by (simp add: R1_design_refine assms)
  finally show ?thesis .
qed 

lemma RHS_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "P\<^sub>1 is R2c" "P\<^sub>2 is R2c" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R2c"
    "$ok\<^sup>< \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>< \<sharp> P\<^sub>2" "$ok\<^sup>> \<sharp> P\<^sub>2"
    "$ok\<^sup>< \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>< \<sharp> Q\<^sub>2" "$ok\<^sup>> \<sharp> Q\<^sub>2"    
    "$wait\<^sup>< \<sharp> P\<^sub>1" "$wait\<^sup>< \<sharp> P\<^sub>2" "$wait\<^sup>< \<sharp> Q\<^sub>1" "$wait\<^sup>< \<sharp> Q\<^sub>2"    
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> R1(R3h(R2c(P\<^sub>1 \<turnstile> P\<^sub>2))) \<sqsubseteq> R1(R3h(R2c(Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp add: R2c_R3h_commute RHS_def)
  also have "... \<longleftrightarrow> R1(R3h(P\<^sub>1 \<turnstile> P\<^sub>2)) \<sqsubseteq> R1(R3h(Q\<^sub>1 \<turnstile> Q\<^sub>2))"
    by (simp add: Healthy_if R2c_design assms)
  also have "... \<longleftrightarrow> R1(R3h(P\<^sub>1 \<turnstile> P\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(R3h(Q\<^sub>1 \<turnstile> Q\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk>"
    by (metis (no_types) R1_R3h_commute R3h_idem R3h_mono R3h_subst_wait pred_ba.le_iff_inf subst_pred(4))
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk>"      
    by (pred_auto)
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)"      
    by (simp add: usubst assms closure unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
    by (simp add: R1_design_refine assms)
  finally show ?thesis .
qed 

lemma rdes_refine_intro:
  assumes "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqsubseteq> \<^bold>R(P\<^sub>2 \<turnstile> Q\<^sub>2)"
  by (simp add: RH_mono assms design_refine_intro)

lemma srdes_refine_intro:
  assumes "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2)"
  by (simp add: RHS_mono assms design_refine_intro)

subsection \<open> Distribution laws \<close>

lemma RHS_design_choice: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqinter> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<or> Q\<^sub>2))"
  by (metis RHS_inf design_choice)
    
lemma RHS_design_sup: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<squnion> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<or> P\<^sub>2) \<turnstile> ((P\<^sub>1 \<longrightarrow> Q\<^sub>1) \<and> (P\<^sub>2 \<longrightarrow> Q\<^sub>2)))"
  by (simp add: RHS_sup[THEN sym] design_inf, pred_simp)

lemma RHS_design_USUP:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A. \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion> i \<in> A. P(i)) \<turnstile> (\<Sqinter> i \<in> A. Q(i)))"
  by (subst RHS_INF[OF assms, THEN sym], simp add: design_UINF_mem assms)

end