section \<open> Stateful-Failure Reactive Relations \<close>

theory utp_sfrd_rel
  imports utp_sfrd_core 
begin

subsection \<open> Healthiness Conditions \<close>
  
text \<open> CSP Reactive Relations \<close>
    
definition CRR :: "('s,'e) sfrd hrel \<Rightarrow> ('s,'e) sfrd hrel" where
[pred]: "CRR(P) = (\<exists> ref\<^sup>< \<Zspot> RR(P))"

expr_constructor CRR

lemma CRR_idem: "CRR(CRR(P)) = CRR(P)"
  by (pred_auto)

lemma Idempotent_CRR [closure]: "Idempotent CRR"
  by (simp add: CRR_idem Idempotent_def)

lemma Continuous_CRR [closure]: "Continuous CRR"
  by (pred_simp, blast)

lemma CRR_intro:
  assumes "$ref\<^sup>< \<sharp> P" "P is RR"
  shows "P is CRR"
  by (simp add: CRR_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma CRR_form: "CRR(P) = (\<exists> (ok\<^sup><, ok\<^sup>>, wait\<^sup><, wait\<^sup>>, ref\<^sup><) \<Zspot> (\<Sqinter> tt\<^sub>0. P\<lbrakk>\<guillemotleft>[]\<guillemotright>/tr\<^sup><\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> \<and> ($tr\<^sup>> = tr\<^sup>< @ \<guillemotleft>tt\<^sub>0\<guillemotright>)\<^sub>e))"
  by (pred_auto; fastforce)

lemma CRR_seqr_form: 
  "CRR(P) ;; CRR(Q) = 
    (\<Sqinter> tt\<^sub>1. \<Sqinter> tt\<^sub>2. ((\<exists> (ok\<^sup><, ok\<^sup>>, wait\<^sup><, wait\<^sup>>, ref\<^sup><) \<Zspot> P)\<lbrakk>\<guillemotleft>[]\<guillemotright>/tr\<^sup><\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup>>\<rbrakk> ;; 
                      (\<exists> (ok\<^sup><, ok\<^sup>>, wait\<^sup><, wait\<^sup>>, ref\<^sup><) \<Zspot> Q)\<lbrakk>\<guillemotleft>[]\<guillemotright>/tr\<^sup><\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup>>\<rbrakk> \<and> ($tr\<^sup>> = $tr\<^sup>< @ \<guillemotleft>tt\<^sub>1\<guillemotright> @ \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e))"
  by (simp add: CRR_form, pred_auto; fastforce)

text \<open> CSP Reactive Finalisers \<close>
    
definition CRF :: "('s,'e) sfrd hrel \<Rightarrow> ('s,'e) sfrd hrel" where
[pred]: "CRF(P) = (\<exists> ref\<^sup>> \<Zspot> CRR(P))"

lemma CRF_idem: "CRF(CRF(P)) = CRF(P)"
  by (pred_auto)

lemma Idempotent_CRF [closure]: "Idempotent CRF"
  by (simp add: CRF_idem Idempotent_def)

lemma Continuous_CRF [closure]: "Continuous CRF"
  by (pred_simp, blast)

lemma CRF_intro:
  assumes "$ref\<^sup>< \<sharp> P" "$ref\<^sup>> \<sharp> P" "P is RR"
  shows "P is CRF"
  by (simp add: CRF_def CRR_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma CRF_implies_CRR [closure]:
  assumes "P is CRF" shows "P is CRR"
proof -
  have "CRR(CRF(P)) = CRF(P)"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

definition crel_skip :: "('s, 'e) sfrd hrel" ("II\<^sub>c") where
[pred]: "crel_skip = ($tr\<^sup>> = $tr\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e"

declare zero_list_def [pred del]

declare zero_list_def [simp]

lemma crel_skip_CRR [closure]: "II\<^sub>c is CRF"
  by (pred_auto)

lemma crel_skip_via_rrel: "II\<^sub>c = CRR(II\<^sub>r)"
  by (pred_auto)

lemma crel_skip_left_unit [rpred]:  
  assumes "P is CRR" 
  shows "II\<^sub>c ;; P = P"
proof -
  have "II\<^sub>c ;; CRR(P) = CRR(P)" by (pred_auto)
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma crel_skip_right_unit [rpred]:  
  assumes "P is CRF" 
  shows "P ;; II\<^sub>c = P"
proof -
  have "CRF(P) ;; II\<^sub>c = CRF(P)" by (pred_auto)
  thus ?thesis by (simp add: Healthy_if assms)
qed

text \<open> CSP Reactive Conditions \<close>

definition CRC :: "('s,'e) sfrd hrel \<Rightarrow> ('s,'e) sfrd hrel" where
[pred]: "CRC(P) = (\<exists> ref\<^sup>< \<Zspot> RC(P))"

expr_constructor CRC

lemma CRC_intro:
  assumes "$ref\<^sup>< \<sharp> P" "P is RC"
  shows "P is CRC"
  by (simp add: CRC_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma CRC_intro':
  assumes "P is CRR" "P is RC"
  shows "P is CRC"
  by (metis CRC_def CRR_def Healthy_def RC_implies_RR assms)

lemma ref_unrest_RR [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> RR P"
  by (pred_auto, blast+)

lemma ref_unrest_RC1 [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> RC1 P"
  by (pred_auto, blast+)

lemma ref_unrest_RC [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> RC P"
  by (simp add: RC_R2_def ref_unrest_RC1 ref_unrest_RR)

lemma RR_ex_ref: "RR (\<exists> ref\<^sup>< \<Zspot> RR P) = (\<exists> ref\<^sup>< \<Zspot> RR P)"
  by (pred_auto)

lemma RC1_ex_ref: "RC1 (\<exists> ref\<^sup>< \<Zspot> RC1 P) = (\<exists> ref\<^sup>< \<Zspot> RC1 P)"
  by (pred_auto, meson dual_order.trans)

lemma ex_ref'_RR_closed [closure]: 
  assumes "P is RR"
  shows "(\<exists> ref\<^sup>> \<Zspot> P) is RR"
proof -
  have "RR (\<exists> ref\<^sup>> \<Zspot> RR(P)) = (\<exists> ref\<^sup>> \<Zspot> RR(P))"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma CRC_idem: "CRC(CRC(P)) = CRC(P)"
  apply (simp add: CRC_def ex_unrest  unrest)
  apply (simp add: RC_def RR_ex_ref)
  apply (metis (no_types, opaque_lifting) Healthy_def RC1_RR_closed RC1_ex_ref RR_ex_ref RR_idem)
done

lemma Idempotent_CRC [closure]: "Idempotent CRC"
  by (simp add: CRC_idem Idempotent_def)

subsection \<open> Closure Properties \<close>

lemma CRR_implies_RR [closure]: 
  assumes "P is CRR"
  shows "P is RR"
proof -
  have "RR(CRR(P)) = CRR(P)"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

lemma CRC_intro'':
  assumes "P is CRR" "P is RC1"
  shows "P is CRC"
  by (simp add: CRC_intro' CRR_implies_RR RC_intro' assms)

lemma CRC_implies_RR [closure]: 
  assumes "P is CRC" 
  shows "P is RR"
proof -
  have "RR(CRC(P)) = CRC(P)"
    by (pred_auto)
       (metis (no_types, lifting) Prefix_Order.prefixE Prefix_Order.prefixI append.assoc append_minus)+
  thus ?thesis
    by (metis Healthy_def assms)
qed
  
lemma CRC_implies_RC [closure]: 
  assumes "P is CRC"
  shows "P is RC"
proof -
  have "RC1(CRC(P)) = CRC(P)"
    by (pred_auto, meson dual_order.trans)
  thus ?thesis
    by (simp add: CRC_implies_RR Healthy_if RC1_def RC_intro assms)
qed

lemma CRR_unrest_ref [unrest]: "P is CRR \<Longrightarrow> $ref\<^sup>< \<sharp> P"
  by (metis CRR_def CRR_implies_RR Healthy_if ex_unrest_iff fst_vwb_lens ns_alpha_mwb ref_vwb_lens vwb_lens_mwb)

lemma CRF_unrest_ref' [unrest]: 
  assumes "P is CRF"
  shows "$ref\<^sup>> \<sharp> P"
proof -
  have "$ref\<^sup>> \<sharp> CRF(P)" by (simp add: CRF_def unrest)
  thus ?thesis by (simp add: assms Healthy_if)
qed

lemma CRC_implies_CRR [closure]:
  assumes "P is CRC"
  shows "P is CRR"
  apply (rule CRR_intro)
   apply (simp_all add: unrest assms closure)
  apply (metis CRC_def CRC_implies_RC Healthy_if assms ex_unrest_iff fst_vwb_lens ns_alpha_mwb ref_vwb_lens vwb_lens.axioms(2))
  done

lemma unrest_ref'_neg_RC [unrest]:
  assumes "P is RR" "P is RC"
  shows "$ref\<^sup>> \<sharp> P"
proof -
  have "$ref\<^sup>> \<sharp> (\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r)"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_if RC1_def RC_implies_RC1 assms(2))
qed

lemma rea_true_CRR [closure]: "true\<^sub>r is CRR"
  by (pred_auto)

lemma rea_true_CRC [closure]: "true\<^sub>r is CRC"
  by (pred_auto)

lemma false_CRR [closure]: "false is CRR"
  by (pred_auto)

lemma false_CRC [closure]: "false is CRC"
  by (pred_auto)

lemma st_pred_CRR [closure]: "[P]\<^sub>S\<^sub>< is CRR"
  by (pred_auto)

lemma st_post_unrest_ref' [unrest]: "$ref\<^sup>> \<sharp> [b]\<^sub>S\<^sub>>"
  by (pred_auto)

lemma st_post_CRR [closure]: "[b]\<^sub>S\<^sub>> is CRR"
  by (pred_auto)

lemma st_cond_CRC [closure]: "[P]\<^sub>S\<^sub>< is CRC"
  by (pred_auto)

lemma st_cond_CRF [closure]: "[b]\<^sub>S\<^sub>< is CRF"
  by (pred_auto)

lemma rea_rename_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "P\<lparr>f\<rparr>\<^sub>r is CRR"
proof -
  have "$ref\<^sup>< \<sharp> (CRR P)\<lparr>f\<rparr>\<^sub>r"
    by (pred_auto)
  thus ?thesis
    by (rule_tac CRR_intro, simp_all add: closure Healthy_if assms)
qed

lemma st_subst_CRR_closed [closure]:
  assumes "P is CRR"
  shows "(\<sigma> \<dagger>\<^sub>S P) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure assms)

lemma st_subst_CRC_closed [closure]:
  assumes "P is CRC"
  shows "(\<sigma> \<dagger>\<^sub>S P) is CRC"
  by (rule CRC_intro, simp_all add: closure assms unrest)

lemma conj_CRC_closed [closure]:
  "\<lbrakk> P is CRC; Q is CRC \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma conj_CRF_closed [closure]: "\<lbrakk> P is CRF; Q is CRF \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRF"
  by (rule CRF_intro, simp_all add: unrest closure)

lemma disj_CRC_closed [closure]:
  "\<lbrakk> P is CRC; Q is CRC \<rbrakk> \<Longrightarrow> (P \<or> Q) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma st_cond_left_impl_CRC_closed [closure]: 
  "P is CRC \<Longrightarrow> ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma unrest_ref_map_st [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> P \<up>\<^sub>2 map_st\<^sub>L[a]"
  by (pred_auto)

lemma unrest_ref'_map_st [unrest]: "$ref\<^sup>> \<sharp> P \<Longrightarrow> $ref\<^sup>> \<sharp> P \<up>\<^sub>2 map_st\<^sub>L[a]"
  by (pred_auto)

lemma unrest_ref_rdes_frame_ext [unrest]: 
  "\<lbrakk> vwb_lens a; $ref\<^sup>< \<sharp> P \<rbrakk> \<Longrightarrow> $ref\<^sup>< \<sharp> a:[P]\<^sub>r\<^sup>+"
  by (pred_simp, blast)

lemma unrest_ref'_rdes_frame_ext [unrest]: 
  "\<lbrakk> vwb_lens a; $ref\<^sup>> \<sharp> P \<rbrakk> \<Longrightarrow> $ref\<^sup>> \<sharp> a:[P]\<^sub>r\<^sup>+"
  by (pred_simp, blast)

lemma map_st_ext_CRR_closed [closure]:
  assumes "P is CRR"
  shows "P \<up>\<^sub>2 map_st\<^sub>L[a] is CRR"
  by (rule CRR_intro, simp_all add: closure unrest assms)

lemma map_st_ext_CRC_closed [closure]:
  assumes "vwb_lens a" "P is CRC"
  shows "P \<up>\<^sub>2 map_st\<^sub>L[a] is CRC"
  apply (rule CRC_intro, simp_all add: closure unrest assms)
  oops

 lemma rdes_frame_ext_CRR_closed [closure]:
  assumes "vwb_lens a" "P is CRR"
  shows "a:[P]\<^sub>r\<^sup>+ is CRR"
  by (rule CRR_intro, simp_all add: closure unrest assms)

lemma USUP_CRC_closed [closure]: "\<lbrakk> A \<noteq> {}; \<And> i. i \<in> A \<Longrightarrow> P i is CRC \<rbrakk> \<Longrightarrow> (\<Squnion> i \<in> A. P i) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma UINF_CRR_closed [closure]: "\<lbrakk> \<And> i. i \<in> A \<Longrightarrow> P i is CRR \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<in> A. P i) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)

lemma cond_CRC_closed [closure]:
  assumes "P is CRC" "Q is CRC"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is CRC"
  by (rule CRC_intro, simp_all add: closure assms unrest)
    
lemma USUP_ind_CRR_closed [closure]:
  assumes "\<And> i. P i is CRR"
  shows "(\<Squnion> i. P(i)) is CRR"
  by (rule CRR_intro, simp_all add: assms unrest closure)

lemma UINF_ind_CRR_closed [closure]:
  assumes "\<And> i. P i is CRR"
  shows "(\<Sqinter> i. P(i)) is CRR"
  by (rule CRR_intro, simp_all add: assms unrest closure)
   
lemma cond_tt_CRR_closed [closure]: 
  assumes "P is CRR" "Q is CRR"
  shows "P \<triangleleft> $tr\<^sup>> = $tr\<^sup>< \<triangleright> Q is CRR"
  by (rule CRR_intro, simp_all add: unrest assms closure unrest_ssubst_expr usubst usubst_eval)

lemma rea_implies_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<longrightarrow>\<^sub>r Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma conj_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma disj_CRR_closed [closure]: 
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<or> Q) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)

lemma rea_not_CRR_closed [closure]:
  "P is CRR \<Longrightarrow> (\<not>\<^sub>r P) is CRR"
  using false_CRR rea_implies_CRR_closed by fastforce
    
lemma cond_st_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<triangleleft> b \<triangleright>\<^sub>R Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma seq_CRR_closed [closure]:
  assumes "P is CRR" "Q is RR"
  shows "(P ;; Q) is CRR"
  by (rule CRR_intro, simp_all add: unrest assms closure)

lemma seq_CRF_closed [closure]:
  assumes "P is CRF" "Q is CRF"
  shows "(P ;; Q) is CRF"
  by (rule CRF_intro, simp_all add: unrest assms closure)

lemma rea_st_cond_CRF [closure]: "[b]\<^sub>S\<^sub>< is CRF"
  by (pred_auto)

lemma wp_rea_CRC [closure]: "\<lbrakk> P is CRR; Q is RC \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma USUP_ind_CRC_closed [closure]: 
  "\<lbrakk> \<And> i. P i is CRC \<rbrakk> \<Longrightarrow> (\<Squnion> i. P i) is CRC"
  by (metis CRC_implies_CRR CRC_implies_RC USUP_ind_CRR_closed USUP_ind_RC_closed false_CRC rea_not_CRR_closed wp_rea_CRC wp_rea_RC_false)

lemma tr_extend_seqr_lit [rdes]:
  fixes P :: "('s, 'e) sfrd hrel"
  assumes "$ok\<^sup>< \<sharp> P" "$wait\<^sup>< \<sharp> P" "$ref\<^sup>< \<sharp> P"
  shows "($tr\<^sup>> = $tr\<^sup>< @ [\<guillemotleft>a\<guillemotright>] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e ;; P = P\<lbrakk>$tr\<^sup>< @ [\<guillemotleft>a\<guillemotright>]/tr\<^sup><\<rbrakk>"
  using assms by (pred_auto, meson)

lemma tr_assign_comp [rdes]:
  fixes P :: "('s, 'e) sfrd hrel"
  assumes "$ok\<^sup>< \<sharp> P" "$wait\<^sup>< \<sharp> P" "$ref\<^sup>< \<sharp> P"
  shows "(($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S) ;; P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"
  using assms by (pred_auto, meson)    

(*
lemma RR_msubst_tt: "RR((P t)\<lbrakk>t\<rightarrow>&tt\<rbrakk>) = (RR (P t))\<lbrakk>t\<rightarrow>&tt\<rbrakk>"
  by (pred_auto)

lemma RR_msubst_ref': "RR((P r)\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) = (RR (P r))\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>"
  by (pred_auto)
    
lemma msubst_tt_RR [closure]: "\<lbrakk> \<And> t. P t is RR \<rbrakk> \<Longrightarrow> (P t)\<lbrakk>t\<rightarrow>&tt\<rbrakk> is RR"
  by (simp add: Healthy_def RR_msubst_tt)
    
lemma msubst_ref'_RR [closure]: "\<lbrakk> \<And> r. P r is RR \<rbrakk> \<Longrightarrow> (P r)\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> is RR"
  by (simp add: Healthy_def RR_msubst_ref')  
*)

lemma conj_less_tr_RR_closed [closure]:
  assumes "P is CRR"
  shows "(P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) is CRR"
proof -
  have "CRR(CRR(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) = (CRR(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)"
    apply (pred_auto, blast+)
    using less_le apply fastforce+
    done
  thus ?thesis
    by (metis (no_types, lifting) Healthy_def' assms)
qed

lemma R4_CRR_closed [closure]: "P is CRR \<Longrightarrow> R4(P) is CRR"
  by (simp add: R4_def conj_less_tr_RR_closed)

lemma R5_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "R5(P) is CRR"
proof -
  have "R5(CRR(P)) is CRR"
    by (pred_auto; blast)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma conj_eq_tr_RR_closed [closure]:
  assumes "P is CRR"
  shows "(P \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) is CRR"
proof -
  have "CRR(CRR(P) \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) = (CRR(P) \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e)"
    by (pred_auto, blast+)
  thus ?thesis
    by (metis (no_types, lifting) Healthy_def' assms)
qed

(*
lemma all_ref_CRC_closed [closure]: 
  "P is CRC \<Longrightarrow> (\<forall> $ref \<bullet> P) is CRC"
  by (simp add: CRC_implies_CRR CRR_unrest_ref all_unrest)
*)

lemma ex_ref_CRR_closed [closure]: 
  "P is CRR \<Longrightarrow> (\<exists> ref\<^sup>< \<Zspot> P) is CRR"
  by (simp add: CRR_unrest_ref ex_unrest)

lemma ex_st'_CRR_closed [closure]: 
  "P is CRR \<Longrightarrow> (\<exists> st\<^sup>> \<Zspot> P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)

lemma ex_ref'_CRR_closed [closure]: 
  "P is CRR \<Longrightarrow> (\<exists> ref\<^sup>> \<Zspot> P) is CRR"
  by (metis CRF_def CRF_idem CRF_implies_CRR Healthy_def)

subsection \<open> Introduction laws \<close>

text \<open> Extensionality principles for introducing refinement and equality of Circus reactive 
  relations. It is necessary only to consider a subset of the variables that are present. \<close>

lemma CRR_refine_ext:
  assumes 
    "P is CRR" "Q is CRR"
    "\<And> t s s' r'. P\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk> \<sqsubseteq> Q\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk>"
  shows "P \<sqsubseteq> Q"
proof -
  have "\<And> t s s' r'. (CRR P)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk>
                    \<sqsubseteq> (CRR Q)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk>"
    using assms by (simp add: Healthy_if)
  hence "CRR P \<sqsubseteq> CRR Q"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemma CRC_refine_ext:
  assumes 
    "P is CRC" "Q is CRC"
    "\<And> t s s' r'. P\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><\<rbrakk> \<sqsubseteq> Q\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><\<rbrakk>"
  shows "P \<sqsubseteq> Q"
proof -
  have "\<And> t s s' r'. (CRC P)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><\<rbrakk>
                    \<sqsubseteq> (CRC Q)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><\<rbrakk>"
    using assms by (simp add: Healthy_if)
  hence "CRC P \<sqsubseteq> CRC Q"
    by (pred_auto, metis (no_types, opaque_lifting) Healthy_def assms(1,2))
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemma CRR_eq_ext:
  assumes 
    "P is CRR" "Q is CRR"
    "\<And> t s s' r'. P\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk> = Q\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk>"
  shows "P = Q"
proof -
  have "\<And> t s s' r'. (CRR P)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk> 
                    = (CRR Q)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk>"
    using assms by (simp add: Healthy_if)
  hence "CRR P = CRR Q"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemma refine_prop_intro:
  assumes "\<Sigma> \<sharp> P" "\<Sigma> \<sharp> Q" "`Q` \<Longrightarrow> `P`"
  shows "P \<sqsubseteq> Q"
  using assms by (pred_auto)

lemma CRR_refine_impl_prop:
  assumes "P is CRR" "Q is CRR" 
    "\<And> t s s' r'. `Q\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk>` \<Longrightarrow> `P\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup>>\<rbrakk>`"
  shows "P \<sqsubseteq> Q"
  using assms
  apply (rule_tac CRR_refine_ext, simp_all add: closure unrest usubst)
  apply (rule refine_prop_intro, simp_all add: unrest unrest_all_circus_vars closure)
  apply (simp add: SEXP_def)
  done

lemma CRC_refine_impl_prop:
  assumes "P is CRC" "Q is CRC" 
    "\<And> t s s' r'. `Q\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><\<rbrakk>` \<Longrightarrow> `P\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>/tr\<^sup><,tr\<^sup>>,st\<^sup><\<rbrakk>`"
  shows "P \<sqsubseteq> Q"
  using assms
  apply (rule_tac CRC_refine_ext, simp_all add: closure unrest usubst)
  apply (rule refine_prop_intro, simp_all add: unrest unrest_pre_circus_vars closure)
  apply (simp add: SEXP_def)
  done

subsection \<open> UTP Theory \<close>

interpretation crf_theory: utp_theory_kleene CRF II\<^sub>c
  rewrites "P \<in> carrier crf_theory.thy_order \<longleftrightarrow> P is CRF"
  and "le rrel_theory.thy_order = (\<sqsubseteq>)"
  and "eq rrel_theory.thy_order = (=)"  
  and crf_top: "crf_theory.utp_top = false"
  and crf_bottom: "crf_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous CRF
    by (unfold_locales, simp_all add: add: Idempotent_CRF Continuous_CRF)
  show top:"utp_top = false"
    by (simp add: healthy_top, pred_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, pred_auto)
  show "utp_theory_kleene CRF II\<^sub>c"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)
  
abbreviation crf_star :: "_ \<Rightarrow> _"  ("_\<^sup>\<star>\<^sup>c" [999] 999) where
"P\<^sup>\<star>\<^sup>c \<equiv> crf_theory.utp_star P"

lemma crf_star_as_rea_star:
  "P is CRF \<Longrightarrow> P\<^sup>\<star>\<^sup>c = P\<^sup>\<star>\<^sup>r ;; II\<^sub>c"
  by (simp add: crf_theory.Star_alt_def rrel_theory.Star_alt_def closure rpred unrest upred_semiring.distrib_right)

lemma crf_star_inductl: "R is CRR \<Longrightarrow> Q \<sqsubseteq> (P ;; Q) \<sqinter> R \<Longrightarrow> Q \<sqsubseteq> P\<^sup>\<star>\<^sup>c ;; R"
  by (simp add: crel_skip_left_unit crf_theory.utp_star_def upred_semiring.mult_assoc ustar_inductl)

subsection \<open> Weakest Precondition \<close>

lemma nil_least [simp]:
  "(\<guillemotleft>[]\<guillemotright> \<le> x)\<^sub>e = true" by pred_auto

(*
lemma minus_nil [simp]:
  "xs - [] = xs" by pred_auto
*)

lemma wp_rea_circus_lemma_1:
  assumes "P is CRR" "$ref\<^sup>> \<sharp> P"
  shows "out\<alpha> \<sharp> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk>"
proof -
  have "out\<alpha> \<sharp> (CRR (\<exists> ref\<^sup>> \<Zspot> P))\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk>"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2) ex_unrest)
qed

lemma wp_rea_circus_lemma_2:
  assumes "P is CRR"
  shows "in\<alpha> \<sharp> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk>"
proof -
  have "in\<alpha> \<sharp> (CRR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk>"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms ex_unrest)
qed

text \<open> The meaning of reactive weakest precondition for Circus. @{term "P wp\<^sub>r Q"} means that,
  whenever $P$ terminates in a state @{term s\<^sub>0} having done the intersfrd hrel trace @{term t\<^sub>0}, which 
  is a prefix of the overall trace, then $Q$ must be satisfied. This in particular means that
  the remainder of the trace after @{term t\<^sub>0} must not be a divergent behaviour of $Q$. \<close>

lemma wp_rea_circus_form:
  assumes "P is CRR" "$ref\<^sup>> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<Squnion> (s\<^sub>0,t\<^sub>0). (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<longrightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk>)"
proof -
  have "(P wp\<^sub>r Q) = (\<not>\<^sub>r (\<Sqinter> t\<^sub>0. (P\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/tr\<^sup><\<rbrakk>) \<and> (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e))"
    by (simp add: wp_rea_def R2_tr_middle closure assms)
  also have "... = (\<not>\<^sub>r (\<Sqinter> (s\<^sub>0,t\<^sub>0). P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk> \<and> (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e))"
    by (pred_simp, blast)
  also have "... = (\<not>\<^sub>r (\<Sqinter> (s\<^sub>0,t\<^sub>0). P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<and> (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk> \<and> (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e))"
    by (simp add: seqr_to_conj add: wp_rea_circus_lemma_1 wp_rea_circus_lemma_2 assms closure pred_ba.inf.commute pred_ba.inf.left_commute)
  also have "... = (\<Squnion> (s\<^sub>0,t\<^sub>0). \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<or> \<not>\<^sub>r (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk> \<or> \<not>\<^sub>r (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e)"
    by (pred_auto)
  also have "... = (\<Squnion> (s\<^sub>0,t\<^sub>0). \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<or> \<not>\<^sub>r (\<not>\<^sub>r RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk> \<or> \<not>\<^sub>r (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e)"
    by (simp add: Healthy_if assms closure)
  also have "... = (\<Squnion> (s\<^sub>0,t\<^sub>0). \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<or> (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk> \<or> \<not>\<^sub>r (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e)"
    by (pred_auto)
  also have "... = (\<Squnion> (s\<^sub>0,t\<^sub>0). (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<longrightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk>)"
    by (pred_auto)
  also have "... = (\<Squnion> (s\<^sub>0,t\<^sub>0). (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<longrightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk>)"
    by (simp add: Healthy_if assms closure)
  finally show ?thesis .
qed

lemma wp_rea_circus_form_alt:
  assumes "P is CRR" "$ref\<^sup>> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<Squnion> (s\<^sub>0,t\<^sub>0). ($tr\<^sup>< @ \<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> 
                                \<longrightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(tt-\<guillemotleft>t\<^sub>0\<guillemotright>)/st\<^sup><,tr\<^sup><,tr\<^sup>>\<rbrakk>))"
proof -
  have "(P wp\<^sub>r Q) = R2(P wp\<^sub>r Q)"
    by (simp add: CRC_implies_RR CRR_implies_RR Healthy_if RR_implies_R2 assms wp_rea_R2_closed)
  also have "... = R2(\<Squnion> (s\<^sub>0,t\<^sub>0). (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup>>\<rbrakk> \<longrightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><\<rbrakk>)"
    by (simp add: wp_rea_circus_form assms closure Healthy_if)
  also have "... = (\<Sqinter> tt\<^sub>0. (\<Squnion> (s\<^sub>0,tr\<^sub>0). (\<guillemotleft>tr\<^sub>0\<guillemotright> \<le> \<guillemotleft>tt\<^sub>0\<guillemotright>)\<^sub>e \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> 
                                        \<longrightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><,tr\<^sup>>\<rbrakk>) 
                                         \<and> ($tr\<^sup>> = $tr\<^sup>< @ \<guillemotleft>tt\<^sub>0\<guillemotright>)\<^sub>e)"
    by (simp add: R2_form, pred_auto)
  also have "... = (\<Sqinter> tt\<^sub>0. (\<Squnion> (s\<^sub>0,tr\<^sub>0). (\<guillemotleft>tr\<^sub>0\<guillemotright> \<le> \<guillemotleft>tt\<^sub>0\<guillemotright>)\<^sub>e \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> 
                                        \<longrightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0-tr\<^sub>0\<guillemotright>/st\<^sup><,tr\<^sup><,tr\<^sup>>\<rbrakk>) 
                                         \<and> ($tr\<^sup>> = $tr\<^sup>< @ \<guillemotleft>tt\<^sub>0\<guillemotright>)\<^sub>e)"
    by (pred_auto)
  also have "... = (\<Sqinter> tt\<^sub>0. (\<Squnion> (s\<^sub>0,tr\<^sub>0). ($tr\<^sup>< @ \<guillemotleft>tr\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> 
                                        \<longrightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(tt-\<guillemotleft>tr\<^sub>0\<guillemotright>)/st\<^sup><,tr\<^sup><,tr\<^sup>>\<rbrakk>) 
                                         \<and> ($tr\<^sup>> = $tr\<^sup>< @ \<guillemotleft>tt\<^sub>0\<guillemotright>)\<^sub>e)"
    by (pred_auto, (metis list_concat_minus_list_concat plus_list_def)+)
  also have "... = (\<Squnion> (s\<^sub>0,tr\<^sub>0). ($tr\<^sup>< @ \<guillemotleft>tr\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> 
                                        \<longrightarrow>\<^sub>r R1((RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(tt-\<guillemotleft>tr\<^sub>0\<guillemotright>)/st\<^sup><,tr\<^sup><,tr\<^sup>>\<rbrakk>))"
    by (pred_auto, blast+)
  also have "... = (\<Squnion> (s\<^sub>0,t\<^sub>0). ($tr\<^sup>< @ \<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>>)\<^sub>e \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> 
                               \<longrightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(tt-\<guillemotleft>t\<^sub>0\<guillemotright>)/st\<^sup><,tr\<^sup><,tr\<^sup>>\<rbrakk>))"
    by (simp add: Healthy_if assms closure)
  finally show ?thesis .
qed

(*
lemma wp_rea_circus_form_alt:
  assumes "P is CRR" "$ref\<^sup>> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr @ \<guillemotleft>t\<^sub>0\<guillemotright> \<le> $tr\<^sup>> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> 
                               \<longrightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(&tt-\<guillemotleft>t\<^sub>0\<guillemotright>)/st\<^sup><,tr\<^sup><,tr\<^sup>>\<rbrakk>))"
  oops
*)

subsection \<open> Trace Substitution \<close>

definition trace_subst  
where [pred]: "trace_subst P v = (P\<lbrakk>(tt-\<lceil>v\<rceil>\<^sub>S\<^sub><)/tt\<rbrakk> \<and> ($tr\<^sup>< + \<lceil>v\<rceil>\<^sub>S\<^sub>< \<le> $tr\<^sup>>)\<^sub>e)"

syntax "_trace_subst" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<lbrakk>_\<rbrakk>\<^sub>t" [999,0] 999)
translations "_trace_subst P v" == "CONST trace_subst P (v)\<^sub>e"

lemma unrest_trace_subst [unrest]:
  "\<lbrakk> vwb_lens x; x \<bowtie> (tr\<^sup><)\<^sub>v; x \<bowtie> (tr\<^sup>>)\<^sub>v; x \<bowtie> (st\<^sup><)\<^sub>v; $x \<sharp> P \<rbrakk> \<Longrightarrow> $x \<sharp> P\<lbrakk>v\<rbrakk>\<^sub>t"
  by (pred_simp, expr_simp add: lens_indep_def)
  
lemma trace_subst_RR_closed [closure]:
  assumes "P is RR"
  shows "P\<lbrakk>v\<rbrakk>\<^sub>t is RR"
proof -
  have "(RR P)\<lbrakk>v\<rbrakk>\<^sub>t is RR"
    apply (pred_auto)
    apply (metis diff_add_cancel_left' trace_class.add_left_mono)
    apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
    using le_add order_trans apply blast
  done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma trace_subst_CRR_closed [closure]:
  assumes "P is CRR"
  shows "P\<lbrakk>v\<rbrakk>\<^sub>t is CRR"
  by (rule CRR_intro, simp_all add: closure assms unrest)

lemma tsubst_nil [usubst]: 
  assumes "P is CRR"
  shows "P\<lbrakk>\<guillemotleft>[]\<guillemotright>\<rbrakk>\<^sub>t = P"
proof -
  have "(CRR P)\<lbrakk>\<guillemotleft>[]\<guillemotright>\<rbrakk>\<^sub>t = CRR P"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma tsubst_false [usubst]: "false\<lbrakk>y\<rbrakk>\<^sub>t = false"
  by pred_auto

lemma cond_rea_tt_subst [usubst]:
  "(P \<triangleleft> b \<triangleright>\<^sub>R Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<triangleleft> b \<triangleright>\<^sub>R Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (pred_auto)
        
lemma tsubst_conj [usubst]: "(P \<and> Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<and> Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (pred_auto)

lemma tsubst_disj [usubst]: "(P \<or> Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<or> Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (pred_auto)
    
lemma rea_subst_R1_closed [closure]: "P\<lbrakk>v\<rbrakk>\<^sub>t is R1"
  apply (pred_auto) using le_add order.trans by blast
  
lemma tsubst_UINF_ind [usubst]: "(\<Sqinter> i. P(i))\<lbrakk>v\<rbrakk>\<^sub>t = (\<Sqinter> i. (P(i))\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (pred_auto)

subsection \<open> Initial Intersfrd hrel \<close>

definition rea_init :: "'s pred \<Rightarrow> ('t::trace, 's) expr \<Rightarrow> ('s, 't, '\<alpha>, '\<beta>) rsp_rel" where
[pred]: "rea_init s t = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<not>\<^sub>r ($tr\<^sup>< + \<lceil>t\<rceil>\<^sub>S\<^sub>< \<le> $tr\<^sup>>)\<^sub>e)" 

syntax "_rea_init" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<I>'(_,_')")
translations "_rea_init s t" == "CONST rea_init (s)\<^sub>e (t)\<^sub>e"
syntax_consts "_rea_init" == "rea_init"

lemma usubst_rea_init' [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<I>(s,t) = \<I>(\<sigma>\<dagger>s,\<sigma>\<dagger>t)"
  by (pred_auto)

lemma unrest_rea_init [unrest]:
  "\<lbrakk> vwb_lens x; x \<bowtie> (tr\<^sup><)\<^sub>v; x \<bowtie> (tr\<^sup>>)\<^sub>v; x \<bowtie> (st\<^sup><)\<^sub>v \<rbrakk> \<Longrightarrow> $x \<sharp> \<I>(s,t)"
  by (pred_simp, expr_simp add: lens_indep_def)

lemma rea_init_R1 [closure]: "\<I>(s,t) is R1"
  by (pred_auto)

lemma rea_init_R2c [closure]: "\<I>(s,t) is R2c"
  apply (pred_auto)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
done

lemma rea_init_R2 [closure]: "\<I>(s,t) is R2"
  by (metis Healthy_def R1_R2c_is_R2 rea_init_R1 rea_init_R2c)
 
lemma csp_init_RR [closure]: "\<I>(s,t) is RR"
  apply (pred_auto)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
done

lemma csp_init_CRR [closure]: "\<I>(s,t) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)

lemma rea_init_RC [closure]: "\<I>(s,t) is CRC"
  apply (pred_auto) by fastforce

lemma rea_init_false [rpred]: "\<I>(False, t) = true\<^sub>r"
  by (pred_auto)

lemma rea_init_nil [rpred]: "\<I>(s,\<guillemotleft>[]\<guillemotright>) = [\<not> s]\<^sub>S\<^sub><"
  by (pred_auto)

lemma rea_not_init [rpred]: "(\<not>\<^sub>r \<I>(P,\<guillemotleft>[]\<guillemotright>)) = \<I>(\<not>P,\<guillemotleft>[]\<guillemotright>)"
  by (pred_auto)
       
lemma rea_init_conj [rpred]:
  "(\<I>(s\<^sub>1,t) \<and> \<I>(s\<^sub>2,t)) = \<I>(s\<^sub>1\<or>s\<^sub>2,t)"
  by (pred_auto)
    
lemma rea_init_disj_same [rpred]: "(\<I>(s\<^sub>1,t) \<or> \<I>(s\<^sub>2,t)) = \<I>(s\<^sub>1 \<and> s\<^sub>2, t)"
  by (pred_auto)

(*
lemma R4_csp_init [rpred]: "R4(\<I>(s,bop Cons x xs)) = \<I>(s,bop Cons x xs)"
  using less_list_def apply (pred_auto)

lemma R5_csp_init [rpred]: "R5(\<I>(s,bop Cons x xs)) = false"
  by (pred_auto)

lemma R4_trace_subst [rpred]:
  "R4 (P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t) = P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t"
  using le_imp_less_or_eq by (rel_blast)

lemma R5_trace_subst [rpred]:
  "R5 (P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t) = false"
  by (pred_auto)
*)

subsection \<open> Enabled Events \<close>

definition csp_enable :: "'s pred \<Rightarrow> ('e list, 's) expr \<Rightarrow> ('e set, 's) expr \<Rightarrow> ('s, 'e) sfrd hrel" where
[pred]: "csp_enable s t E = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup>< @ \<lceil>t\<rceil>\<^sub>S\<^sub><)\<^sub>e \<and> (\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub><. \<guillemotleft>e\<guillemotright> \<notin> $ref\<^sup>>)\<^sub>e)"

syntax "_csp_enable" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<E>'(_, _, _')")
translations "_csp_enable s t E" == "CONST csp_enable (s)\<^sub>e (t)\<^sub>e (E)\<^sub>e"
syntax_consts "_csp_enable" == csp_enable

text \<open> Predicate @{term "\<E>(s, t, E)"} states that, if the initial state satisfies predicate @{term s},
  then @{term t} is a possible (failure) trace, such that the events in the set @{term E} are enabled
  after the given intersfrd hrel. \<close>

lemma csp_enable_R1_closed [closure]: "\<E>(s,t,E) is R1"
  by (pred_auto)

lemma csp_enable_R2_closed [closure]: "\<E>(s,t,E) is R2c"
  by (pred_auto)
    
lemma csp_enable_RR [closure]: "\<E>(s,t,E) is CRR"
  by (pred_auto)

lemma tsubst_csp_enable [usubst]: "\<E>(s,t\<^sub>2,e)\<lbrakk>t\<^sub>1\<rbrakk>\<^sub>t = \<E>(s,t\<^sub>1@t\<^sub>2,e)"
  apply (pred_auto)
  apply (metis add.assoc diff_add_cancel_left' plus_list_def trace_class.add_diff_cancel_left)
  apply (simp add: list_concat_minus_list_concat plus_list_def)
done

lemma csp_enable_unrests [unrest]:
  "\<lbrakk> vwb_lens x; x \<bowtie> (tr\<^sup><)\<^sub>v; x \<bowtie> (tr\<^sup>>)\<^sub>v; x \<bowtie> (st\<^sup><)\<^sub>v; x \<bowtie> (ref\<^sup>>)\<^sub>v \<rbrakk> \<Longrightarrow> $x \<sharp> \<E>(s,t,e)"
  by (pred_simp, expr_simp add: lens_indep_def)

lemma st_unrest_csp_enable [unrest]: "\<lbrakk> $\<^bold>v \<sharp> s; $\<^bold>v \<sharp> t; $\<^bold>v \<sharp> E \<rbrakk> \<Longrightarrow> $st\<^sup>< \<sharp> \<E>(s, t, E)" 
  by (pred_simp, expr_simp add: lens_indep_def, blast)

lemma csp_enable_tr'_eq_tr [rpred]:
  "\<E>(s,\<guillemotleft>[]\<guillemotright>,r) \<triangleleft> $tr\<^sup>> = $tr\<^sup>< \<triangleright> false = \<E>(s,\<guillemotleft>[]\<guillemotright>,r)"
  by (pred_auto)
    
lemma csp_enable_st_pred [rpred]: 
  "([s\<^sub>1]\<^sub>S\<^sub>< \<and> \<E>(s\<^sub>2,t,E)) = \<E>(s\<^sub>1 \<and> s\<^sub>2,t,E)"
  by (pred_auto)

lemma csp_enable_conj [rpred]:
  "(\<E>(s, t, E\<^sub>1) \<and> \<E>(s, t, E\<^sub>2)) = \<E>(s, t, E\<^sub>1 \<union> E\<^sub>2)"
  by (pred_auto)

lemma csp_enable_cond [rpred]:
  "\<E>(s\<^sub>1, t\<^sub>1, E\<^sub>1) \<triangleleft> b \<triangleright>\<^sub>R \<E>(s\<^sub>2, t\<^sub>2, E\<^sub>2) = \<E>(s\<^sub>1 \<triangleleft> b \<triangleright> s\<^sub>2, t\<^sub>1 \<triangleleft> b \<triangleright> t\<^sub>2, E\<^sub>1 \<triangleleft> b \<triangleright> E\<^sub>2)"
  by (pred_auto)

lemma csp_enable_rea_assm [rpred]: 
  "[b]\<^sup>\<top>\<^sub>r ;; \<E>(s,t,E) = \<E>(b\<and>s,t,E)"
  by (pred_auto)

lemma csp_enable_tr_empty: "\<E>(True, [], {v}) = ($tr\<^sup>> = $tr\<^sup>< \<and> \<lceil>v\<rceil>\<^sub>S\<^sub>< \<notin> $ref\<^sup>>)\<^sub>e"
  by (pred_auto)

lemma csp_enable_nothing: "\<E>(True, [], {}) = ($tr\<^sup>> = $tr\<^sup><)\<^sub>e"
  by (pred_auto)

(*
lemma msubst_nil_csp_enable [usubst]: 
  "\<E>(s(x),t(x),E(x))\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk> = \<E>(s(x)\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk>,t(x)\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk>,E(x)\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk>)"
  by (pred_auto)

lemma msubst_csp_enable [usubst]: 
  "\<E>(s(x),t(x),E(x))\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk> = \<E>(s(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,t(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,E(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (pred_auto)
*)

lemma csp_enable_false [rpred]: "\<E>(False,t,E) = false"
  by (pred_auto)

lemma conj_csp_enable [rpred]: "(\<E>(b\<^sub>1, t, E\<^sub>1) \<and> \<E>(b\<^sub>2, t, E\<^sub>2)) = \<E>(b\<^sub>1 \<and> b\<^sub>2, t, E\<^sub>1 \<union> E\<^sub>2)"
  by (pred_auto)

lemma refine_csp_enable: "\<E>(b\<^sub>1, t, E\<^sub>1) \<sqsubseteq> \<E>(b\<^sub>2, t, E\<^sub>2) \<longleftrightarrow> (`b\<^sub>2 \<longrightarrow> b\<^sub>1 \<and> E\<^sub>1 \<subseteq> E\<^sub>2`)"
  by (pred_simp, blast)

lemma USUP_csp_enable [rpred]:
  "(\<Squnion> x. \<E>(s, t, A(x))) = \<E>(s, t, (\<Sqinter> x. A(x)))"
  by (pred_auto)

lemma R4_csp_enable_nil [rpred]:
  "R4(\<E>(s, \<guillemotleft>[]\<guillemotright>, E)) = false"
  by (pred_auto)

lemma R5_csp_enable_nil [rpred]:
  "R5(\<E>(s, \<guillemotleft>[]\<guillemotright>, E)) = \<E>(s, \<guillemotleft>[]\<guillemotright>, E)"
  by (pred_auto)

lemma R4_csp_enable_Cons [rpred]: 
  "R4(\<E>(s,x # xs, E)) = \<E>(s,x # xs, E)"
  by (pred_auto, simp add: Prefix_Order.strict_prefixI')

lemma R5_csp_enable_Cons [rpred]: 
  "R5(\<E>(s,x # xs, E)) = false"
  by (pred_auto)

lemma rel_aext_csp_enable [alpha]: 
  "vwb_lens a \<Longrightarrow> \<E>(s, t, E) \<up>\<^sub>2 map_st\<^sub>L[a] = \<E>(s \<up> a, t \<up> a, E \<up> a)"
  by (pred_auto)

subsection \<open> Completed Trace Intersfrd hrel \<close>

definition csp_do :: "'s pred \<Rightarrow> 's subst \<Rightarrow> ('e list, 's) expr \<Rightarrow> ('s, 'e) sfrd hrel" where
[pred]: "csp_do s \<sigma> t = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup>< @ \<lceil>t\<rceil>\<^sub>S\<^sub><)\<^sub>e \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)"

syntax "_csp_do" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<Phi>'(_,_,_')")
translations "_csp_do s \<sigma> t" == "CONST csp_do (s)\<^sub>e \<sigma> (t)\<^sub>e"
syntax_consts "_csp_do" == csp_do

lemma csp_do_eq_intro:
  assumes "s\<^sub>1 = s\<^sub>2" "\<sigma>\<^sub>1 = \<sigma>\<^sub>2" "t\<^sub>1 = t\<^sub>2"
  shows "\<Phi>(s\<^sub>1, \<sigma>\<^sub>1, t\<^sub>1) = \<Phi>(s\<^sub>2, \<sigma>\<^sub>2, t\<^sub>2)"
  by (simp add: assms)

text \<open> Predicate @{term "\<Phi>(s,\<sigma>,t)"} states that if the initial state satisfies @{term s}, and
  the trace @{term t} is performed, then afterwards the state update @{term \<sigma>} is executed. \<close>

lemma unrest_csp_do [unrest]: 
  "\<lbrakk> vwb_lens x; x \<bowtie> (tr\<^sup><)\<^sub>v; x \<bowtie> (tr\<^sup>>)\<^sub>v; x \<bowtie> (st\<^sup><)\<^sub>v; x \<bowtie> (st\<^sup>>)\<^sub>v \<rbrakk> \<Longrightarrow> $x \<sharp> \<Phi>(s,\<sigma>,t)"
  by (pred_simp, expr_simp add: lens_indep_def)
    
lemma csp_do_CRF [closure]: "\<Phi>(s,\<sigma>,t) is CRF"
  by (pred_auto)

lemma csp_do_R4_closed [closure]:
  "\<Phi>(b,\<sigma>, x # xs) is R4"
  by (pred_auto, simp add: Prefix_Order.strict_prefixI')

lemma st_pred_conj_csp_do [rpred]: 
  "([b]\<^sub>S\<^sub>< \<and> \<Phi>(s,\<sigma>,t)) = \<Phi>(b \<and> s,\<sigma>,t)"
  by (pred_auto)

lemma trea_subst_csp_do [usubst]:
  "(\<Phi>(s,\<sigma>,t\<^sub>2))\<lbrakk>t\<^sub>1\<rbrakk>\<^sub>t = \<Phi>(s,\<sigma>,t\<^sub>1 @ t\<^sub>2)"
  apply (pred_auto)
  apply (metis add_monoid_diff_cancel_left append_assoc diff_add_cancel_left' plus_list_def)
  apply (simp add: list_concat_minus_list_concat plus_list_def)
  done

lemma st_subst_csp_do [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<Phi>(s,\<rho>,t) = \<Phi>(\<sigma> \<dagger> s,\<rho> \<circ>\<^sub>s \<sigma>,\<sigma> \<dagger> t)"
  by (pred_auto)

lemma csp_do_nothing: "\<Phi>(True,[\<leadsto>],\<guillemotleft>[]\<guillemotright>) = II\<^sub>c"
  by (pred_auto)

lemma csp_do_nothing_0: "\<Phi>(True,[\<leadsto>],0) = II\<^sub>c"
  by (pred_auto)

lemma csp_do_false [rpred]: "\<Phi>(False,s,t) = false"
  by (pred_auto)
            
lemma subst_state_csp_enable [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<E>(s,t\<^sub>2,e) = \<E>(\<sigma> \<dagger> s, \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> e)"
  by (pred_auto)
    
lemma csp_do_assign_enable [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<E>(s\<^sub>2,t\<^sub>2,e) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ (\<sigma> \<dagger> t\<^sub>2), (\<sigma> \<dagger> e))"
  by (pred_auto)

lemma csp_do_assign_do [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<Phi>(s\<^sub>2,\<rho>,t\<^sub>2) = \<Phi>(s\<^sub>1 \<and> (\<sigma> \<dagger> s\<^sub>2), \<rho> \<circ>\<^sub>s \<sigma>, t\<^sub>1 @ (\<sigma> \<dagger> t\<^sub>2))"
  by (pred_auto)

lemma csp_do_cond [rpred]:
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) \<triangleleft> b \<triangleright>\<^sub>R \<Phi>(s\<^sub>2,\<rho>,t\<^sub>2) = \<Phi>(s\<^sub>1 \<triangleleft> b \<triangleright> s\<^sub>2, \<sigma> \<triangleleft> b \<triangleright> \<rho>, t\<^sub>1 \<triangleleft> b \<triangleright> t\<^sub>2)"
  by (pred_auto)

lemma rea_assm_csp_do [rpred]: 
  "[b]\<^sup>\<top>\<^sub>r ;; \<Phi>(s,\<sigma>,t) = \<Phi>(b\<and>s,\<sigma>,t)"
  by (pred_auto)

lemma csp_do_comp:
  assumes "P is CRR"
  shows "\<Phi>(s,\<sigma>,t) ;; P = ([s]\<^sub>S\<^sub>< \<and> (\<sigma> \<dagger>\<^sub>S P)\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,\<sigma>,t) ;; (CRR P) = ([s]\<^sub>S\<^sub>< \<and> ((\<sigma> \<dagger>\<^sub>S CRR P))\<lbrakk>t\<rbrakk>\<^sub>t)"
    by (pred_auto, (metis plus_list_def)+)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma csp_do_iter: "(;; x \<leftarrow> xs. \<Phi>(True,[\<leadsto>],[\<guillemotleft>x\<guillemotright>])) = (if xs = [] then II else \<Phi>(True,[\<leadsto>],\<guillemotleft>xs\<guillemotright>))"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis by (simp del: SEXP_apply)
  next
    case False
    then show ?thesis by (simp del: SEXP_apply add: Cons rpred usubst, pred_simp)
  qed
qed

lemma csp_do_iter_seq [rpred]: 
  assumes "P is CRR"
  shows "(;; x \<leftarrow> xs. \<Phi>(True,[\<leadsto>],[\<guillemotleft>x\<guillemotright>])) ;; P = (\<Phi>(True,[\<leadsto>],\<guillemotleft>xs\<guillemotright>) ;; P)"
  by (metis assms crel_skip_left_unit csp_do_iter csp_do_nothing_0 seqr_left_unit
      zero_list_def)

lemma wp_rea_csp_do_lemma:
  fixes P :: "('\<sigma>, '\<phi>) sfrd hrel"
  assumes "$ok\<^sup>< \<sharp> P" "$wait\<^sup>< \<sharp> P" "$ref\<^sup>< \<sharp> P"
  shows "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> ($tr\<^sup>> = $tr\<^sup>< @ \<lceil>t\<rceil>\<^sub>S\<^sub><)\<^sub>e) ;; P = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>$tr\<^sup>< @ \<lceil>t\<rceil>\<^sub>S\<^sub></tr\<^sup><\<rbrakk>"
  using assms by (pred_auto, meson)

text \<open> This operator sets an upper bound on the permissible traces, when starting from a particular state \<close>

lemma wp_rea_csp_do [wp]:
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) wp\<^sub>r \<I>(s\<^sub>2,t\<^sub>2) = \<I>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2)"
  by (pred_auto)

lemma wp_rea_csp_do_false' [wp]:
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) wp\<^sub>r false = \<I>(s\<^sub>1, t\<^sub>1)"
  by (pred_auto)

lemma st_pred_impl_csp_do_wp [rpred]:
  "([s\<^sub>1]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<Phi>(s\<^sub>2,\<sigma>,t) wp\<^sub>r P) = \<Phi>(s\<^sub>1\<and>s\<^sub>2,\<sigma>,t) wp\<^sub>r P"
  by (pred_auto)

lemma csp_do_seq_USUP_distl [rpred]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P(i) is CRR" "A \<noteq> {}"
  shows "\<Phi>(s,\<sigma>,t) ;; (\<Squnion> i\<in>A. P(i)) = (\<Squnion> i\<in>A. \<Phi>(s,\<sigma>,t) ;; P(i))"
proof -
  from assms(2) have "\<Phi>(s,\<sigma>,t) ;; (\<Squnion> i\<in>A. CRR(P(i))) = (\<Squnion> i\<in>A. \<Phi>(s,\<sigma>,t) ;; CRR(P(i)))"
    by (pred_auto)
  thus ?thesis
    by (simp cong: INF_cong add: assms(1) Healthy_if)
qed

lemma csp_do_seq_conj_distl:
  assumes "P is CRR" "Q is CRR"
  shows "\<Phi>(s,\<sigma>,t) ;; (P \<and> Q) = (\<Phi>(s,\<sigma>,t) ;; P \<and> \<Phi>(s,\<sigma>,t) ;; Q)"
proof -
  have "\<Phi>(s,\<sigma>,t) ;; (CRR(P) \<and> CRR(Q)) = ((\<Phi>(s,\<sigma>,t) ;; (CRR P)) \<and> (\<Phi>(s,\<sigma>,t) ;; (CRR Q)))"
    by (pred_auto, blast+)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma tr_iter_Suc_left: "tr_iter (Suc n) t = t + tr_iter n t"
  by (induct n, simp_all add: add.assoc)

lemma csp_do_power_Suc [rpred]:
  "\<Phi>(True, [\<leadsto>], t) \<^bold>^ (Suc i) = \<Phi>(True, [\<leadsto>], tr_iter \<guillemotleft>Suc i\<guillemotright> t)"
proof (induct i)
  case 0
  then show ?case by (pred_simp add: power.power.power_0 power.power.power_Suc)
next
  case (Suc i)

  then show ?case 
    apply (simp del:SEXP_apply add: plus_list_def[THEN sym] power.power.power_Suc rpred usubst_eval usubst)
    apply (pred_auto add: inf_fun_def )
     apply (metis plus_list_def tr_iter_Suc tr_iter_Suc_left)+
    done
qed

lemma csp_power_do_comp [rpred]:
  assumes "P is CRR"
  shows "\<Phi>(True, [\<leadsto>], t) \<^bold>^ i ;; P = \<Phi>(True, [\<leadsto>], tr_iter \<guillemotleft>i\<guillemotright> t) ;; P"
proof -
  have "\<Phi>(True, [\<leadsto>], t) \<^bold>^ i ;; CRR P = \<Phi>(True, [\<leadsto>], tr_iter \<guillemotleft>i\<guillemotright> t) ;; CRR P"
    by (cases i, simp_all add: csp_do_comp rpred usubst assms closure)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma csp_do_id [rpred]:
  "P is CRR \<Longrightarrow> \<Phi>(b,[\<leadsto>],\<guillemotleft>[]\<guillemotright>) ;; P = ([b]\<^sub>S\<^sub>< \<and> P)"
  by (simp add: csp_do_comp usubst)

lemma csp_do_id_wp [wp]: 
  "P is CRR \<Longrightarrow> \<Phi>(b,[\<leadsto>],\<guillemotleft>[]\<guillemotright>) wp\<^sub>r P = ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P)"
  by (simp add: wp_rea_def rpred closure rea_impl_def)

lemma wp_rea_csp_do_st_pre [wp]: "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) wp\<^sub>r [s\<^sub>2]\<^sub>S\<^sub>< = \<I>(s\<^sub>1 \<and> \<not> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1)"
  by (pred_auto)

lemma wp_rea_csp_do_skip [wp]:
  fixes Q :: "('\<sigma>, '\<phi>) sfrd hrel"
  assumes "P is CRR"
  shows "\<Phi>(s,\<sigma>,t) wp\<^sub>r P = (\<I>(s,t) \<and> (\<sigma> \<dagger>\<^sub>S P)\<lbrakk>t\<rbrakk>\<^sub>t)"
  apply (simp add: wp_rea_def)
  apply (subst csp_do_comp)
  apply (simp_all add: closure assms usubst)
  oops

(*
lemma msubst_csp_do [usubst]: 
  "\<Phi>(s(x),\<sigma>,t(x))\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk> = \<Phi>(s(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,\<sigma>,t(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (pred_auto)

lemma rea_frame_ext_csp_do [frame]: 
  "vwb_lens a \<Longrightarrow> a:[\<Phi>(s,\<sigma>,t)]\<^sub>r\<^sup>+ = \<Phi>(s \<oplus>\<^sub>p a,\<sigma> \<oplus>\<^sub>s a ,t \<oplus>\<^sub>p a)"
  by (pred_auto)
*)

lemma R5_csp_do_nil [rpred]: "R5(\<Phi>(s,\<sigma>,\<guillemotleft>[]\<guillemotright>)) = \<Phi>(s,\<sigma>,\<guillemotleft>[]\<guillemotright>)"
  by (pred_auto)

lemma R5_csp_do_Cons [rpred]: "R5(\<Phi>(s,\<sigma>,x # xs)) = false"
  by (pred_auto)

text \<open> Iterated do relations \<close>

fun titr :: "nat \<Rightarrow> 's subst \<Rightarrow> ('a list, 's) expr \<Rightarrow> ('a list, 's) expr" where
"titr 0 \<sigma> t = 0" |
"titr (Suc n) \<sigma> t = (titr n \<sigma> t) + ((\<sigma> ^^ n) \<dagger> t)"

expr_constructor titr (2)

lemma titr_as_list_sum: "titr n \<sigma> t = list_sum (map (\<lambda> i. (\<sigma> ^^ i) \<dagger> t) [0..<n])"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  hence "titr (Suc n) \<sigma> t = list_sum (map (\<lambda>i. \<sigma> ^^ i \<dagger> t) [0..<n]) + (\<sigma> ^^ n \<dagger> t)"
    by (metis titr.simps(2))
  also have "... = list_sum (map (\<lambda>i. \<sigma> ^^ i \<dagger> t) [0..<Suc n])"
    by (simp add: fold_plus_sum_list_rev foldr_conv_fold)
  finally show ?case .
qed
        
lemma titr_as_foldr: "titr n \<sigma> t = foldr (\<lambda> i e. (\<sigma> ^^ i) \<dagger> t + e) [0..<n] 0"
  by (simp add: titr_as_list_sum foldr_map comp_def)

lemma list_sum_uexpr_rep_eq: "list_sum xs s = list_sum (map (\<lambda> e. e s) xs)"
  by (induct xs, simp_all)

lemma titr_rep_eq: "titr n \<sigma> t s = foldr (@) (map (\<lambda>x. t ((\<sigma> ^^ x) s)) [0..<n]) []"
  by (simp add: titr_as_list_sum list_sum_uexpr_rep_eq comp_def, pred_simp)

lemma titr_lemma:
  "t + (\<sigma> \<dagger> titr n \<sigma> t) + ((\<sigma> ^^ n \<circ>\<^sub>s \<sigma>) \<dagger> t) = (titr n \<sigma> t + ((\<sigma> ^^ n) \<dagger> t)) + ((\<sigma> \<circ>\<^sub>s \<sigma> ^^ n) \<dagger> t)"
  by (induct n, simp_all add: usubst add.assoc plus_list_def subst_app_def subst_comp_def funpow_swap1)

lemma csp_do_power [rpred]:
  "\<Phi>(s, \<sigma>, t)\<^bold>^(Suc n) = \<Phi>(\<forall> i\<in>{0..\<guillemotleft>n\<guillemotright>}. (\<sigma>^^i) \<dagger> s, \<sigma>^^Suc n, titr (Suc n) \<sigma> t)"
  apply (induct n)
   apply (pred_simp)
   apply (simp add: power.power.power_0 power.power.power_Suc)
  apply (simp del:SEXP_apply add: power.power.power_Suc rpred usubst)
  apply (thin_tac "_")
  apply (rule csp_do_eq_intro)
    apply (pred_auto)
  apply (metis (mono_tags, opaque_lifting) atLeastAtMost_iff funpow.simps(2) funpow_0 funpow_swap1 least_zero not_less_eq_eq o_apply
      old.nat.exhaust)
  apply (simp add: atLeast0_atMost_Suc_eq_insert_0)
  apply (metis Suc_le_mono atLeastAtMost_iff bot_nat_0.extremum funpow_Suc_right o_def)
  apply (metis comp_apply funpow_swap1 subst_comp_def)
  apply (metis (mono_tags, lifting) SEXP_def append_eq_appendI comp_apply plus_fun_apply plus_list_def subst_app_def subst_comp_def
      titr_lemma)
  done

lemma csp_do_rea_star [rpred]:
  "\<Phi>(s, \<sigma>, t)\<^sup>\<star>\<^sup>r = II\<^sub>r \<sqinter> (\<Sqinter> n. \<Phi>(\<forall> i\<in>{0..\<guillemotleft>n\<guillemotright>}. (\<sigma>^^i) \<dagger> s, \<sigma>^^Suc n, titr (Suc n) \<sigma> t))"
  by (simp add: rrel_theory.Star_alt_def closure uplus_power_def rpred)

lemma SUP_atLeast_Suc:
  "(\<Sqinter> i \<in> {Suc m..}. P(i)) = (\<Sqinter> i \<in> {m..}. P(Suc i))"
proof -
  have "(\<Sqinter> i \<in> {m..}. P(Suc i)) = \<Sqinter> (P ` Suc ` {m..})"
    by (simp add: image_image)
  also have "... = \<Sqinter> (P ` {Suc m..})"
    by (metis image_add_atLeast plus_1_eq_Suc)
  finally show ?thesis
    by simp
qed

lemma csp_do_csp_star [rpred]:
  "\<Phi>(s, \<sigma>, t)\<^sup>\<star>\<^sup>c = (\<Sqinter> n. \<Phi>(\<forall> i \<in> {0..<\<guillemotleft>n\<guillemotright>}. (\<sigma> ^^ i) \<dagger> s,\<sigma> ^^ n,titr n \<sigma> t))"
  (is "?lhs = (\<Sqinter> n. ?G(n))")
proof -
  have "?lhs = II\<^sub>c \<sqinter> (\<Sqinter> n. \<Phi>(\<forall> i \<in> {0..\<guillemotleft>n\<guillemotright>}. (\<sigma>^^i) \<dagger> s, \<sigma>^^Suc n, titr (Suc n) \<sigma> t))"
    (is "_ = II\<^sub>c \<sqinter> (\<Sqinter> n. ?F(n))")
    by (simp add: crf_theory.Star_alt_def closure uplus_power_def rpred)
  also have "... = II\<^sub>c \<sqinter> (\<Sqinter> n\<in>{1..}. ?F(n - 1))"
    by (simp add: SUP_atLeast_Suc, pred_simp)
  also have "... = II\<^sub>c \<sqinter> (\<Sqinter> n \<in> {1..}. \<Phi>(\<forall> i \<in> {0..<\<guillemotleft>n\<guillemotright>}. (\<sigma> ^^ i) \<dagger> s,\<sigma> ^^ n,titr n \<sigma> t))"
  proof -
    have "(\<Sqinter> n\<in>{1..}. ?F(n - 1)) = (\<Sqinter> n \<in> {1..}. ?G(n))"
      by (rule SUP_cong, simp)
         (metis (no_types, lifting) ext Suc_diff_le atLeastLessThanSuc_atLeastAtMost atLeast_iff diff_Suc_1)
    thus ?thesis by simp
  qed
  also have "... = ?G(0) \<sqinter> (\<Sqinter> n \<in> {1..}. ?G(n))"
    by (simp add: usubst)
       (metis SEXP_def csp_do_nothing_0 eq_id_iff subst_app_def subst_id_apply zero_list_def)
  also have "... = (\<Sqinter> n \<in> insert 0 {1..}. ?G(n))"
    by (simp add: zero_fun_def)
  also have "... = (\<Sqinter> n. ?G(n))"
  proof -                                     
    have "insert (0::nat) {1..} = {0..}" by auto
    thus ?thesis
      by simp
  qed
  finally show ?thesis .
qed

subsection \<open> Assumptions \<close>

syntax "_crf_assume" :: "logic \<Rightarrow> logic" ("[_]\<^sub>c")
translations "_crf_assume b" == "\<Phi>(b, [\<leadsto>], [])"

lemma crf_assume_true [rpred]: "P is CRR \<Longrightarrow> [True]\<^sub>c ;; P = P"
  by (simp add: crel_skip_left_unit csp_do_nothing)

subsection \<open> Downward closure of refusals \<close>

text \<open> We define downward closure of the pericondition by the following healthiness condition \<close>

definition CDC :: "('s, 'e) sfrd hrel \<Rightarrow> ('s, 'e) sfrd hrel" where
[pred]: "CDC(P) = (\<Sqinter> ref\<^sub>0. P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/ref\<^sup>>\<rbrakk> \<and> ($ref\<^sup>> \<subseteq> \<guillemotleft>ref\<^sub>0\<guillemotright>)\<^sub>e)"

lemma CDC_idem: "CDC(CDC(P)) = CDC(P)"
  by (pred_auto)

lemma CDC_Continuous [closure]: "Continuous CDC"
  by (pred_auto)

lemma CDC_RR_commute: "CDC(RR(P)) = RR(CDC(P))"
  by (pred_auto; blast)

lemma CDC_RR_closed [closure]: "P is RR \<Longrightarrow> CDC(P) is RR"
  by (metis CDC_RR_commute Healthy_def)

lemma CDC_CRR_commute: "CDC (CRR P) = CRR (CDC P)"
  by (pred_auto; blast)

lemma CDC_CRR_closed [closure]:
  assumes "P is CRR"
  shows "CDC(P) is CRR"
  by (rule CRR_intro, simp add: CDC_def unrest unrest_ssubst_expr var_alpha_combine usubst usubst_eval assms closure, simp add: unrest assms closure)

lemma CDC_unrest [unrest]: "\<lbrakk> vwb_lens x; (ref\<^sup>>)\<^sub>v \<bowtie> x; $x \<sharp> P \<rbrakk> \<Longrightarrow> $x \<sharp> CDC(P)"
  by (simp add: CDC_def unrest unrest_ssubst_expr var_alpha_combine usubst usubst_eval lens_indep_sym)

lemma CDC_R4_commute: "CDC(R4(P)) = R4(CDC(P))"
  by (pred_auto)

lemma R4_CDC_closed [closure]: "P is CDC \<Longrightarrow> R4(P) is CDC"
  by (simp add: CDC_R4_commute Healthy_def)

lemma CDC_R5_commute: "CDC(R5(P)) = R5(CDC(P))"
  by (pred_auto)

lemma R5_CDC_closed [closure]: "P is CDC \<Longrightarrow> R5(P) is CDC"
  by (simp add: CDC_R5_commute Healthy_def)

lemma rea_true_CDC [closure]: "true\<^sub>r is CDC"
  by (pred_auto)

lemma false_CDC [closure]: "false is CDC"
  by (pred_auto)

lemma CDC_UINF_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is CDC"
  shows "(\<Sqinter> i \<in> I. P i) is CDC"
  using assms by (pred_auto; blast)

lemma CDC_disj_closed [closure]:
  assumes "P is CDC" "Q is CDC"
  shows "(P \<or> Q) is CDC"
proof -
  have "CDC(P \<or> Q) = (CDC(P) \<or> CDC(Q))"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def assms(1) assms(2))
qed

lemma CDC_USUP_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is CDC"
  shows "(\<Squnion> i \<in> I. P i) is CDC"
  using assms by (pred_auto; blast)

lemma CDC_conj_closed [closure]:
  assumes "P is CDC" "Q is CDC"
  shows "(P \<and> Q) is CDC"
  using assms by (pred_auto, blast, meson)

lemma CDC_rea_impl [rpred]:
  "$ref\<^sup>> \<sharp> P \<Longrightarrow> CDC(P \<longrightarrow>\<^sub>r Q) = (P \<longrightarrow>\<^sub>r CDC(Q))"
  by (pred_auto; blast)

lemma rea_impl_CDC_closed [closure]:
  assumes "$ref\<^sup>> \<sharp> P" "Q is CDC"
  shows "(P \<longrightarrow>\<^sub>r Q) is CDC"
  using assms by (simp add: CDC_rea_impl Healthy_def)

lemma seq_CDC_closed [closure]:
  assumes "Q is CDC"
  shows "(P ;; Q) is CDC"
proof -
  have "CDC(P ;; Q) = P ;; CDC(Q)"
    by (pred_auto; blast)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma st_subst_CDC_closed [closure]:
  assumes "P is CDC"
  shows "(\<sigma> \<dagger>\<^sub>S P) is CDC"
proof -
  have "(\<sigma> \<dagger>\<^sub>S CDC P) is CDC"
    by (pred_auto)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma rea_st_cond_CDC [closure]: "[g]\<^sub>S\<^sub>< is CDC"
  by (pred_auto)

lemma csp_enable_CDC [closure]: "\<E>(s,t,E) is CDC"
  by (pred_auto)

lemma state_srea_CDC_closed [closure]:
  assumes "P is CDC"
  shows "state 'a \<bullet> P is CDC"
proof -
  have "state 'a \<bullet> CDC(P) is CDC"
    by (pred_auto; blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma csp_do_CDC [closure]: "\<Phi>(s,\<sigma>,t) is CDC"
  by (pred_auto; blast)

end