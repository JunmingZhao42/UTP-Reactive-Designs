section \<open> Reactive Design Triples \<close>

theory utp_rdes_triples
  imports utp_rdes_designs
begin

subsection \<open> Diamond notation\<close>

definition wait'_cond ::
  "('t::trace,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel" (infixr "\<diamondop>" 89) where
[pred]: "(P \<diamondop> Q) = (P \<triangleleft> $wait\<^sup>> \<triangleright> Q)"

expr_constructor wait'_cond

lemma wait'_cond_unrest [unrest]:
  "\<lbrakk> mwb_lens x; (wait\<^sup>>)\<^sub>v \<bowtie> x; $x \<sharp> P; $x \<sharp> Q \<rbrakk> \<Longrightarrow> $x \<sharp> (P \<diamondop> Q)"
  by (pred_simp)
  
lemma wait'_cond_subst [usubst]:
  "$wait\<^sup>> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P \<diamondop> Q) = (\<sigma> \<dagger> P) \<diamondop> (\<sigma> \<dagger> Q)"
  by (simp add: wait'_cond_def usubst unrest subst_apply_unrest)

lemma wait'_cond_left_false: "false \<diamondop> P = (\<not> wait\<^sup>> \<and> P)"
  by (pred_auto)

lemma expr_if_cond_def: "P \<triangleleft> B \<triangleright> Q = ((B \<and> P)\<^sub>e \<or> (\<not> B \<and> Q)\<^sub>e)"
  by pred_auto

lemma wait'_cond_seq: "((P \<diamondop> Q) ;; R) = ((P ;; (wait\<^sup>< \<and> R)) \<or> (Q ;; (\<not>wait\<^sup>< \<and> R)))"
  by (simp add: wait'_cond_def expr_if_cond_def seqr_or_distl, pred_auto, metis+)

lemma wait'_cond_true: "(P \<diamondop> Q \<and> wait\<^sup>>) = (P \<and> wait\<^sup>>)"
  by (pred_auto)

lemma wait'_cond_false: "(P \<diamondop> Q \<and> \<not>wait\<^sup>>) = (Q \<and> \<not>wait\<^sup>>)"
  by (pred_auto)

lemma wait'_cond_idem: "P \<diamondop> P = P"
  by (pred_auto)

lemma wait'_cond_conj_exchange:
  "((P \<diamondop> Q) \<and> (R \<diamondop> S)) = (P \<and> R) \<diamondop> (Q \<and> S)"
  by (pred_auto)

lemma subst_wait'_cond_true [usubst]: "(P \<diamondop> Q)\<lbrakk>True/wait\<^sup>>\<rbrakk> = P\<lbrakk>True/wait\<^sup>>\<rbrakk>"
  by (pred_auto)

lemma subst_wait'_cond_false [usubst]: "(P \<diamondop> Q)\<lbrakk>False/wait\<^sup>>\<rbrakk> = Q\<lbrakk>False/wait\<^sup>>\<rbrakk>"
  by (pred_auto)

lemma subst_wait'_left_subst: "(P\<lbrakk>True/wait\<^sup>>\<rbrakk> \<diamondop> Q) = (P \<diamondop> Q)"
  by (pred_auto)

lemma subst_wait'_right_subst: "(P \<diamondop> Q\<lbrakk>False/wait\<^sup>>\<rbrakk>) = (P \<diamondop> Q)"
  by (pred_auto)

lemma wait'_cond_split: "P\<lbrakk>True/wait\<^sup>>\<rbrakk> \<diamondop> P\<lbrakk>False/wait\<^sup>>\<rbrakk> = P"
  by (simp add: wait'_cond_def expr_if_bool_var_left expr_if_bool_var_right)

lemma wait_cond'_assoc [simp]: "P \<diamondop> Q \<diamondop> R = P \<diamondop> R"
  by (pred_auto)

lemma wait_cond'_shadow: "(P \<diamondop> Q) \<diamondop> R = P \<diamondop> Q \<diamondop> R"
  by (pred_auto)

lemma wait_cond'_conj [simp]: "P \<diamondop> (Q \<and> (R \<diamondop> S)) = P \<diamondop> (Q \<and> S)"
  by (pred_auto)

lemma R1_wait'_cond: "R1(P \<diamondop> Q) = R1(P) \<diamondop> R1(Q)"
  by (pred_auto)

lemma R2s_wait'_cond: "R2s(P \<diamondop> Q) = R2s(P) \<diamondop> R2s(Q)"
  by (simp add: wait'_cond_def R2s_def R2s_def usubst)

lemma R2_wait'_cond: "R2(P \<diamondop> Q) = R2(P) \<diamondop> R2(Q)"
  by (simp add: R2_def R2s_wait'_cond R1_wait'_cond)
    
lemma wait'_cond_R1_closed [closure]: 
  "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> P \<diamondop> Q is R1"
  by (simp add: Healthy_def R1_wait'_cond)

lemma wait'_cond_R2c_closed [closure]: "\<lbrakk> P is R2c; Q is R2c \<rbrakk> \<Longrightarrow> P \<diamondop> Q is R2c"
  by (simp add: R2c_condr wait'_cond_def Healthy_def, pred_auto)

subsection \<open> Export laws \<close>


lemma RH_design_peri_R1: "\<^bold>R(P \<turnstile> R1(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_idem R1_wait'_cond RH_design_export_R1)
  
lemma RH_design_post_R1: "\<^bold>R(P \<turnstile> Q \<diamondop> R1(R)) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_wait'_cond RH_design_export_R1 RH_design_peri_R1)

lemma RH_design_peri_R2s: "\<^bold>R(P \<turnstile> R2s(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_post_R2s: "\<^bold>R(P \<turnstile> Q \<diamondop> R2s(R)) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_peri_R2c: "\<^bold>R(P \<turnstile> R2c(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_R2s_R2c RH_design_peri_R1 RH_design_peri_R2s)

lemma RHS_design_peri_R1: "\<^bold>R\<^sub>s(P \<turnstile> R1(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_idem R1_wait'_cond RHS_design_export_R1)

lemma RHS_design_post_R1: "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R1(R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_wait'_cond RHS_design_export_R1 RHS_design_peri_R1)

lemma RHS_design_peri_R2s: "\<^bold>R\<^sub>s(P \<turnstile> R2s(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RHS_design_export_R2s)

lemma RHS_design_post_R2s: "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R2s(R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R2s_wait'_cond RHS_design_export_R2s RHS_design_peri_R2s)

lemma RHS_design_peri_R2c: "\<^bold>R\<^sub>s(P \<turnstile> R2c(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_R2s_R2c RHS_design_peri_R1 RHS_design_peri_R2s)

lemma RH_design_lemma1:
  "RH(P \<turnstile> (R1(R2c(Q)) \<or> R) \<diamondop> S) = RH(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R1_R2s_R2c R2_R1_form R2_disj R2c_idem RH_design_peri_R1 RH_design_peri_R2s)

lemma RHS_design_lemma1:
  "RHS(P \<turnstile> (R1(R2c(Q)) \<or> R) \<diamondop> S) = RHS(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R1_R2s_R2c R2_R1_form R2_disj R2c_idem RHS_design_peri_R1 RHS_design_peri_R2s)

subsection \<open> Pre-, peri-, and postconditions \<close>

subsubsection \<open> Definitions \<close>

abbreviation "pre\<^sub>s  \<equiv> [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> False, wait\<^sup>< \<leadsto> False]"
abbreviation "cmt\<^sub>s  \<equiv> [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True, wait\<^sup>< \<leadsto> False]"
abbreviation "peri\<^sub>s \<equiv> [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True, wait\<^sup>< \<leadsto> False, wait\<^sup>> \<leadsto> True]"
abbreviation "post\<^sub>s \<equiv> [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True, wait\<^sup>< \<leadsto> False, wait\<^sup>> \<leadsto> False]"

abbreviation "npre\<^sub>R(P) \<equiv> pre\<^sub>s \<dagger> P"

definition [pred]: "pre\<^sub>R(P)  = (\<not>\<^sub>r npre\<^sub>R(P))"
definition [pred]: "cmt\<^sub>R(P)  = R1(cmt\<^sub>s \<dagger> P)"
definition [pred]: "peri\<^sub>R(P) = R1(peri\<^sub>s \<dagger> P)"
definition [pred]: "post\<^sub>R(P) = R1(post\<^sub>s \<dagger> P)"

expr_constructor pre\<^sub>R cmt\<^sub>R peri\<^sub>R post\<^sub>R npre\<^sub>R

subsubsection \<open> Unrestriction laws \<close>

lemma ok_pre_unrest [unrest]: "$ok\<^sup>< \<sharp> pre\<^sub>R P"
  by pred_auto

lemma ok_peri_unrest [unrest]: "$ok\<^sup>< \<sharp> peri\<^sub>R P"
  by pred_auto

lemma ok_post_unrest [unrest]: "$ok\<^sup>< \<sharp> post\<^sub>R P"
  by pred_auto

lemma ok_cmt_unrest [unrest]: "$ok\<^sup>< \<sharp> cmt\<^sub>R P"
  by pred_auto

lemma ok'_pre_unrest [unrest]: "$ok\<^sup>> \<sharp> pre\<^sub>R P"
  by pred_auto

lemma ok'_peri_unrest [unrest]: "$ok\<^sup>> \<sharp> peri\<^sub>R P"
  by pred_auto

lemma ok'_post_unrest [unrest]: "$ok\<^sup>> \<sharp> post\<^sub>R P"
  by pred_auto

lemma ok'_cmt_unrest [unrest]: "$ok\<^sup>> \<sharp> cmt\<^sub>R P"
  by pred_auto

lemma wait_pre_unrest [unrest]: "$wait\<^sup>< \<sharp> pre\<^sub>R P"
  by pred_auto

lemma wait_peri_unrest [unrest]: "$wait\<^sup>< \<sharp> peri\<^sub>R P"
  by pred_auto

lemma wait_post_unrest [unrest]: "$wait\<^sup>< \<sharp> post\<^sub>R P"
  by pred_auto

lemma wait_cmt_unrest [unrest]: "$wait\<^sup>< \<sharp> cmt\<^sub>R P"
  by pred_auto

lemma wait'_peri_unrest [unrest]: "$wait\<^sup>> \<sharp> peri\<^sub>R P"
  by pred_auto

lemma wait'_post_unrest [unrest]: "$wait\<^sup>> \<sharp> post\<^sub>R P"
  by pred_auto

subsubsection \<open> Substitution laws \<close>

lemma pre\<^sub>s_design: "pre\<^sub>s \<dagger> (P \<turnstile> Q) = (\<not> pre\<^sub>s \<dagger> P)"
  by (simp add: design_def pre\<^sub>R_def usubst, pred_simp)

lemma peri\<^sub>s_design: "peri\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = peri\<^sub>s \<dagger> (P \<longrightarrow> Q)"
  by (simp add: design_def usubst wait'_cond_def, pred_simp)

lemma post\<^sub>s_design: "post\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = post\<^sub>s \<dagger> (P \<longrightarrow> R)"
  by (simp add: design_def usubst wait'_cond_def, pred_simp)

lemma cmt\<^sub>s_design: "cmt\<^sub>s \<dagger> (P \<turnstile> Q) = cmt\<^sub>s \<dagger> (P \<longrightarrow> Q)"
  by (simp add: design_def usubst wait'_cond_def, pred_simp)

lemma pre\<^sub>s_R1 [usubst]: "pre\<^sub>s \<dagger> R1(P) = R1(pre\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma pre\<^sub>s_R2c [usubst]: "pre\<^sub>s \<dagger> R2c(P) = R2c(pre\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst, pred_simp)

lemma peri\<^sub>s_R1 [usubst]: "peri\<^sub>s \<dagger> R1(P) = R1(peri\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma peri\<^sub>s_R2c [usubst]: "peri\<^sub>s \<dagger> R2c(P) = R2c(peri\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst, pred_simp)

lemma post\<^sub>s_R1 [usubst]: "post\<^sub>s \<dagger> R1(P) = R1(post\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma post\<^sub>s_R2c [usubst]: "post\<^sub>s \<dagger> R2c(P) = R2c(post\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst, pred_simp)

lemma cmt\<^sub>s_R1 [usubst]: "cmt\<^sub>s \<dagger> R1(P) = R1(cmt\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma cmt\<^sub>s_R2c [usubst]: "cmt\<^sub>s \<dagger> R2c(P) = R2c(cmt\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst, pred_simp)

lemma pre_wait_false:
  "pre\<^sub>R(P\<lbrakk>False/wait\<^sup><\<rbrakk>) = pre\<^sub>R(P)"
  by (pred_auto)

lemma cmt_wait_false:
  "cmt\<^sub>R(P\<lbrakk>False/wait\<^sup><\<rbrakk>) = cmt\<^sub>R(P)"
  by (pred_auto)

lemma rea_pre_RH_design: "pre\<^sub>R(\<^bold>R(P \<turnstile> Q)) = R1(R2c(pre\<^sub>s \<dagger> P))"
  by (simp add: RH_def usubst R3c_def pre\<^sub>R_def pre\<^sub>s_design R1_negate_R1 R2c_not rea_not_def)

lemma rea_pre_RHS_design: "pre\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q)) = R1(R2c(pre\<^sub>s \<dagger> P))"
  by (simp add: RHS_def usubst R3h_def pre\<^sub>R_def pre\<^sub>s_design R1_negate_R1 R2c_not rea_not_def)

lemma rea_cmt_RH_design: "cmt\<^sub>R(\<^bold>R(P \<turnstile> Q)) = R1(R2c(cmt\<^sub>s \<dagger> (P \<longrightarrow> Q)))"
  by (simp add: RH_def usubst R3c_def cmt\<^sub>R_def cmt\<^sub>s_design R1_idem)

lemma rea_cmt_RHS_design: "cmt\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q)) = R1(R2c(cmt\<^sub>s \<dagger> (P \<longrightarrow> Q)))"
  by (simp add: RHS_def usubst R3h_def cmt\<^sub>R_def cmt\<^sub>s_design R1_idem)

lemma rea_peri_RH_design: "peri\<^sub>R(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = R1(R2c(peri\<^sub>s \<dagger> (P \<longrightarrow>\<^sub>r Q)))"
  by pred_auto

lemma rea_peri_RHS_design: "peri\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = R1(R2c(peri\<^sub>s \<dagger> (P \<longrightarrow>\<^sub>r Q)))"
  by (simp add:RHS_def usubst peri\<^sub>R_def R3h_def peri\<^sub>s_design, pred_auto)

lemma rea_post_RH_design: "post\<^sub>R(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = R1(R2c(post\<^sub>s \<dagger> (P \<longrightarrow>\<^sub>r R)))"
  by pred_auto

lemma rea_post_RHS_design: "post\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = R1(R2c(post\<^sub>s \<dagger> (P \<longrightarrow>\<^sub>r R)))"
  by (simp add:RHS_def usubst post\<^sub>R_def R3h_def post\<^sub>s_design, pred_auto)

lemma peri_cmt_def: "peri\<^sub>R(P) = (cmt\<^sub>R(P))\<lbrakk>True/wait\<^sup>>\<rbrakk>"
  by (pred_auto)

lemma post_cmt_def: "post\<^sub>R(P) = (cmt\<^sub>R(P))\<lbrakk>False/wait\<^sup>>\<rbrakk>"
  by (pred_auto)

lemma rdes_export_cmt: "\<^bold>R\<^sub>s(P \<turnstile> (cmt\<^sub>s \<dagger> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (pred_auto)

lemma rdes_export_pre: "\<^bold>R\<^sub>s((P\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (pred_auto)

subsubsection \<open> Healthiness laws \<close>

lemma wait'_unrest_pre_SRD [unrest]:
  "$wait\<^sup>> \<sharp> pre\<^sub>R(P) \<Longrightarrow>  $wait\<^sup>> \<sharp> pre\<^sub>R (SRD P)"
  apply (pred_auto)
  using least_zero apply blast+
done

lemma R1_R2s_cmt_SRD:
  assumes "P is SRD"
  shows "R1(R2s(cmt\<^sub>R(P))) = cmt\<^sub>R(P)"
  by (metis (no_types, lifting) R1_R2c_commute R1_R2s_R2c R1_idem R2c_idem SRD_reactive_design assms rea_cmt_RHS_design)

lemma R1_R2s_peri_SRD:
  assumes "P is SRD"
  shows "R1(R2s(peri\<^sub>R(P))) = peri\<^sub>R(P)"
  by (metis (no_types, lifting) R1_R2s_cmt_SRD R1_wait'_true R2s_subst_wait'_true assms peri_cmt_def)

lemma R1_peri_SRD:
  assumes "P is SRD"
  shows "R1(peri\<^sub>R(P)) = peri\<^sub>R(P)"
proof -
  have "R1(peri\<^sub>R(P)) = R1(R1(R2s(peri\<^sub>R(P))))"
    by (simp add: R1_R2s_peri_SRD assms)
  also have "... = peri\<^sub>R(P)"
    by (simp add: R1_idem, simp add: R1_R2s_peri_SRD assms)
  finally show ?thesis .
qed

lemma R1_R2c_peri_RHS:
  assumes "P is SRD"
  shows "R1(R2c(peri\<^sub>R(P))) = peri\<^sub>R(P)"
  by (metis R1_R2s_R2c R1_R2s_peri_SRD assms)

lemma R1_R2s_post_SRD:
  assumes "P is SRD"
  shows "R1(R2s(post\<^sub>R(P))) = post\<^sub>R(P)"
  by (metis R1_R2s_R2c R1_R2s_cmt_SRD R2_R2c_def R2_subst_wait'_false assms post_cmt_def)

lemma R2c_peri_SRD:
  assumes "P is SRD"
  shows "R2c(peri\<^sub>R(P)) = peri\<^sub>R(P)"
  by (metis R1_R2c_commute R1_R2c_peri_RHS R1_peri_SRD assms)

lemma R1_post_SRD:
  assumes "P is SRD"
  shows "R1(post\<^sub>R(P)) = post\<^sub>R(P)"
proof -
  have "R1(post\<^sub>R(P)) = R1(R1(R2s(post\<^sub>R(P))))"
    by (simp add: R1_R2s_post_SRD assms)
  also have "... = post\<^sub>R(P)"
    by (simp add: R1_idem, simp add: R1_R2s_post_SRD assms)
  finally show ?thesis .
qed

lemma R2c_post_SRD:
  assumes "P is SRD"
  shows "R2c(post\<^sub>R(P)) = post\<^sub>R(P)"
  by (metis R1_R2c_commute R1_R2s_R2c R1_R2s_post_SRD R1_post_SRD assms)

lemma R1_R2c_post_RHS:
  assumes "P is SRD"
  shows "R1(R2c(post\<^sub>R(P))) = post\<^sub>R(P)"
  by (metis R1_R2s_R2c R1_R2s_post_SRD assms)

lemma R2_cmt_conj_wait':
  "P is SRD \<Longrightarrow> R2(cmt\<^sub>R P \<and> \<not> wait\<^sup>>) = (cmt\<^sub>R P \<and> \<not> wait\<^sup>>)"
  by (simp add: R2_def R2s_conj R2s_not R2s_wait' R1_extend_conj R1_R2s_cmt_SRD)

lemma R2c_preR:
  "P is SRD \<Longrightarrow> R2c(pre\<^sub>R(P)) = pre\<^sub>R(P)"
  by (metis (no_types, lifting) R1_R2c_commute R2c_idem SRD_reactive_design rea_pre_RHS_design)

lemma preR_R2_closed [closure]: 
  assumes "P is R2"
  shows "pre\<^sub>R P is R2"
proof -
  have "R2(pre\<^sub>R(R2(P))) = pre\<^sub>R(R2(P))"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma periR_R2_closed [closure]: 
  assumes "P is R2"
  shows "peri\<^sub>R P is R2"
proof -
  have "R2(peri\<^sub>R(R2(P))) = peri\<^sub>R(R2(P))"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma postR_R2_closed [closure]: 
  assumes "P is R2"
  shows "post\<^sub>R P is R2"
proof -
  have "R2(post\<^sub>R(R2(P))) = post\<^sub>R(R2(P))"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma postR_SRD_R1 [closure]: "P is SRD \<Longrightarrow> post\<^sub>R(P) is R1"
  by (simp add: Healthy_def' R1_post_SRD)

lemma R2c_periR:
  "P is SRD \<Longrightarrow> R2c(peri\<^sub>R(P)) = peri\<^sub>R(P)"
  by (metis (no_types, lifting) R1_R2c_commute R1_R2s_R2c R1_R2s_peri_SRD R2c_idem)

lemma R2c_postR:
  "P is SRD \<Longrightarrow> R2c(post\<^sub>R(P)) = post\<^sub>R(P)"
  by (metis (no_types, opaque_lifting) R1_R2c_commute R1_R2c_is_R2 R1_R2s_post_SRD R2_def R2s_idem)

lemma periR_RR [closure]: "P is R2 \<Longrightarrow> peri\<^sub>R(P) is RR"
  by (rule RR_intro, simp_all add: closure unrest)
  
lemma postR_RR [closure]: "P is R2 \<Longrightarrow> post\<^sub>R(P) is RR"
  by (rule RR_intro, simp_all add: closure unrest)

lemma wpR_trace_ident_pre [wp]:
  "(($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R) wp\<^sub>r pre\<^sub>R P = pre\<^sub>R P"
  by (pred_auto)
    
lemma R1_preR [closure]:
  "pre\<^sub>R(P) is R1"
  by (pred_auto)

lemma trace_ident_left_periR:
  "(($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R) ;; peri\<^sub>R(P) = peri\<^sub>R(P)"
  by (pred_auto)

lemma trace_ident_left_postR:
  "(($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R) ;; post\<^sub>R(P) = post\<^sub>R(P)"
  by (pred_auto)

lemma trace_ident_right_postR:
  "post\<^sub>R(P) ;; (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R) = post\<^sub>R(P)"
  by (pred_auto)

subsubsection \<open> Calculation laws \<close>

lemma wait'_cond_peri_post_cmt [rdes]:
  "cmt\<^sub>R P = peri\<^sub>R P \<diamondop> post\<^sub>R P"
  by (simp add: peri_cmt_def post_cmt_def wait'_cond_split)

lemma preR_rdes [rdes]: 
  assumes "P is RR"
  shows "pre\<^sub>R(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = P"
  by (simp add: rea_pre_RH_design unrest usubst assms Healthy_if RR_implies_R2c RR_implies_R1)

lemma preR_srdes [rdes]: 
  assumes "P is RR"
  shows "pre\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = P"
  by (simp add: rea_pre_RHS_design unrest usubst assms Healthy_if RR_implies_R2c RR_implies_R1)

lemma periR_rdes [rdes]: 
  assumes "P is RR" "Q is RR"
  shows "peri\<^sub>R(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = (P \<longrightarrow>\<^sub>r Q)"
  by (simp add: rea_peri_RH_design unrest usubst assms Healthy_if RR_implies_R2c closure)

lemma periR_srdes [rdes]: 
  assumes "P is RR" "Q is RR"
  shows "peri\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = (P \<longrightarrow>\<^sub>r Q)"
  by (simp add: rea_peri_RHS_design unrest usubst assms Healthy_if RR_implies_R2c closure)

lemma postR_rdes [rdes]: 
  assumes "P is RR" "R is RR"
  shows "post\<^sub>R(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = (P \<longrightarrow>\<^sub>r R)"
  by (simp add: rea_post_RH_design unrest usubst assms Healthy_if RR_implies_R2c closure)

lemma postR_srdes [rdes]: 
  assumes "P is RR" "R is RR"
  shows "post\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = (P \<longrightarrow>\<^sub>r R)"
  by (simp add: rea_post_RHS_design unrest usubst assms Healthy_if RR_implies_R2c closure)
    
lemma preR_Chaos [rdes]: "pre\<^sub>R(Chaos) = false"
  by (simp add: Chaos_def, pred_simp)

lemma periR_Chaos [rdes]: "peri\<^sub>R(Chaos) = true\<^sub>r"
  by (simp add: Chaos_def, pred_simp)

lemma postR_Chaos [rdes]: "post\<^sub>R(Chaos) = true\<^sub>r"
  by (simp add: Chaos_def, pred_simp)

lemma preR_Miracle [rdes]: "pre\<^sub>R(Miracle) = true\<^sub>r"
  by (simp add: Miracle_def, pred_auto)

lemma periR_Miracle [rdes]: "peri\<^sub>R(Miracle) = false"
  by (simp add: Miracle_def, pred_auto)

lemma postR_Miracle [rdes]: "post\<^sub>R(Miracle) = false"
  by (simp add: Miracle_def, pred_auto)

lemma preR_srdes_skip [rdes]: "pre\<^sub>R(II\<^sub>R) = true\<^sub>r"
  by (pred_auto)

lemma periR_srdes_skip [rdes]: "peri\<^sub>R(II\<^sub>R) = false"
  by (pred_auto)

lemma postR_srdes_skip [rdes]: "post\<^sub>R(II\<^sub>R) = (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R)"
  by (pred_auto)

lemma preR_INF [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> A) = (\<Squnion> P\<in>A. pre\<^sub>R(P))"
  by (pred_auto)

lemma periR_INF [rdes]: "peri\<^sub>R(\<Sqinter> A) = (\<Sqinter> P\<in>A. peri\<^sub>R(P))"
  by (pred_auto)

lemma postR_INF [rdes]: "post\<^sub>R(\<Sqinter> A) = (\<Sqinter> P\<in>A. post\<^sub>R(P))"
  by (pred_auto)

lemma preR_UINF [rdes]: "pre\<^sub>R(\<Sqinter> i. P(i)) = (\<Squnion> i. pre\<^sub>R(P(i)))"
  by (pred_auto)

lemma periR_UINF [rdes]: "peri\<^sub>R(\<Sqinter> i. P(i)) = (\<Sqinter> i. peri\<^sub>R(P(i)))"
  by (pred_auto)

lemma postR_UINF [rdes]: "post\<^sub>R(\<Sqinter> i. P(i)) = (\<Sqinter> i. post\<^sub>R(P(i)))"
  by (pred_auto)

lemma preR_UINF_member [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> i\<in>A. P(i)) = (\<Squnion> i\<in>A. pre\<^sub>R(P(i)))"
  by (pred_auto)
    
lemma preR_UINF_member_2 [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> (i,j)\<in>A. P i j) = (\<Squnion> (i,j)\<in>A. pre\<^sub>R(P i j))"
  by (simp add: preR_UINF_member prod.case_distrib)

lemma preR_UINF_member_3 [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> (i,j,k)\<in>A. P i j k) = (\<Squnion> (i,j,k)\<in>A. pre\<^sub>R(P i j k))"
  by (simp add: preR_UINF_member prod.case_distrib)

lemma periR_UINF_member [rdes]: "peri\<^sub>R(\<Sqinter> i\<in>A. P(i)) = (\<Sqinter> i\<in>A. peri\<^sub>R(P(i)))"
  by (pred_auto)
    
lemma periR_UINF_member_2 [rdes]: "peri\<^sub>R(\<Sqinter> (i,j)\<in>A. P i j) = (\<Sqinter> (i,j)\<in>A. peri\<^sub>R(P i j))"
  by (simp add: periR_UINF_member prod.case_distrib)

lemma periR_UINF_member_3 [rdes]: "peri\<^sub>R(\<Sqinter> (i,j,k)\<in>A. P i j k) = (\<Sqinter> (i,j,k)\<in>A. peri\<^sub>R(P i j k))"
  by (simp add: periR_UINF_member prod.case_distrib)

lemma postR_UINF_member [rdes]: "post\<^sub>R(\<Sqinter> i\<in>A. P(i)) = (\<Sqinter> i\<in>A. post\<^sub>R(P(i)))"
  by (pred_auto)

lemma postR_UINF_member_2 [rdes]: "post\<^sub>R(\<Sqinter> (i,j)\<in>A. P i j) = (\<Sqinter> (i,j)\<in>A. post\<^sub>R(P i j))"
  by (metis (mono_tags, lifting) Inf.INF_cong postR_UINF_member prod.case_eq_if)
    
lemma postR_UINF_member_3 [rdes]: "post\<^sub>R(\<Sqinter> (i,j,k)\<in>A. P i j k) = (\<Sqinter> (i,j,k)\<in>A. post\<^sub>R(P i j k))"
  by (metis (mono_tags, lifting) Inf.INF_cong postR_UINF_member prod.case_eq_if)
    
lemma preR_inf [rdes]: "pre\<^sub>R(P \<sqinter> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"
  by (pred_auto)

lemma periR_inf [rdes]: "peri\<^sub>R(P \<sqinter> Q) = (peri\<^sub>R(P) \<or> peri\<^sub>R(Q))"
  by (pred_auto)

lemma postR_inf [rdes]: "post\<^sub>R(P \<sqinter> Q) = (post\<^sub>R(P) \<or> post\<^sub>R(Q))"
  by (pred_auto)

lemma preR_SUP [rdes]: "pre\<^sub>R(\<Squnion> A) = (\<Sqinter> P\<in>A. pre\<^sub>R(P))"
  by (pred_auto)

lemma periR_SUP [rdes]: "A \<noteq> {} \<Longrightarrow> peri\<^sub>R(\<Squnion> A) = (\<Squnion> P\<in>A. peri\<^sub>R(P))"
  by (pred_auto)

lemma postR_SUP [rdes]: "A \<noteq> {} \<Longrightarrow> post\<^sub>R(\<Squnion> A) = (\<Squnion> P\<in>A. post\<^sub>R(P))"
  by (pred_auto)

text \<open> An R1 relation has @{term "pre\<^sub>R P = true\<^sub>r"} exactly when it
  never diverges from an active prior. \<close>

lemma preR_true_iff:
  "P is R1 \<Longrightarrow>
    (pre\<^sub>R P = true\<^sub>r) = (\<forall>x z. P (x,z) \<and> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z)"
  by (simp add: pre\<^sub>R_def Healthy_def; pred_auto; metis (full_types))

subsection \<open> Formation laws \<close>

subsubsection \<open> Regular \<close>

lemma rdes_skip_tri_design [rdes_def]: "II\<^sub>C = \<^bold>R(true\<^sub>r \<turnstile> false \<diamondop> II\<^sub>r)"
  apply (simp add: skip_rea_def, pred_auto)
  using minus_zero_eq apply blast+
  done

lemma RH_tri_design_form:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = (II\<^sub>C \<triangleleft> $wait\<^sup>< \<triangleright> ((ok\<^sup>< \<and> P\<^sub>1) \<longrightarrow>\<^sub>r (ok\<^sup>> \<and> (P\<^sub>2 \<diamondop> P\<^sub>3))))"
proof -
  have "\<^bold>R(RR(P\<^sub>1) \<turnstile> RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)) = (II\<^sub>C \<triangleleft> $wait\<^sup>< \<triangleright> ((ok\<^sup>< \<and> RR(P\<^sub>1)) \<longrightarrow>\<^sub>r (ok\<^sup>> \<and> (RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)))))"
    apply (pred_auto) using minus_zero_eq by blast+
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma RH_design_pre_post_form:
  "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
proof -
  have "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R((\<not> P\<^sup>f\<^sub>f)\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (simp add: design_subst_ok)
  also have "... = \<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: pre\<^sub>R_def cmt\<^sub>R_def usubst, pred_auto)
  finally show ?thesis .
qed

lemma RD_as_reactive_design:
  "RD(P) = \<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
  by (simp add: RH_design_pre_post_form RD_RH_design_form)

lemma RD_reactive_design_alt:
  assumes "P is RD"
  shows "\<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = P"
proof -
  have "\<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: RH_design_pre_post_form)
  thus ?thesis
    by (simp add: RD_reactive_design assms)
qed

lemma RD_reactive_tri_design_lemma:
  "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>True/wait\<^sup>>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
  by (simp add: RD_RH_design_form wait'_cond_split)

lemma RD_as_reactive_tri_design:
  "RD(P) = \<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
proof -
  have "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>True/wait\<^sup>>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
    by (simp add: RD_RH_design_form wait'_cond_split)
  also have "... = \<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (pred_auto)
  finally show ?thesis .
qed

lemma RD_reactive_tri_design:
  assumes "P is RD"
  shows "\<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
  by (metis Healthy_if RD_as_reactive_tri_design assms)
    
lemma RD_elimination [RD_elim]: "\<lbrakk> P is RD; Q(\<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: RD_reactive_tri_design)

lemma RD_elimination_ind_1 [RD_elim]: "\<lbrakk> \<And> i. P i is RD; Q(\<lambda> i. \<^bold>R(pre\<^sub>R(P i) \<turnstile> peri\<^sub>R(P i) \<diamondop> post\<^sub>R(P i)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: RD_reactive_tri_design)

lemma RD_elimination_ind_2 [RD_elim]: "\<lbrakk> \<And> i j. P i j is RD; Q(\<lambda> i j. \<^bold>R(pre\<^sub>R(P i j) \<turnstile> peri\<^sub>R(P i j) \<diamondop> post\<^sub>R(P i j)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: RD_reactive_tri_design)

lemma RH_tri_design_is_RD [closure]:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>> \<sharp> R"
  shows "\<^bold>R(P \<turnstile> Q \<diamondop> R) is RD"
  by (rule RH_design_is_RD, simp_all add: unrest assms)

lemma RD_rdes_intro [closure]:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "\<^bold>R(P \<turnstile> Q \<diamondop> R) is RD"
  by (rule RH_tri_design_is_RD, simp_all add: unrest closure assms)

subsubsection \<open> Stateful \<close>

lemma srdes_skip_tri_design [rdes_def]: "II\<^sub>R = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> II\<^sub>r)"
  by (simp add: srdes_skip_def, pred_auto)

lemma Chaos_tri_def [rdes_def]: "Chaos = \<^bold>R\<^sub>s(false \<turnstile> false \<diamondop> false)"
  by (simp add: Chaos_def design_false_pre)

lemma Miracle_tri_def [rdes_def]: "Miracle = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> false)"
  by (simp add: Miracle_def R1_design_R1_pre wait'_cond_idem)

lemma RHS_tri_design_form:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = (II\<^sub>R \<triangleleft> $wait\<^sup>< \<triangleright> ((ok\<^sup>< \<and> P\<^sub>1) \<longrightarrow>\<^sub>r (ok\<^sup>> \<and> (P\<^sub>2 \<diamondop> P\<^sub>3))))"
proof -
  have "\<^bold>R\<^sub>s(RR(P\<^sub>1) \<turnstile> RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)) = (II\<^sub>R \<triangleleft> $wait\<^sup>< \<triangleright> ((ok\<^sup>< \<and> RR(P\<^sub>1)) \<longrightarrow>\<^sub>r (ok\<^sup>> \<and> (RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)))))"
    apply (pred_auto) using minus_zero_eq by blast+
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma RHS_design_pre_post_form:
  "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
proof -
  have "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f)\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (simp add: design_subst_ok)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: pre\<^sub>R_def cmt\<^sub>R_def usubst, pred_auto)
  finally show ?thesis .
qed

lemma SRD_as_reactive_design:
  "SRD(P) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
  by (simp add: RHS_design_pre_post_form SRD_RH_design_form)

lemma SRD_reactive_design_alt:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = P"
proof -
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: RHS_design_pre_post_form)
  thus ?thesis
    by (simp add: SRD_reactive_design assms)
qed

lemma SRD_reactive_tri_design_lemma:
  "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>True/wait\<^sup>>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
  by (simp add: SRD_RH_design_form wait'_cond_split)

lemma SRD_as_reactive_tri_design:
  "SRD(P) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
proof -
  have "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>True/wait\<^sup>>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
    by (simp add: SRD_RH_design_form wait'_cond_split)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    apply (simp add: usubst)
    apply (subst design_subst_ok_ok'[THEN sym])
    apply (simp add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst unrest)
    apply (pred_auto)
  done
  finally show ?thesis .
qed

lemma SRD_reactive_tri_design:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
  by (metis Healthy_if SRD_as_reactive_tri_design assms)
    
lemma SRD_elim [RD_elim]: "\<lbrakk> P is SRD; Q(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: SRD_reactive_tri_design)

lemma SRD_elim_ind_1 [RD_elim]: "\<lbrakk> \<And> i. P i is SRD; Q(\<lambda> i. \<^bold>R\<^sub>s(pre\<^sub>R(P i) \<turnstile> peri\<^sub>R(P i) \<diamondop> post\<^sub>R(P i)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: SRD_reactive_tri_design)

lemma SRD_elim_ind_2 [RD_elim]: "\<lbrakk> \<And> i j. P i j is SRD; Q(\<lambda> i j. \<^bold>R\<^sub>s(pre\<^sub>R(P i j) \<turnstile> peri\<^sub>R(P i j) \<diamondop> post\<^sub>R(P i j)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: SRD_reactive_tri_design)

lemma RHS_tri_design_is_SRD [closure]:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is SRD"
  by (rule RHS_design_is_SRD, simp_all add: unrest assms)

lemma SRD_rdes_intro [closure]:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is SRD"
  by (rule RHS_tri_design_is_SRD, simp_all add: unrest closure assms)
        
lemma USUP_R1_R2s_cmt_SRD:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<Squnion> P \<in> A. R1 (R2s (cmt\<^sub>R P))) = (\<Squnion> P \<in> A. cmt\<^sub>R P)"
  by (rule INF_cong[of A], simp, metis R1_R2s_cmt_SRD assms is_Healthy_subset_member)

lemma UINF_R1_R2s_cmt_SRD:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<Sqinter> P \<in> A. R1 (R2s (cmt\<^sub>R P))) = (\<Sqinter> P \<in> A. cmt\<^sub>R P)"
  by (rule SUP_cong[of A], simp, metis (mono_tags, lifting) Ball_Collect R1_R2s_cmt_SRD assms)

subsubsection \<open> Order laws \<close>

lemma preR_antitone: "P \<sqsubseteq> Q \<Longrightarrow> pre\<^sub>R(Q) \<sqsubseteq> pre\<^sub>R(P)"
  by (pred_auto)

lemma periR_monotone: "P \<sqsubseteq> Q \<Longrightarrow> peri\<^sub>R(P) \<sqsubseteq> peri\<^sub>R(Q)"
  by (pred_auto)

lemma postR_monotone: "P \<sqsubseteq> Q \<Longrightarrow> post\<^sub>R(P) \<sqsubseteq> post\<^sub>R(Q)"
  by (pred_auto)

subsection \<open>Non-Divergent Reactive Designs\<close>

(* NDRD P = P \<and> \<^bold>R(true\<^sub>r \<turnstile> true\<^sub>r). *)
definition NDRD :: "('t::trace, '\<alpha>) rp_hrel \<Rightarrow> ('t, '\<alpha>) rp_hrel" where
[pred]: "NDRD P \<equiv> P \<squnion> \<^bold>R(true\<^sub>r \<turnstile> true\<^sub>r)"

lemma NDRD_idem: "NDRD (NDRD P) = NDRD P"
  by (simp add: NDRD_def inf_assoc)

lemma NDRD_Idempotent [closure]: "Idempotent NDRD"
  by (simp add: Idempotent_def NDRD_idem)

lemma NDRD_healthy_iff:
  assumes rd: "P is RD"
  shows "P is NDRD \<longleftrightarrow> pre\<^sub>R P = true\<^sub>r"
proof -
  have fixed: "P is NDRD \<longleftrightarrow> \<^bold>R(true\<^sub>r \<turnstile> true\<^sub>r) \<sqsubseteq> P"
    by (simp add: Healthy_def' NDRD_def ref_lattice.le_iff_sup inf_commute)
  have pre_nd: "pre\<^sub>R (\<^bold>R(true\<^sub>r \<turnstile> true\<^sub>r)) = true\<^sub>r"
    by (simp add: rea_pre_RH_design rpred; pred_auto)
  have intro: "pre\<^sub>R P = true\<^sub>r \<Longrightarrow> \<^bold>R(true\<^sub>r \<turnstile> true\<^sub>r) \<sqsubseteq> P"
  proof -
    assume pre: "pre\<^sub>R P = true\<^sub>r"
    have "\<^bold>R(true\<^sub>r \<turnstile> true\<^sub>r) \<sqsubseteq>
        \<^bold>R(pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
      using pre by (rule_tac rdes_refine_intro; simp)
    then show ?thesis by (simp add: RD_reactive_design_alt[OF rd])
  qed
  show ?thesis
    using fixed pre_nd intro
    by (metis Healthy_if R1_mono R1_preR preR_antitone
        pred_ba.order_antisym rel_theory.utp_bottom)
qed

subsection \<open> Composition laws \<close>

lemma wait_unrest_R2s [unrest]: "$wait\<^sup>< \<sharp> P \<Longrightarrow> $wait\<^sup>< \<sharp> R2s P"
  by (pred_auto)

lemma R2s_wait_subst [usubst]: "R2s Q\<^sub>2\<lbrakk>False/wait\<^sup>>\<rbrakk> = R2s(Q\<^sub>2\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
  by (pred_auto)

lemma cond_and_T_integrate:
  "((P \<and> (b)\<^sub>e) \<or> (Q \<triangleleft> b \<triangleright> R)) = ((P \<or> Q) \<triangleleft> b \<triangleright> R)"
  by (pred_auto)

lemma rea_skip_tr_def: "II\<^sub>r = (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R)"
  by (pred_simp)

lemma unrest_ok_tr_eq [unrest]: "$ok\<^sup>< \<sharp> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e" "$ok\<^sup>> \<sharp> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e"
  by (pred_auto)+

lemma unrest_wait_tr_eq [unrest]: "$wait\<^sup>< \<sharp> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e" "$wait\<^sup>> \<sharp> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e"
  by (pred_auto)+

theorem R1_design_composition_RR:
  assumes "P is RR" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  apply (subst R1_design_composition)
  apply (simp_all add: assms unrest wp_rea_def Healthy_if closure)
  apply (pred_auto)
done

theorem R1_design_composition_RC:
  assumes "P is RC" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1((P \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  by (simp add: R1_design_composition_RR assms unrest Healthy_if closure wp)

subsubsection \<open> Regular \<close>

lemma R2c_conj: "R2c(P \<and> Q) = (R2c P \<and> R2c Q)"
  by pred_auto

lemma seqr_right_one_point_false':
  assumes "vwb_lens x"
  shows "(P ;; (\<not>($x\<^sup><)\<^sub>e \<and> Q)) = (P\<lbrakk>False/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>False/x\<^sup><\<rbrakk>)"
  using assms by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

theorem RH_tri_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>2" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S\<^sub>1" "$ok\<^sup>< \<sharp> S\<^sub>2"
          "$wait\<^sup>< \<sharp> R" "$wait\<^sup>> \<sharp> Q\<^sub>2" "$wait\<^sup>< \<sharp> S\<^sub>1" "$wait\<^sup>< \<sharp> S\<^sub>2"
  shows "(\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       \<^bold>R((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1(R2s Q\<^sub>2) ;; R1 (\<not> R2s R))) \<turnstile>
                       ((Q\<^sub>1 \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> ((R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) =
        (\<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)))"
    by (metis (no_types, opaque_lifting) R1_extend_conj R2s_conj R2s_not R2s_wait' wait'_cond_false)
  have 2: "(R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 (((R1 (R2s Q\<^sub>1)) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
  proof -
    have "(R1 (R2s Q\<^sub>1) ;; (wait\<^sup>< \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                       = (((R1 (R2s Q\<^sub>1)) \<and> wait\<^sup>>))"
    proof -
      have "(R1 (R2s Q\<^sub>1) ;; (wait\<^sup>< \<and> ((\<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
           = (R1 (R2s Q\<^sub>1) ;; (wait\<^sup>< \<and> (\<lceil>II\<rceil>\<^sub>D)))"
        by (simp add: aext_get_fst cond_and_R pred_ba.boolean_algebra.conj_disj_distrib pred_ba.inf.commute subst_apply_SEXP)
      also have "... = ((R1 (R2s Q\<^sub>1) ;; \<lceil>II\<rceil>\<^sub>D) \<and> wait\<^sup>>)"
        by (pred_auto)
      also from assms(2) have "... = ((R1 (R2s Q\<^sub>1)) \<and> wait\<^sup>>)"
        by (pred_auto, blast)
      finally show ?thesis .
    qed

    moreover have "(R1 (R2s Q\<^sub>2) ;; (\<not> wait\<^sup>< \<and> ((\<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                  = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
    proof -
      have "(R1 (R2s Q\<^sub>2) ;; (\<not> wait\<^sup>< \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
            = (R1 (R2s Q\<^sub>2) ;; (\<not> wait\<^sup>< \<and> (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))"
        by (simp add: aext_var cond_and_R pred_ba.boolean_algebra.conj_disj_distrib pred_ba.inf.commute)

      also have "... = ((R1 (R2s Q\<^sub>2))\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk>)"
        by (simp add: aext_var seqr_right_one_point_false')

      also have "... = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest closure rcond_seq_right_distr assms)

      finally show ?thesis .
    qed

    moreover
    have "((R1 (R2s Q\<^sub>1) \<and> wait\<^sup>>) \<or> ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
          = (R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
      by (simp add: wait'_cond_def rcond_seq_right_distr cond_and_T_integrate unrest usubst_eval)

    ultimately show ?thesis
      by (simp add: R2s_wait'_cond R1_wait'_cond wait'_cond_seq pred_ex_simps unrest)  
  qed

  from assms(7,8) have 3: "(R1 (R2s Q\<^sub>2) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R) = R1 (R2s Q\<^sub>2) ;; R1 (\<not> R2s R)"
    by (pred_auto, meson)

  show ?thesis
    by (simp add: RH_design_composition unrest assms 1 2 3, simp add: R1_R2s_R2c RH_design_lemma1)
qed

theorem RH_tri_design_composition_wp:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>2" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S\<^sub>1" "$ok\<^sup>< \<sharp> S\<^sub>2"
          "$wait\<^sup>< \<sharp> R" "$wait\<^sup>> \<sharp> Q\<^sub>2" "$wait\<^sup>< \<sharp> S\<^sub>1" "$wait\<^sup>< \<sharp> S\<^sub>2"
          "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
          "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> ((Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R ((\<not> R1 (\<not> P) ;; R1 true \<and> \<not> Q\<^sub>2 ;; R1 (\<not> R)) \<turnstile> (Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: RH_tri_design_composition assms Healthy_if R2c_healthy_R2s disj_pred_def)
       (metis (no_types, opaque_lifting) R1_negate_R1 R2c_healthy_R2s assms(11,16))
  also have "... = ?rhs"
    by (metis (no_types, opaque_lifting) R1_extend_conj R1_extend_conj' R1_negate_R1 RH_design_neg_R1_pre pred_ba.boolean_algebra.compl_zero pred_ba.boolean_algebra.double_compl rea_not_def wp_rea_def)    
  finally show ?thesis .
qed

theorem RH_tri_design_composition_RR_wp:
  assumes "P is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR"
          "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> ((Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
  by (simp add: RH_tri_design_composition_wp add: closure assms unrest RR_implies_R2c)

lemma RH_tri_normal_design_composition:
  assumes
    "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>2" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S\<^sub>1" "$ok\<^sup>< \<sharp> S\<^sub>2"
    "$wait\<^sup>< \<sharp> R" "$wait\<^sup>> \<sharp> Q\<^sub>2" "$wait\<^sup>< \<sharp> S\<^sub>1" "$wait\<^sup>< \<sharp> S\<^sub>2"
    "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
    "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
    "R1 (\<not> P) ;; R1(true) = R1(\<not> P)"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
        \<^bold>R((R1 (\<not> P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp_all add: RH_tri_design_composition_wp rea_not_def assms unrest)
  also have "... = \<^bold>R((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: assms wp_rea_def ex_unrest, pred_auto)
  finally show ?thesis .
qed

lemma RH_tri_normal_design_composition' [rdes_def]:
  assumes "P is RC" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "R1 (\<not> P) ;; R1 true = R1(\<not> P)"
    using RC_implies_RC1[OF assms(1)]
    by (simp add: Healthy_def RC1_def rea_not_def)
       (metis R1_negate_R1 R1_seqr pred_ba.double_compl)
  thus ?thesis
    by (simp add: RH_tri_normal_design_composition assms closure unrest RR_implies_R2c)
qed

lemma RH_tri_design_right_unit_lemma:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>> \<sharp> R" "$wait\<^sup>> \<sharp> R"
  shows "\<^bold>R(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>C = \<^bold>R((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> (Q \<diamondop> R))"
proof -
  have "\<^bold>R(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>C = \<^bold>R(P \<turnstile> Q \<diamondop> R) ;; \<^bold>R(true \<turnstile> false \<diamondop> (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R))"
    by (simp add: rdes_skip_tri_design, pred_auto)
  also have "... = \<^bold>R ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> Q \<diamondop> (R1 (R2s R) ;; R1 (R2s (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R))))"
    by (simp_all add: RH_tri_design_composition assms unrest R2s_true R1_false R2s_false)
  also have "... = \<^bold>R ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> Q \<diamondop> R1 (R2s R))"
  proof -
    from assms(3,4) have "(R1 (R2s R) ;; R1 (R2s (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R))) = R1 (R2s R)"
      by (pred_auto, metis (no_types, lifting) minus_zero_eq, meson order_refl trace_class.diff_cancel)
    thus ?thesis
      by simp
  qed
  also have "... = \<^bold>R((\<not> (\<not> P) ;; R1 true) \<turnstile> (Q \<diamondop> R))"
    by (metis (no_types, lifting) R1_R2s_R1_true_lemma R1_R2s_R2c R2c_not RH_design_R2c_pre RH_design_neg_R1_pre RH_design_post_R1 RH_design_post_R2s)
  also have "... = \<^bold>R((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> Q \<diamondop> R)"
    by (pred_auto)
  finally show ?thesis .
qed

subsubsection \<open> Stateful \<close>

theorem RHS_tri_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>2" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S\<^sub>1" "$ok\<^sup>< \<sharp> S\<^sub>2"
          "$wait\<^sup>< \<sharp> R" "$wait\<^sup>> \<sharp> Q\<^sub>2" "$wait\<^sup>< \<sharp> S\<^sub>1" "$wait\<^sup>< \<sharp> S\<^sub>2"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1(R2s Q\<^sub>2) ;; R1 (\<not> R2s R))) \<turnstile>
                       (((\<exists> st\<^sup>> \<Zspot> Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> ((R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) =
        (\<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)))"
    by (metis (no_types, opaque_lifting) R1_extend_conj R2s_conj R2s_not R2s_wait' wait'_cond_false)
  have 2: "(R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 (((\<exists> st\<^sup>> \<Zspot> R1 (R2s Q\<^sub>1)) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
  proof -
    have "(R1 (R2s Q\<^sub>1) ;; (wait\<^sup>< \<and> ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                       = (\<exists> st\<^sup>> \<Zspot> ((R1 (R2s Q\<^sub>1)) \<and> wait\<^sup>>))"
    proof -
      have "(R1 (R2s Q\<^sub>1) ;; (wait\<^sup>< \<and> ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
           = (R1 (R2s Q\<^sub>1) ;; (wait\<^sup>< \<and> (\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D)))"
        by (pred_auto, blast+)
      also have "... = ((R1 (R2s Q\<^sub>1) ;; (\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D)) \<and> wait\<^sup>>)"
        by (pred_auto)
      also from assms(2) have "... = (\<exists> st\<^sup>> \<Zspot> ((R1 (R2s Q\<^sub>1)) \<and> wait\<^sup>>))"
        by (pred_auto, blast)
      finally show ?thesis .
    qed

    moreover have "(R1 (R2s Q\<^sub>2) ;; (\<not> wait\<^sup>< \<and> ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                  = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
    proof -
      have "(R1 (R2s Q\<^sub>2) ;; (\<not> wait\<^sup>< \<and> ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
            = (R1 (R2s Q\<^sub>2) ;; (\<not> wait\<^sup>< \<and> (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))"
        by (simp add: aext_var cond_and_R pred_ba.boolean_algebra.conj_disj_distrib pred_ba.inf.commute)

      also have "... = ((R1 (R2s Q\<^sub>2))\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk>)"
        by (simp add: aext_var seqr_right_one_point_false')

      also have "... = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms closure)

      finally show ?thesis .
    qed

    moreover
    have "((R1 (R2s Q\<^sub>1) \<and> wait\<^sup>>) \<or> ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
          = (R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
      by (simp add: wait'_cond_def rcond_seq_right_distr cond_and_T_integrate usubst_eval unrest)
      
    ultimately show ?thesis
      apply (simp add: R2s_wait'_cond R1_wait'_cond wait'_cond_seq pred_ex_simps unrest usubst_eval)
      apply (simp add: cond_and_T_integrate rcond_seq_right_distr unrest wait'_cond_def)
      done
  qed

  from assms(7,8) have 3: "(R1 (R2s Q\<^sub>2) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R) = R1 (R2s Q\<^sub>2) ;; R1 (\<not> R2s R)"
    by (pred_auto, blast, meson)

  show ?thesis
    apply (subst RHS_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2 3)
    apply (simp add: R1_R2s_R2c RHS_design_lemma1)
    apply (metis R1_R2c_ex_st RHS_design_lemma1)
  done
qed
 
theorem RHS_tri_design_composition_wp:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>2" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S\<^sub>1" "$ok\<^sup>< \<sharp> S\<^sub>2"
          "$wait\<^sup>< \<sharp> R" "$wait\<^sup>> \<sharp> Q\<^sub>2" "$wait\<^sup>< \<sharp> S\<^sub>1" "$wait\<^sup>< \<sharp> S\<^sub>2"
          "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
          "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R\<^sub>s(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (((\<exists> st\<^sup>> \<Zspot> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s ((\<not> R1 (\<not> P) ;; R1 true \<and> \<not> Q\<^sub>2 ;; R1 (\<not> R)) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: RHS_tri_design_composition assms Healthy_if R2c_healthy_R2s disj_pred_def)
       (metis (no_types, opaque_lifting) R1_negate_R1 R2c_healthy_R2s assms(11,16))
  also have "... = ?rhs"
    by (metis (no_types, lifting) R1_conj R1_design_R1_pre rea_not_def rea_not_false wp_rea_def)
  finally show ?thesis .
qed

theorem RHS_tri_design_composition_RR_wp:
  assumes "P is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR"
          "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R\<^sub>s(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (((\<exists> st\<^sup>> \<Zspot> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
  by (simp add: RHS_tri_design_composition_wp add: closure assms unrest RR_implies_R2c)

lemma RHS_tri_normal_design_composition:
  assumes
    "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>2" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S\<^sub>1" "$ok\<^sup>< \<sharp> S\<^sub>2"
    "$wait\<^sup>< \<sharp> R" "$wait\<^sup>> \<sharp> Q\<^sub>2" "$wait\<^sup>< \<sharp> S\<^sub>1" "$wait\<^sup>< \<sharp> S\<^sub>2"
    "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
    "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
    "R1 (\<not> P) ;; R1(true) = R1(\<not> P)" "$st\<^sup>> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
        \<^bold>R\<^sub>s ((R1 (\<not> P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp_all add: RHS_tri_design_composition_wp rea_not_def assms unrest)
  also have "... = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: assms wp_rea_def ex_unrest, pred_auto)
  finally show ?thesis .
qed
  
lemma RHS_tri_normal_design_composition' [rdes_def]:
  assumes "P is RC" "Q\<^sub>1 is RR" "$st\<^sup>> \<sharp> Q\<^sub>1" "Q\<^sub>2 is RR" "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "R1 (\<not> P) ;; R1 true = R1(\<not> P)"
    using RC_implies_RC1[OF assms(1)]
    by (simp add: Healthy_def RC1_def rea_not_def)
       (metis R1_negate_R1 R1_seqr pred_ba.boolean_algebra.double_compl)
       
  thus ?thesis
    by (simp add: RHS_tri_normal_design_composition assms closure unrest RR_implies_R2c)
qed

lemma RHS_tri_design_right_unit_lemma:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>> \<sharp> R" "$wait\<^sup>> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> Q) \<diamondop> R))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R))"
    by (simp add: srdes_skip_tri_design rea_skip_tr_def R1_design_R1_pre)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> st\<^sup>> \<Zspot> Q) \<diamondop> (R1 (R2s R) ;; R1 (R2s (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R))))"
    by (simp_all add: RHS_tri_design_composition assms unrest R2s_true R1_false R2s_false)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> st\<^sup>> \<Zspot> Q) \<diamondop> R1 (R2s R))"
  proof -
    from assms(3,4) have "(R1 (R2s R) ;; R1 (R2s (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R))) = R1 (R2s R)"
      by (pred_auto, metis (no_types, lifting) minus_zero_eq, meson order_refl trace_class.diff_cancel)
    thus ?thesis
      by simp
  qed
  also have "... = \<^bold>R\<^sub>s((\<not> (\<not> P) ;; R1 true) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> Q) \<diamondop> R))"
    by (metis (no_types, lifting) R1_R2s_R1_true_lemma R1_R2s_R2c R2c_not RHS_design_R2c_pre RHS_design_neg_R1_pre RHS_design_post_R1 RHS_design_post_R2s)
  also have "... = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> Q) \<diamondop> R))"
    by (pred_simp, blast)
  finally show ?thesis .
qed

lemma RD_composition_wp:
  assumes "P is RD" "Q is RD"
  shows "(P ;; Q) = \<^bold>R (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
  (is "?lhs = ?rhs")
proof -
  have "(P ;; Q) = (\<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; \<^bold>R(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: RD_reactive_tri_design assms(1) assms(2))
  also from assms
  have "... = ?rhs"
    by (simp add: RH_tri_design_composition_wp unrest closure disj_pred_def)
  finally show ?thesis .
qed

lemma SRD_composition_wp:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile>
                       ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
  (is "?lhs = ?rhs")
proof -
  have "(P ;; Q) = (\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: SRD_reactive_tri_design assms(1) assms(2))
  also from assms
  have "... = ?rhs"
    by (simp add: RHS_tri_design_composition_wp disj_pred_def unrest assms closure)
  finally show ?thesis .
qed

subsection \<open> Refinement introduction laws \<close>

subsubsection \<open> Regular \<close>

lemma RH_tri_design_refine:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2` \<and> `P\<^sub>1 \<and> Q\<^sub>3 \<longrightarrow> P\<^sub>3`"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3 \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (simp add: RH_design_refine assms closure RR_implies_R2c unrest ex_unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `(P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (pred_auto)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>True/wait\<^sup>>\<rbrakk>` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>False/wait\<^sup>>\<rbrakk>`"
    by (pred_auto, metis)
  also have "... \<longleftrightarrow> ?rhs"
    by (simp add: usubst subst_apply_SEXP unrest assms, pred_simp)
  finally show ?thesis .
qed

lemma RH_tri_design_refine':
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> (Q\<^sub>1 \<sqsubseteq> P\<^sub>1) \<and> (P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)) \<and> (P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3))"
  by (simp add: RH_tri_design_refine assms, pred_auto)

lemma rdes_tri_refine_intro:
  assumes "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> Q\<^sub>1`" "`P\<^sub>1 \<and> R\<^sub>2 \<longrightarrow> R\<^sub>1`"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac rdes_refine_intro, simp_all, pred_auto)  
    
lemma rdes_tri_refine_intro':
  assumes "P\<^sub>2 \<sqsubseteq> P\<^sub>1" "Q\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)" "R\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> R\<^sub>2)"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac rdes_tri_refine_intro, simp_all add: pred_refine_as_impl, pred_simp+)

subsubsection \<open> Stateful \<close>

lemma RHS_tri_design_refine:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2` \<and> `P\<^sub>1 \<and> Q\<^sub>3 \<longrightarrow> P\<^sub>3`"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3 \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (simp add: RHS_design_refine assms closure RR_implies_R2c unrest ex_unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `(P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (pred_auto)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>True/wait\<^sup>>\<rbrakk>` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>False/wait\<^sup>>\<rbrakk>`"
    by (pred_auto, metis)
  also have "... \<longleftrightarrow> ?rhs"
    by (simp add: usubst unrest subst_apply_SEXP assms, pred_simp)
  finally show ?thesis .
qed

lemma RHS_tri_design_refine':
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> (Q\<^sub>1 \<sqsubseteq> P\<^sub>1) \<and> (P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)) \<and> (P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3))"
  by (simp add: RHS_tri_design_refine assms, pred_auto)

lemma srdes_tri_refine_intro:
  assumes "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> Q\<^sub>1`" "`P\<^sub>1 \<and> R\<^sub>2 \<longrightarrow> R\<^sub>1`"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac srdes_refine_intro, simp_all, pred_auto)  
    
lemma srdes_tri_refine_intro':
  assumes "P\<^sub>2 \<sqsubseteq> P\<^sub>1" "Q\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)" "R\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> R\<^sub>2)"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac srdes_tri_refine_intro; pred_simp)

lemma SRD_peri_under_pre:
  assumes "P is SRD" "$wait\<^sup>> \<sharp> pre\<^sub>R(P)"
  shows "(pre\<^sub>R(P) \<longrightarrow>\<^sub>r peri\<^sub>R(P)) = peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(P) =
        peri\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = (pre\<^sub>R P \<longrightarrow>\<^sub>r peri\<^sub>R P)"
    by (simp add: rea_pre_RHS_design rea_peri_RHS_design assms 
        unrest usubst R1_peri_SRD R2c_preR R1_rea_impl R2c_rea_impl R2c_periR)
  finally show ?thesis ..
qed

lemma SRD_post_under_pre:
  assumes "P is SRD" "$wait\<^sup>> \<sharp> pre\<^sub>R(P)"
  shows "(pre\<^sub>R(P) \<longrightarrow>\<^sub>r post\<^sub>R(P)) = post\<^sub>R(P)"
proof -
  have "post\<^sub>R(P) =
        post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = (pre\<^sub>R P \<longrightarrow>\<^sub>r post\<^sub>R P)"
    by (simp add: rea_pre_RHS_design rea_post_RHS_design assms 
        unrest usubst R1_post_SRD R2c_preR R1_rea_impl R2c_rea_impl R2c_postR)
  finally show ?thesis ..
qed

lemma SRD_refine_intro:
  assumes
    "P is SRD" "Q is SRD"
    "`pre\<^sub>R(P) \<longrightarrow> pre\<^sub>R(Q)`" "`pre\<^sub>R(P) \<and> peri\<^sub>R(Q) \<longrightarrow> peri\<^sub>R(P)`" "`pre\<^sub>R(P) \<and> post\<^sub>R(Q) \<longrightarrow> post\<^sub>R(P)`"
  shows "P \<sqsubseteq> Q"
proof -
  have "SRD P \<sqsubseteq> SRD Q"
    by (simp add: SRD_as_reactive_tri_design assms(3) assms(4) assms(5) srdes_tri_refine_intro)
  then show ?thesis
    by (metis Healthy_def' assms(1) assms(2))
qed
  

lemma SRD_refine_intro':
  assumes
    "P is SRD" "Q is SRD"
    "`pre\<^sub>R(P) \<longrightarrow> pre\<^sub>R(Q)`" "peri\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> peri\<^sub>R(Q))" "post\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(Q))"
  shows "P \<sqsubseteq> Q"
  using assms by (rule_tac SRD_refine_intro, simp_all add: pred_refine_as_impl; pred_simp)
 
lemma SRD_eq_intro:
  assumes
    "P is SRD" "Q is SRD" "pre\<^sub>R(P) = pre\<^sub>R(Q)" "peri\<^sub>R(P) = peri\<^sub>R(Q)" "post\<^sub>R(P) = post\<^sub>R(Q)"
  shows "P = Q"
  by (metis SRD_reactive_tri_design assms)

lemma srdes_tri_eq_iff:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> (P\<^sub>1 = Q\<^sub>1 \<and> (P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2) \<and> (P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> 
        (\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<and> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3))"
    by fastforce
  also have "... = (Q\<^sub>1 \<sqsubseteq> P\<^sub>1 \<and> P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2) \<and> P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3) \<and> P\<^sub>1 \<sqsubseteq> Q\<^sub>1 \<and> Q\<^sub>2 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>2) \<and> Q\<^sub>3 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>3))"
    by (simp add: RHS_tri_design_refine' assms)
  also have "... = (P\<^sub>1 = Q\<^sub>1 \<and> P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2) \<and> P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3) \<and> Q\<^sub>2 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>2) \<and> Q\<^sub>3 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>3))"
    by fastforce
  also have "... = (P\<^sub>1 = Q\<^sub>1 \<and> (P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2) \<and> (P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3))"
    by (safe, simp_all add: pred_ba.inf.absorb_iff1 pred_ba.inf.left_commute pred_ba.inf_commute)
  finally show ?thesis .
qed

lemma rdes_tri_eq_intro:
  assumes "P\<^sub>1 = Q\<^sub>1" "(P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2)" "(P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3)"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)

lemma srdes_tri_eq_intro:
  assumes "P\<^sub>1 = Q\<^sub>1" "(P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2)" "(P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3)"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)

lemma rdes_tri_eq_intro':
  assumes "P\<^sub>1 = Q\<^sub>1" "P\<^sub>2 = Q\<^sub>2" "P\<^sub>3 = Q\<^sub>3"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  using assms by (simp)

lemma srdes_tri_eq_R1_R2c_intro:
  assumes "R1 (R2c P\<^sub>1) = R1 (R2c Q\<^sub>1)" "R1 (R2c (P\<^sub>1 \<and> Q\<^sub>2)) = R1 (R2c (Q\<^sub>1 \<and> P\<^sub>2))" "R1 (R2c (P\<^sub>1 \<and> Q\<^sub>3)) = R1 (R2c (Q\<^sub>1 \<and> P\<^sub>3))"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(R2c P\<^sub>1 \<turnstile> R2c P\<^sub>2 \<diamondop> R2c P\<^sub>3)"
    by (metis (no_types, opaque_lifting) R1_R2s_R2c RHS_design_R2c_pre RHS_design_peri_R2c RHS_design_post_R1
        RHS_design_post_R2s)
  also have "... = \<^bold>R\<^sub>s(R1 (R2c P\<^sub>1) \<turnstile> R1 (R2c P\<^sub>2) \<diamondop> R1 (R2c P\<^sub>3))"
    by (simp add: R1_design_R1_pre RHS_design_peri_R1 RHS_design_post_R1)
  also have "... = \<^bold>R\<^sub>s(R1 (R2c Q\<^sub>1) \<turnstile> R1 (R2c Q\<^sub>2) \<diamondop> R1 (R2c Q\<^sub>3))"
    by (metis (no_types, lifting) R1_extend_conj R2c_conj RHS_design_peri_R1 RHS_design_post_R1 assms(1,2,3)
        srdes_tri_eq_intro)
  also have "... = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
    by (metis (no_types, opaque_lifting) R1_R2s_R2c R1_design_R1_pre RHS_design_R2c_pre RHS_design_peri_R1 RHS_design_peri_R2s
        RHS_design_post_R1 RHS_design_post_R2s)
  finally show ?thesis .
qed

lemma srdes_tri_eq_intro':
  assumes "P\<^sub>1 = Q\<^sub>1" "P\<^sub>2 = Q\<^sub>2" "P\<^sub>3 = Q\<^sub>3"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  using assms by (simp)

subsection \<open> Closure laws \<close>

subsubsection \<open> Regular \<close>

lemma RD_srdes_skip [closure]: "II\<^sub>C is RD"
  by (simp add: rdes_skip_def RH_design_is_RD unrest)
 
lemma RD_seqr_closure [closure]:
  assumes "P is RD" "Q is RD"
  shows "(P ;; Q) is RD"
proof -
  have 1:"(P ;; Q) = \<^bold>R (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile> 
                       (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: RD_composition_wp assms(1) assms(2))
  also have 2:"... is RD"
    by (rule RH_design_is_RD, simp_all add: wp_rea_def unrest)
  show ?thesis
    by (simp add: 1 2)
qed

lemma RD_power_Suc [closure]: "P is RD \<Longrightarrow> P\<^bold>^(Suc n) is RD"
proof (induct n)
  case 0
  then show ?case
    by (simp)
next
  case (Suc n)
  then show ?case
    using RD_seqr_closure by (simp add: RD_seqr_closure upred_semiring.power_Suc) 
qed

lemma RD_power_comp [closure]: "P is RD \<Longrightarrow> P ;; P\<^bold>^n is RD"
  by (metis RD_power_Suc upred_semiring.power_Suc)

lemma uplus_RD_closed [closure]: "P is RD \<Longrightarrow> P\<^bold>+ is RD"
  by (simp add: uplus_power_def closure)

subsubsection \<open> Stateful \<close>

lemma SRD_srdes_skip [closure]: "II\<^sub>R is SRD"
  by (simp add: srdes_skip_def RHS_design_is_SRD unrest)

lemma unrest_ex_out [unrest]:
  "\<lbrakk> mwb_lens x; $x \<sharp> P; x \<bowtie> y \<rbrakk> \<Longrightarrow> $x \<sharp> (\<exists> y \<Zspot> P)"
  by (simp add: ex_expr_def unrest_lens, metis lens_indep.lens_put_comm)


lemma SRD_seqr_closure [closure]:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) is SRD"
proof -
  have 1:"(P ;; Q) = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile> 
                       ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: SRD_composition_wp assms(1) assms(2))
  have 2:"... is SRD"
    by (rule RHS_design_is_SRD, simp_all add: wp_rea_def unrest)
  show ?thesis by (simp add: 1 2)
qed

lemma SRD_power_Suc [closure]: "P is SRD \<Longrightarrow> P\<^bold>^(Suc n) is SRD"
proof (induct n)
  case 0
  then show ?case
    by (simp)
next
  case (Suc n)
  then show ?case
    using SRD_seqr_closure by (simp add: SRD_seqr_closure upred_semiring.power_Suc) 
qed

lemma SRD_power_comp [closure]: "P is SRD \<Longrightarrow> P ;; P\<^bold>^n is SRD"
  by (metis SRD_power_Suc upred_semiring.power_Suc)

lemma uplus_SRD_closed [closure]: "P is SRD \<Longrightarrow> P\<^bold>+ is SRD"
  by (simp add: uplus_power_def closure)

lemma SRD_Sup_closure [closure]:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H" "A \<noteq> {}"
  shows "(\<Sqinter> A) is SRD"
proof -
  have "SRD (\<Sqinter> A) = (\<Sqinter> (SRD `A))"
    by (meson Continuous_def SRD_Continuous assms(2))
  also have "... = (\<Sqinter> A)"
    by (simp only: Healthy_carrier_image assms)
  finally show ?thesis by (simp add: Healthy_def)
qed

subsection \<open> Distribution laws \<close>

lemma RHS_tri_design_choice [rdes_def]: 
  "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqinter> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3))"
  apply (simp add: RHS_design_choice)
  apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"])
   apply (simp)
  apply (pred_auto)
  done

lemma RHS_tri_design_disj [rdes_def]: 
  "(\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<or> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3))"
  by (simp add: RHS_tri_design_choice disj_pred_def)

lemma RHS_tri_design_sup [rdes_def]: 
  "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<squnion> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R\<^sub>s((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2)) \<diamondop> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3)))"
proof -
  have 1: "R2((P\<^sub>1 \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow> Q\<^sub>2 \<diamondop> Q\<^sub>3)) = R2(((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2)) \<diamondop> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3)))"
    by pred_auto
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<squnion> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R\<^sub>s ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: RHS_design_sup)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> R2((P\<^sub>1 \<longrightarrow> P\<^sub>2 \<diamondop> P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (meson RHS_design_export_R2)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> R2(((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2)) \<diamondop> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3))))"
    by (simp add: 1)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2)) \<diamondop> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3)))"
    by (metis RHS_design_export_R2)
  finally show ?thesis .
qed

lemma RHS_tri_design_conj [rdes_def]: 
  "(\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<and> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)) = \<^bold>R\<^sub>s((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2)) \<diamondop> ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3)))"
  by (simp add: RHS_tri_design_sup conj_pred_def)

lemma SRD_UINF [rdes_def]:
  assumes "A \<noteq> {}" "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "\<Sqinter> A = \<^bold>R\<^sub>s((\<Squnion> P\<in>A. pre\<^sub>R(P)) \<turnstile> (\<Sqinter> P\<in>A. peri\<^sub>R(P)) \<diamondop> (\<Sqinter> P\<in>A. post\<^sub>R(P)))"
proof -
  have "\<Sqinter> A = \<^bold>R\<^sub>s(pre\<^sub>R(\<Sqinter> A) \<turnstile> peri\<^sub>R(\<Sqinter> A) \<diamondop> post\<^sub>R(\<Sqinter> A))"
    by (metis SRD_as_reactive_tri_design assms srdes_theory.healthy_inf srdes_theory.healthy_inf_def)
  also have "... = \<^bold>R\<^sub>s((\<Squnion> P\<in>A. pre\<^sub>R(P)) \<turnstile> (\<Sqinter> P\<in>A. peri\<^sub>R(P)) \<diamondop> (\<Sqinter> P\<in>A. post\<^sub>R(P)))"
    by (simp add: preR_INF periR_INF postR_INF assms)
  finally show ?thesis .
qed

lemma RHS_tri_design_USUP [rdes_def]:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A. \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i) \<diamondop> R(i))) = \<^bold>R\<^sub>s((\<Squnion> i \<in> A. P(i)) \<turnstile> (\<Sqinter> i \<in> A. Q(i)) \<diamondop> (\<Sqinter> i \<in> A. R(i)))"
proof -
  have 1:"(\<Sqinter>x\<in>A. Q x \<diamondop> R x) = (\<Sqinter> (Q ` A) \<diamondop> \<Sqinter> (R ` A))"
    by pred_auto
  thus ?thesis
    by (simp add: RHS_design_USUP assms)
qed

lemma SRD_UINF_mem:
  assumes "A \<noteq> {}" "\<And> i. P i is SRD"
  shows "(\<Sqinter> i\<in>A. P i) = \<^bold>R\<^sub>s((\<Squnion> i\<in>A. pre\<^sub>R(P i)) \<turnstile> (\<Sqinter> i\<in>A. peri\<^sub>R(P i)) \<diamondop> (\<Sqinter> i\<in>A. post\<^sub>R(P i)))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs =  \<^bold>R\<^sub>s ((\<Squnion> Pa \<in> P ` A. pre\<^sub>R Pa) \<turnstile> (\<Sqinter> Pa \<in> P ` A. peri\<^sub>R Pa) \<diamondop> (\<Sqinter> Pa \<in> P ` A. post\<^sub>R Pa))"
    by (subst rdes_def, simp_all add: assms image_subsetI)
  also have "... = ?rhs"
    by (pred_auto)
  finally show ?thesis .
qed

lemma RHS_tri_design_UINF_ind [rdes_def]:
  "(\<Sqinter> i. \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) = \<^bold>R\<^sub>s((\<Squnion> i. P\<^sub>1 i) \<turnstile> (\<Sqinter> i. P\<^sub>2(i)) \<diamondop> (\<Sqinter> i. P\<^sub>3(i)))"
  by (simp add: RHS_tri_design_USUP)

lemma cond_srea_form [rdes_def]:
  "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
   \<^bold>R\<^sub>s((P \<triangleleft> b \<triangleright>\<^sub>R R) \<turnstile> (Q\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>1) \<diamondop> (Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) = \<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<triangleleft> R2c(\<lceil>b\<rceil>\<^sub>S\<^sub><) \<triangleright> \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)"
    by (pred_auto)
  also have "... = \<^bold>R\<^sub>s (P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)"
    by (simp add: RHS_cond lift_cond_srea_def)
  also have "... = \<^bold>R\<^sub>s ((P \<triangleleft> b \<triangleright>\<^sub>R R) \<turnstile> (Q\<^sub>1 \<diamondop> Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>1 \<diamondop> S\<^sub>2))"
    by (simp add: design_condr lift_cond_srea_def)
       (metis design_condr drop_pre_inv out_alpha_unrest_st_lift_pre rcond_alt_def)
  also have "... = \<^bold>R\<^sub>s((P \<triangleleft> b \<triangleright>\<^sub>R R) \<turnstile> (Q\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>1) \<diamondop> (Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>2))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  finally show ?thesis .
qed

lemma SRD_cond_srea [closure]:
  assumes "P is SRD" "Q is SRD"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is SRD"
proof -
  have 1:"P \<triangleleft> b \<triangleright>\<^sub>R Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    by (simp add: SRD_reactive_tri_design assms)
  have 2:"... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> (post\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R post\<^sub>R Q))"
    by (simp add: cond_srea_form)
  have 3:"... is SRD"
    by (simp add: RHS_tri_design_is_SRD lift_cond_srea_def unrest)
  show ?thesis by (simp add: 1 2 3)
qed

subsection \<open> Algebraic laws \<close>

lemma RD_left_unit:
  assumes "P is RD"
  shows "II\<^sub>C ;; P = P"
  by (simp add: RD1_left_unit RD_healths(1) RD_healths(4) assms)

lemma skip_rdes_self_unit [simp]:
  "II\<^sub>C ;; II\<^sub>C = II\<^sub>C"
  by (simp add: RD_left_unit closure)

lemma ex_expr_false: "(\<exists> x \<Zspot> false) = false"
  by (pred_auto)

lemma SRD_left_unit:
  assumes "P is SRD"
  shows "II\<^sub>R ;; P = P"
  by (simp add: SRD_composition_wp closure rdes wp ex_expr_false R1_negate_R1 R1_false 
      rpred trace_ident_left_periR trace_ident_left_postR SRD_reactive_tri_design assms)

lemma skip_srea_self_unit [simp]:
  "II\<^sub>R ;; II\<^sub>R = II\<^sub>R"
  by (simp add: SRD_left_unit closure)

lemma SRD_right_unit_tri_lemma:
  assumes "P is SRD"
  shows "P ;; II\<^sub>R = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> (\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
  by (simp add: SRD_composition_wp closure rdes wp rpred trace_ident_right_postR assms)

lemma Miracle_left_zero:
  assumes "P is SRD"
  shows "Miracle ;; P = Miracle"
proof -
  have "Miracle ;; P = \<^bold>R\<^sub>s(true \<turnstile> false) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: Miracle_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (simp add: RHS_design_composition unrest R1_false R2s_false R2s_true)
  also have "... = Miracle"
    by (simp add: Miracle_def)
  finally show ?thesis .
qed

lemma Chaos_left_zero:
  assumes "P is SRD"
  shows "(Chaos ;; P) = Chaos"
proof -
  have "Chaos ;; P = \<^bold>R\<^sub>s(false \<turnstile> true) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: Chaos_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 true \<and> \<not> (R1 true \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s (pre\<^sub>R P))) \<turnstile>
                       (R1 true ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s (cmt\<^sub>R P)))))"
    by (simp add: RHS_design_composition unrest R2s_false R2s_true R1_false)
  also have "... = \<^bold>R\<^sub>s ((false \<and> \<not> (R1 true \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s (pre\<^sub>R P))) \<turnstile>
                       (R1 true ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> R1 (R2s (cmt\<^sub>R P)))))"
    by (simp add: RHS_design_conj_neg_R1_pre)
  also have "... = \<^bold>R\<^sub>s(true)"
    by (simp add: design_false_pre)
  also have "... = \<^bold>R\<^sub>s(false \<turnstile> true)"
    by pred_simp
  also have "... = Chaos"
    by (simp add: Chaos_def)
  finally show ?thesis .
qed

lemma SRD_right_Chaos_tri_lemma:
  assumes "P is SRD"
  shows "P ;; Chaos = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r false) \<turnstile> (\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> false)"
  by (simp add: SRD_composition_wp closure rdes assms wp, pred_auto)

lemma SRD_right_Miracle_tri_lemma:
  assumes "P is SRD"
  shows "P ;; Miracle = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> (\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> false)"
  by (simp add: SRD_composition_wp closure rdes assms wp, pred_simp)

text \<open> Reactive designs are left unital \<close>

interpretation rdes_left_unital: utp_theory_left_unital "RD" "II\<^sub>C"
  by (unfold_locales, simp_all add: closure RD_left_unit)

text \<open> Stateful reactive designs are left unital \<close>

interpretation srdes_left_unital: utp_theory_left_unital "SRD" "II\<^sub>R"
  by (unfold_locales, simp_all add: closure SRD_left_unit)

subsection \<open> Recursion laws \<close>

lemma pred_ref_monoI:
  fixes F :: "'\<alpha> pred \<Rightarrow> '\<beta> pred"
  assumes "(\<And>P Q. P \<sqsubseteq> Q \<Longrightarrow> F P \<sqsubseteq> F Q)"
  shows "mono F"
  using assms by (simp add: monoI pred_ref_iff_le)

lemma mono_srd_iter:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "mono (\<lambda>X. \<^bold>R\<^sub>s(pre\<^sub>R(F X) \<turnstile> peri\<^sub>R(F X) \<diamondop> post\<^sub>R (F X)))"
  apply (rule pred_ref_monoI)
  apply (rule srdes_tri_refine_intro')
  apply (simp add: assms(1) preR_antitone pred_ref_monoD)
  apply (metis assms(1) periR_monotone pred_ba.inf.coboundedI2 pred_ref_monoD)
  apply (simp add: assms(1) postR_monotone pred_ba.inf.coboundedI2 pred_ref_monoD)
done

lemma mu_srd_SRD:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<mu> X. \<^bold>R\<^sub>s (pre\<^sub>R (F X) \<turnstile> peri\<^sub>R (F X) \<diamondop> post\<^sub>R (F X))) is SRD"
  apply (subst gfp_unfold)
  apply (simp add: mono_srd_iter assms)
  apply (rule RHS_tri_design_is_SRD)
  apply (simp_all add: unrest)
done

lemma mu_srd_iter:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<mu> X. \<^bold>R\<^sub>s(pre\<^sub>R(F(X)) \<turnstile> peri\<^sub>R(F(X)) \<diamondop> post\<^sub>R(F(X)))) = F(\<mu> X. \<^bold>R\<^sub>s(pre\<^sub>R(F(X)) \<turnstile> peri\<^sub>R(F(X)) \<diamondop> post\<^sub>R(F(X))))"
  apply (subst gfp_unfold)
   apply (simp add: mono_srd_iter assms)
  apply (subst SRD_as_reactive_tri_design[THEN sym])
  apply (simp add: Healthy_apply_closed SRD_as_reactive_design SRD_reactive_design_alt assms(1) assms(2) mu_srd_SRD)
  done

lemma mu_srd_form:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "\<mu>\<^sub>R F = (\<mu> X. \<^bold>R\<^sub>s(pre\<^sub>R(F(X)) \<turnstile> peri\<^sub>R(F(X)) \<diamondop> post\<^sub>R(F(X))))"
proof -
  have 1: "F (\<mu> X. \<^bold>R\<^sub>s(pre\<^sub>R (F X) \<turnstile> peri\<^sub>R(F X) \<diamondop> post\<^sub>R (F X))) is SRD"
    by (simp add: Healthy_apply_closed assms(1) assms(2) mu_srd_SRD)
  have 2:"Mono\<^bsub>utp_order SRD\<^esub> F"
    by (simp add: assms(1) mono_Monotone_utp_order)
  hence 3:"\<mu>\<^sub>R F = F (\<mu>\<^sub>R F)"
    by (simp add: srdes_theory.LFP_unfold[THEN sym] assms)
  hence "\<^bold>R\<^sub>s(pre\<^sub>R (F (F (\<mu>\<^sub>R F))) \<turnstile> peri\<^sub>R (F (F (\<mu>\<^sub>R F))) \<diamondop> post\<^sub>R (F (F (\<mu>\<^sub>R F)))) = \<mu>\<^sub>R F"
    using SRD_reactive_tri_design by force
  hence "(\<mu> X. \<^bold>R\<^sub>s(pre\<^sub>R (F X) \<turnstile> peri\<^sub>R(F X) \<diamondop> post\<^sub>R (F X))) \<sqsubseteq> F (\<mu>\<^sub>R F)"
    by (metis (no_types, lifting) "3" gfp_upperbound pred_ba.order.eq_iff ref_by_pred_is_leq)
  thus ?thesis
    using assms 1 3 srdes_theory.weak.LFP_lowerbound eq_iff mu_srd_iter
    by (metis (mono_tags, lifting) pred_ba.dual_order.eq_iff)
qed

lemma Monotonic_SRD_comp [closure]: "Monotonic ((;;) P \<circ> SRD)"
  by (rule pred_ref_monoI, simp add: R1_R2c_is_R2 R2_mono R3h_mono RD1_mono RD2_mono RHS_def SRD_def seqr_mono)

end