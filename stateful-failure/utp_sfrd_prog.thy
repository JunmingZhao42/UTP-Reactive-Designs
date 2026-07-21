section \<open> Stateful-Failure Programs \<close>

theory utp_sfrd_prog
  imports
    utp_sfrd_extchoice
begin

subsection \<open> Conditionals \<close>

lemma NCSP_cond_srea [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is NCSP"
  by (rule NCSP_NSRD_intro, simp_all add: closure rdes assms unrest)

subsection \<open> Guarded commands \<close>

lemma GuardedCommR_NCSP_closed [closure]: 
  assumes "P is NCSP"
  shows "g \<rightarrow>\<^sub>R P is NCSP"
  by (simp add: gcmd_def closure assms)

subsection \<open> Alternation \<close>

lemma AlternateR_NCSP_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P(i) is NCSP" "Q is NCSP"
  shows "AlternateR A g P Q is NCSP"
proof (cases "A = {}")
  case True
  then show ?thesis
    by (simp add: AlternateR_def GuardedCommR_NCSP_closed assms(2))
next
  case False
  then show ?thesis
    by (simp add: AlternateR_def closure assms)
qed

lemma AlternateR_list_NCSP_closed [closure]:
  assumes "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is NCSP" "Q is NCSP"
  shows "(AlternateR_list A Q) is NCSP"
  apply (simp add: AlternateR_list_def)
  apply (rule AlternateR_NCSP_closed)
  apply (auto simp add: assms)
  apply (metis assms(1) eq_snd_iff nth_mem)
  done

subsection \<open> Specification Statement \<close>

definition SpecC :: "('a \<Longrightarrow> 's) \<Rightarrow> 's pred \<Rightarrow> 's pred \<Rightarrow> ('s, 'e) sfrd hrel" ("_:[_,_]\<^sub>C" [999,0,0] 999) where
[rdes_def]: "SpecC frm P Q = \<^bold>R\<^sub>s([P]\<^sub>S\<^sub>< \<turnstile> false \<diamondop> [$frm:[Q\<^sup>>]]\<^sub>S)"

lemma SpecC_is_NCSP [closure]: "frm:[P,Q]\<^sub>C is NCSP"
  apply (simp add: SpecC_def)
  apply (rule NCSP_rdes_intro)
      apply (simp_all add: closure unrest)
   apply (pred_auto)+
  done

lemma SpecC_skip: "{}\<^sub>v:[true,true]\<^sub>C = Skip"
  by (rdes_eq)

lemma SpecC_false_pre: "a:[false,q]\<^sub>C = Chaos"
  by (rdes_eq)

(*
lemma SpecC_false_post: "a:[true,false]\<^sub>C = Miracle"
  by (rdes_eq)

lemma SpecC_refine_seq:
  "vwb_lens a \<Longrightarrow> a:[p,q]\<^sub>C \<sqsubseteq> a:[p,r]\<^sub>C ;; a:[r,q]\<^sub>C"
  by ((rdes_refine_split; rel_simp), metis vwb_lens.put_eq)
*)

subsection \<open> Assumptions \<close>

definition AssumeCircus ("[_]\<^sub>C") where
"[b]\<^sub>C = b \<rightarrow>\<^sub>R Skip"

lemma AssumeCircus_rdes_def [rdes_def]: "[b]\<^sub>C = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> [b]\<^sub>c)"
  unfolding AssumeCircus_def by rdes_eq

lemma AssumeCircus_NCSP [closure]: "[b]\<^sub>C is NCSP"
  by (simp add: AssumeCircus_def GuardedCommR_NCSP_closed NCSP_Skip)

lemma AssumeCircus_AssumeR: "Skip ;; [b]\<^sup>\<top>\<^sub>R = [b]\<^sub>C" "[b]\<^sup>\<top>\<^sub>R ;; Skip = [b]\<^sub>C"
  by (rdes_eq)+

lemma AssumeR_comp_AssumeCircus: "P is NCSP \<Longrightarrow> P ;; [b]\<^sup>\<top>\<^sub>R = P ;; [b]\<^sub>C"
  by (metis AssumeCircus_AssumeR(1) Skip_right_unit upred_semiring.mult_assoc)

lemma gcmd_AssumeCircus: 
  "P is NCSP \<Longrightarrow> b \<rightarrow>\<^sub>R P = [b]\<^sub>C ;; P"
  by (simp add: AssumeCircus_def NCSP_implies_NSRD Skip_left_unit gcmd_seq_distr)

lemma rdes_assume_pre_refine:
  assumes "P is NCSP"
  shows "P \<sqsubseteq> [b]\<^sub>C ;; P"
  by (rdes_refine cls: assms)

subsection \<open> While Loops \<close>

lemma NSRD_coerce_NCSP:
  "P is NSRD \<Longrightarrow> Skip ;; P ;; Skip is NCSP"
  by (metis (no_types, opaque_lifting) CSP3_Skip CSP3_def CSP4_def Healthy_def NCSP_Skip NCSP_implies_CSP NCSP_intro NSRD_is_SRD upred_semiring.mult_assoc SRD_seqr_closure)

definition WhileC :: "'s pred \<Rightarrow> ('s, 'e) sfrd hrel \<Rightarrow> ('s, 'e) sfrd hrel" ("while\<^sub>C _ do _ od") where
"while\<^sub>C b do P od = Skip ;; while\<^sub>R b do P od ;; Skip"

lemma WhileC_NCSP_closed [closure]:
  assumes "P is NCSP" "P is Productive"
  shows "while\<^sub>C b do P od is NCSP"
  by (simp add: WhileC_def NSRD_coerce_NCSP assms closure)

theorem WhileC_iter_form:
  assumes "P is NCSP" "P is Productive"
  shows "while\<^sub>C b do P od = ([b]\<^sub>C ;; P)\<^sup>\<star>\<^sup>C ;; [\<not> b]\<^sub>C"
  by (simp add: WhileC_def WhileR_iter_form assms closure)
     (metis (no_types, lifting) StarC_def AssumeCircus_AssumeR(2) AssumeCircus_NCSP upred_semiring.mult_assoc assms(1) csp_theory.Healthy_Sequence csp_theory.Star_Healthy csp_theory.Unit_Left sfrd_star_as_rdes_star)

theorem WhileC_rdes_def [rdes_def]:
  assumes "P is CRC" "Q is CRR" "R is CRF" "$st\<^sup>> \<sharp> Q" "R is R4"
  shows "while\<^sub>C b do \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) od = 
         \<^bold>R\<^sub>s ((([b]\<^sub>c ;; R)\<^sup>\<star>\<^sup>c wp\<^sub>r ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P)) \<turnstile> (([b]\<^sub>c ;; R)\<^sup>\<star>\<^sup>c ;; [b]\<^sub>c ;; Q) \<diamondop> (([b]\<^sub>c ;; R)\<^sup>\<star>\<^sup>c ;; [\<not> b]\<^sub>c))" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = ([b]\<^sub>C ;; \<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R))\<^sup>\<star>\<^sup>C ;; [\<not> b]\<^sub>C"
    by (simp add: WhileC_iter_form assms closure unrest Productive_rdes_RR_intro)
  also have "... = ?rhs"
    by (simp add: rdes_def assms closure unrest unrest_ssubst_expr usubst_eval usubst rpred wp del: rea_star_wp, metis SEXP_def atomize_upred(3))
  finally show ?thesis .
qed

lemma WhileC_false: 
  "P is NCSP \<Longrightarrow> WhileC (False)\<^sub>e P = Skip"
  by (simp add: NCSP_implies_NSRD Skip_srdes_left_unit WhileC_def WhileR_false)

lemma WhileC_unfold: 
  assumes "P is NCSP" "P is Productive"
  shows "WhileC b P = (P ;; WhileC b P) \<triangleleft> b \<triangleright>\<^sub>R Skip"
proof -
  have "WhileC b P = (Skip \<or> [b]\<^sub>C ;; P ;; ([b]\<^sub>C ;; P)\<^sup>\<star>\<^sup>C) ;; [\<not> b]\<^sub>C"
    by (simp add: WhileC_iter_form assms closure)
       (metis (no_types, lifting) AssumeCircus_NCSP upred_semiring.mult_assoc StarC_unfold assms(1) csp_theory.Healthy_Sequence disj_pred_def)
  also have "... = ([\<not> b]\<^sub>C \<or> [b]\<^sub>C ;; P ;; ([b]\<^sub>C ;; P)\<^sup>\<star>\<^sup>C ;; [\<not> b]\<^sub>C)"
    by (metis (no_types, lifting) AssumeCircus_AssumeR(1) upred_semiring.mult_assoc csp_theory.Unit_self seqr_or_distl)
  also have "... = (P ;; WhileC b P) \<triangleleft> b \<triangleright>\<^sub>R Skip"
    by (simp add: WhileC_iter_form assms closure,
        metis (no_types, lifting) AssumeCircus_AssumeR(2) AssumeCircus_NCSP NCSP_Skip NCSP_implies_NSRD NCSP_seqr_closure Skip_left_unit
        StarC_def assms(1) cond_srea_AssumeR_form csp_theory.Star_Healthy disj_pred_def pred_ba.sup_commute
        upred_semiring.mult_assoc)
  finally show ?thesis .
qed

subsection \<open> Iteration Construction \<close>

(*
definition IterateC :: "'a set \<Rightarrow> ('a \<Rightarrow> 's pred) \<Rightarrow> ('a \<Rightarrow> ('s, 'e) sfrd hrel) \<Rightarrow> ('s, 'e) sfrd hrel"
where [pred, ndes_simp]: "IterateC A g P = while\<^sub>C (\<Or> i\<in>A \<bullet> g(i)) do (if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) fi) od"

lemma IterateC_IterateR_def: "IterateC A g P = Skip ;; IterateR A g P ;; Skip"
  by (simp add: IterateC_def IterateR_def WhileC_def)

definition IterateC_list :: "('s pred \<times> ('s, 'e) sfrd hrel) list \<Rightarrow> ('s, 'e) sfrd hrel" where 
[pred, ndes_simp]:
  "IterateC_list xs = IterateC {0..<length xs} (\<lambda> i. map fst xs ! i) (\<lambda> i. map snd xs ! i)"

syntax
  "_iter_C"    :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("do\<^sub>C _\<in>_ \<bullet> _ \<rightarrow> _ od")
  "_iter_gcommC" :: "gcomms \<Rightarrow> logic" ("do\<^sub>C/ _ /od")

translations
  "_iter_C x A g P" => "CONST IterateC A (\<lambda> x. g) (\<lambda> x. P)"
  "_iter_C x A g P" <= "CONST IterateC A (\<lambda> x. g) (\<lambda> x'. P)"
  "_iter_gcommC cs" \<rightharpoonup> "CONST IterateC_list cs"
  "_iter_gcommC (_gcomm_show cs)" \<leftharpoondown> "CONST IterateC_list cs"

lemma IterateC_NCSP_closed [closure]:
  assumes 
    "\<And> i. i \<in> I \<Longrightarrow> P(i) is NCSP" 
    "\<And> i. i \<in> I \<Longrightarrow> P(i) is Productive"
  shows "do\<^sub>C i\<in>I \<bullet> g(i) \<rightarrow> P(i) od is NCSP"
  by (simp add: IterateC_IterateR_def IterateR_NSRD_closed NCSP_implies_NSRD NSRD_coerce_NCSP assms(1) assms(2))

lemma IterateC_list_NCSP_closed [closure]:
  assumes 
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is NCSP"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is Productive"
  shows "IterateC_list A is NCSP"
  apply (simp add: IterateC_list_def, rule IterateC_NCSP_closed)
   apply (metis assms atLeastLessThan_iff nth_map nth_mem prod.collapse)+
  done

lemma IterateC_list_alt_def:
  "IterateC_list xs = while\<^sub>C (\<Or> b \<in> set(map fst xs) \<bullet> b) do AlternateR_list xs Chaos od"
proof -
  have "(\<Or> i \<in> {0..<length(xs)} \<bullet> (map fst xs) ! i) = (\<Or> b \<in> set(map fst xs) \<bullet> b)"
    by (pred_auto, metis fst_conv in_set_conv_nth nth_map)
  thus ?thesis
    by (simp add: IterateC_list_def IterateC_def AlternateR_list_def)
qed

lemma IterateC_empty: 
  "do\<^sub>C i\<in>{} \<bullet> g(i) \<rightarrow> P(i) od = Skip"
  by (simp add: IterateC_IterateR_def IterateR_empty closure Skip_srdes_left_unit)

lemma IterateC_singleton: 
  assumes "P k is NCSP" "P k is Productive"
  shows "do\<^sub>C i\<in>{k} \<bullet> g(i) \<rightarrow> P(i) od = while\<^sub>C g(k) do P(k) od" (is "?lhs = ?rhs")
  by (simp add: IterateC_IterateR_def IterateR_singleton NCSP_implies_NSRD WhileC_def assms)

lemma IterateC_outer_refine_intro:
  assumes "I \<noteq> {}" "\<And> i. i \<in> I \<Longrightarrow> P i is NCSP" "\<And> i. i \<in> I \<Longrightarrow> P i is Productive"
    "\<And> i. i \<in> I \<Longrightarrow> S \<sqsubseteq> (b i \<rightarrow>\<^sub>R P i ;; S)" "S is NCSP"
    "S \<sqsubseteq> [\<not> (\<Sqinter> i \<in> I \<bullet> b i)]\<^sup>\<top>\<^sub>R"
  shows "S \<sqsubseteq> do\<^sub>C i\<in>I \<bullet> b(i) \<rightarrow> P(i) od"
proof -
  have "S \<sqsubseteq> do\<^sub>R i\<in>I \<bullet> b(i) \<rightarrow> P(i) od"
    by (simp add: IterateR_outer_refine_intro NCSP_implies_NSRD assms)
  thus ?thesis
    unfolding IterateC_IterateR_def
    by (metis (full_types) Skip_left_unit Skip_right_unit assms(5) urel_dioid.mult_isol urel_dioid.mult_isor)
qed

lemma IterateC_outer_refine_init_intro:
  assumes 
    "\<And> i. i \<in> A \<Longrightarrow> P i is NCSP" 
    "\<And> i. i \<in> A \<Longrightarrow> P i is Productive" 
    "S is NCSP" "I is NCSP"
    "S \<sqsubseteq> I ;; [\<not> (\<Sqinter> i \<in> A \<bullet> b i)]\<^sup>\<top>\<^sub>R"
    "\<And> i. i \<in> A \<Longrightarrow> S \<sqsubseteq> S ;; b i \<rightarrow>\<^sub>R P i"
    "\<And> i. i \<in> A \<Longrightarrow> S \<sqsubseteq> I ;; b i \<rightarrow>\<^sub>R P i"
  shows "S \<sqsubseteq> I ;; do\<^sub>C i\<in>A \<bullet> b(i) \<rightarrow> P(i) od"
proof (cases "A = {}")
  case True
  with assms(5) show ?thesis 
    by (simp add: IterateC_empty assms closure Skip_right_unit AssumeR_true NSRD_right_unit)
next
  case False
  have "S \<sqsubseteq> I ;; do\<^sub>R i\<in>A \<bullet> b(i) \<rightarrow> P(i) od"
    by (simp add: IterateR_outer_refine_init_intro NCSP_implies_NSRD assms False)
  thus ?thesis
    unfolding IterateC_IterateR_def
    by (metis (no_types, opaque_lifting) upred_semiring.mult_assoc Skip_right_unit assms(3) assms(4) urel_dioid.mult_isor) 
qed


lemma IterateC_list_outer_refine_intro:
  assumes 
    "A \<noteq> []" "S is NCSP"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is NCSP"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is Productive"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> S \<sqsubseteq> (b \<rightarrow>\<^sub>R P ;; S)"
    "S \<sqsubseteq> [\<not> (\<Sqinter> (b, P) \<in> set A \<bullet> b)]\<^sup>\<top>\<^sub>R" 
  shows "S \<sqsubseteq> IterateC_list A"
proof -
  have "(\<Sqinter> i \<in> {0..<length(A)} \<bullet> (map fst A) ! i) = (\<Sqinter> (b, P) \<in> set A \<bullet> b)"
    by (pred_auto, metis nth_mem prod.exhaust_sel, metis fst_conv in_set_conv_nth nth_map)
  thus ?thesis
    apply (simp add: IterateC_list_def)
    apply (rule IterateC_outer_refine_intro)
     apply (simp_all add: closure assms)
    apply (metis assms(3) nth_mem prod.collapse)
    apply (metis assms(4) nth_mem prod.collapse)
    done
qed

lemma IterateC_list_outer_refine_init_intro:
  assumes 
    "S is NCSP" "I is NCSP"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is NCSP"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is Productive"
    "S \<sqsubseteq> I ;; [\<not> (\<Sqinter> (b, P) \<in> set A \<bullet> b)]\<^sup>\<top>\<^sub>R"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> S \<sqsubseteq> S ;; b \<rightarrow>\<^sub>R P"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> S \<sqsubseteq> I ;; b \<rightarrow>\<^sub>R P" 
  shows "S \<sqsubseteq> I ;; IterateC_list A"
proof -
  have "(\<Sqinter> i \<in> {0..<length(A)} \<bullet> (map fst A) ! i) = (\<Sqinter> (b, P) \<in> set A \<bullet> b)"
    by (pred_auto, metis nth_mem prod.exhaust_sel, metis fst_conv in_set_conv_nth nth_map)
  thus ?thesis
    apply (simp add: IterateC_list_def)
    apply (rule IterateC_outer_refine_init_intro)
     apply (simp_all add: closure assms)
    apply (metis assms(3) nth_mem prod.collapse)
    apply (metis assms(4) nth_mem prod.collapse)
    done
qed
*)

subsection \<open> Assignment \<close>

definition AssignsCSP :: "'\<sigma> subst \<Rightarrow> ('\<sigma>, '\<phi>) sfrd hrel" ("\<langle>_\<rangle>\<^sub>C") where
[pred]: "AssignsCSP \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S))" 

abbreviation "AssignCSP x v \<equiv> \<^bold>R\<^sub>s([$\<^bold>v \<in> \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>]\<^sub>S\<^sub>< \<turnstile> false \<diamondop> \<Phi>(True,[x \<leadsto> v], \<guillemotleft>[]\<guillemotright>))"

syntax
  "_assign_csp" :: "svid \<Rightarrow> logic \<Rightarrow> logic" (infix ":=\<^sub>C" 61)

translations
  "_assign_csp x e" == "CONST AssignsCSP (CONST subst_upd (CONST subst_id) x (e)\<^sub>e)"

lemma preR_AssignsCSP [rdes]: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = true\<^sub>r"
  by (pred_auto)

lemma periR_AssignsCSP [rdes]: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = false"
  by (pred_auto)

lemma postR_AssignsCSP [rdes]: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = \<Phi>(True,\<sigma>,\<guillemotleft>[]\<guillemotright>)"
  by (pred_auto)

lemma AssignsCSP_rdes_def [rdes_def] : "\<langle>\<sigma>\<rangle>\<^sub>C = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> \<Phi>(True,\<sigma>,\<guillemotleft>[]\<guillemotright>))"
  by (pred_auto)

lemma AssignsCSP_CSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP"
  by (simp add: AssignsCSP_def RHS_tri_design_is_SRD unrest)

lemma AssignsCSP_CSP3 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP3"
  by (rule CSP3_intro, simp add: closure, pred_auto)

lemma AssignsCSP_CSP4 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP4"
  by (rule CSP4_intro, simp add: closure, pred_auto+)

lemma AssignsCSP_NCSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is NCSP"
  by (simp add: AssignsCSP_CSP AssignsCSP_CSP3 AssignsCSP_CSP4 NCSP_intro)

lemma AssignsCSP_ICSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is ICSP"
  apply (rule ICSP_intro, simp add: closure, simp add: rdes_def)
  apply (rule ISRD1_rdes_intro)
  apply (simp_all add: closure)
  apply (pred_auto)
done

lemma unproductive_AssignsCSP: "\<not> (\<langle>\<sigma>\<rangle>\<^sub>C is Productive)"
  unfolding rdes_def by (rule unproductive_form, simp_all add: closure, pred_auto+)

lemma AssignsCSP_as_AssignsR: "\<langle>\<sigma>\<rangle>\<^sub>R ;; Skip = \<langle>\<sigma>\<rangle>\<^sub>C"
  by (rdes_eq)

lemma AssignC_init_refine_intro:
  assumes 
    "vwb_lens x" "$st:x\<^sup>< \<sharp> P\<^sub>2" "$st:x\<^sup>< \<sharp> P\<^sub>3"
    "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q is NCSP"
    "\<^bold>R\<^sub>s([$x = \<guillemotleft>k\<guillemotright>]\<^sub>S\<^sub>< \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> Q"
  shows "\<^bold>R\<^sub>s(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> (x :=\<^sub>C \<guillemotleft>k\<guillemotright>) ;; Q"
  by (simp add: AssignsCSP_as_AssignsR[THEN sym] assms seqr_assoc Skip_left_unit AssignR_init_refine_intro closure)

(*
lemma AssignsCSP_refines_sinv: 
  assumes "`\<sigma> \<dagger> b`"
  shows "sinv\<^sub>R(b) \<sqsubseteq> \<langle>\<sigma>\<rangle>\<^sub>C"
  apply (rdes_refine_split)
  apply (simp_all)
   apply (metis rea_st_cond_true st_cond_conj utp_pred_laws.inf.absorb_iff2 utp_pred_laws.inf_top_left)
  using assms apply (pred_auto)
  done
*)

subsection \<open> State abstraction \<close>

(*
lemma ref_unrest_abs_st [unrest]:
  "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> \<langle>P\<rangle>\<^sub>S"
  "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> \<langle>P\<rangle>\<^sub>S"
  by (rel_simp)+
  
lemma NCSP_state_srea [closure]: "P is NCSP \<Longrightarrow> state 'a \<bullet> P is NCSP"
  apply (rule NCSP_NSRD_intro)
  apply (simp_all add: closure rdes)
  apply (simp_all add: state_srea_def unrest closure)
done
*)

subsection \<open> Guards \<close>

definition GuardCSP ::
  "'\<sigma> pred \<Rightarrow>
   ('\<sigma>, '\<phi>) sfrd hrel \<Rightarrow>
   ('\<sigma>, '\<phi>) sfrd hrel"  where
[pred]: "GuardCSP g A = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R(A)) \<turnstile> ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R(A)) \<or> (\<lceil>\<not> g\<rceil>\<^sub>S\<^sub><) \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"

syntax
  "_GuardCSP" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "&\<^sub>C" 60)

translations
  "_GuardCSP b P" == "CONST GuardCSP (b)\<^sub>e P"

lemma Guard_tri_design:
  "g &\<^sub>C P = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P)))"
proof -
  have "(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R P \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>) = (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P))"
    by (pred_auto, (metis (full_types))+)
  thus ?thesis by (simp add: GuardCSP_def)
qed

lemma csp_do_cond_conj:
  assumes "P is CRR"
  shows "(\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> P) = \<Phi>(b, [\<leadsto>], []) ;; P"
proof -
  have "(\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> CRR(P)) = \<Phi>(b, [\<leadsto>], \<guillemotleft>[]\<guillemotright>) ;; CRR(P)"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  
lemma Guard_rdes_def [rdes_def]:
  assumes "P is RR" "Q is CRR" "R is CRR"
  shows "g &\<^sub>C \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) = \<^bold>R\<^sub>s (([g]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) \<turnstile> ((\<Phi>(g, [\<leadsto>], \<guillemotleft>[]\<guillemotright>) ;; Q) \<or> \<E>(\<not>g,[],{})) \<diamondop> (\<Phi>(g, [\<leadsto>], []) ;; R))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) \<turnstile> ((P \<longrightarrow>\<^sub>r Q) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<longrightarrow>\<^sub>r R)))"
    by (simp add: Guard_tri_design rdes assms closure)
  also have "... = \<^bold>R\<^sub>s (([g]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) \<turnstile> ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q) \<or> \<E>(\<not>g,[],{})) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R))"
    by (rule srdes_tri_eq_intro, pred_auto+)
  also have "... = \<^bold>R\<^sub>s (([g]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) \<turnstile> ((\<Phi>(g, [\<leadsto>], \<guillemotleft>[]\<guillemotright>) ;; Q) \<or> \<E>(\<not>g,[],{})) \<diamondop> (\<Phi>(g, [\<leadsto>], \<guillemotleft>[]\<guillemotright>) ;; R))"
    by (simp add: assms(2) assms(3) csp_do_cond_conj)
  finally show ?thesis .
qed

lemma Guard_rdes_def':
  assumes "$ok\<^sup>> \<sharp> P"
  shows "g &\<^sub>C (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
proof -
  have "g &\<^sub>C (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
    by (simp add: GuardCSP_def)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<longrightarrow> Q))) \<or>  \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<longrightarrow> Q))) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>)))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<longrightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>)))"
     by (simp add: R1_R2c_commute R1_disj R1_extend_conj' R1_idem R2c_and R2c_disj R2c_idem)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<longrightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
     by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<longrightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>)))"
     by (simp add: rdes_export_cmt)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<longrightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>)))"
     by (simp add: usubst)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<longrightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
     by (simp add: rdes_export_cmt)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r (pre\<^sub>s \<dagger> P)) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<longrightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
     by (pred_auto)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>s \<dagger> P)\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<longrightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
     by (simp add: rdes_export_pre)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P)\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<longrightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
   proof -
     from assms have "pre\<^sub>s \<dagger> P = P\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
       by (pred_auto)
     thus ?thesis
       by (simp add: usubst rea_impl_def usubst_eval unrest assms)
   qed
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<longrightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
     by (simp add: rdes_export_pre)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"
     by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
   finally show ?thesis .
qed

lemma CSP_Guard [closure]: "b &\<^sub>C P is CSP"
  by (simp add: GuardCSP_def, rule RHS_design_is_SRD, simp_all add: unrest)

lemma preR_Guard [rdes]: "P is CSP \<Longrightarrow> pre\<^sub>R(b &\<^sub>C P) = ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P)"
  by (simp add: Guard_tri_design rea_pre_RHS_design usubst unrest R2c_preR R2c_lift_state_pre
      R2c_rea_impl R1_rea_impl R1_preR Healthy_if, pred_auto)

lemma periR_Guard [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(b &\<^sub>C P) = (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R \<E>(True,[],{}))"
proof -
  have "peri\<^sub>R(b &\<^sub>C P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P) \<longrightarrow>\<^sub>r (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e))"
    by (simp add: assms Guard_tri_design rea_peri_RHS_design usubst unrest R1_rea_impl R2c_rea_not 
        R2c_rea_impl R2c_preR R2c_periR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr closure
        Healthy_if R1_cond R1_tr'_eq_tr unrest_ssubst_expr usubst_eval, pred_simp, meson)
  also have "... = ((pre\<^sub>R P \<longrightarrow>\<^sub>r peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e)"
    by (pred_auto)
  also have "... = (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e)"      
    by (simp add: SRD_peri_under_pre add: unrest closure assms)
  finally show ?thesis
    by pred_auto
qed
      
lemma postR_Guard [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(b &\<^sub>C P) = ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
proof -
  have "post\<^sub>R(b &\<^sub>C P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P) \<longrightarrow>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P))"
    by (simp add: Guard_tri_design rea_post_RHS_design usubst unrest R2c_rea_not R2c_and R2c_rea_impl
        R2c_preR R2c_postR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr R1_rea_impl R1_extend_conj'
        R1_post_SRD closure assms unrest_ssubst_expr usubst_eval, pred_simp)
  also have "... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (pre\<^sub>R P \<longrightarrow>\<^sub>r post\<^sub>R P))"
    by (pred_auto)
  also have "... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
    by (simp add: SRD_post_under_pre add: unrest closure assms)
  also have "... = ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
    by (simp add: assms csp_do_cond_conj csp_do_id postR_CRR)      
  finally show ?thesis .
qed
        
lemma CSP3_Guard [closure]:
  assumes "P is CSP" "P is CSP3"
  shows "b &\<^sub>C P is CSP3"
proof -
  from assms have 1:"$ref\<^sup>< \<sharp> P\<lbrakk>False/wait\<^sup><\<rbrakk>"
    by (simp add: CSP_Guard CSP3_iff)
  hence "$ref\<^sup>< \<sharp> pre\<^sub>R (P\<lbrakk>0/tr\<^sup><\<rbrakk>)" "$ref\<^sup>< \<sharp> pre\<^sub>R P" "$ref\<^sup>< \<sharp> cmt\<^sub>R P"
    by (pred_auto; blast)+
  hence "$ref\<^sup>< \<sharp> (b &\<^sub>C P)\<lbrakk>False/wait\<^sup><\<rbrakk>"
    apply (simp add: CSP3_iff GuardCSP_def)
    apply (rule RHS_design_ref_unrest)
     apply pred_auto+
    done
  thus ?thesis
    by (metis CSP3_intro CSP_Guard)
qed

lemma CSP4_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>C P is CSP4"
proof (rule CSP4_tri_intro[OF CSP_Guard])
  show "(\<not>\<^sub>r pre\<^sub>R (b &\<^sub>C P)) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R (b &\<^sub>C P))"
  proof -
    have a:"(\<not>\<^sub>r pre\<^sub>R P) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R P)"
      by (simp add: CSP4_neg_pre_unit assms closure)
    have "(\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true = (\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P))"
    proof -
      have 1:"(\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P)) = ([b]\<^sub>S\<^sub>< \<and> (\<not>\<^sub>r pre\<^sub>R P))"
        by (pred_auto)
      also have 2:"... = ([b]\<^sub>S\<^sub>< \<and> ((\<not>\<^sub>r pre\<^sub>R P) ;; R1 true))"
        by (simp add: a)
      also have 3:"... = (\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true"
        by (pred_auto)
      finally show ?thesis ..
    qed
    thus ?thesis
      by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro closure assms unrest)
  qed
  show "$st\<^sup>> \<sharp> peri\<^sub>R (b &\<^sub>C P)"
    by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro closure assms unrest)
  show "$ref\<^sup>> \<sharp> post\<^sub>R (b &\<^sub>C P)"
    by (simp add: preR_Guard postR_Guard NSRD_CSP4_intro closure assms unrest)
qed

lemma NCSP_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>C P is NCSP"
proof -
  have "P is CSP"
    using NCSP_implies_CSP assms by blast
  then show ?thesis
    by (metis (no_types) CSP3_Guard CSP3_commutes_CSP4 CSP4_Guard CSP4_Idempotent CSP_Guard Healthy_Idempotent Healthy_def NCSP_def assms comp_apply)
qed

lemma Productive_Guard [closure]:
  assumes "P is CSP" "P is Productive" "$wait\<^sup>> \<sharp> pre\<^sub>R(P)"
  shows "b &\<^sub>C P is Productive"
proof -
  have "b &\<^sub>C P = b &\<^sub>C \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
    by (simp add: Productive_form[THEN sym] assms Healthy_if)
  also have "... =
        \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P) \<turnstile>
          ((pre\<^sub>R P \<longrightarrow>\<^sub>r peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) \<diamondop> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (pre\<^sub>R P \<longrightarrow>\<^sub>r post\<^sub>R P \<and> ($tr\<^sup>> > $tr\<^sup><)\<^sub>e)))"
    by (simp add: Guard_tri_design rea_pre_RHS_design rea_peri_RHS_design rea_post_RHS_design unrest assms
        usubst R1_preR Healthy_if R1_rea_impl R1_peri_SRD R1_extend_conj' R2c_preR R2c_not R2c_rea_impl 
        R2c_periR R2c_postR R2c_and R2c_tr_less_tr' R1_tr_less_tr')             
  also have "... = \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) \<diamondop> ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P) \<and> ($tr\<^sup>> > $tr\<^sup><)\<^sub>e))"
    by (pred_auto)
  also have "... = Productive(b &\<^sub>C P)"
    by (simp add: Productive_def Guard_tri_design RHS_tri_design_par unrest)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

(*
lemma Guard_refines_sinv: 
  assumes "P is NCSP" "sinv\<^sub>R(b) \<sqsubseteq> P"
  shows "sinv\<^sub>R(b) \<sqsubseteq> g &\<^sub>C P"
proof -
  from assms
  have "\<^bold>R\<^sub>s([b]\<^sub>S\<^sub>< \<turnstile> R1 true \<diamondop> [b]\<^sub>S\<^sub>>) \<sqsubseteq> \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: rdes_def NCSP_implies_CSP SRD_reactive_tri_design)
  thus ?thesis
    apply (simp add: RHS_tri_design_refine' closure unrest assms)
    apply (safe)
    apply (rdes_refine cls: assms(1))
    done
qed
*)

subsection \<open> Basic events\<close>

definition do\<^sub>u ::
  "('\<phi>, '\<sigma>) expr \<Rightarrow> ('\<sigma>, '\<phi>) sfrd hrel" where
[pred]: "do\<^sub>u e = (($tr\<^sup>> = $tr\<^sup>< \<and> \<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin> $ref\<^sup>>)\<^sub>e \<triangleleft> wait\<^sup>> \<triangleright> ($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>e\<rceil>\<^sub>S\<^sub><] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e)"

definition DoCSP :: "('\<phi>, '\<sigma>) expr \<Rightarrow> ('\<sigma>, '\<phi>) sfrd hrel" where
[pred]: "DoCSP a = \<^bold>R\<^sub>s(true \<turnstile> do\<^sub>u a)"

syntax "_DoCSP" :: "logic \<Rightarrow> logic" ("do\<^sub>C")
translations "_DoCSP a" == "CONST DoCSP (a)\<^sup>e"

lemma R1_DoAct: "R1(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (pred_auto)

lemma R2c_DoAct: "R2c(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (pred_auto)

lemma DoCSP_alt_def: "do\<^sub>C(a) = R3h(CSP1(ok\<^sup>> \<and> do\<^sub>u(a)))"
  apply (simp add: DoCSP_def RHS_def design_def  R1_R3h_commute R2c_R3h_commute R2c_disj
                   R2c_not R2c_ok R2c_ok' R2c_and R2c_DoAct R1_disj R1_extend_conj' R1_DoAct)
  apply (pred_auto)
done

lemma DoAct_unrests [unrest]:
  "$ok\<^sup>< \<sharp> do\<^sub>u(a)" "$wait\<^sup>< \<sharp> do\<^sub>u(a)"
  by (pred_auto)+

lemma DoCSP_RHS_tri [rdes_def]:
  "do\<^sub>C(a) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (\<E>(True,[],{a}) \<diamondop> \<Phi>(True,[\<leadsto>],[a])))"
  by (simp add: DoCSP_def do\<^sub>u_def wait'_cond_def, pred_auto)

lemma CSP_DoCSP [closure]: "do\<^sub>C(a) is CSP"
  apply (simp add: DoCSP_def do\<^sub>u_def RHS_design_is_SRD unrest unrest_ssubst_expr usubst_eval usubst)
  apply (rule RHS_design_is_SRD)
   apply (simp_all add:unrest)
  apply pred_auto
  done

lemma preR_DoCSP [rdes]: "pre\<^sub>R(do\<^sub>C(a)) = true\<^sub>r"
  by (simp add: DoCSP_def rea_pre_RHS_design unrest usubst R2c_true)

lemma periR_DoCSP [rdes]: "peri\<^sub>R(do\<^sub>C(a)) = \<E>(True,\<guillemotleft>[]\<guillemotright>,{a})"
  by (pred_auto) 

lemma postR_DoCSP [rdes]: "post\<^sub>R(do\<^sub>C(a)) = \<Phi>(True,[\<leadsto>],[a])"
  by (pred_auto)

lemma CSP3_DoCSP [closure]: "do\<^sub>C(a) is CSP3"
  apply (rule CSP3_intro[OF CSP_DoCSP])
  apply (simp add: DoCSP_def do\<^sub>u_def RHS_def design_def R1_def R2c_def R2s_def R3h_def unrest usubst unrest_ssubst_expr usubst_eval)
  apply (pred_simp)
  done

lemma CSP4_DoCSP [closure]: "do\<^sub>C(a) is CSP4"
  by (rule CSP4_tri_intro[OF CSP_DoCSP], simp_all add: preR_DoCSP periR_DoCSP postR_DoCSP unrest)

lemma NCSP_DoCSP [closure]: "do\<^sub>C(a) is NCSP"
  by (metis CSP3_DoCSP CSP4_DoCSP CSP_DoCSP Healthy_def NCSP_def comp_apply)

lemma Productive_DoCSP [closure]:
  "(do\<^sub>C a :: ('\<sigma>, '\<psi>) sfrd hrel) is Productive"
proof -
  have "((\<Phi>(True,[\<leadsto>],[a]) \<and> ($tr\<^sup>> > $tr\<^sup><)\<^sub>e) :: ('\<sigma>, '\<psi>) sfrd hrel)
        = (\<Phi>(True,[\<leadsto>],[a]))"
    by (pred_auto, simp add: Prefix_Order.strict_prefixI')
  hence "Productive(do\<^sub>C a) = do\<^sub>C a"
    by (simp add: Productive_RHS_design_form DoCSP_RHS_tri unrest)
  thus ?thesis
    by (simp add: Healthy_def)
qed

lemma PCSP_DoCSP [closure]:
  "(do\<^sub>C a :: ('\<sigma>, '\<psi>) sfrd hrel) is PCSP"
  by (simp add: Healthy_comp NCSP_DoCSP Productive_DoCSP)

lemma wp_rea_DoCSP_lemma:
  fixes P :: "('\<sigma>, '\<phi>) sfrd hrel"
  assumes "$ok\<^sup>< \<sharp> P" "$wait\<^sup>< \<sharp> P"
  shows "($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e ;; P = (\<exists> ref\<^sup>< \<Zspot> P\<lbrakk>$tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><]/tr\<^sup><\<rbrakk>)"
  using assms
  by (pred_auto, meson)

lemma wp_rea_DoCSP:
  assumes "P is NCSP"
  shows "($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e wp\<^sub>r pre\<^sub>R P = 
         (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><]/tr\<^sup><\<rbrakk>)"
proof -
  have "$ref\<^sup>< \<sharp>\<^sub>s [tr\<^sup>< \<leadsto> $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><]]"
    by pred_auto

  hence "$ref\<^sup>< \<sharp> (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><]/tr\<^sup><\<rbrakk>"
    using CRR_unrest_ref assms preR_CRR rea_not_CRR_closed unrest_subst_apply by blast
  thus ?thesis
    by (simp add: wp_rea_def wp_rea_DoCSP_lemma unrest assms closure ex_unrest)
qed

lemma wp_rea_DoCSP_alt:
  assumes "P is NCSP"
  shows "($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e wp\<^sub>r pre\<^sub>R P = 
         (($tr\<^sup>> \<ge> $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><])\<^sub>e \<longrightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>$tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><]/tr\<^sup><\<rbrakk>)"  
  apply (simp add: wp_rea_DoCSP assms)
  apply (simp add: rea_not_def R1_def usubst unrest)
  apply (pred_auto)
  done

(*
lemma DoCSP_refine_sinv: "sinv\<^sub>R(b) \<sqsubseteq> do\<^sub>C(a)"
  by (rdes_refine)
*)

subsection \<open> Event prefix \<close>

definition PrefixCSP ::
  "('\<phi>, '\<sigma>) expr \<Rightarrow>
  ('\<sigma>, '\<phi>) sfrd hrel \<Rightarrow>
  ('\<sigma>, '\<phi>) sfrd hrel" where
[pred]: "PrefixCSP a P = (do\<^sub>C(a) ;; CSP(P))"

syntax "_PrefixCSP" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>C _" [81, 80] 80)
translations "_PrefixCSP a P" == "CONST PrefixCSP (a)\<^sub>e P"
syntax_consts "_PrefixCSP" == PrefixCSP

abbreviation "OutputCSP c v P \<equiv> PrefixCSP (c\<cdot>v)\<^sub>u P"

lemma CSP_PrefixCSP [closure]: "PrefixCSP a P is CSP"
  by (simp add: PrefixCSP_def closure)

lemma CSP3_PrefixCSP [closure]:
  "PrefixCSP a P is CSP3"
  by (metis (no_types, opaque_lifting) CSP3_DoCSP CSP3_def Healthy_def PrefixCSP_def seqr_assoc)

lemma CSP4_PrefixCSP [closure]:
  assumes "P is CSP" "P is CSP4"
  shows "PrefixCSP a P is CSP4"
  by (metis (no_types, opaque_lifting) CSP4_def Healthy_def PrefixCSP_def assms(1) assms(2) seqr_assoc)

lemma NCSP_PrefixCSP [closure]:
  assumes "P is NCSP"
  shows "PrefixCSP a P is NCSP"
  by (metis (no_types, opaque_lifting) CSP3_PrefixCSP CSP3_commutes_CSP4 CSP4_Idempotent CSP4_PrefixCSP
            CSP_PrefixCSP Healthy_Idempotent Healthy_def NCSP_def NCSP_implies_CSP assms comp_apply)

lemma Productive_PrefixCSP [closure]: "P is NCSP \<Longrightarrow> PrefixCSP a P is Productive"
  by (simp add: Healthy_if NCSP_DoCSP NCSP_implies_NSRD NSRD_is_SRD PrefixCSP_def Productive_DoCSP Productive_seq_1)

lemma PCSP_PrefixCSP [closure]: "P is NCSP \<Longrightarrow> PrefixCSP a P is PCSP"
  by (simp add: Healthy_comp NCSP_PrefixCSP Productive_PrefixCSP)
  
lemma PrefixCSP_Guarded [closure]: "Guarded (PrefixCSP a)"
proof -
  have "PrefixCSP a = (\<lambda> X. do\<^sub>C(a) ;; CSP(X))"
    by (simp add: fun_eq_iff PrefixCSP_def)
  thus ?thesis
    using Guarded_if_Productive NCSP_DoCSP NCSP_implies_NSRD Productive_DoCSP by auto
qed

lemma PrefixCSP_type [closure]: "PrefixCSP a \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using CSP_PrefixCSP by blast

lemma PrefixCSP_Continuous [closure]: "Continuous (PrefixCSP a)"
  by (simp add: Continuous_def PrefixCSP_def ContinuousD[OF SRD_Continuous] image_image seq_Sup_distl)

lemma PrefixCSP_RHS_tri_lemma1:
  "R1 (R2s (($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><])\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R)) = (($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><])\<^sub>e \<and> \<lceil>II\<rceil>\<^sub>R)"
  by (pred_auto)

lemma PrefixCSP_RHS_tri_lemma2:
  fixes P :: "('\<sigma>, '\<phi>) sfrd hrel"
  assumes "$ok\<^sup>< \<sharp> P" "$wait\<^sup>< \<sharp> P"
  shows "(($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e \<and> \<not> wait\<^sup>>) ;; P = (\<exists> ref\<^sup>< \<Zspot> P\<lbrakk>$tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><]/tr\<^sup><\<rbrakk>)"
  using assms
  by (pred_auto, meson, fastforce)

lemma tr_extend_seqr:
  fixes P :: "('\<sigma>, '\<phi>) sfrd hrel"
  assumes "$ok\<^sup>< \<sharp> P" "$wait\<^sup>< \<sharp> P" "$ref\<^sup>< \<sharp> P"
  shows "($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e ;; P = P\<lbrakk>$tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><]/tr\<^sup><\<rbrakk>"
  using assms 
  by (simp add: wp_rea_DoCSP_lemma, pred_auto, meson)
          
lemma trace_ext_R1_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>$tr\<^sup>< @ e/tr\<^sup><\<rbrakk> is R1"
  by (pred_auto; blast)
    
lemma preR_PrefixCSP_NCSP [rdes]:
  assumes "P is NCSP"
  shows "pre\<^sub>R(PrefixCSP a P) = (\<Phi>(True,[\<leadsto>],[a]) wp\<^sub>r pre\<^sub>R P)"
  by (simp add: PrefixCSP_def assms closure rdes rpred Healthy_if wp usubst unrest)

(*
lemma periR_PrefixCSP [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(PrefixCSP a P) = (\<E>(true,\<guillemotleft>[]\<guillemotright>,{a}\<^sub>u) \<or> (peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
proof -
  have "peri\<^sub>R(PrefixCSP a P) =  peri\<^sub>R (do\<^sub>C a ;; P)"
    by (simp add: PrefixCSP_def closure assms Healthy_if)
  also have "... = undefined"
    apply (simp add: rdes closure assms rpred)
  also have "... = ((\<Phi>(true,id,\<langle>a\<rangle>) wp\<^sub>r pre\<^sub>R P) \<longrightarrow>\<^sub>r ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (simp add: assms NSRD_CSP4_intro csp_enable_tr_empty closure rdes unrest ex_unrest usubst rpred csp_do_comp wp)
  also have "... = (\<E>(true,\<guillemotleft>[]\<guillemotright>,{a}\<^sub>u) \<or> ((\<Phi>(true,id,\<langle>a\<rangle>) wp\<^sub>r pre\<^sub>R P) \<longrightarrow>\<^sub>r peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t))"
    by (pred_auto)
  also have "... = (\<E>(true,\<guillemotleft>[]\<guillemotright>,{a}\<^sub>u) \<or> ((pre\<^sub>R(P) \<longrightarrow>\<^sub>r peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t))"
    by (pred_auto)
  also have "... = (\<E>(true,\<guillemotleft>[]\<guillemotright>,{a}\<^sub>u) \<or> (peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"      
    by (simp add: SRD_peri_under_pre assms closure unrest)
  finally show ?thesis .
qed
  
lemma postR_PrefixCSP [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(PrefixCSP a P) = (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t"
proof -
  have "post\<^sub>R(PrefixCSP a P) = ((\<I>(true,\<langle>a\<rangle>) \<longrightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<longrightarrow>\<^sub>r (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (simp add: PrefixCSP_def assms Healthy_if) 
       (simp add: assms Healthy_if wp closure rdes rpred wp_rea_DoCSP_lemma unrest  ex_unrest usubst)
  also have "... = (\<I>(true,\<langle>a\<rangle>) \<and> (pre\<^sub>R P \<longrightarrow>\<^sub>r post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (pred_auto)
  also have "... = (\<I>(true,\<langle>a\<rangle>) \<and> (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"      
    by (simp add: SRD_post_under_pre assms closure unrest)
  also have "... = (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t"
    by (pred_auto)
  finally show ?thesis .
qed
*)  
    
lemma PrefixCSP_RHS_tri:
  assumes "P is NCSP"
  shows "PrefixCSP a P = \<^bold>R\<^sub>s ((\<Phi>(True,[\<leadsto>],[a]) wp\<^sub>r pre\<^sub>R P) \<turnstile> (\<E>(True,[], {a}) \<or> \<Phi>(True,[\<leadsto>],[a]) ;; peri\<^sub>R P) \<diamondop> (\<Phi>(True,[\<leadsto>],[a]) ;; post\<^sub>R P))"
  by (simp add: PrefixCSP_def Healthy_if unrest assms closure NSRD_composition_wp rdes rpred usubst wp unrest_ssubst_expr usubst_eval)

text \<open> For prefix, we can chose whether to propagate the assumptions or not, hence there
  are two laws. \<close>
    
lemma PrefixCSP_rdes_def_1 [rdes_def]:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<^sup>> \<sharp> Q" "$ref\<^sup>> \<sharp> R"
        shows "PrefixCSP a (\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = 
               \<^bold>R\<^sub>s ((\<Phi>(True,[\<leadsto>],[a]) wp\<^sub>r P) \<turnstile> (\<E>(True,[], {a}) \<or> \<Phi>(True,[\<leadsto>],[a]) ;; Q) \<diamondop> (\<Phi>(True,[\<leadsto>],[a]) ;; R))"
  by (simp add: PrefixCSP_def Healthy_if assms closure, rdes_simp cls: assms)

(*
lemma PrefixCSP_rdes_def_2:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<^sup>> \<sharp> Q" "$ref\<acute> \<sharp> R"
  shows "PrefixCSP a (\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s((\<I>(true,\<langle>a\<rangle>) \<longrightarrow>\<^sub>r P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<turnstile> (\<E>(true,\<guillemotleft>[]\<guillemotright>, {a}\<^sub>u) \<or> (P\<and>Q)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<diamondop> (P\<and>R)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  apply (subst PrefixCSP_RHS_tri)
   apply (rule NCSP_rdes_intro)
       apply (simp_all add: assms rdes closure)
  apply (pred_auto)
  done
*)

subsection \<open> Guarded external choice \<close>

abbreviation GuardedChoiceCSP :: "'\<theta> set \<Rightarrow> ('\<theta> \<Rightarrow> ('\<sigma>, '\<theta>) sfrd hrel) \<Rightarrow> ('\<sigma>, '\<theta>) sfrd hrel" where
"GuardedChoiceCSP A P \<equiv> (\<box> x\<in>A. PrefixCSP (\<guillemotleft>x\<guillemotright>)\<^sub>e (P(x)))"

syntax
  "_GuardedChoiceCSP" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<^bold>\<rightarrow> _" [0,0,85] 86)

translations
  "\<box> x\<in>A \<^bold>\<rightarrow> P" == "CONST GuardedChoiceCSP A (\<lambda> x. P)"

lemma GuardedChoiceCSP [rdes_def]:
  assumes "\<And> x. P(x) is NCSP" "A \<noteq> {}"
  shows "(\<box> x\<in>A \<^bold>\<rightarrow> P(x)) =
             \<^bold>R\<^sub>s ((\<Squnion> x\<in>A. \<Phi>(True,[\<leadsto>],\<guillemotleft>[x]\<guillemotright>) wp\<^sub>r pre\<^sub>R (P x)) \<turnstile>
                 ((\<Squnion> x\<in>A. \<E>(True,[], {\<guillemotleft>x\<guillemotright>})) \<triangleleft> $tr\<^sup>> = $tr\<^sup>< \<triangleright> (\<Sqinter> x\<in>A. \<Phi>(True,[\<leadsto>],\<guillemotleft>[x]\<guillemotright>) ;; peri\<^sub>R (P x))) \<diamondop>
                  (\<Sqinter> x\<in>A. \<Phi>(True,[\<leadsto>],\<guillemotleft>[x]\<guillemotright>) ;; post\<^sub>R (P x)))"
  apply (simp add: PrefixCSP_RHS_tri assms ExtChoice_tri_rdes closure unrest)
  apply (rule srdes_tri_eq_intro)
    apply (pred_auto)+
  done

subsection \<open> Input prefix \<close>

definition InputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> pred) \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<theta>) sfrd hrel) \<Rightarrow> ('\<sigma>, '\<theta>) sfrd hrel" where
[pred]: "InputCSP c A P = (\<box> x\<in>UNIV. @(A x) &\<^sub>C PrefixCSP (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u (P x))"

definition InputVarCSP :: "('a, '\<theta>) chan \<Rightarrow> ('a \<Longrightarrow> '\<sigma>) \<Rightarrow> ('a \<Rightarrow> '\<sigma> pred) \<Rightarrow> ('\<sigma>, '\<theta>) sfrd hrel" where
[pred, rdes_def]: "InputVarCSP c x A = InputCSP c A (\<lambda> v. \<langle>[x \<leadsto> \<guillemotleft>v\<guillemotright>]\<rangle>\<^sub>C)"

expr_constructor chan_apply

definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  ('a \<Longrightarrow> ('\<sigma>, '\<theta>) sfrd) \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<theta>) sfrd hrel) \<Rightarrow>
  ('\<sigma>, '\<theta>) sfrd hrel" where
"do\<^sub>I c x P = (
  (($tr\<^sup>> = $tr\<^sup>< \<and> {(c\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u | v. @(P v)} \<inter> $ref\<^sup>> = {})\<^sub>e
    \<triangleleft> wait\<^sup>> \<triangleright>
  (($tr\<^sup>> - $tr\<^sup><) \<in> {[(c\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u] | v. @(P v)} \<and> (c\<cdot>$x\<^sup>>)\<^sub>u = last($tr\<^sup>>))\<^sub>e))"

lemma InputCSP_CSP [closure]: "InputCSP c A P is CSP"
  by (simp add: CSP_ExtChoice InputCSP_def)

lemma InputCSP_NCSP [closure]: "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> InputCSP c A P is NCSP"
  apply (simp add: InputCSP_def)
  apply (rule NCSP_ExtChoice)
  apply (simp add: NCSP_Guard NCSP_PrefixCSP image_Collect_subsetI top_set_def)
  done

lemma InputVarCSP_NCSP [closure]: "InputVarCSP c x A is NCSP"
  by (simp add: AssignsCSP_NCSP InputCSP_NCSP InputVarCSP_def)

lemma Productive_InputCSP [closure]:
  "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> InputCSP x A P is Productive"
  by (auto simp add: InputCSP_def unrest closure intro: Productive_ExtChoice)

lemma Productive_InputVarCSP [closure]: "InputVarCSP c x A is Productive"
  by (simp add: InputVarCSP_def closure)

(*
lemma preR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "pre\<^sub>R(InputCSP a A P) = (\<Squnion> v \<bullet> [A(v)]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<longrightarrow>\<^sub>r (pre\<^sub>R (P(v)))\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
  by (simp add: InputCSP_def rdes closure assms alpha usubst unrest)
    
lemma periR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "peri\<^sub>R(InputCSP a A P) =
           ((\<Squnion> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<E>(true, \<guillemotleft>[]\<guillemotright>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u))) 
              \<triangleleft> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<triangleright>
            (\<Sqinter> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<and> (peri\<^sub>R (P x))\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)" 
  by (simp add: InputCSP_def rdes closure assms, pred_auto)

lemma postR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "post\<^sub>R(InputCSP a A P) =
          (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> post\<^sub>R (P x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
  using assms by (simp add: InputCSP_def rdes closure assms usubst unrest)
*)

lemma R4_st_pred_conj_do [rpred]:
  "((R4 [s\<^sub>1]\<^sub>S\<^sub><) \<and> \<Phi>(s\<^sub>2,\<sigma>,t) ;; P) = R4(\<Phi>(s\<^sub>1 \<and> s\<^sub>2,\<sigma>,t) ;; P) "
  by (pred_auto)

lemma unrest_ref'_R4 [unrest]: "$ref\<^sup>> \<sharp> P \<Longrightarrow> $ref\<^sup>> \<sharp> R4(P)"
  by (simp add: R4_def unrest unrest_ssubst_expr usubst_eval usubst)

lemma st_pred_conj_seq [rpred]:
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> ([s]\<^sub>S\<^sub>< \<and> P ;; Q) = (([s]\<^sub>S\<^sub>< \<and> P) ;; Q)"
  by (metis (no_types, lifting) R1_seqr_closure RR_implies_R1 cond_st_distr cond_st_miracle seqr_left_zero)
  
lemma InputCSP_rdes_def [rdes_def]:
  assumes "\<And> v. P(v) is CRC" "\<And> v. Q(v) is CRR" "\<And> v. R(v) is CRR"
          "\<And> v. $st\<^sup>> \<sharp> Q(v)" "\<And> v. $ref\<^sup>> \<sharp> R(v)"
  shows "InputCSP a A (\<lambda> v. \<^bold>R\<^sub>s(P(v) \<turnstile> Q(v) \<diamondop> R(v))) = 
           \<^bold>R\<^sub>s((\<Squnion> x. \<Phi>(@(A x),[\<leadsto>],[(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u]) wp\<^sub>r P x) \<turnstile>
             ((\<Squnion> x. \<E>(@(A x),\<guillemotleft>[]\<guillemotright>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}) \<or> \<E>(\<not> @(A x),[], {})) \<or> (\<Sqinter> x. \<Phi>(@(A x),[\<leadsto>],[(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u]) ;; Q x)) \<diamondop> 
             (\<Sqinter> x. \<Phi>(@(A x),[\<leadsto>],[(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u]) ;; R x))"
  by (simp add: InputCSP_def, rdes_simp cls: assms, pred_simp)

(*
lemma InputCSP_rdes_def [rdes_def]:
  assumes "\<And> v. P(v) is CRC" "\<And> v. Q(v) is CRR" "\<And> v. R(v) is CRR"
          "\<And> v. $st\<^sup>> \<sharp> Q(v)" "\<And> v. $ref\<acute> \<sharp> R(v)"
  shows "InputCSP a A (\<lambda> v. \<^bold>R\<^sub>s(P(v) \<turnstile> Q(v) \<diamondop> R(v))) = 
         \<^bold>R\<^sub>s( (\<Squnion> v \<bullet> ([A(v)]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<longrightarrow>\<^sub>r (P v)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))
           \<turnstile> (((\<Squnion> x \<bullet> R5([A(x)]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<E>(true, \<guillemotleft>[]\<guillemotright>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u)))) 
               \<or>
               (\<Sqinter> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<and> (P x \<and> Q x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))
           \<diamondop> (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<and> R x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))" (is "?lhs = ?rhs")
proof -
  have 1:"pre\<^sub>R(?lhs) = (\<Squnion> v \<bullet> [A v]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<longrightarrow>\<^sub>r P v\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)" (is "_ = ?A")
    by (simp add: rdes NCSP_rdes_intro assms conj_comm closure)
  have 2:"peri\<^sub>R(?lhs) = (\<Squnion> x \<bullet> [A x]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r \<E>(true,\<guillemotleft>[]\<guillemotright>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u)) \<triangleleft> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<triangleright> (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<longrightarrow>\<^sub>r Q x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
    (is "_ = ?B")
    by (simp add: rdes NCSP_rdes_intro assms closure)
  have 3:"post\<^sub>R(?lhs) = (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<longrightarrow>\<^sub>r R x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
    (is "_ = ?C")
    by (simp add: rdes NCSP_rdes_intro assms closure)
  have "?lhs = \<^bold>R\<^sub>s(?A \<turnstile> ?B \<diamondop> ?C)"
    by (subst SRD_reactive_tri_design[THEN sym], simp_all add: closure 1 2 3)
  also have "... = ?rhs"
    by (pred_auto)
  finally show ?thesis .
qed
*)

subsection \<open> Algebraic laws \<close>

lemma AssignCSP_conditional:
  assumes "vwb_lens x"
  shows "x :=\<^sub>C e \<triangleleft> b \<triangleright>\<^sub>R x :=\<^sub>C f = x :=\<^sub>C (e \<triangleleft> b \<triangleright> f)" 
  by (rdes_eq cls: assms)

lemma AssignsCSP_id: "\<langle>[\<leadsto>]\<rangle>\<^sub>C = Skip"
  by (pred_auto)

lemma Guard_comp:
  "g &\<^sub>C h &\<^sub>C P = (g \<and> h) &\<^sub>C P"
  by pred_auto

lemma Guard_false [simp]: "False &\<^sub>C P = Stop"
  unfolding GuardCSP_def
  by (simp add: GuardCSP_def Stop_def rpred closure alpha R1_design_R1_pre, pred_auto)

lemma Guard_true [simp]:
  assumes "P is CSP"
  shows "True &\<^sub>C P = P"
proof -
  have "True &\<^sub>C P = \<^bold>R\<^sub>s (((True)\<^sub>e \<longrightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (cmt\<^sub>R P \<or> (False)\<^sub>e \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> ($wait\<^sup>>)\<^sub>e))"
    by (simp add: GuardCSP_def alpha closure usubst rpred)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by pred_auto
  also have "... = P"
    by (simp add: SRD_reactive_design_alt assms)
  finally show ?thesis .
qed

lemma Guard_conditional:
  assumes "P is NCSP"
  shows "b &\<^sub>C P = P \<triangleleft> b \<triangleright>\<^sub>R Stop"  
  by (rdes_eq cls: assms)

lemma Guard_expansion:
  assumes "P is NCSP"
  shows "(g\<^sub>1 \<or> g\<^sub>2) &\<^sub>C P = (g\<^sub>1 &\<^sub>C P) \<box> (g\<^sub>2 &\<^sub>C P)"
  apply (rdes_eq_split cls: assms) 
    apply (pred_simp, fastforce simp add: dual_order.order_iff_strict)
   apply (pred_simp, simp add: dual_order.order_iff_strict, fastforce)
  apply (pred_simp, simp add: dual_order.order_iff_strict, fastforce)
  done

lemma Conditional_as_Guard:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q = (b &\<^sub>C P) \<box> ((\<not> b) &\<^sub>C Q)"
  apply (rdes_eq_split cls: assms)
    apply (pred_auto)
   apply (pred_simp, simp add: le_less, meson)+
  done

lemma PrefixCSP_dist:
  "PrefixCSP a (P \<sqinter> Q) = (PrefixCSP a P) \<sqinter> (PrefixCSP a Q)"
  by (meson Continuous_choice_dist PrefixCSP_Continuous)

lemma DoCSP_is_Prefix:
  "do\<^sub>C(a) = PrefixCSP a Skip"
  by (simp add: PrefixCSP_def Healthy_if closure, metis CSP4_DoCSP CSP4_def Healthy_def)

lemma PrefixCSP_seq:
  assumes "P is CSP" "Q is CSP"
  shows "(PrefixCSP a P) ;; Q = (PrefixCSP a (P ;; Q))"
  by (simp add: PrefixCSP_def seqr_assoc Healthy_if assms closure)

lemma PrefixCSP_extChoice_dist:
  assumes "P is NCSP" "Q is NCSP" "R is NCSP"
  shows "((a \<rightarrow>\<^sub>C P) \<box> (b \<rightarrow>\<^sub>C Q)) ;; R  = (a \<rightarrow>\<^sub>C P ;; R) \<box> (b \<rightarrow>\<^sub>C Q ;; R)"
  by (simp add: PCSP_PrefixCSP assms(1) assms(2) assms(3) extChoice_seq_distr)

lemma GuardedChoiceCSP_dist: 
  assumes "\<And> i. i\<in>A \<Longrightarrow> P(i) is NCSP" "Q is NCSP"
  shows "\<box> x\<in>A \<^bold>\<rightarrow> P(x) ;; Q = \<box> x\<in>A \<^bold>\<rightarrow> (P(x) ;; Q)"
  by (simp add: ExtChoice_seq_distr PrefixCSP_seq closure assms cong: ExtChoice_cong)

text \<open> Alternation can be re-expressed as an external choice when the guards are disjoint \<close>

declare ExtChoice_tri_rdes [rdes_def]
declare ExtChoice_tri_rdes' [rdes_def del]

declare extChoice_rdes_def [rdes_def]
declare extChoice_rdes_def' [rdes_def del]

(*
lemma AlternateR_as_ExtChoice:
  assumes 
    "\<And> i. i \<in> A \<Longrightarrow> P(i) is NCSP" "Q is NCSP"
    "\<And> i j. \<lbrakk> i \<in> A; j \<in> A; i \<noteq> j \<rbrakk> \<Longrightarrow> (g i \<and> g j) = false" 
  shows "(if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) else Q fi) = 
         (\<box> i\<in>A \<bullet> g(i) &\<^sub>C P(i)) \<box> (\<And> i\<in>A \<bullet> \<not> g(i)) &\<^sub>C Q"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: ExtChoice_empty extChoice_Stop closure assms)
next
  case False
  show ?thesis
  
  proof -
    have 1:"(\<Sqinter> i \<in> A \<bullet> g i \<rightarrow>\<^sub>R P i) = (\<Sqinter> i \<in> A \<bullet> g i \<rightarrow>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(P i) \<turnstile> peri\<^sub>R(P i) \<diamondop> post\<^sub>R(P i)))"
      by (rule UINF_cong, simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(1))
    have 2:"(\<box> i\<in>A \<bullet> g(i) &\<^sub>C P(i)) = (\<box> i\<in>A \<bullet> g(i) &\<^sub>C \<^bold>R\<^sub>s(pre\<^sub>R(P i) \<turnstile> peri\<^sub>R(P i) \<diamondop> post\<^sub>R(P i)))"
      by (rule ExtChoice_cong, simp add: NCSP_implies_NSRD NSRD_is_SRD SRD_reactive_tri_design assms(1))
    from assms(3) show ?thesis
      by (simp add: AlternateR_def 1 2)
         (rdes_eq' cls: assms(1-2) simps: False cong: UINF_cong USUP_cong ExtChoice_cong)
  qed
qed
*)

declare ExtChoice_tri_rdes [rdes_def del]
declare ExtChoice_tri_rdes' [rdes_def]

declare extChoice_rdes_def [rdes_def del]
declare extChoice_rdes_def' [rdes_def]

find_theorems R4

end