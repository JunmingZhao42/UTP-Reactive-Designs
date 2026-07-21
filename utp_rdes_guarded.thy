section \<open> Guarded Recursion \<close>

theory utp_rdes_guarded
  imports utp_rdes_productive
begin

subsection \<open> Traces with a size measure \<close>

text \<open> Guarded recursion relies on our ability to measure the trace's size, in order to see if it
  is decreasing on each iteration. Thus, we here equip the trace algebra with the @{term size}
  function that provides this. \<close>

class size_trace = trace + size +
  assumes
    size_zero: "size 0 = 0" and
    size_nzero: "s > 0 \<Longrightarrow> size(s) > 0" and
    size_plus: "size (s + t) = size(s) + size(t)"
  \<comment> \<open> These axioms may be stronger than necessary. In particular, @{thm size_nzero} requires that
       a non-empty trace have a positive size. But this may not be the case with all trace models
       and is possibly more restrictive than necessary. In future we will explore weakening. \<close>
begin

lemma size_mono: "s \<le> t \<Longrightarrow> size(s) \<le> size(t)"
  by (metis le_add1 local.diff_add_cancel_left' local.size_plus)

lemma size_strict_mono: "s < t \<Longrightarrow> size(s) < size(t)"
  by (metis cancel_ab_semigroup_add_class.add_diff_cancel_left' local.diff_add_cancel_left' local.less_iff local.minus_gr_zero_iff local.size_nzero local.size_plus zero_less_diff)

lemma trace_strict_prefixE: "xs < ys \<Longrightarrow> (\<And>zs. \<lbrakk> ys = xs + zs; size(zs) > 0 \<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (metis local.diff_add_cancel_left' local.less_iff local.minus_gr_zero_iff local.size_nzero)

lemma size_minus_trace: "y \<le> x \<Longrightarrow> size(x - y) = size(x) - size(y)"
  by (metis diff_add_inverse local.diff_add_cancel_left' local.size_plus)

end

text \<open> Both natural numbers and lists are measurable trace algebras. \<close>

instance nat :: size_trace
  by (intro_classes, simp_all)

instance list :: (type) size_trace
  by (intro_classes, simp_all add: less_list_def' plus_list_def prefix_length_less zero_list_def)

subsection \<open> Guardedness \<close>

definition gvrt :: "(('t::size_trace,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) chain" where
[pred]: "gvrt(n) \<equiv> ($tr\<^sup>< \<le> $tr\<^sup>> \<and> size(tt) < \<guillemotleft>n\<guillemotright>)\<^sub>e"

lemma gvrt_chain: "chain gvrt"
  unfolding chain_def by pred_auto

lemma gvrt_limit: "\<Sqinter> (range gvrt) = ($tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e"
  by (pred_auto)

definition Guarded :: "(('t::size_trace,'\<alpha>) rp_hrel \<Rightarrow> ('t,'\<alpha>) rp_hrel) \<Rightarrow> bool" where
[pred]: "Guarded(F) = (\<forall> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)))"

lemma GuardedI: "\<lbrakk> \<And> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)) \<rbrakk> \<Longrightarrow> Guarded F"
  by (simp add: Guarded_def)

text \<open> Guarded reactive designs yield unique fixed-points. \<close>

theorem guarded_fp_uniq:
  assumes "mono F" "F \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H" "Guarded F"
  shows "\<mu> F = \<nu> F"
proof -
  have "constr F gvrt"
    using assms    
    by (auto simp add: constr_def gvrt_chain Guarded_def tcontr_alt_def')
  hence "(($tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e \<and> \<mu> F) = (($tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e \<and> \<nu> F)"
    apply (rule constr_fp_uniq)
     apply (simp add: assms)
    using gvrt_limit apply blast
    done
  moreover have "(($tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e \<and> \<mu> F) = \<mu> F"
  proof -
    have "\<mu> F is R1"
      by (rule SRD_healths(1), rule Healthy_mu, simp_all add: assms)
    thus ?thesis
      by (simp add: Healthy_def' R1_def pred_ba.inf.commute)
  qed
  moreover have "(($tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e \<and> \<nu> F) = \<nu> F"
  proof -
    have "\<nu> F is R1"
      by (rule SRD_healths(1), rule Healthy_nu, simp_all add: assms)
    thus ?thesis
      by (simp add: Healthy_def' R1_def pred_ba.inf.commute)
  qed
  ultimately show ?thesis
    by (simp)
qed

lemma Guarded_const [closure]: "Guarded (\<lambda> X. P)"
  by (simp add: Guarded_def)

lemma UINF_Guarded [closure]:
  assumes  "\<And> P. P \<in> A \<Longrightarrow> Guarded P"
  shows "Guarded (\<lambda> X. \<Sqinter>P\<in>A. P(X))"
proof (rule GuardedI)
  fix X n
  have "\<And> Y. ((\<Sqinter>P\<in>A. P Y) \<and> gvrt(n+1)) = ((\<Sqinter>P\<in>A. (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
    by pred_auto
  moreover have "((\<Sqinter>P\<in>A. (P X \<and> gvrt(n+1))) \<and> gvrt(n+1)) =  ((\<Sqinter>P\<in>A. (P (X \<and> gvrt(n)) \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    have "(\<Sqinter>P\<in>A. (P X \<and> gvrt(n+1))) = (\<Sqinter>P\<in>A. (P (X \<and> gvrt(n)) \<and> gvrt(n+1)))"
    proof (rule SUP_cong, simp)
      fix P assume "P \<in> A"
      thus "(P X \<and> gvrt(n+1)) = (P (X \<and> gvrt(n)) \<and> gvrt(n+1))"
        using Guarded_def assms by blast
    qed
    thus ?thesis by simp
  qed
  ultimately show "((\<Sqinter>P\<in>A. P X) \<and> gvrt(n+1)) = ((\<Sqinter>P\<in>A. (P (X \<and> gvrt(n)))) \<and> gvrt(n+1))"
    by simp
qed

lemma intChoice_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<sqinter> Q(X))"
proof -
  have "Guarded (\<lambda> X. \<Sqinter>F\<in>{P,Q}. F(X))"
    by (rule UINF_Guarded, auto simp add: assms)
  thus ?thesis
    by (simp)
qed

lemma cond_srea_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<triangleleft> b \<triangleright>\<^sub>R Q(X))"
  using assms by (pred_simp, meson)

text \<open> A tail recursive reactive design with a productive body is guarded. \<close>

lemma SRD_left_zero_2:
  assumes "P is SRD"
  shows "(\<exists> st\<^sup>< \<Zspot> II\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>) ;; P = (\<exists> st\<^sup>< \<Zspot> II\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>)"
proof -
  have "(\<exists> st\<^sup>< \<Zspot> II\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>) ;; R3h(P) = (\<exists> st\<^sup>< \<Zspot> II\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>)"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if SRD_healths(3) assms)
qed

lemma pred_expr_simps [simp]: "((True)\<^sub>e \<and> P) = P" by pred_simp

lemma Guarded_if_Productive [closure]:
  fixes P :: "('s, 't::size_trace,'\<alpha>) rsp_hrel"
  assumes "P is NSRD" "P is Productive"
  shows "Guarded (\<lambda> X. P ;; SRD(X))"
proof (clarsimp simp add: Guarded_def)
  \<comment> \<open> We split the proof into three cases corresponding to valuations for ok, wait, and wait'
        respectively. \<close>
  fix X n
  have a:"(P ;; SRD(X) \<and> gvrt (Suc n))\<lbrakk>False/ok\<^sup><\<rbrakk> =
        (P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>False/ok\<^sup><\<rbrakk>"
    by (simp add: usubst closure assms )
       (simp add: Healthy_def' SRD_idem SRD_left_zero_1)
  have b:"((P ;; SRD(X) \<and> gvrt (Suc n))\<lbrakk>True/ok\<^sup><\<rbrakk>)\<lbrakk>True/wait\<^sup><\<rbrakk> =
          ((P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>True/ok\<^sup><\<rbrakk>)\<lbrakk>True/wait\<^sup><\<rbrakk>"
    by (simp add: Healthy_Idempotent usubst closure SRD_left_zero_2 assms)
  have c:"((P ;; SRD(X) \<and> gvrt (Suc n))\<lbrakk>True/ok\<^sup><\<rbrakk>)\<lbrakk>False/wait\<^sup><\<rbrakk> =
          ((P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>True/ok\<^sup><\<rbrakk>)\<lbrakk>False/wait\<^sup><\<rbrakk>"
  proof -
    have 1:"(P\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; (SRD X)\<lbrakk>True/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> =
          (P\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>True/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (simp add: Healthy_Idempotent R3h_wait_true SRD_Idempotent SRD_healths(3))
    have 2:"(P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD X)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> =
          (P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
    proof -
      have exp:"\<And> Y::('s, 't,'\<alpha>) rsp_hrel. (P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> =
                  ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>False/wait\<^sup><\<rbrakk> \<or> (post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) ;; (SRD Y)\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>))
                     \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
      proof -
        fix Y :: "('s, 't,'\<alpha>) rsp_hrel"

        have "(P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> =
              ((\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
          by (metis (no_types) Healthy_def Productive_form assms(1) assms(2) NSRD_is_SRD)
        also have "... =
             ((R1(R2c(pre\<^sub>R(P) \<longrightarrow> (ok\<^sup>> \<and> post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))))\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
          by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def RD1_def RD2_def wait'_cond_def usubst_eval usubst unrest assms closure design_def)

        also have "... =
             (((\<not>\<^sub>r pre\<^sub>R(P) \<or> (ok\<^sup>> \<and> post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
          by (simp add: impl_neg_disj R2c_disj R1_disj R2c_not  assms closure R2c_and
              R2c_preR rea_not_def R1_extend_conj' R2c_ok' R2c_post_SRD R1_tr_less_tr' R2c_tr_less_tr')
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>False/wait\<^sup><\<rbrakk> \<or> (ok\<^sup>> \<and> post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
          by (simp add: usubst unrest assms closure seqr_or_distl NSRD_neg_pre_left_zero)
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>False/wait\<^sup><\<rbrakk> \<or> (post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) ;; (SRD Y)\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
        proof -
          have "(ok\<^sup>> \<and> post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk> =
                ((post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) \<and> ($ok\<^sup>>)\<^sub>e) ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk>"
            by (simp add: pred_ba.inf_assoc pred_ba.inf_commute aext_var)
          also have "... = (post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)\<lbrakk>True/ok\<^sup>>\<rbrakk> ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk>\<lbrakk>True/ok\<^sup><\<rbrakk>"
            using seqr_left_one_point[of ok "(post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)" True "(SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk>"]
            by simp
          finally show ?thesis by (simp add: usubst unrest)
        qed
        finally 
        show "(P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD Y)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> =
                  ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>False/wait\<^sup><\<rbrakk> \<or> (post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) ;; (SRD Y)\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>))
                     \<and> gvrt (Suc n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>" .        
      qed


      have 1:"((post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) ;; (SRD X)\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<and> gvrt (Suc n)) =
               ((post\<^sub>R P \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) ;; (SRD (X \<and> gvrt n))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<and> gvrt (Suc n))"
        apply (pred_auto add: size_minus_trace less_diff_conv2 size_mono)
        apply (smt (z3) add_strict_left_mono nat_neq_iff not_less_eq order_less_trans size_strict_mono)
        apply (smt (z3) add_strict_left_mono nat_neq_iff not_less_eq order_le_less order_less_le_trans size_strict_mono)
         apply blast+
          done
      have 2:"(\<not>\<^sub>r pre\<^sub>R P) ;; (SRD X)\<lbrakk>False/wait\<^sup><\<rbrakk> = (\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(X \<and> gvrt n))\<lbrakk>False/wait\<^sup><\<rbrakk>"
        by (simp add: Healthy_Idempotent NSRD_neg_pre_left_zero R1_wait_false_closed RD1_wait_false SRD_Idempotent SRD_healths(1) SRD_healths(4) assms(1))
      show ?thesis
        by (simp add: "1" "2" exp pred_ba.boolean_algebra.conj_disj_distrib2)
    qed

    show ?thesis
    proof -
      have "(P ;; (SRD X) \<and> gvrt (n+1))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> =
          ((P\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; (SRD X)\<lbrakk>True/wait\<^sup><\<rbrakk> \<and> gvrt (n+1))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<or>
          (P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD X)\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (n+1))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>)"
        by (subst seqr_bool_split[of wait], simp_all add: usubst pred_ba.boolean_algebra.conj_disj_distrib2)

      also
      have "... = ((P\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>True/wait\<^sup><\<rbrakk> \<and> gvrt (n+1))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<or>
                 (P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>False/wait\<^sup><\<rbrakk> \<and> gvrt (n+1))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>)"
        by (simp add: 1 2)

      also
      have "... = ((P\<lbrakk>True/wait\<^sup>>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>True/wait\<^sup><\<rbrakk> \<or>
                    P\<lbrakk>False/wait\<^sup>>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>False/wait\<^sup><\<rbrakk>) \<and> gvrt (n+1))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
        by (simp add: usubst pred_ba.boolean_algebra.conj_disj_distrib2)

      also have "... = (P ;; (SRD (X \<and> gvrt n)) \<and> gvrt (n+1))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>"
        by (subst seqr_bool_split[of wait], simp_all add: usubst)
      finally show ?thesis by (simp add: usubst)
    qed

  qed
  show "(P ;; SRD(X) \<and> gvrt (Suc n)) = (P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))"
    apply (rule_tac bool_eq_substI[of "(ok\<^sup><)\<^sub>v"])
      apply (simp_all add: a)
    apply (rule_tac bool_eq_substI[of "(wait\<^sup><)\<^sub>v"])
      apply (simp_all add: b c)
  done
qed

subsection \<open> Tail recursive fixed-point calculations \<close>

declare upred_semiring.power_Suc [simp]

lemma mu_csp_form_1 [rdes]:
  fixes P :: "('s, 't::size_trace,'\<alpha>) rsp_hrel"
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X. P ;; SRD(X)) = (\<Sqinter>i. P \<^bold>^ (i+1)) ;; Miracle"
proof -
  have 1:"Continuous (\<lambda>X. P ;; SRD X)"
    using SRD_Continuous
    by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], drule_tac x="A" in spec, simp)
  have 2: "(\<lambda>X. P ;; SRD X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"  
    by (blast intro: funcsetI closure assms)
  with 1 2 have "(\<mu> X. P ;; SRD(X)) = (\<nu> X. P ;; SRD(X))"
    by (simp add: guarded_fp_uniq Guarded_if_Productive[OF assms] funcsetI closure)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; SRD X) ^^ i) false)"
    by (simp add: sup_continuous_lfp 1 sup_continuous_Continuous false_pred_def bot_fun_def SEXP_def)
  also have "... = ((\<lambda>X. P ;; SRD X) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P ;; SRD X) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; SRD X) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1) ;; Miracle)"
  proof (rule SUP_cong, simp_all) 
    fix i
    show "P ;; SRD (((\<lambda>X. P ;; SRD X) ^^ i) false) = (P ;; P \<^bold>^ i) ;; Miracle"
    proof (induct i)
      case 0
      then show ?case
        by (simp, metis srdes_theory.healthy_top)
    next
      case (Suc i)
      then show ?case
        by (simp add: Healthy_if NSRD_is_SRD SRD_power_comp SRD_seqr_closure assms(1) seqr_assoc[THEN sym] srdes_theory.top_closed)
    qed
  qed
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1)) ;; Miracle"
    by (simp add: seq_SUP_distr)
  finally show ?thesis
    by blast
qed

lemma mu_csp_form_NSRD [closure]:
  fixes P :: "('s, 't::size_trace,'\<alpha>) rsp_hrel"
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X. P ;; SRD(X)) is NSRD"
  by (simp add: mu_csp_form_1 assms closure)

lemma mu_csp_form_1':
  fixes P :: "('s, 't::size_trace,'\<alpha>) rsp_hrel"
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X. P ;; SRD(X)) = (P ;; P\<^sup>\<star>) ;; Miracle"
proof -
  have "(\<mu> X. P ;; SRD(X)) = (\<Sqinter> i\<in>UNIV. P ;; P \<^bold>^ i) ;; Miracle"
    by (simp add: mu_csp_form_1 assms closure ustar_def)
  also have "... = (P ;; P\<^sup>\<star>) ;; Miracle"
    by (simp only: seq_SUP_distl[THEN sym], simp add: ustar_def)
  finally show ?thesis .
qed

declare upred_semiring.power_Suc [simp del]

subsection \<open> Tail-recursive with non-deterministic termination \<close>

text \<open> A more general recursive pattern with an exit branch \<close>

lemma SUP_atLeastLessThan_Zero:
  fixes P :: "nat \<Rightarrow> 'b::complete_lattice"
  shows "(\<Sqinter>i\<in>{0..<Suc n}. P(i)) = P(0) \<sqinter> (\<Sqinter>i\<in>{1..<Suc n}. P(i))"
  by (simp add: atLeast0_lessThan_Suc_eq_insert_0)

lemma SUP_atLeastLessThan_Suc:
  fixes P :: "nat \<Rightarrow> 'b::complete_lattice"
  shows "(\<Sqinter>i\<in>{0..<Suc n}. P(i)) = (\<Sqinter>i\<in>{0..<n}. P(i)) \<sqinter> P(n)"
  by (simp add: atLeast0_lessThan_Suc sup_commute)

declare sup_apply [simp del]
declare Sup_apply [simp del]
declare SUP_apply [simp del]

lemma funpow_ndet_iter_expand: 
  assumes "P is SRD" "Q is SRD"
  shows "((\<lambda>X. (P ;; SRD X) \<sqinter> Q) ^^ (Suc i)) false = (P\<^bold>^(Suc i) ;; Miracle) \<sqinter> (\<Sqinter>j\<in>{0..<Suc i}. P\<^bold>^j ;; Q)"
proof (induct i)
  case 0
  then show ?case
    by (simp add: srdes_theory.healthy_top)
next
  case (Suc i)                         
  have 1: "(P ;; P \<^bold>^ i ;; Miracle) is SRD"
    by (simp add: SRD_power_comp SRD_seqr_closure assms rel_RA1 srdes_theory.top_closed)
  have 2: "(\<Sqinter>x\<in>{0..<Suc i}. P \<^bold>^ x ;; Q) is SRD"
  proof -
    have "\<And>x. x \<in> {0..<Suc i} \<Longrightarrow> P \<^bold>^ x ;; Q is SRD"
      by (metis SRD_power_Suc SRD_seqr_closure assms old.nat.exhaust power.power.power_0 upred_semiring.mult.left_neutral)
    thus ?thesis
      by (metis (lifting) SRD_Continuous Sup_Continuous_closed atLeast0LessThan empty_iff lessThan_iff zero_less_Suc)
  qed
  have 3: "(P ;; (\<Sqinter>x\<in>{0..<Suc i}. P \<^bold>^ x ;; Q)) \<sqinter> Q = (\<Sqinter>x\<in>{0..<Suc (Suc i)}. P \<^bold>^ x ;; Q)"
  proof -
    have "P ;; (\<Sqinter>x\<in>{0..<Suc i}. P \<^bold>^ x ;; Q) = (\<Sqinter>x\<in>{0..<Suc i}. P ;; (P \<^bold>^ x ;; Q))"
      by (simp add: seq_SUP_distl)
    also have "... = (\<Sqinter>x\<in>{0..<Suc i}. P \<^bold>^ Suc x ;; Q)"
      by (simp add: rel_RA1 upred_semiring.power_Suc)
    also have "... = ((\<Sqinter>x\<in>{1..<Suc (Suc i)}. P \<^bold>^ x ;; Q))"
      by (metis One_nat_def atLeastLessThanSuc_atLeastAtMost image_Suc_atLeastAtMost image_image seq_SUP_distr)
    finally show ?thesis
      by (simp add: SUP_atLeastLessThan_Zero sup_commute)
  qed
  from Suc 1 2 3 show ?case
    by (simp add: upred_semiring.distrib_left Continuous_choice_dist seqr_assoc closure assms upred_semiring.power_Suc srdes_theory.healthy_top[THEN sym]
       ,simp add: Healthy_if sup_assoc)
qed

lemma mu_csp_form_2 [rdes]:
  fixes P Q :: "('s,'t::size_trace,'\<alpha>) rsp_hrel"
  assumes "P is NSRD" "P is Productive" "Q is NSRD"
  shows "(\<mu> X. (P ;; SRD X) \<sqinter> Q) = (\<Sqinter>i. (P\<^bold>^(Suc i) ;; Miracle) \<sqinter> (\<Sqinter>j\<in>{0..<Suc i}. P\<^bold>^j ;; Q))"
proof -
  have 1:"Continuous (\<lambda>X. (P ;; SRD X) \<sqinter> Q)"
    using SRD_Continuous
    by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym] ref_lattice.INF_inf_const1 ref_lattice.inf_commute, drule_tac x="A" in spec, simp)
  have 2: "(\<lambda>X. (P ;; SRD X) \<sqinter> Q) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
    by (rule funcsetI, simp add: closure assms)
  with 1 2 have "(\<mu> X. (P ;; SRD X) \<sqinter> Q) = (\<nu> X. (P ;; SRD X) \<sqinter> Q)"
    by (simp add: guarded_fp_uniq funcsetI closure assms)
  also have "... = (\<Sqinter>i. ((\<lambda>X. (P ;; SRD X) \<sqinter> Q) ^^ i) false)"
    by (simp add: "1" sup_continuous_Continuous sup_continuous_lfp top_false)
  also have "... = ((\<lambda>X. (P ;; SRD X) \<sqinter> Q) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. (P ;; SRD X) \<sqinter> Q) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. (P ;; SRD X) \<sqinter> Q) ^^ (Suc i)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. (P \<^bold>^ Suc i ;; Miracle) \<sqinter> (\<Sqinter>j\<in>{0..<Suc i}. P\<^bold>^j ;; Q))"
    by (metis (lifting) NSRD_iff assms(1,3) funpow_ndet_iter_expand)
  finally show ?thesis .
qed

declare sup_apply [simp]
declare Sup_apply [simp]
declare SUP_apply [simp]

end