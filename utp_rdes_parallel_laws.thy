section \<open> Ordinary reactive design merge healthiness and parallel laws \<close>

theory utp_rdes_parallel_laws
  imports utp_rdes_parallel
begin

text \<open>
  Ordinary RD merge laws for R1, R2, R3c, RD1 and RD2.
  State-merge lifting is in @{text utp_rdes_parallel_lift};
  stateful laws are in @{text utp_srdes_parallel_laws}.
\<close>

subsection \<open> Merge Healthiness \<close>

subsubsection \<open> Definitions \<close>

text \<open>
  @{const R2m} enforces trace growth and removes the common history.
  @{const RD1m} handles prior divergence, @{const RD2} output termination,
  and @{text R3cm} prior waiting with ordinary reactive skip.
  RADm combines these conditions.
\<close>

definition R3cm :: "('t::trace, 'a) rp merge \<Rightarrow> ('t, 'a) rp merge" where
  [pred]: "R3cm M \<equiv> (RD1m skip\<^sub>m \<triangleleft> $(<:wait\<^sup><) \<triangleright> M)"

definition RADm :: "('t::trace, 'a) rp merge \<Rightarrow> ('t, 'a) rp merge" where
  "RADm \<equiv> RD1m \<circ> R3cm \<circ> R2m \<circ> RD2"

subsubsection \<open> Component Idempotence and Monotonicity \<close>

text \<open>
  Idempotence and monotonicity of @{const R1m}, @{const R2m} and @{const RD2}
  are supplied upstream.
\<close>

lemma RD1m_idem: "RD1m (RD1m M) = RD1m M"
  by pred_auto

lemma RD1m_Idempotent [closure]: "Idempotent RD1m"
  by (simp add: Idempotent_def RD1m_idem)

lemma RD1m_mono: "M \<sqsubseteq> N \<Longrightarrow> RD1m M \<sqsubseteq> RD1m N"
  by pred_auto

lemma RD1m_Monotonic [closure]: "Monotonic RD1m"
  by (rule MonotonicI, rule RD1m_mono)

lemma R3cm_idem: "R3cm (R3cm M) = R3cm M"
  by (pred_auto)

lemma R3cm_mono: "M \<sqsubseteq> N \<Longrightarrow> R3cm M \<sqsubseteq> R3cm N"
  by (pred_auto)

lemma R3cm_Idempotent [closure]: "Idempotent R3cm"
  by (simp add: Idempotent_def R3cm_idem)

lemma R3cm_Monotonic [closure]: "Monotonic R3cm"
  by (auto simp: Monotonic_refine intro: R3cm_mono)

subsubsection \<open> Component Commutation \<close>

lemma RD1m_R3cm_commute: "RD1m (R3cm M) = R3cm (RD1m M)"
  by (pred_auto)

lemma RD1m_R2m_commute: "RD1m (R2m M) = R2m (RD1m M)"
  by (pred_auto)

lemma R2m_R3cm_commute: "R2m (R3cm M) = R3cm (R2m M)"
  by (pred_auto; metis minus_zero_eq)

lemma RD2_RD1m_commute: "RD2 (RD1m M) = RD1m (RD2 M)"
  by (simp add: RD2_def H2_split; pred_auto)

lemma RD2_R3cm_commute: "RD2 (R3cm M) = R3cm (RD2 M)"
  by (simp add: RD2_def H2_split; pred_auto)

lemma RD2_R2m_commute: "RD2 (R2m M) = R2m (RD2 M)"
  by (simp add: RD2_def H2_split; pred_auto)

lemmas R2m_RD1m_commute = RD1m_R2m_commute[THEN sym]
lemmas R2m_RD2_commute = RD2_R2m_commute[THEN sym]
lemmas RD1m_RD2_commute = RD2_RD1m_commute[THEN sym]

subsubsection \<open> RADm Idempotence and Monotonicity \<close>

lemma RADm_idem: "RADm (RADm M) = RADm M"
  by (simp add: RADm_def RD2_RD1m_commute RD2_R3cm_commute RD2_R2m_commute
      RD1m_R2m_commute[symmetric] R2m_R3cm_commute RD1m_R3cm_commute[symmetric]
      RD1m_idem R3cm_idem R2m_idem RD2_idem)

lemma RADm_mono: "M \<sqsubseteq> N \<Longrightarrow> RADm M \<sqsubseteq> RADm N"
  by (simp add: RADm_def RD1m_mono R3cm_mono R2m_mono RD2_mono)

lemma RADm_healthy [closure]: "RADm M is RADm"
  by (simp add: Healthy_def' RADm_idem)

lemma RADm_Idempotent [closure]: "Idempotent RADm"
  by (simp add: Idempotent_def RADm_idem)

lemma RADm_Monotonic [closure]: "Monotonic RADm"
  by (auto simp: Monotonic_refine intro: RADm_mono)

subsubsection \<open> RADm Fixed Points \<close>

lemma RADm_healths:
  "RADm M is RD1m" "RADm M is R3cm" "RADm M is R2m" "RADm M is RD2"
  by (simp_all add: Healthy_def' RADm_def
      RD2_RD1m_commute RD2_R3cm_commute RD2_R2m_commute
      RD1m_R2m_commute[symmetric] RD1m_R3cm_commute
      R2m_R3cm_commute RD1m_idem R3cm_idem R2m_idem RD2_idem)

lemma RADm_healthy_iff:
  "(M is RADm) \<longleftrightarrow> ((M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2))"
proof
  assume M: "M is RADm"
  show "(M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2)"
    using RADm_healths[of M] by (simp only: Healthy_if[OF M])
next
  assume "(M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2)"
  then show "M is RADm" by (simp add: Healthy_def' RADm_def)
qed

subsubsection \<open> Trace Growth \<close>

lemma RADm_R1m:
  assumes "M is RADm"
  shows "M is R1m"
proof -
  have h: "M is R2m" using assms by (simp add: RADm_healthy_iff)
  have "R1m M = R1m (R2m M)" by (simp only: Healthy_if[OF h])
  also have "... = R2m M" by (simp add: R2m_def R1m_idem)
  also have "... = M" by (rule Healthy_if[OF h])
  finally show ?thesis by (simp only: Healthy_def')
qed

subsection \<open> Merge Evaluation \<close>

(* RD1m(M)(x,p,q,z) \<leftrightarrow> M(x,p,q,z) \<or> (\<not>ok(x) \<and> tr(x) \<le> tr(z)) *)
lemma RD1m_eval:
  "merge_eval (RD1m M) x p q z \<longleftrightarrow>
    merge_eval M x p q z \<or> (\<not> des_vars.ok\<^sub>v x \<and> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z)"
  by (pred_auto)

(* R3cm(M)(x,p,q,z) = (if wait(x) then
     z = x \<or> (\<not>ok(x) \<and> tr(x) \<le> tr(z)) else M(x,p,q,z)) *)
lemma R3cm_eval:
  "merge_eval (R3cm M) x p q z =
    (if rea_vars.wait\<^sub>v x then
      z = x \<or> (\<not> des_vars.ok\<^sub>v x \<and> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z)
     else merge_eval M x p q z)"
  by (pred_auto)

lemma RADm_unstarted:
  assumes "\<not> des_vars.ok\<^sub>v x"
  shows "merge_eval (RADm M) x p q z \<longleftrightarrow> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z"
  using assms by (simp add: RADm_def R3cm_def; pred_auto)

subsection \<open> Merge Algebra \<close>

subsubsection \<open> Disjunction and Conjunction \<close>

text \<open>
  The @{thm [source] R2m_disj} and @{thm [source] R2m_conj} laws are supplied
  by @{theory "UTP-Reactive.utp_rea_parallel"}.
\<close>

lemma RD1m_disj: "RD1m (M \<or> N) = (RD1m M \<or> RD1m N)"
  by pred_auto

lemma RD1m_conj: "RD1m (M \<and> N) = (RD1m M \<and> RD1m N)"
  by pred_auto

lemma RD2_merge_disj: "RD2 (M \<or> N) = (RD2 M \<or> RD2 N)"
  by (simp add: RD2_def H2_def seqr_or_distl)

lemma RD2_merge_conj:
  fixes M N :: "('t::trace, 'a) rp merge"
  assumes "M is RD2" "N is RD2"
  shows "RD2 (M \<and> N) = (RD2 M \<and> RD2 N)"
  using assms
  by (metis H2m_conj RD2_def H2m_def H2_def Healthy_def)

subsubsection \<open> Symmetry \<close>

lemma SymMerge_RD1m [closure]:
  assumes "M is SymMerge"
  shows "RD1m M is SymMerge"
  using assms by (pred_simp; blast)

lemma SymMerge_R2m [closure]:
  assumes "M is SymMerge"
  shows "R2m M is SymMerge"
  using assms by (pred_simp; blast)

lemma SymMerge_RD2 [closure]:
  assumes "M is SymMerge"
  shows "RD2 M is SymMerge"
  using assms
  by (simp add: Healthy_def' RD2_def H2_def seqr_assoc[THEN sym])

lemma RADm_SymMerge:
  assumes "M is SymMerge"
  shows "RADm M is SymMerge"
  using assms
  by (simp add: RADm_def Healthy_def' fun_eq_iff RD2_def H2_split; pred_auto; blast)

subsubsection \<open> Associativity \<close>

text \<open>
  @{const AssocMerge} is cyclic equality of two merge applications.
  @{const R2m} and @{const R3cm} preserve it. @{const RD1m} also preserves
  it under R1m, which R2m supplies in @{const RADm}.
  The combined rule requires associativity after @{const RD2};
  for an RD2-healthy input, @{const AssocMerge} alone suffices.
\<close>

lemma AssocMerge_RD1m:
  fixes M :: "('t::trace, 'a) rp merge"
  assumes growth: "M is R1m" and assoc: "AssocMerge M"
  shows "AssocMerge (RD1m M)"
proof -
  have bound: "merge_eval M x p q z \<Longrightarrow> tr\<^sub>v x \<le> tr\<^sub>v z" for x p q z
    using R1m_merge_eval[of M x p q z]
    by (simp only: Healthy_if[OF growth]; blast)
  have fold: "(\<exists>u. merge_eval (RD1m M) x p q u \<and>
      merge_eval (RD1m M) x u r z) =
    (if ok\<^sub>v x then
      (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z)
     else tr\<^sub>v x \<le> tr\<^sub>v z)" for x p q r z
    by (cases "ok\<^sub>v x"; simp add: RD1m_eval; blast dest: bound intro: exI[where x=x])
  show ?thesis using assoc unfolding AssocMerge_cyclic_eval
    by (simp only: fold if_bool_eq_conj; blast)
qed

lemma AssocMerge_R3cm:
  assumes assoc: "AssocMerge M"
  shows "AssocMerge (R3cm M)"
proof -
  have fold: "(\<exists>u. merge_eval (R3cm M) x p q u \<and>
      merge_eval (R3cm M) x u r z) =
    (if wait\<^sub>v x then
      z = x \<or> (\<not> ok\<^sub>v x \<and> tr\<^sub>v x \<le> tr\<^sub>v z)
     else (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z))"
    for x p q r z
    by (cases "wait\<^sub>v x"; simp add: R3cm_eval; blast intro: exI[where x=x])
  show ?thesis using assms unfolding AssocMerge_cyclic_eval
    by (simp only: fold if_bool_eq_conj; blast)
qed

lemma AssocMerge_R2m:
  fixes M :: "('t::trace, 'a) rp merge"
  assumes "AssocMerge M"
  shows "AssocMerge (R2m M)"
proof -
  define obs where
    "obs \<equiv> \<lambda>(x :: ('t, 'a) rp) (u :: ('t, 'a) rp).
      rea_vars.tr\<^sub>v_update (\<lambda>_. tr\<^sub>v u - tr\<^sub>v x) u"
  have restore:
    "obs x (rea_vars.tr\<^sub>v_update (\<lambda>_. tr\<^sub>v x + tr\<^sub>v u) u) = u"
    "tr\<^sub>v x \<le> tr\<^sub>v (rea_vars.tr\<^sub>v_update (\<lambda>_. tr\<^sub>v x + tr\<^sub>v u) u)"
    for x u
    by (cases u; simp add: obs_def)+
  have fold: "(\<exists>u. merge_eval (R2m M) x p q u \<and>
      merge_eval (R2m M) x u r z) =
    (tr\<^sub>v x \<le> tr\<^sub>v z \<and>
     (\<exists>u. merge_eval M (obs x x) (obs x p) (obs x q) u \<and>
       merge_eval M (obs x x) u (obs x r) (obs x z)))"
    for x p q r z
    by (auto simp: R2m_merge_eval obs_def; metis restore[unfolded obs_def])
  show ?thesis
    using assms unfolding AssocMerge_cyclic_eval
    by (simp only: fold; blast)
qed

subsubsection \<open> RADm Associativity \<close>

lemma RADm_AssocMerge_RD2:
  assumes "AssocMerge (RD2 M)"
  shows "AssocMerge (RADm M)"
proof -
  have trace: "R2m (RD2 M) is R1m"
    by (simp add: Healthy_def' R2m_def R1m_idem)
  have "AssocMerge (R3cm (RD1m (R2m (RD2 M))))"
    by (intro AssocMerge_R3cm AssocMerge_RD1m[OF trace] AssocMerge_R2m assms)
  then show ?thesis by (simp only: RADm_def comp_apply RD1m_R3cm_commute)
qed

lemma RADm_AssocMerge:
  assumes "M is RD2" "AssocMerge M"
  shows "AssocMerge (RADm M)"
  by (rule RADm_AssocMerge_RD2; simp only: Healthy_if[OF assms(1)] assms(2))

subsection \<open> Generic Parallel Laws \<close>

subsubsection \<open> Healthiness Closure \<close>

text \<open>
  Upstream supplies @{thm [source] R1_par_by_merge},
  @{thm [source] R2_par_by_merge}, @{thm [source] RD1_par_by_merge}
  and @{thm [source] RD2_par_by_merge}.
  The rules below add R3c and RD closure for the supplied merge.
\<close>

lemma R3cm_par_by_merge:
  fixes P Q :: "('t::trace, 'a) rp_hrel" and M :: "('t, 'a) rp merge"
  assumes "P is R3c" "Q is R3c" "M is R3cm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c"
proof -
  have wait: "R3c P (x,z) =
      (if rea_vars.wait\<^sub>v x then
        z = x \<or> (\<not> des_vars.ok\<^sub>v x \<and> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z)
       else P (x,z))" for P :: "('t,'a) rp_hrel" and x z
    by (pred_auto)
  have "R3c (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q) = (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q)"
  proof (rule ext, unfold split_paired_all)
    fix x z :: "('t, 'a) rp"
    show "R3c (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q) (x,z) = (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q) (x,z)"
      by (cases "rea_vars.wait\<^sub>v x"; simp add: wait par_by_merge_eval R3cm_eval; blast intro: exI[where x=x])
  qed
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)]
        Healthy_if[OF assms(3)] Healthy_def')
qed

lemma RD_par_by_RADm [closure]:
  assumes "P is RD" "Q is RD" "M is RADm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD"
proof -
  have m: "M is RD1m" "M is R3cm" "M is R2m" "M is RD2" "M is R1m"
    using assms(3) RADm_R1m unfolding RADm_healthy_iff by auto
  have h: "(P \<parallel>\<^bsub>M\<^esub> Q) is R1" "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
    "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c" "(P \<parallel>\<^bsub>M\<^esub> Q) is RD1" "(P \<parallel>\<^bsub>M\<^esub> Q) is RD2"
    using assms(1,2) m
    by (auto intro: R1_par_by_merge R2_par_by_merge R3cm_par_by_merge
        RD1_par_by_merge RD2_par_by_merge RD_healths)
  show ?thesis
    using h R2_implies_R2c[OF h(2)]
    by (simp add: Healthy_def' RD_alt_def RH_def)
qed

subsubsection \<open> Commutativity \<close>

lemma RADm_parallel_comm:
  assumes "M is SymMerge"
  shows "P \<parallel>\<^bsub>RADm M\<^esub> Q = Q \<parallel>\<^bsub>RADm M\<^esub> P"
  by (rule par_by_merge_comm[OF RADm_SymMerge[OF assms]])

subsubsection \<open> Associativity \<close>

lemma RADm_parallel_assoc:
  assumes "M is RD2" "M is SymMerge" "AssocMerge M"
  shows "(P \<parallel>\<^bsub>RADm M\<^esub> Q) \<parallel>\<^bsub>RADm M\<^esub> R = P \<parallel>\<^bsub>RADm M\<^esub> (Q \<parallel>\<^bsub>RADm M\<^esub> R)"
  by (rule par_by_merge_assoc[OF RADm_SymMerge[OF assms(2)]
        RADm_AssocMerge[OF assms(1,3)]])

end
