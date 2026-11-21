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
  ORDm combines these conditions.
\<close>

definition R3cm :: "('t::trace, 'a) rp merge \<Rightarrow> ('t, 'a) rp merge" where
  [pred]: "R3cm M \<equiv> (RD1m skip\<^sub>m \<triangleleft> $(<:wait\<^sup><) \<triangleright> M)"

definition ORDm :: "('t::trace, 'a) rp merge \<Rightarrow> ('t, 'a) rp merge" where
  "ORDm \<equiv> RD1m \<circ> R3cm \<circ> R2m \<circ> RD2"

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

lemma R3cm_Idempotent [closure]: "Idempotent R3cm"
  by (rule IdempotentI, pred_auto)

lemma R3cm_Monotonic [closure]: "Monotonic R3cm"
  by (rule MonotonicI, pred_auto)

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

subsubsection \<open> ORDm Idempotence and Monotonicity \<close>

lemma ORDm_Idempotent [closure]: "Idempotent ORDm"
  by (rule IdempotentI, simp add: ORDm_def RD2_RD1m_commute RD2_R3cm_commute RD2_R2m_commute
      RD1m_R2m_commute[symmetric] R2m_R3cm_commute RD1m_R3cm_commute[symmetric]
      RD1m_idem R3cm_Idempotent[unfolded Idempotent_def] R2m_idem RD2_idem)

lemma ORDm_mono: "M \<sqsubseteq> N \<Longrightarrow> ORDm M \<sqsubseteq> ORDm N"
  by (simp add: ORDm_def RD1m_mono R3cm_Monotonic[unfolded Monotonic_refine] R2m_mono RD2_mono)

lemma ORDm_Monotonic [closure]: "Monotonic ORDm"
  by (rule MonotonicI, rule ORDm_mono)

lemma ORDm_healthy [closure]: "ORDm M is ORDm"
  by (rule Healthy_Idempotent[OF ORDm_Idempotent])

subsubsection \<open> ORDm Fixed Points \<close>

lemma ORDm_healthy_iff:
  "(M is ORDm) \<longleftrightarrow> ((M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2))"
proof
  assume M: "M is ORDm"
  have "ORDm M is RD1m" "ORDm M is R3cm" "ORDm M is R2m" "ORDm M is RD2"
    by (simp_all add: Healthy_def' ORDm_def
        RD2_RD1m_commute RD2_R3cm_commute RD2_R2m_commute
        RD1m_R2m_commute[symmetric] RD1m_R3cm_commute R2m_R3cm_commute
        RD1m_idem R3cm_Idempotent[unfolded Idempotent_def] R2m_idem RD2_idem)
  then show "(M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2)"
    by (simp only: Healthy_if[OF M])
next
  assume "(M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2)"
  then show "M is ORDm" by (simp add: Healthy_def' ORDm_def)
qed

lemma ORDm_healths [closure]:
  assumes "M is ORDm"
  shows "M is RD1m" "M is R3cm" "M is R2m" "M is RD2"
  using assms by (simp_all add: ORDm_healthy_iff)

lemma ORDm_intro:
  assumes "M is RD1m" "M is R3cm" "M is R2m" "M is RD2"
  shows "M is ORDm"
  by (simp add: ORDm_healthy_iff assms)

subsubsection \<open> Trace Growth \<close>

lemma ORDm_R1m:
  assumes "M is ORDm"
  shows "M is R1m"
proof -
  have h: "M is R2m" using assms by (simp add: ORDm_healthy_iff)
  have "R1m M = R1m (R2m M)" by (simp only: Healthy_if[OF h])
  also have "... = R2m M" by (simp add: R2m_def R1m_idem)
  also have "... = M" by (rule Healthy_if[OF h])
  finally show ?thesis by (simp only: Healthy_def')
qed

subsubsection \<open> Design Merge Healthiness \<close>

text \<open>
  We can read @{const ORDm} as design merge healthiness followed by the reactive
  conditions: @{const RD2} on merges is @{const H2m}, and @{const RD1m} after
  @{const R2m} is @{const H1m} before it.
\<close>

lemma ORDm_HDm:
  fixes M :: "('t::trace, 'a) rp merge"
  shows "ORDm M = R3cm (R2m (HDm M))"
proof -
  have rd2: "RD2 N = H2m N" for N :: "('t, 'a) rp merge"
    by (simp add: RD2_def H2_def H2m_def)
  have rd1: "RD1m (R2m N) = R2m (H1m N)" for N :: "('t, 'a) rp merge"
    by pred_auto
  show ?thesis
    by (simp add: ORDm_def HDm_def RD1m_R3cm_commute rd1 rd2)
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

(* RD3c(M)(x,p,q,z) \<leftrightarrow> \<exists>u. M(x,p,q,u) \<and> (z = u \<or> (\<not>ok(u) \<and> tr(u) \<le> tr(z))) *)
lemma RD3c_merge_eval:
  "merge_eval (RD3c M) x p q z =
    (\<exists>u. merge_eval M x p q u \<and>
      (z = u \<or> (\<not> des_vars.ok\<^sub>v u \<and> rea_vars.tr\<^sub>v u \<le> rea_vars.tr\<^sub>v z)))"
  by (simp add: RD3c_def skip_rea_def; pred_auto)

lemma ORDm_unstarted:
  assumes "\<not> des_vars.ok\<^sub>v x"
  shows "merge_eval (ORDm M) x p q z \<longleftrightarrow> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z"
  using assms by (simp add: ORDm_def R3cm_def; pred_auto)

subsection \<open> Reactive Skip Completion \<close>

text \<open> @{const RD3c} commutes with each component of @{const ORDm}, so
  completing an ORDm-healthy merge with reactive skip keeps it ORDm-healthy. \<close>

lemma RD2_RD3c_commute: "RD2 (RD3c M) = RD3c (RD2 M)"
  by (simp only: RD3c_right_subsumes_RD2 RD3c_left_subsumes_RD2)

lemma RD1m_RD3c_commute:
  fixes M :: "('t::trace, 'a) rp merge"
  shows "RD1m (RD3c M) = RD3c (RD1m M)"
  by (rule rp_merge_eqI; simp only: RD1m_eval RD3c_merge_eval; blast intro: order_trans)

lemma R3cm_RD3c_commute:
  fixes M :: "('t::trace, 'a) rp merge"
  shows "R3cm (RD3c M) = RD3c (R3cm M)"
  by (rule rp_merge_eqI; simp only: R3cm_eval RD3c_merge_eval;
      auto intro: order_trans)

lemma R2m_RD3c_commute:
  fixes M :: "('t::trace, 'a) rp merge"
  shows "R2m (RD3c M) = RD3c (R2m M)"
proof (rule rp_merge_eqI)
  fix x p q z :: "('t, 'a) rp"
  let ?s = "\<lambda>u. rea_vars.tr\<^sub>v_update (\<lambda>_. tr\<^sub>v u - tr\<^sub>v x) u"
  let ?x0 = "rea_vars.tr\<^sub>v_update (\<lambda>_. 0) x"
  show "merge_eval (R2m (RD3c M)) x p q z = merge_eval (RD3c (R2m M)) x p q z"
  proof
    assume "merge_eval (R2m (RD3c M)) x p q z"
    then obtain v where hz: "tr\<^sub>v x \<le> tr\<^sub>v z" and m: "merge_eval M ?x0 (?s p) (?s q) v"
      and c: "?s z = v \<or> (\<not> ok\<^sub>v v \<and> tr\<^sub>v v \<le> tr\<^sub>v z - tr\<^sub>v x)"
      by (auto simp only: R2m_merge_eval RD3c_merge_eval; simp)
    let ?u = "rea_vars.tr\<^sub>v_update (\<lambda>_. tr\<^sub>v x + tr\<^sub>v v) v"
    have su: "?s ?u = v" by simp
    have "merge_eval (R2m M) x p q ?u"
      using m by (simp only: R2m_merge_eval su; simp)
    moreover have "z = ?u \<or> (\<not> ok\<^sub>v ?u \<and> tr\<^sub>v ?u \<le> tr\<^sub>v z)"
      using c hz
      by (cases z rule: rea_vars.cases_scheme; cases v rule: rea_vars.cases_scheme;
          auto simp: diff_add_cancel_left' dest: add_left_mono[where c="tr\<^sub>v x"])
    ultimately show "merge_eval (RD3c (R2m M)) x p q z"
      by (simp only: RD3c_merge_eval; blast)
  next
    assume "merge_eval (RD3c (R2m M)) x p q z"
    then obtain u where hu: "tr\<^sub>v x \<le> tr\<^sub>v u" and m: "merge_eval M ?x0 (?s p) (?s q) (?s u)"
      and c: "z = u \<or> (\<not> ok\<^sub>v u \<and> tr\<^sub>v u \<le> tr\<^sub>v z)"
      by (auto simp only: RD3c_merge_eval R2m_merge_eval)
    have hz: "tr\<^sub>v x \<le> tr\<^sub>v z" using c hu by (auto intro: order_trans)
    have "?s z = ?s u \<or> (\<not> ok\<^sub>v (?s u) \<and> tr\<^sub>v (?s u) \<le> tr\<^sub>v (?s z))"
      using c hu by (auto intro: minus_cancel_le)
    then show "merge_eval (R2m (RD3c M)) x p q z"
      using m hz by (simp only: R2m_merge_eval RD3c_merge_eval; auto)
  qed
qed

lemma ORDm_RD3c_commute:
  fixes M :: "('t::trace, 'a) rp merge"
  shows "ORDm (RD3c M) = RD3c (ORDm M)"
  by (simp add: ORDm_def RD1m_RD3c_commute R3cm_RD3c_commute R2m_RD3c_commute
      RD2_RD3c_commute)

lemma RD3c_ORDm [closure]:
  fixes M :: "('t::trace, 'a) rp merge"
  shows "M is ORDm \<Longrightarrow> RD3c M is ORDm"
  by (metis Healthy_def ORDm_RD3c_commute)

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

lemma ORDm_SymMerge:
  assumes "M is SymMerge"
  shows "ORDm M is SymMerge"
  using assms
  by (simp add: ORDm_def Healthy_def' fun_eq_iff RD2_def H2_split; pred_auto; blast)

subsubsection \<open> Associativity \<close>

text \<open>
  @{const AssocMerge} is cyclic equality of two merge applications.
  @{const R2m} and @{const R3cm} preserve it. @{const RD1m} also preserves
  it under R1m, which R2m supplies in @{const ORDm}.
  The combined rule requires associativity after @{const RD2}.
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
  show ?thesis using assoc unfolding AssocMerge_iff
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
  show ?thesis using assms unfolding AssocMerge_iff
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
    using assms unfolding AssocMerge_iff
    by (simp only: fold; blast)
qed

subsubsection \<open> ORDm Associativity \<close>

(* Move an intermediate J step through M to the final output. *)
lemma AssocMerge_RD2:
  fixes M :: "('t::trace, 'a) rp merge"
  assumes assoc: "AssocMerge M"
    and compat: "\<And>x u v r z. \<lbrakk> J (u,v); merge_eval M x v r z \<rbrakk> \<Longrightarrow>
      \<exists>y. merge_eval M x u r y \<and> J (y,z)"
  shows "AssocMerge (RD2 M)"
proof -
  have step: "merge_eval (RD2 M) x p q z =
      (\<exists>u. merge_eval M x p q u \<and> J (u,z))" for x p q z
    by (simp add: RD2_def H2_def; pred_auto)
  have refl: "J (u,u)" for u :: "('t, 'a) rp"
    by (pred_auto)
  have trans: "\<lbrakk> J (u,v); J (v,z) \<rbrakk> \<Longrightarrow> J (u,z)"
    for u v z :: "('t, 'a) rp"
    by (pred_auto)
  have fold: "(\<exists>u. merge_eval (RD2 M) x p q u \<and>
      merge_eval (RD2 M) x u r z) =
    (\<exists>u y. merge_eval M x p q u \<and> merge_eval M x u r y \<and> J (y,z))"
    for x p q r z
    unfolding step using compat refl trans by blast
  show ?thesis
    using assoc unfolding AssocMerge_iff
    by (simp only: fold; blast)
qed

lemma ORDm_AssocMerge_RD2:
  assumes "AssocMerge (RD2 M)"
  shows "AssocMerge (ORDm M)"
proof -
  have trace: "R2m (RD2 M) is R1m"
    by (simp add: Healthy_def' R2m_def R1m_idem)
  have "AssocMerge (R3cm (RD1m (R2m (RD2 M))))"
    by (intro AssocMerge_R3cm AssocMerge_RD1m[OF trace] AssocMerge_R2m assms)
  then show ?thesis by (simp only: ORDm_def comp_apply RD1m_R3cm_commute)
qed

subsubsection \<open> Nondivergence \<close>

text \<open> @{text NDRDm} requires a started, non-waiting merge of terminating
  branches to terminate. \<close>

(* NDRDm M ((ok,s),(okL,sL),(okR,sR),(ok',s')) =
     M (...) \<and> (ok \<and> \<not>wait \<and> okL \<and> okR \<longrightarrow> ok') *)
definition NDRDm :: "('t::trace, 'a) rp merge \<Rightarrow> ('t, 'a) rp merge" where
  "NDRDm M \<equiv> (\<lambda>(m,z). M (m,z) \<and>
    (ok\<^sub>v (mrg_prior\<^sub>v m) \<and> \<not> wait\<^sub>v (mrg_prior\<^sub>v m) \<and>
      ok\<^sub>v (mrg_left\<^sub>v m) \<and> ok\<^sub>v (mrg_right\<^sub>v m) \<longrightarrow> ok\<^sub>v z))"

lemma NDRDm_eval:
  "merge_eval (NDRDm M) x p q z =
    (merge_eval M x p q z \<and> (ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z))"
  by (simp add: NDRDm_def)

lemma NDRDm_Idempotent [closure]: "Idempotent NDRDm"
  by (rule IdempotentI, simp add: NDRDm_def fun_eq_iff)

lemma NDRDm_Monotonic [closure]: "Monotonic NDRDm"
  by (auto simp: mono_def NDRDm_def pred_refine_iff)

lemma NDRDm_healthy_iff:
  "M is NDRDm \<longleftrightarrow>
    (\<forall>x p q z. merge_eval M x p q z \<longrightarrow>
      ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z)"
proof
  assume h: "M is NDRDm"
  show "\<forall>x p q z. merge_eval M x p q z \<longrightarrow>
      ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z"
  proof (intro allI impI)
    fix x p q z
    assume "merge_eval M x p q z" "ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q"
    then show "ok\<^sub>v z"
      using NDRDm_eval[of M x p q z] Healthy_if[OF h] by simp
  qed
next
  assume a: "\<forall>x p q z. merge_eval M x p q z \<longrightarrow>
      ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z"
  show "M is NDRDm"
    unfolding Healthy_def'
  proof (rule ext, clarify)
    fix m z
    show "NDRDm M (m, z) = M (m, z)"
      using a by (cases m; auto simp: NDRDm_def)
  qed
qed

text \<open> @{const NDRDm} commutes with @{const R1m}, @{const R2m}, @{const R3cm} and
  @{const RD1m}, but not with @{const RD2} in general. \<close>

lemma NDRDm_R1m_commute: "NDRDm (R1m M) = R1m (NDRDm M)"
  by (simp add: NDRDm_def fun_eq_iff; pred_auto)

lemma NDRDm_R2m_commute: "NDRDm (R2m M) = R2m (NDRDm M)"
  by (simp add: NDRDm_def fun_eq_iff; pred_auto)

lemma NDRDm_R3cm_commute: "NDRDm (R3cm M) = R3cm (NDRDm M)"
  by (simp add: NDRDm_def R3cm_def fun_eq_iff; pred_auto)

lemma NDRDm_RD1m_commute: "NDRDm (RD1m M) = RD1m (NDRDm M)"
  by (simp add: NDRDm_def fun_eq_iff; pred_auto)

subsection \<open> Generic Parallel Laws \<close>

subsubsection \<open> Healthiness Closure \<close>

text \<open>
  Upstream supplies @{thm [source] R1_par_by_merge},
  @{thm [source] R2_par_by_merge}, @{thm [source] RD1_par_by_merge}
  and @{thm [source] RD2_par_by_merge}.
  The rules below add R3c and RD closure for the supplied merge.
\<close>

lemma R3c_par_by_merge:
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

lemma RD_par_by_merge [closure]:
  assumes "P is RD" "Q is RD" "M is ORDm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD"
proof -
  have m: "M is RD1m" "M is R3cm" "M is R2m" "M is RD2" "M is R1m"
    using ORDm_healths[OF assms(3)] ORDm_R1m[OF assms(3)] by simp_all
  have h: "(P \<parallel>\<^bsub>M\<^esub> Q) is R1" "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
    "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c" "(P \<parallel>\<^bsub>M\<^esub> Q) is RD1" "(P \<parallel>\<^bsub>M\<^esub> Q) is RD2"
    using assms(1,2) m
    by (auto intro: R1_par_by_merge R2_par_by_merge R3c_par_by_merge
        RD1_par_by_merge RD2_par_by_merge RD_healths)
  show ?thesis
    using h R2_implies_R2c[OF h(2)]
    by (simp add: Healthy_def' RD_alt_def RH_def)
qed

subsubsection \<open> Commutativity \<close>

lemma ORDm_parallel_comm:
  assumes "M is SymMerge"
  shows "P \<parallel>\<^bsub>ORDm M\<^esub> Q = Q \<parallel>\<^bsub>ORDm M\<^esub> P"
  by (rule par_by_merge_comm[OF ORDm_SymMerge[OF assms]])

subsubsection \<open> Associativity \<close>

text \<open>
  Parallel is associative on RD and NDRD operands when the merge is symmetric,
  NDRDm-healthy, and associative on branches that do not diverge from a
  started, non-waiting prior.
\<close>

lemma par_by_merge_assoc_NDRD:
  fixes M :: "('t::trace, 'a) rp merge"
  assumes rd: "P is RD" "Q is RD" "R is RD"
    and nondiv: "P is NDRD" "Q is NDRD" "R is NDRD"
    and merge: "M is SymMerge" "M is NDRDm"
      "AssocMerge (merge_guard (\<lambda>x z. ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z) M)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<parallel>\<^bsub>M\<^esub> R = P \<parallel>\<^bsub>M\<^esub> (Q \<parallel>\<^bsub>M\<^esub> R)"
proof (rule par_by_merge_assoc_guard[OF SymMerge_merge_guard[OF merge(1)] merge(3)])
  show "\<lbrakk> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v p; ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v q;
      merge_eval M x p q z \<rbrakk> \<Longrightarrow> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z" for x p q z
    using merge(2) by (simp add: NDRDm_healthy_iff)
  have pre: "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "pre\<^sub>R R = true\<^sub>r"
    using rd nondiv by (simp_all add: NDRD_healthy_iff)
  show "P (x,z) \<Longrightarrow> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z"
    "Q (x,z) \<Longrightarrow> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z"
    "R (x,z) \<Longrightarrow> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z" for x z
    using rd pre by (blast dest: preR_true_iff[OF RD_healths(1), THEN iffD1])+
qed

end
