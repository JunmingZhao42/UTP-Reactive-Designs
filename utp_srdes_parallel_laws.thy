section \<open> Stateful reactive design merge healthiness and parallel laws \<close>

theory utp_srdes_parallel_laws
  imports utp_rdes_parallel_laws
begin

text \<open>
  Stateful merge healthiness and laws for upstream's completed parallel.
  Shared RD merge laws are in @{theory "UTP-Reactive-Designs.utp_rdes_parallel_laws"}.
\<close>

subsection \<open> Stateful Merge Healthiness \<close>

subsubsection \<open> Definitions \<close>

text \<open>
  For the merge in @{term "P \<parallel>\<^bsub>M\<^esub> Q"}, @{const R1m} requires
  trace growth, @{const R2m} removes common history, @{const R3hm} handles
  prior waiting, @{const RD1m} prior divergence, and @{const RD2} output
  termination. @{const RD3} composes with stateful reactive skip.
  SRDM combines the premises of @{thm [source] SRD_par_by_merge};
  R2m implies R1m. Its fixed points need not be flag-independent.
\<close>

(* SRDM packages healthiness of the merge used directly in parallel. *)
definition SRDM :: "('s, 't::trace, 'a) rsp merge \<Rightarrow> ('s, 't, 'a) rsp merge" where
  "SRDM \<equiv> RD1m \<circ> RD2 \<circ> R3hm \<circ> R2m"

subsubsection \<open> Idempotence and Monotonicity \<close>

text \<open>
  Upstream supplies the @{const R1m}, @{const R2m} and @{const RD2}
  properties, and idempotence of @{const R3hm} and @{const RD3}.
\<close>

lemma R3hm_Idempotent [closure]: "Idempotent R3hm"
  by (simp add: Idempotent_def R3hm_idem)

lemma R3hm_mono: "M \<sqsubseteq> N \<Longrightarrow> R3hm M \<sqsubseteq> R3hm N"
  by pred_auto

lemma R3hm_Monotonic [closure]: "Monotonic R3hm"
  by (rule MonotonicI, rule R3hm_mono)

subsubsection \<open> Commutation \<close>

lemma R2m_R3hm_commute: "R2m (R3hm M) = R3hm (R2m M)"
  by (pred_auto; simp add: minus_zero_eq)

lemma RD1m_R3hm_commute: "RD1m (R3hm M) = R3hm (RD1m M)"
  by pred_auto

lemma R3hm_RD2_commute: "R3hm (RD2 M) = RD2 (R3hm M)"
  by (simp add: R3hm_def RD2_def H2_def rcond_seq_left_distr unrest, pred_auto)

lemma RD1m_RD3_commute:
  "RD1m (RD3 M) = RD3 (RD1m M)"
  by (simp add: RD1m_def RD3_def seqr_or_distl; pred_auto; blast intro: order_trans)

lemma R3hm_RD3_commute:
  "R3hm (RD3 M) = RD3 (R3hm M)"
proof -
  have skip: "II\<^sub>R\<^sub>M ;; II\<^sub>R = II\<^sub>R\<^sub>M"
    by (pred_auto; blast intro: order_trans)
  show ?thesis
    by (simp add: R3hm_def RD3_def rcond_seq_left_distr skip unrest)
qed

subsubsection \<open> Combined Healthiness \<close>

lemma SRDM_image_healths [closure]:
  "SRDM M is R2m"
  "SRDM M is R3hm"
  "SRDM M is RD1m"
  "SRDM M is RD2"
  by (simp_all add: Healthy_def' SRDM_def R2m_RD1m_commute R2m_RD2_commute
      R2m_R3hm_commute R2m_idem RD1m_R3hm_commute[symmetric]
      R3hm_RD2_commute R3hm_idem RD1m_idem RD1m_RD2_commute[symmetric] RD2_idem)

lemma SRDM_fixed_iff:
  "M is SRDM \<longleftrightarrow>
    (M is R1m) \<and> (M is R2m) \<and> (M is R3hm) \<and> (M is RD1m) \<and> (M is RD2)"
proof
  assume "M is SRDM"
  then show "(M is R1m) \<and> (M is R2m) \<and> (M is R3hm) \<and> (M is RD1m) \<and> (M is RD2)"
    using SRDM_image_healths[of M] R2m_implies_R1m
    by (auto simp: Healthy_def')
next
  assume "(M is R1m) \<and> (M is R2m) \<and> (M is R3hm) \<and> (M is RD1m) \<and> (M is RD2)"
  then show "M is SRDM"
    by (simp add: Healthy_def' SRDM_def)
qed

lemma SRDM_healths [closure]:
  assumes "M is SRDM"
  shows "M is R1m" "M is R2m" "M is R3hm" "M is RD1m" "M is RD2"
  using assms by (simp_all add: SRDM_fixed_iff)

lemma SRDM_intro:
  assumes "M is R2m" "M is R3hm" "M is RD1m" "M is RD2"
  shows "M is SRDM"
  by (simp add: SRDM_fixed_iff R2m_implies_R1m assms)

lemma SRDM_idem: "SRDM (SRDM M) = SRDM M"
  using SRDM_intro[OF SRDM_image_healths]
  by (simp add: Healthy_def')

lemma SRDM_Idempotent [closure]: "Idempotent SRDM"
  by (simp add: Idempotent_def SRDM_idem)

lemma SRDM_mono: "M \<sqsubseteq> N \<Longrightarrow> SRDM M \<sqsubseteq> SRDM N"
  by (simp add: SRDM_def RD1m_mono RD2_mono R3hm_mono R2m_mono)

lemma SRDM_Monotonic [closure]: "Monotonic SRDM"
  by (rule MonotonicI, rule SRDM_mono)

subsubsection \<open> Disjunction and Conjunction \<close>

lemma R3hm_disj: "R3hm (M \<or> N) = (R3hm M \<or> R3hm N)"
  by pred_auto

lemma R3hm_conj: "R3hm (M \<and> N) = (R3hm M \<and> R3hm N)"
  by pred_auto

lemma SRDM_disj: "SRDM (M \<or> N) = (SRDM M \<or> SRDM N)"
  by (simp add: SRDM_def R2m_disj R3hm_disj RD2_merge_disj RD1m_disj)

lemma SRDM_disj_closed [closure]:
  assumes "M is SRDM" "N is SRDM"
  shows "(M \<or> N) is SRDM"
  using assms by (simp add: Healthy_def' SRDM_disj)

lemma SRDM_conj_closed [closure]:
  assumes "M is SRDM" "N is SRDM"
  shows "(M \<and> N) is SRDM"
  apply (rule SRDM_intro)
  using SRDM_healths[OF assms(1)] SRDM_healths[OF assms(2)]
  by (simp_all add: Healthy_def' R2m_conj R3hm_conj RD1m_conj RD2_merge_conj)

subsubsection \<open> Symmetry \<close>

lemma SymMerge_R3hm [closure]:
  assumes "M is SymMerge"
  shows "R3hm M is SymMerge"
  using assms by (pred_simp; blast)

lemma SymMerge_SRDM [closure]:
  assumes "M is SymMerge"
  shows "SRDM M is SymMerge"
  by (simp add: SRDM_def assms SymMerge_RD1m SymMerge_RD2 SymMerge_R3hm SymMerge_R2m)

subsubsection \<open> Right Completion \<close>

lemma R2m_RD3_closed:
  fixes M :: "('s, 't::trace, 'a) rsp merge"
  assumes "M is R2m"
  shows "RD3 M is R2m"
proof -
  define obs where
    "obs x u = rea_vars.tr\<^sub>v_update (\<lambda>_. tr\<^sub>v u - tr\<^sub>v x) u"
    for x u :: "('s, 't, 'a) rsp"
  define shift where
    "shift x u = rea_vars.tr\<^sub>v_update (\<lambda>_. tr\<^sub>v x + tr\<^sub>v u) u"
    for x u :: "('s, 't, 'a) rsp"
  have undo: "obs x (shift x u) = u"
    and growth: "tr\<^sub>v x \<le> tr\<^sub>v (shift x u)" for x u
    by (cases u rule: srea_vars.cases_scheme; simp add: obs_def shift_def)+
  have restore: "tr\<^sub>v x \<le> tr\<^sub>v u \<Longrightarrow> shift x (obs x u) = u"
    for x u
    by (cases u rule: srea_vars.cases_scheme; simp add: obs_def shift_def diff_add_cancel_left')
  have add_eq: "(h + x = h + y) = (x = y)" for h x y :: "'t"
    by (auto dest: arg_cong[where f="\<lambda>t. t - h"])
  have add_le: "(h + x \<le> h + y) = (x \<le> y)" for h x y :: "'t"
    by (metis trace_class.add_le_imp_le_left trace_class.add_left_mono)
  have skip_shift: "II\<^sub>R (shift x u, shift x z) = II\<^sub>R (u,z)"
    for x u z
    by (cases u rule: srea_vars.cases_scheme; cases z rule: srea_vars.cases_scheme;
        simp add: shift_def; pred_simp; simp add: add_eq add_le)
  have skip_growth: "II\<^sub>R (u,z) \<Longrightarrow> tr\<^sub>v u \<le> tr\<^sub>v z" for u z :: "('s, 't, 'a) rsp"
    using fun_cong[OF Healthy_if[OF skip_srea_R1], of "(u,z)"]
    by (simp add: R1_def; pred_simp; blast)
  have normal:
    "merge_eval M x p q u \<longleftrightarrow>
      tr\<^sub>v x \<le> tr\<^sub>v u \<and>
      merge_eval M (obs x x) (obs x p) (obs x q) (obs x u)"
    for x p q u
    using R2m_merge_eval[of M x p q u]
    by (simp add: Healthy_if[OF assms] obs_def)
  have completed:
    "merge_eval (RD3 M) x p q z \<longleftrightarrow>
      (\<exists>u. merge_eval M x p q u \<and> II\<^sub>R (u,z))"
    for x p q z
    by (simp add: RD3_def; pred_auto)
  have fold:
    "merge_eval (RD3 M) x p q z \<longleftrightarrow>
      tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      (\<exists>u. merge_eval M (obs x x) (obs x p) (obs x q) u \<and>
        II\<^sub>R (u,obs x z))"
    for x p q z
  proof
    assume "merge_eval (RD3 M) x p q z"
    then obtain u where m: "merge_eval M x p q u" and skip: "II\<^sub>R (u,z)"
      by (auto simp only: completed)
    have hu: "tr\<^sub>v x \<le> tr\<^sub>v u" using m normal by blast
    have ho: "tr\<^sub>v x \<le> tr\<^sub>v z" using hu skip_growth[OF skip] by order
    have "II\<^sub>R (obs x u,obs x z)"
      using skip_shift[of x "obs x u" "obs x z"] restore[OF hu] restore[OF ho] skip by simp
    then show "tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      (\<exists>u. merge_eval M (obs x x) (obs x p) (obs x q) u \<and>
        II\<^sub>R (u,obs x z))"
      using ho m normal by blast
  next
    assume "tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      (\<exists>u. merge_eval M (obs x x) (obs x p) (obs x q) u \<and>
        II\<^sub>R (u,obs x z))"
    then obtain u where ho: "tr\<^sub>v x \<le> tr\<^sub>v z"
      and m: "merge_eval M (obs x x) (obs x p) (obs x q) u"
      and skip: "II\<^sub>R (u,obs x z)" by blast
    have "merge_eval M x p q (shift x u)"
      using normal[of x p q "shift x u"] growth[of x u] undo[of x u] m by simp
    moreover have "II\<^sub>R (shift x u,z)"
      using skip_shift[of x u "obs x z"] restore[OF ho] skip by simp
    ultimately show "merge_eval (RD3 M) x p q z" using completed by blast
  qed
  show ?thesis
    by (rule Healthy_intro, rule ext, case_tac x, rename_tac m z,
        hypsubst, case_tac m; simp only: R2m_merge_eval fold obs_def completed; simp)
qed

subsection \<open> Generic Parallel Laws \<close>

subsubsection \<open> Healthiness Closure \<close>

text \<open>
  @{thm [source] SRD_par_by_merge} combines the upstream rules
  @{thm [source] R1_par_by_merge}, @{thm [source] R2_par_by_merge},
  @{thm [source] R3h_par_by_merge}, @{thm [source] RD1_par_by_merge}
  and @{thm [source] RD2_par_by_merge}.
  The rules below add RD3, SRD and NSRD closure for the supplied merge,
  without applying @{const nmerge_rd} or @{const merge_rd}.
\<close>

lemma RD3_par_by_merge [closure]:
  assumes "M is RD3"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD3"
  using assms
  by (simp add: Healthy_def' RD3_def par_by_merge_def seqr_assoc)

lemma SRDM_par_by_merge [closure]:
  assumes "P is SRD" "Q is SRD" "M is SRDM"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is SRD"
  by (rule SRD_par_by_merge; simp add: assms SRDM_healths)

lemma NSRD_par_by_merge [closure]:
  assumes "P is SRD" "Q is SRD" "M is SRDM" "M is RD3"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is NSRD"
  by (rule SRD_RD3_implies_NSRD)
     (simp_all add: assms SRDM_par_by_merge RD3_par_by_merge)

subsection \<open> Upstream RD Merge Construction \<close>

subsubsection \<open> Flag-Independent Input Merges \<close>

text \<open>
  @{const RDM} requires R2m and independence from all prior, branch
  and output @{term ok} and @{term wait} flags. Use @{thm [source] RDM_intro};
  @{thm [source] RDM_R1m}, @{thm [source] RDM_R2m} and
  @{thm [source] RDM_unrests} give its component properties.
\<close>

lemma RDM_trace_growth:
  assumes "M is RDM" "merge_eval M x p q z"
  shows "tr\<^sub>v x \<le> tr\<^sub>v z"
  using R1m_merge_eval[of M x p q z] assms(2)
  by (simp add: Healthy_if[OF RDM_R1m[OF assms(1)]])

subsubsection \<open> Control Behaviour and Completion \<close>

text \<open>
  @{term "N\<^sub>R(M)"} adds R1m, R3hm and RD1m; it preserves R2m
  by @{thm [source] nmerge_rd_is_R2m}.
  The completed merge @{term "M\<^sub>R(M) = N\<^sub>R(M) ;; II\<^sub>R"} satisfies
  RD3 and RD2 by @{thm [source] merge_rd_is_RD3} and
  @{thm [source] merge_rd_is_RD2}. RDM constrains the input merge.
\<close>

lemma merge_rd_is_SRDM [closure]:
  assumes "M is RDM"
  shows "M\<^sub>R(M) is SRDM"
proof (rule SRDM_intro)
  show "M\<^sub>R(M) is R2m"
    using R2m_RD3_closed[OF nmerge_rd_is_R2m[OF RDM_R2m[OF assms]]]
    by (simp add: merge_rd_def RD3_def)
  show "M\<^sub>R(M) is R3hm" "M\<^sub>R(M) is RD1m"
    by (simp_all add: Healthy_def' merge_rd_def RD3_def[THEN sym]
        R3hm_RD3_commute RD1m_RD3_commute
        Healthy_if[OF nmerge_rd_is_R3hm] Healthy_if[OF nmerge_rd_is_RD1m])
  show "M\<^sub>R(M) is RD2"
    by (rule merge_rd_is_RD2)
qed

subsubsection \<open> Constructed Parallel Closure \<close>

text \<open>
  @{const RDM} constrains the flag-independent input; @{const SRDM}
  constrains the merge used directly in generic parallel.
  @{thm [source] par_rdes_NSRD} gives NSRD closure for the completed operator
  with SRD operands and an RDM input. The rules below recover this result
  through @{thm [source] SRDM_par_by_merge} and @{thm [source] NSRD_par_by_merge}.
  The lift supplies RDM by construction.
\<close>

lemma rdes_parallel_SRD [closure]:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q is SRD"
  by (rule SRDM_par_by_merge[OF assms(1,2) merge_rd_is_SRDM[OF assms(3)]])

lemma rdes_parallel_NSRD [closure]:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q is NSRD"
  by (rule NSRD_par_by_merge[OF assms(1,2) merge_rd_is_SRDM[OF assms(3)]
        merge_rd_is_RD3])

subsection \<open> Completed RD Parallel Laws \<close>

subsubsection \<open> Evaluation \<close>

text \<open>
  In the active case, waiting hides the output state. Divergence requires
  a feasible merged trace that the final trace extends.
\<close>

(* For M is RDM, fix the prior and branch observations. Write J(t,s,e) for M
   with output trace t, program state s and extension e; output flags are irrelevant.
   Let k \<equiv> okL \<and> okR and w \<equiv> waitL \<or> waitR. Then
   M_R(M) \<equiv>
     (\<not>ok \<and> tr \<le> tr') \<or>
     (ok \<and> wait \<and> ok' \<and> wait' \<and> tr' = tr \<and> e' = e) \<or>
     (ok \<and> \<not>wait \<and>
       ((k \<and> \<not>w \<and> ok' \<and> \<not>wait' \<and> J(tr',s',e')) \<or>
        (k \<and> w \<and> ok' \<and> wait' \<and> (\<exists>s'. J(tr',s',e'))) \<or>
        (\<not>k \<and> (\<exists>t s' e'. J(t,s',e') \<and> t \<le> tr')))).
   Here e/e' denote the prior/output extension observations. *)
lemma merge_rd_eval:
  fixes M :: "('s, 't::trace, 'a) rsp merge"
    and x p q z :: "('s, 't, 'a) rsp"
  assumes "M is RDM"
  defines "k \<equiv> ok\<^sub>v p \<and> ok\<^sub>v q"
      and "w \<equiv> wait\<^sub>v p \<or> wait\<^sub>v q"
  shows "merge_eval (M\<^sub>R(M)) x p q z \<longleftrightarrow>
    (\<not> ok\<^sub>v x \<and> tr\<^sub>v x \<le> tr\<^sub>v z) \<or>
    (ok\<^sub>v x \<and> wait\<^sub>v x \<and>
      z = srea_vars.st\<^sub>v_update (\<lambda>_. st\<^sub>v z) x) \<or>
    (ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and>
      ((k \<and> \<not> w \<and> ok\<^sub>v z \<and> \<not> wait\<^sub>v z \<and>
          merge_eval M x p q z) \<or>
       (k \<and> w \<and> ok\<^sub>v z \<and> wait\<^sub>v z \<and>
          (\<exists>v. merge_eval M x p q
            (srea_vars.st\<^sub>v_update (\<lambda>_. v) z))) \<or>
       (\<not> k \<and> (\<exists>u. merge_eval M x p q u \<and>
          tr\<^sub>v u \<le> tr\<^sub>v z))))"
proof -
  define J where "J t v e = merge_eval M x p q
    \<lparr>ok\<^sub>v = False, wait\<^sub>v = False, tr\<^sub>v = t, st\<^sub>v = v, \<dots> = e\<rparr>"
    for t v e
  have flags:
    "merge_eval M x p q
      \<lparr>ok\<^sub>v = b, wait\<^sub>v = w, tr\<^sub>v = t, st\<^sub>v = v, \<dots> = e\<rparr> = J t v e"
    for b w t v e
  proof -
    have change: "M\<lbrakk>False,False/ok\<^sup>>,wait\<^sup>>\<rbrakk> = M"
      by (simp add: usubst unrest assms(1))
    note point = fun_cong[OF change,
      of "(\<lparr>mrg_prior\<^sub>v = x, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q,
          \<dots> = ()\<rparr>,
        \<lparr>ok\<^sub>v = b, wait\<^sub>v = w, tr\<^sub>v = t, st\<^sub>v = v, \<dots> = e\<rparr>)"]
    show ?thesis
      using point unfolding J_def
      by pred_simp
  qed
  have growth: "J t v e \<Longrightarrow> tr\<^sub>v x \<le> t" for t v e
    unfolding J_def
    by (drule RDM_trace_growth[OF assms(1)]; simp)
  show ?thesis
    apply (simp add: merge_rd_def nmerge_rd_def nmerge_rd1_def nmerge_rd0_def
        skip_srea_form ex_unrest unrest assms(1))
    apply (cases "ok\<^sub>v x"; cases "wait\<^sub>v x";
        cases z rule: srea_vars.cases_scheme; pred_simp)
    apply (simp_all add: flags k_def w_def ex_bool_eq)
    apply (cases x rule: srea_vars.cases_scheme; simp)
    by (blast dest: growth intro: order_trans)+
qed

subsubsection \<open> Commutativity \<close>

lemma rdes_parallel_comm:
  assumes "M is SymMerge"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q = Q \<parallel>\<^sub>R\<^bsub>M\<^esub> P"
  by (rule par_by_merge_comm[OF SymMerge_merge_rd[OF assms]])

subsubsection \<open> Associativity \<close>

lemma rdes_parallel_assoc:
  assumes "M is SymMerge" "AssocMerge (M\<^sub>R(M))"
  shows "(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q) \<parallel>\<^sub>R\<^bsub>M\<^esub> R =
    P \<parallel>\<^sub>R\<^bsub>M\<^esub> (Q \<parallel>\<^sub>R\<^bsub>M\<^esub> R)"
  by (rule par_by_merge_assoc[OF SymMerge_merge_rd[OF assms(1)] assms(2)])

text \<open>Completion can turn a divergent intermediate result into a later terminating one.\<close>

lemma BasicMerge_completed_not_AssocMerge:
  "\<not> AssocMerge (M\<^sub>R(N\<^sub>B :: (unit,nat,unit) rsp merge))"
proof (rule notI)
  assume assoc: "AssocMerge (M\<^sub>R(N\<^sub>B :: (unit,nat,unit) rsp merge))"
  let ?K = "M\<^sub>R(N\<^sub>B :: (unit,nat,unit) rsp merge)"
  let ?x = "\<lparr>ok\<^sub>v=True, wait\<^sub>v=False, tr\<^sub>v=0, st\<^sub>v=(), \<dots>=()\<rparr> :: (unit,nat,unit) rsp"
  let ?p = "\<lparr>ok\<^sub>v=False, wait\<^sub>v=False, tr\<^sub>v=1, st\<^sub>v=(), \<dots>=()\<rparr> :: (unit,nat,unit) rsp"
  let ?q = "\<lparr>ok\<^sub>v=True, wait\<^sub>v=False, tr\<^sub>v=1, st\<^sub>v=(), \<dots>=()\<rparr> :: (unit,nat,unit) rsp"
  let ?r = "\<lparr>ok\<^sub>v=True, wait\<^sub>v=False, tr\<^sub>v=2, st\<^sub>v=(), \<dots>=()\<rparr> :: (unit,nat,unit) rsp"
  let ?u = ?r
  let ?z = ?u
  have basic_eval: "merge_eval (N\<^sub>B :: (unit,nat,unit) rsp merge) x p q z =
    (tr\<^sub>v x \<le> tr\<^sub>v z \<and>
     tr\<^sub>v z - tr\<^sub>v x = tr\<^sub>v p - tr\<^sub>v x \<and>
     tr\<^sub>v z - tr\<^sub>v x = tr\<^sub>v q - tr\<^sub>v x \<and>
     st\<^sub>v z = st\<^sub>v x)" for x p q z
    by (simp add: BasicMerge_def; pred_auto)
  have left: "merge_eval ?K ?x ?p ?q ?u \<and> merge_eval ?K ?x ?u ?r ?z"
    by (simp add: merge_rd_eval[OF BasicMerge_RDM] basic_eval;
        rule exI[where x="?q"]; simp)
  have right: "\<not> (\<exists>u. merge_eval ?K ?x ?q ?r u)"
    by (auto simp: merge_rd_eval[OF BasicMerge_RDM] basic_eval)
  from assoc have eq: "(\<exists>u. merge_eval ?K ?x ?p ?q u \<and> merge_eval ?K ?x u ?r ?z) =
    (\<exists>u. merge_eval ?K ?x ?q ?r u \<and> merge_eval ?K ?x u ?p ?z)"
    by (simp only: AssocMerge_cyclic_eval; blast)
  from left right eq show False by blast
qed

subsubsection \<open> Miracle Zero Laws \<close>

text \<open>
  @{thm [source] Miracle_parallel_left_zero} and
  @{thm [source] Miracle_parallel_right_zero} require an SRD operand
  and an RDM input merge. The instances below include Chaos.
\<close>

lemma Miracle_parallel_Chaos:
  assumes "M is RDM"
  shows "Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> Chaos = Miracle"
    and "Chaos \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle = Miracle"
  by (simp_all add: Miracle_parallel_left_zero Miracle_parallel_right_zero
      NSRD_is_SRD NSRD_Chaos assms)

subsubsection \<open> Chaos Zero: Exact Criterion \<close>

(* Chaos \<equiv> (\<not>ok \<and> tr \<le> tr') \<or>
           (ok \<and> wait \<and> ok' \<and> wait' \<and> tr' = tr \<and> e' = e) \<or>
           (ok \<and> \<not>wait \<and> tr \<le> tr').
   e/e' denote extension observations; the output state s' is unrestricted. *)

text \<open>
  For an active prior, divergence requires a divergent branch pair and
  a feasible merged trace. Such a pair admits every output extending that
  trace, with no operand healthiness premise.
\<close>

lemma rdes_parallel_divergent_eval:
  fixes P Q :: "('s, 't::trace, 'a) rsp_hrel"
  assumes merge: "M is RDM"
      and active: "ok\<^sub>v x" "\<not> wait\<^sub>v x"
      and divergent: "\<not> ok\<^sub>v z"
  shows "(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q) (x,z) \<longleftrightarrow>
    (\<exists>p q u. P (x,p) \<and> Q (x,q) \<and>
      \<not> (ok\<^sub>v p \<and> ok\<^sub>v q) \<and>
      merge_eval M x p q u \<and> tr\<^sub>v u \<le> tr\<^sub>v z)"
  using active divergent
  by (simp add: par_by_merge_eval merge_rd_eval[OF merge])

lemma rdes_parallel_divergentI:
  fixes P Q :: "('s, 't::trace, 'a) rsp_hrel"
  assumes merge: "M is RDM"
      and active: "ok\<^sub>v x" "\<not> wait\<^sub>v x"
      and branches: "P (x,p)" "Q (x,q)" "\<not> (ok\<^sub>v p \<and> ok\<^sub>v q)"
      and feasible: "merge_eval M x p q u" "tr\<^sub>v u \<le> tr\<^sub>v z"
  shows "(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q) (x,z)"
  using active branches feasible
  by (auto simp: par_by_merge_eval merge_rd_eval[OF merge])

text \<open>
  At the prior trace, RDM trace growth makes the feasible witness trace equal
  to the prior trace. The converse uses divergence introduction; the witness
  need not have the final output's program state.
\<close>

lemma rdes_parallel_Chaos_iff:
  fixes P Q :: "('s, 't::trace, 'a) rsp_hrel"
  assumes P: "P is SRD" and Q: "Q is SRD" and M: "M is RDM"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q = Chaos \<longleftrightarrow>
    (\<forall>x. ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow>
      (\<exists>p q u. P (x,p) \<and> Q (x,q) \<and>
        \<not> (ok\<^sub>v p \<and> ok\<^sub>v q) \<and> merge_eval M x p q u \<and>
        tr\<^sub>v u = tr\<^sub>v x))" (is "_ \<longleftrightarrow> ?feasible")
proof
  have trace: "(merge_eval M x p q u \<and> tr\<^sub>v u \<le> tr\<^sub>v x) =
      (merge_eval M x p q u \<and> tr\<^sub>v u = tr\<^sub>v x)" for x p q u
    using RDM_trace_growth[OF M, of x p q u]
    by (auto intro: antisym)
  assume eq: "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q = Chaos"
  show ?feasible
  proof (intro allI impI)
    fix x :: "('s, 't, 'a) rsp"
    assume active: "ok\<^sub>v x \<and> \<not> wait\<^sub>v x"
    have "(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q) (x, des_vars.ok\<^sub>v_update (\<lambda>_. False) x)"
      using eq active by (simp add: Chaos_eval)
    then show "\<exists>p q u. P (x,p) \<and> Q (x,q) \<and>
        \<not> (ok\<^sub>v p \<and> ok\<^sub>v q) \<and> merge_eval M x p q u \<and> tr\<^sub>v u = tr\<^sub>v x"
      using active by (simp add: rdes_parallel_divergent_eval[OF M] trace)
  qed
next
  assume witnesses: ?feasible
  show "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q = Chaos"
  proof (rule SRD_Chaos_eqI[OF NSRD_is_SRD[OF par_rdes_NSRD[OF P Q M]]])
    fix x z :: "('s, 't, 'a) rsp"
    assume active: "ok\<^sub>v x" "\<not> wait\<^sub>v x"
      and growth: "tr\<^sub>v x \<le> tr\<^sub>v z"
    obtain p q u where branches: "P (x,p)" "Q (x,q)"
        "\<not> (ok\<^sub>v p \<and> ok\<^sub>v q)"
      and merge: "merge_eval M x p q u"
      and trace: "tr\<^sub>v u = tr\<^sub>v x"
      using witnesses active by blast
    show "(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q) (x,z)"
      by (rule rdes_parallel_divergentI[where p=p and q=q and u=u];
          simp_all add: M active branches merge trace growth)
  qed
qed


end
