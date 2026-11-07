section \<open> Ordinary reactive design parallel from a trace and extension merge \<close>

theory utp_rdes_parallel_lift
  imports utp_rdes_parallel_laws
begin

text \<open>
  The raw lift applies @{term j} to traces and extension observations,
  conjoins branch @{term ok} flags, and disjoins branch @{term wait} flags.
  @{const ORDm} makes the merge RD-healthy; @{const RD3c} adds reactive skip
  completion. The unit-state bridge is in @{text utp_rdes_parallel_unit_state}.
\<close>

subsection \<open> Lifting a Trace and Extension Merge \<close>

subsubsection \<open> Construction \<close>

(* merge_rdes_raw j ((ok,wait,tr,s), (okL,waitL,trL,sL), (okR,waitR,trR,sR), (ok',wait',tr',s')) =
     ok' = (okL \<and> okR) \<and>
     wait' = (waitL \<or> waitR) \<and>
     j((tr,s), (trL,sL), (trR,sR), (tr',s')) *)
definition merge_rdes_raw ::
  "('t::trace \<times> 'a) merge \<Rightarrow> ('t, 'a) rp merge" where
  [pred]: "merge_rdes_raw j \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; p = mrg_left\<^sub>v m; q = mrg_right\<^sub>v m
    in ok\<^sub>v z = (ok\<^sub>v p \<and> ok\<^sub>v q) \<and>
       wait\<^sub>v z = (wait\<^sub>v p \<or> wait\<^sub>v q) \<and>
       merge_eval j (tr\<^sub>v x, rea_vars.more x)
         (tr\<^sub>v p, rea_vars.more p) (tr\<^sub>v q, rea_vars.more q)
         (tr\<^sub>v z, rea_vars.more z))"

(* merge_rdes = RD3c \<circ> ORDm \<circ> merge_rdes_raw,
     cf. merge_des = H3m \<circ> HDm \<circ> merge_des_raw *)
definition merge_rdes ::
  "('t::trace \<times> 'a) merge \<Rightarrow> ('t, 'a) rp merge" where
  "merge_rdes j \<equiv> RD3c (ORDm (merge_rdes_raw j))"

subsubsection \<open> Evaluation \<close>

lemma ORDm_merge_rdes_raw_eval:
  "merge_eval (ORDm (merge_rdes_raw j)) x p q z =
    ((\<not> ok\<^sub>v x \<and> tr\<^sub>v x \<le> tr\<^sub>v z) \<or>
    (ok\<^sub>v x \<and> wait\<^sub>v x \<and> z = x) \<or>
    (ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and>
      ((ok\<^sub>v p \<and> ok\<^sub>v q) \<longrightarrow> ok\<^sub>v z) \<and>
      wait\<^sub>v z = (wait\<^sub>v p \<or> wait\<^sub>v q) \<and>
      tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      merge_eval j (0, rea_vars.more x)
        (tr\<^sub>v p - tr\<^sub>v x, rea_vars.more p)
        (tr\<^sub>v q - tr\<^sub>v x, rea_vars.more q)
        (tr\<^sub>v z - tr\<^sub>v x, rea_vars.more z)))"
  by (simp add: ORDm_def R3cm_def RD2_def H2_split; pred_auto)

lemma merge_rdes_seq_eval:
  "merge_eval (merge_rdes j) x p q z =
    (\<exists>u. merge_eval (ORDm (merge_rdes_raw j)) x p q u \<and>
      (z = u \<or> (\<not> ok\<^sub>v u \<and> tr\<^sub>v u \<le> tr\<^sub>v z)))"
  by (simp only: merge_rdes_def RD3c_merge_eval)

text \<open>
  For an active prior, @{term j} uses traces relative to the prior trace.
  With both branches ok, it constrains the output. If either diverges, it
  needs only a witness whose trace is no longer than the final trace; the
  output flags and extension are free. A nondivergent waiting prior is preserved.
\<close>

(* merge_rdes j ((ok,wait,tr,s), (okL,waitL,trL,sL), (okR,waitR,trR,sR), (ok',wait',tr',s')) =
     (\<not>ok \<and> tr \<le> tr') \<or>
     (ok \<and> wait \<and> (ok',wait',tr',s') = (ok,wait,tr,s)) \<or>
     (ok \<and> \<not>wait \<and> okL \<and> okR \<and> ok' \<and> wait' = (waitL \<or> waitR) \<and> tr \<le> tr' \<and>
        j((0,s), (trL-tr,sL), (trR-tr,sR), (tr'-tr,s'))) \<or>
     (ok \<and> \<not>wait \<and> \<not>(okL \<and> okR) \<and> tr \<le> tr' \<and>
        (\<exists>t e. t \<le> tr'-tr \<and> j((0,s), (trL-tr,sL), (trR-tr,sR), (t,e)))) *)
lemma merge_rdes_eval:
  fixes x p q z :: "('t::trace, 'a) rp" and j :: "('t \<times> 'a) merge"
  shows "merge_eval (merge_rdes j) x p q z =
    ((\<not> ok\<^sub>v x \<and> tr\<^sub>v x \<le> tr\<^sub>v z) \<or>
    (ok\<^sub>v x \<and> wait\<^sub>v x \<and> z = x) \<or>
    (ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<and> ok\<^sub>v z \<and>
      wait\<^sub>v z = (wait\<^sub>v p \<or> wait\<^sub>v q) \<and> tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      merge_eval j (0, rea_vars.more x)
        (tr\<^sub>v p - tr\<^sub>v x, rea_vars.more p)
        (tr\<^sub>v q - tr\<^sub>v x, rea_vars.more q)
        (tr\<^sub>v z - tr\<^sub>v x, rea_vars.more z)) \<or>
    (ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> \<not> (ok\<^sub>v p \<and> ok\<^sub>v q) \<and> tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      (\<exists>t e. t \<le> tr\<^sub>v z - tr\<^sub>v x \<and> merge_eval j (0, rea_vars.more x)
          (tr\<^sub>v p - tr\<^sub>v x, rea_vars.more p)
          (tr\<^sub>v q - tr\<^sub>v x, rea_vars.more q) (t, e))))"
    (is "?L = ?R")
proof
  assume ?L
  then obtain u where "merge_eval (ORDm (merge_rdes_raw j)) x p q u"
    and "z = u \<or> (\<not> ok\<^sub>v u \<and> tr\<^sub>v u \<le> tr\<^sub>v z)"
    by (auto simp only: merge_rdes_seq_eval)
  then show ?R
    using minus_cancel_le[of "tr\<^sub>v x" "tr\<^sub>v u" "tr\<^sub>v z"]
      order_trans[of "tr\<^sub>v x" "tr\<^sub>v u" "tr\<^sub>v z"]
    by (cases "ok\<^sub>v x"; cases "wait\<^sub>v x"; cases "ok\<^sub>v p \<and> ok\<^sub>v q";
        auto simp: ORDm_merge_rdes_raw_eval)
next
  assume r: ?R
  show ?L
  proof (cases "ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<and> \<not> (ok\<^sub>v p \<and> ok\<^sub>v q)")
    case False
    with r show ?thesis
      unfolding merge_rdes_seq_eval
      by (auto simp: ORDm_merge_rdes_raw_eval)
  next
    case True
    with r obtain t e where hz: "tr\<^sub>v x \<le> tr\<^sub>v z" and ht: "t \<le> tr\<^sub>v z - tr\<^sub>v x"
      and je: "merge_eval j (0, rea_vars.more x)
        (tr\<^sub>v p - tr\<^sub>v x, rea_vars.more p) (tr\<^sub>v q - tr\<^sub>v x, rea_vars.more q) (t, e)"
      by blast
    from True je add_left_mono[OF ht, of "tr\<^sub>v x"] hz show ?thesis
      unfolding merge_rdes_seq_eval
      by (intro exI[where x="\<lparr>ok\<^sub>v = False, wait\<^sub>v = (wait\<^sub>v p \<or> wait\<^sub>v q),
            tr\<^sub>v = tr\<^sub>v x + t, \<dots> = e\<rparr>"])
        (simp add: ORDm_merge_rdes_raw_eval diff_add_cancel_left')
  qed
qed

subsubsection \<open> Healthiness \<close>

lemma merge_rdes_ORDm [closure]: "merge_rdes j is ORDm"
  by (simp add: merge_rdes_def RD3c_ORDm ORDm_healthy)

lemma merge_rdes_healths [closure]:
  "merge_rdes j is R1m"
  "merge_rdes j is R2m"
  "merge_rdes j is R3cm"
  "merge_rdes j is RD1m"
  "merge_rdes j is RD2"
  using merge_rdes_ORDm ORDm_R1m ORDm_healthy_iff by blast+

subsubsection \<open> Monotonicity and Symmetry \<close>

lemma merge_rdes_mono:
  "j \<sqsubseteq> k \<Longrightarrow> merge_rdes j \<sqsubseteq> merge_rdes k"
proof -
  assume assms: "j \<sqsubseteq> k"
  show ?thesis
  unfolding merge_rdes_def RD3c_def
    apply (rule seqr_mono[OF ORDm_mono])
    using assms by (auto simp: pred_refine_iff merge_rdes_raw_def Let_def)
qed

lemma ORDm_merge_rdes_raw_SymMerge:
  "j is SymMerge \<Longrightarrow> ORDm (merge_rdes_raw j) is SymMerge"
proof -
  assume assms: "j is SymMerge"
  have swap: "merge_eval j x p q z = merge_eval j x q p z" for x p q z
    using assms unfolding SymMerge_eval by blast
  have "merge_rdes_raw j is SymMerge"
    by (simp add: SymMerge_eval merge_rdes_raw_def Let_def swap
        conj_commute disj_commute)
  then show ?thesis by (rule ORDm_SymMerge)
qed

lemma merge_rdes_SymMerge:
  "j is SymMerge \<Longrightarrow> merge_rdes j is SymMerge"
proof -
  assume assms: "j is SymMerge"
  show ?thesis
  using ORDm_merge_rdes_raw_SymMerge[OF assms]
    by (simp add: Healthy_def' seqr_assoc[THEN sym] merge_rdes_def RD3c_def)
qed

subsection \<open> Parallel with the Lifted Merge \<close>

abbreviation rdes_lift_par ::
  "('t::trace, 'a) rp_hrel \<Rightarrow> ('t \<times> 'a) merge \<Rightarrow>
    ('t, 'a) rp_hrel \<Rightarrow> ('t, 'a) rp_hrel"
  ("_ \<parallel>\<^sub>R\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q \<equiv>
  P \<parallel>\<^bsub>merge_rdes j\<^esub> Q"

lemma rdes_lift_parallel_RD [closure]:
  "\<lbrakk> P is RD; Q is RD \<rbrakk> \<Longrightarrow> (P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) is RD"
proof -
  assume assms: "P is RD" "Q is RD"
  show ?thesis
  by (rule RD_par_by_ORDm[OF assms merge_rdes_ORDm])
qed

lemma rdes_lift_parallel_comm:
  "j is SymMerge \<Longrightarrow> P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P"
proof -
  assume assms: "j is SymMerge"
  show ?thesis
  by (rule par_by_merge_comm[OF merge_rdes_SymMerge[OF assms]])
qed

subsubsection \<open> Associativity for Nondivergent Operands \<close>

text \<open>
  Completion can extend a divergent intermediate trace, breaking associativity.
  The premises keep branch results ok at active priors, where completion agrees
  with the uncompleted merge.
\<close>

lemma rdes_lift_parallel_assoc_nondiv:
  fixes j :: "('t::trace \<times> 'a) merge"
  assumes merge: "j is SymMerge" "AssocMerge j"
      and rd: "P is RD" "Q is RD" "R is RD"
      and nondiv: "P is NDRD" "Q is NDRD" "R is NDRD"
  shows "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R =
    P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  let ?M = "merge_rdes j" and ?N = "ORDm (merge_rdes_raw j)"
  let ?G = "\<lambda>x z. ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z"
  have ex_rp: "(\<exists>u. F u) = (\<exists>b w t e. F \<lparr>ok\<^sub>v = b, wait\<^sub>v = w, tr\<^sub>v = t, \<dots> = e\<rparr>)"
    for F :: "('t, 'a) rp \<Rightarrow> bool"
    by (metis rea_vars.surjective)
  have eval: "merge_eval (RD2 (merge_rdes_raw j)) x p q z =
      (((ok\<^sub>v p \<and> ok\<^sub>v q) \<longrightarrow> ok\<^sub>v z) \<and> wait\<^sub>v z = (wait\<^sub>v p \<or> wait\<^sub>v q) \<and>
      merge_eval j (tr\<^sub>v x, rea_vars.more x) (tr\<^sub>v p, rea_vars.more p)
        (tr\<^sub>v q, rea_vars.more q) (tr\<^sub>v z, rea_vars.more z))" for x p q z
    by (simp add: RD2_def H2_split merge_rdes_raw_def; pred_auto)
  have fold: "(\<exists>u. merge_eval (RD2 (merge_rdes_raw j)) x p q u \<and>
      merge_eval (RD2 (merge_rdes_raw j)) x u r z) =
    (((ok\<^sub>v p \<and> ok\<^sub>v q \<and> ok\<^sub>v r) \<longrightarrow> ok\<^sub>v z) \<and>
    wait\<^sub>v z = (wait\<^sub>v p \<or> wait\<^sub>v q \<or> wait\<^sub>v r) \<and>
    (\<exists>a. merge_eval j (tr\<^sub>v x, rea_vars.more x) (tr\<^sub>v p, rea_vars.more p)
        (tr\<^sub>v q, rea_vars.more q) a \<and>
      merge_eval j (tr\<^sub>v x, rea_vars.more x) a (tr\<^sub>v r, rea_vars.more r)
        (tr\<^sub>v z, rea_vars.more z)))" for x p q r z
    by (simp add: eval ex_rp ex_bool_eq; blast)
  have assoc: "AssocMerge (RD2 (merge_rdes_raw j))"
    using merge(2) unfolding AssocMerge_cyclic_eval by (simp only: fold; blast)
  have agree: "merge_eval ?M x p q z = merge_eval ?N x p q z"
    if "?G x p" "?G x q" for x p q z
    using that by (auto simp: merge_rdes_eval ORDm_merge_rdes_raw_eval)
  have closed: "?G x z"
    if "?G x p" "?G x q" "merge_eval ?M x p q z" for x p q z
    using that by (simp only: merge_rdes_eval; blast)
  have pre: "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "pre\<^sub>R R = true\<^sub>r"
    using rd nondiv by (simp_all add: NDRD_healthy_iff)
  have g: "P (x,z) \<Longrightarrow> ?G x z" "Q (x,z) \<Longrightarrow> ?G x z" "R (x,z) \<Longrightarrow> ?G x z" for x z
    using rd pre by (blast dest: preR_true_iff[OF RD_healths(1), THEN iffD1])+
  show ?thesis
  proof (rule par_by_merge_assoc_on[OF _ g])
    fix x p q r z :: "('t, 'a) rp"
    assume guard: "?G x p" "?G x q" "?G x r"
    have "(\<exists>u. merge_eval ?M x p q u \<and> merge_eval ?M x u r z) =
        (\<exists>u. merge_eval ?N x p q u \<and> merge_eval ?N x u r z)"
      using closed[OF guard(1,2)] agree[OF _ guard(3)]
      by (simp only: agree[OF guard(1,2), symmetric]; blast)
    also have "... = (\<exists>u. merge_eval ?N x q r u \<and> merge_eval ?N x p u z)"
      using par_by_merge_assoc_iff[where M="?N"] par_by_merge_assoc[OF
          ORDm_merge_rdes_raw_SymMerge[OF merge(1)] ORDm_AssocMerge_RD2[OF assoc]]
      by blast
    also have "... = (\<exists>u. merge_eval ?M x q r u \<and> merge_eval ?M x p u z)"
      using closed[OF guard(2,3)] agree[OF guard(1)]
      by (simp only: agree[OF guard(2,3), symmetric]; blast)
    finally show "(\<exists>u. merge_eval ?M x p q u \<and> merge_eval ?M x u r z) =
        (\<exists>u. merge_eval ?M x q r u \<and> merge_eval ?M x p u z)" .
  qed
qed

end
