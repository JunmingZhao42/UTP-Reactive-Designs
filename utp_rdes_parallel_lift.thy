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
  by (rule RD_par_by_merge[OF assms merge_rdes_ORDm])
qed

lemma rdes_lift_parallel_NDRD [closure]:
  assumes rd: "P is RD" "Q is RD"
      and nondiv: "P is NDRD" "Q is NDRD"
  shows "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) is NDRD"
proof -
  have rd_par: "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) is RD"
    by (rule rdes_lift_parallel_RD[OF rd])
  have pre: "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
    using rd nondiv by (simp_all add: NDRD_healthy_iff)
  have branch: "P (x,z) \<Longrightarrow> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z"
    "Q (x,z) \<Longrightarrow> ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z" for x z
    using rd pre by (blast dest: preR_true_iff[OF RD_healths(1), THEN iffD1])+
  have "\<forall>x z. (P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) (x,z) \<and>
      ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z"
    using branch by (auto simp only: par_by_merge_eval merge_rdes_eval)
  then show ?thesis
    by (simp only: NDRD_healthy_iff[OF rd_par]
        preR_true_iff[OF RD_healths(1)[OF rd_par]])
qed

lemma rdes_lift_parallel_comm:
  "j is SymMerge \<Longrightarrow> P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P"
proof -
  assume assms: "j is SymMerge"
  show ?thesis
  by (rule par_by_merge_comm[OF merge_rdes_SymMerge[OF assms]])
qed

subsubsection \<open> Zero Laws \<close>

(* We let Miracle absorb any reactive design: Miracle has no active
   observation, and RD fixes the inactive ones:
     P \<parallel>RD[j] \<top>RD = \<top>RD *)
lemma rdes_lift_parallel_miracle:
  fixes P :: "('t::trace, 'a) rp_hrel"
  assumes "P is RD"
  shows "P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>R\<^sub>D = \<^bold>\<top>\<^sub>R\<^sub>D" "\<^bold>\<top>\<^sub>R\<^sub>D \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>R\<^sub>D"
  by (rule RD_eq_active, simp_all add: assms closure par_by_merge_eval top_RD_eval)+

(* Chaos diverges at once, but the output must still extend the merged trace.
   So we need P to have an observation at the prior trace, and j to merge empty
   traces into an empty trace:
     (P \<and> tr' = tr) is H4 \<Longrightarrow> P \<parallel>RD[j] \<bottom>RD = \<bottom>RD *)
lemma rdes_lift_parallel_chaos:
  fixes P :: "('t::trace, 'a) rp_hrel" and j :: "('t \<times> 'a) merge"
  assumes rd: "P is RD"
      and stop: "(P \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) is H4"
      and empty: "\<And>s sL sR. \<exists>s'. merge_eval j (0, s) (0, sL) (0, sR) (0, s')"
  shows "P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> \<^bold>\<bottom>\<^sub>R\<^sub>D = \<^bold>\<bottom>\<^sub>R\<^sub>D" "\<^bold>\<bottom>\<^sub>R\<^sub>D \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<bottom>\<^sub>R\<^sub>D"
proof -
  have upper: "\<^bold>\<bottom>\<^sub>R\<^sub>D (x, z)" if "(X \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Y) (x, z)" for X Y :: "('t, 'a) rp_hrel" and x z
    using that by (auto simp: par_by_merge_eval merge_rdes_eval bottom_RD_eval)
  (* at an active prior, P stops at the prior trace and Chaos diverges there *)
  have lower: "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> \<^bold>\<bottom>\<^sub>R\<^sub>D) (x, z) \<and> (\<^bold>\<bottom>\<^sub>R\<^sub>D \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P) (x, z)"
    if "ok\<^sub>v x" "\<not> wait\<^sub>v x" "\<^bold>\<bottom>\<^sub>R\<^sub>D (x, z)" for x z
  proof -
    obtain p where p: "P (x, p)" "tr\<^sub>v p = tr\<^sub>v x"
      using fun_cong[OF is_H4_alt_def[THEN iffD1, OF stop], of "(x, x)"]
      by (simp add: seq_def true_pred_def; pred_simp; blast)
    obtain e e' where
      e: "merge_eval j (0, rea_vars.more x) (0, rea_vars.more p) (0, rea_vars.more x) (0, e)" and
      e': "merge_eval j (0, rea_vars.more x) (0, rea_vars.more x) (0, rea_vars.more p) (0, e')"
      using empty by blast
    let ?q = "des_vars.ok\<^sub>v_update (\<lambda>_. False) x"
    have "(\<^bold>\<bottom>\<^sub>R\<^sub>D :: ('t, 'a) rp_hrel) (x, ?q)"
      using that by (simp add: bottom_RD_eval)
    moreover have "merge_eval (merge_rdes j) x p ?q z"
      using that p e by (simp add: merge_rdes_eval bottom_RD_eval; blast intro: least_zero)
    moreover have "merge_eval (merge_rdes j) x ?q p z"
      using that p e' by (simp add: merge_rdes_eval bottom_RD_eval; blast intro: least_zero)
    ultimately show ?thesis
      using p(1) unfolding par_by_merge_eval by blast
  qed
  show "P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> \<^bold>\<bottom>\<^sub>R\<^sub>D = \<^bold>\<bottom>\<^sub>R\<^sub>D" "\<^bold>\<bottom>\<^sub>R\<^sub>D \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<bottom>\<^sub>R\<^sub>D"
    by (rule RD_eq_active, simp add: closure rd, rule bottom_RD_is_RD,
        rule iffI, erule upper, use lower in blast)+
qed

subsubsection \<open> Associativity for Nondivergent Operands \<close>

lemma ORDm_merge_rdes_raw_AssocMerge:
  fixes j :: "('t::trace \<times> 'a) merge"
  assumes "AssocMerge j"
  shows "AssocMerge (ORDm (merge_rdes_raw j))"
proof -
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
  have "AssocMerge (RD2 (merge_rdes_raw j))"
    using assms unfolding AssocMerge_iff by (simp only: fold; blast)
  then show ?thesis
    by (rule ORDm_AssocMerge_RD2)
qed

lemma merge_rdes_NDRDm [closure]: "merge_rdes j is NDRDm"
  by (simp add: NDRDm_healthy_iff merge_rdes_eval; blast)

text \<open>
  Completion can extend a divergent intermediate trace, so @{term "merge_rdes j"}
  is not associative in general. On branches that do not diverge from a started,
  non-waiting prior, it agrees with the uncompleted merge.
\<close>

lemma merge_rdes_guard_AssocMerge:
  fixes j :: "('t::trace \<times> 'a) merge"
  assumes "AssocMerge j"
  shows "AssocMerge (merge_guard (\<lambda>x z. ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z) (merge_rdes j))"
proof -
  let ?G = "\<lambda>x z :: ('t, 'a) rp. ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z"
  have eq: "merge_guard ?G (merge_rdes j) = merge_guard ?G (ORDm (merge_rdes_raw j))"
    by (rule merge_guard_cong; auto simp: merge_rdes_eval ORDm_merge_rdes_raw_eval)
  have "AssocMerge (merge_guard ?G (ORDm (merge_rdes_raw j)))"
    by (rule AssocMerge_merge_guard[OF ORDm_merge_rdes_raw_AssocMerge[OF assms]];
        auto simp: ORDm_merge_rdes_raw_eval)
  then show ?thesis
    by (simp only: eq)
qed

lemma rdes_lift_parallel_assoc_nd:
  fixes j :: "('t::trace \<times> 'a) merge"
  assumes merge: "j is SymMerge" "AssocMerge j"
      and rd: "P is RD" "Q is RD" "R is RD"
      and nondiv: "P is NDRD" "Q is NDRD" "R is NDRD"
  shows "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R =
    P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R)"
  by (rule par_by_merge_assoc_NDRD[OF rd nondiv merge_rdes_SymMerge[OF merge(1)]
        merge_rdes_NDRDm merge_rdes_guard_AssocMerge[OF merge(2)]])

subsubsection \<open> Associativity for Normal Operands \<close>

(* A divergent intermediate result may end with any extension u of its merged
   trace. For the other bracketing to produce u, we need a divergent input to
   reach it, so we ask j to absorb extensions: with p \<otimes> q the merged results
   and \<up> adding trace extensions with any state,
     \<up>(p \<otimes> q) \<subseteq> \<up>p \<otimes> q *)
lemma rdes_lift_parallel_assoc_nrd:
  fixes P Q R :: "('t::trace, 'a) rp_hrel" and j :: "('t \<times> 'a) merge"
  assumes nrd: "P is NRD" "Q is NRD" "R is NRD"
      and sym: "j is SymMerge" and assoc: "AssocMerge j"
      and absorb: "\<And>x p q. {u. \<exists>z. merge_eval j x p q z \<and> fst z \<le> fst u} \<subseteq>
        {u. \<exists>p'. fst p \<le> fst p' \<and> merge_eval j x p' q u}"
  shows "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have swap: "merge_eval j x p q z \<longleftrightarrow> merge_eval j x q p z" for x p q z
    using sym unfolding SymMerge_eval by blast
  have rotate: "\<exists>v. merge_eval j x q r v \<and> merge_eval j x p v z"
    if "merge_eval j x p q u" "merge_eval j x u r z" for x p q r u z
    using that assoc[unfolded AssocMerge_iff] swap by blast
  have absorb': "\<exists>p'. fst p \<le> fst p' \<and> merge_eval j x p' q u"
    if "merge_eval j x p q z" "fst z \<le> fst u" for x p q z u
    using absorb[of x p q] that by blast
  (* A divergent observation of a normal process extends to absorb u. *)
  have extend: "\<exists>p'. X (x, p') \<and> \<not> ok\<^sub>v p' \<and> merge_eval j (0, rea_vars.more x)
      (tr\<^sub>v p' - tr\<^sub>v x, rea_vars.more p') b (tr\<^sub>v u - tr\<^sub>v x, rea_vars.more u)"
    if nrdX: "X is NRD" and px: "X (x, p)" and dp: "\<not> ok\<^sub>v p"
      and pw: "merge_eval j (0, rea_vars.more x) (tr\<^sub>v p - tr\<^sub>v x, rea_vars.more p) b w"
      and wu: "fst w \<le> tr\<^sub>v u - tr\<^sub>v x"
    for X :: "('t, 'a) rp_hrel" and x p b w u
  proof -
    obtain p0 where p0: "tr\<^sub>v p - tr\<^sub>v x \<le> fst p0"
      "merge_eval j (0, rea_vars.more x) p0 b (tr\<^sub>v u - tr\<^sub>v x, rea_vars.more u)"
      using absorb'[OF pw, of "(tr\<^sub>v u - tr\<^sub>v x, rea_vars.more u)"] wu by auto
    let ?p' = "\<lparr>ok\<^sub>v = False, wait\<^sub>v = False, tr\<^sub>v = tr\<^sub>v x + fst p0, \<dots> = snd p0\<rparr>
      :: ('t, 'a) rp"
    have "tr\<^sub>v x \<le> tr\<^sub>v p"
      using px fun_cong[OF Healthy_if[OF RD_healths(1)[OF NRD_is_RD[OF nrdX]]], of "(x, p)"]
      by (simp add: R1_def; pred_auto)
    then have le: "tr\<^sub>v p \<le> tr\<^sub>v ?p'"
      using add_left_mono[OF p0(1), of "tr\<^sub>v x"] by (simp add: diff_add_cancel_left')
    have rd3c: "X is RD3c"
      using nrdX by (metis Healthy_def NRD_def RD1_RD3c_commute RD3c_idem comp_apply)
    have "X (x, ?p')"
      using px dp le fun_cong[OF Healthy_if[OF rd3c], of "(x, ?p')"]
      by (cases p; simp add: RD3c_def skip_rea_def; pred_simp; metis)
    show ?thesis
      by (rule exI[of _ ?p']) (use \<open>X (x, ?p')\<close> p0(2) in simp)
  qed
  have incl: "(P' \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (Q' \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R')) (x, z)"
    if ops: "P' is NRD" "Q' is NRD" "R' is NRD"
      and lhs: "((P' \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q') \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R') (x, z)"
    for P' Q' R' :: "('t, 'a) rp_hrel" and x z
  proof -
    obtain p q r u where p: "P' (x, p)" and q: "Q' (x, q)" and r: "R' (x, r)"
      and mpq: "merge_eval (merge_rdes j) x p q u" and mur: "merge_eval (merge_rdes j) x u r z"
      using lhs unfolding par_by_merge_eval by blast
    show ?thesis
    proof (cases "ok\<^sub>v x \<and> \<not> wait\<^sub>v x")
      case False
      then show ?thesis
        using p q r mur unfolding par_by_merge_eval by (auto simp: merge_rdes_eval)
    next
      case started: True
      let ?x0 = "(0, rea_vars.more x)"
      let ?r = "\<lambda>y :: ('t, 'a) rp. (tr\<^sub>v y - tr\<^sub>v x, rea_vars.more y)"
      have M: "merge_eval (merge_rdes j) x p q z \<longleftrightarrow> tr\<^sub>v x \<le> tr\<^sub>v z \<and>
          ((ok\<^sub>v p \<and> ok\<^sub>v q \<and> ok\<^sub>v z \<and> wait\<^sub>v z = (wait\<^sub>v p \<or> wait\<^sub>v q) \<and>
              merge_eval j ?x0 (?r p) (?r q) (?r z)) \<or>
            (\<not> (ok\<^sub>v p \<and> ok\<^sub>v q) \<and>
              (\<exists>y. merge_eval j ?x0 (?r p) (?r q) y \<and> fst y \<le> tr\<^sub>v z - tr\<^sub>v x)))" for p q z
        using started by (simp add: merge_rdes_eval; blast)
      have wit: "\<exists>y. merge_eval j ?x0 (?r p) (?r q) y \<and> fst y \<le> tr\<^sub>v z - tr\<^sub>v x"
        if "merge_eval (merge_rdes j) x p q z" for p q z
        using that by (auto simp: M)
      have z: "tr\<^sub>v x \<le> tr\<^sub>v z"
        using mur by (simp add: M)
      show ?thesis
      proof (cases "ok\<^sub>v p \<and> ok\<^sub>v q \<and> ok\<^sub>v r")
        case True
        then have "merge_eval j ?x0 (?r p) (?r q) (?r u)" "merge_eval j ?x0 (?r u) (?r r) (?r z)"
          "ok\<^sub>v u" "ok\<^sub>v z" "wait\<^sub>v z = (wait\<^sub>v p \<or> wait\<^sub>v q \<or> wait\<^sub>v r)"
          using mpq mur by (auto simp: M)
        then obtain v0 where v0: "merge_eval j ?x0 (?r q) (?r r) v0" "merge_eval j ?x0 (?r p) v0 (?r z)"
          using rotate by blast
        let ?v = "\<lparr>ok\<^sub>v = True, wait\<^sub>v = (wait\<^sub>v q \<or> wait\<^sub>v r), tr\<^sub>v = tr\<^sub>v x + fst v0,
          \<dots> = snd v0\<rparr> :: ('t, 'a) rp"
        have "merge_eval (merge_rdes j) x q r ?v" "merge_eval (merge_rdes j) x p ?v z"
          using True v0 z \<open>ok\<^sub>v z\<close> \<open>wait\<^sub>v z = _\<close> by (simp_all add: M)
        then show ?thesis
          using p q r unfolding par_by_merge_eval by blast
      next
        case False
        (* Some branch diverges: we move u into a divergent input. *)
        obtain p1 q1 where p1: "P' (x, p1)" and q1: "Q' (x, q1)"
          and div: "\<not> (ok\<^sub>v p1 \<and> ok\<^sub>v q1 \<and> ok\<^sub>v r)"
          and u: "merge_eval j ?x0 (?r p1) (?r q1) (?r u)"
        proof (cases "ok\<^sub>v p \<and> ok\<^sub>v q")
          case True
          then show ?thesis
            using that[of p q] p q False mpq by (auto simp: M)
        next
          case False
          obtain w where w: "merge_eval j ?x0 (?r p) (?r q) w" "fst w \<le> tr\<^sub>v u - tr\<^sub>v x"
            using wit[OF mpq] by blast
          show ?thesis
          proof (cases "ok\<^sub>v p")
            case False
            then obtain p1 where "P' (x, p1)" "\<not> ok\<^sub>v p1" "merge_eval j ?x0 (?r p1) (?r q) (?r u)"
              using extend[OF ops(1) p _ w] by blast
            then show ?thesis
              using that[of p1 q] q by blast
          next
            case True
            then have "\<not> ok\<^sub>v q"
              using \<open>\<not> (ok\<^sub>v p \<and> ok\<^sub>v q)\<close> by blast
            moreover have "merge_eval j ?x0 (?r q) (?r p) w"
              using w(1) swap by blast
            ultimately obtain q1 where "Q' (x, q1)" "\<not> ok\<^sub>v q1" "merge_eval j ?x0 (?r p) (?r q1) (?r u)"
              using extend[OF ops(2) q _ _ w(2)] swap by blast
            then show ?thesis
              using that[of p q1] p by blast
          qed
        qed
        obtain w where w: "merge_eval j ?x0 (?r u) (?r r) w" "fst w \<le> tr\<^sub>v z - tr\<^sub>v x"
          using wit[OF mur] by blast
        obtain v0 where v0: "merge_eval j ?x0 (?r q1) (?r r) v0" "merge_eval j ?x0 (?r p1) v0 w"
          using rotate[OF u w(1)] by blast
        let ?v = "\<lparr>ok\<^sub>v = (ok\<^sub>v q1 \<and> ok\<^sub>v r), wait\<^sub>v = (wait\<^sub>v q1 \<or> wait\<^sub>v r),
          tr\<^sub>v = tr\<^sub>v x + fst v0, \<dots> = snd v0\<rparr> :: ('t, 'a) rp"
        have "merge_eval (merge_rdes j) x q1 r ?v"
          using v0(1) by (cases v0; cases "ok\<^sub>v q1 \<and> ok\<^sub>v r"; simp add: M; blast)
        moreover have "merge_eval (merge_rdes j) x p1 ?v z"
          using div z v0(2) w by (cases v0; cases w; simp add: M; blast)
        ultimately show ?thesis
          using p1 q1 r unfolding par_by_merge_eval by blast
      qed
    qed
  qed
  have comm: "X \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Y = Y \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> X" for X Y :: "('t, 'a) rp_hrel"
    by (rule rdes_lift_parallel_comm[OF sym])
  show ?thesis
  proof (rule ext, clarify, rule iffI)
    fix x z
    assume "((P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R) (x, z)"
    then show "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R)) (x, z)"
      by (rule incl[OF nrd])
  next
    fix x z
    assume "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R)) (x, z)"
    then have "((R \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P) (x, z)"
      by (simp only: comm[of P] comm[of Q])
    then have "(R \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> P)) (x, z)"
      by (rule incl[OF nrd(3) nrd(2) nrd(1)])
    then show "((P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> R) (x, z)"
      by (simp only: comm[of R] comm[of Q])
  qed
qed

end
