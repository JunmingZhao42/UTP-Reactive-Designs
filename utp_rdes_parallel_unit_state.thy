section \<open> Ordinary RD parallel as upstream RD parallel at unit state \<close>

theory utp_rdes_parallel_unit_state
  imports utp_rdes_parallel_lift utp_srdes_parallel_laws
begin

text \<open> We show that @{const merge_rdes} agrees with the upstream stateful
  completion @{term "M\<^sub>R"} at the unit program state @{term "()"}. \<close>

subsection \<open> Unit-State Input Merge \<close>

(* Apply j to trace contributions and extensions at st = (). *)
definition unit_state_rd_merge ::
  "('t::trace \<times> 'a) merge \<Rightarrow> (unit, 't, 'a) rsp merge" where
  [pred]: "unit_state_rd_merge j \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; p = mrg_left\<^sub>v m; q = mrg_right\<^sub>v m
    in tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      merge_eval j (0, srea_vars.more x)
        (tr\<^sub>v p - tr\<^sub>v x, srea_vars.more p)
        (tr\<^sub>v q - tr\<^sub>v x, srea_vars.more q)
        (tr\<^sub>v z - tr\<^sub>v x, srea_vars.more z))"

lemma unit_state_rd_merge_eval:
  "merge_eval (unit_state_rd_merge j) x p q z =
    (tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      merge_eval j (0, srea_vars.more x)
        (tr\<^sub>v p - tr\<^sub>v x, srea_vars.more p)
        (tr\<^sub>v q - tr\<^sub>v x, srea_vars.more q)
        (tr\<^sub>v z - tr\<^sub>v x, srea_vars.more z))"
  by (simp add: unit_state_rd_merge_def Let_def)

lemma unit_state_rd_merge_unrest [unrest]:
  "$0:ok\<^sup>< \<sharp> unit_state_rd_merge j"
  "$1:ok\<^sup>< \<sharp> unit_state_rd_merge j"
  "$<:ok\<^sup>< \<sharp> unit_state_rd_merge j"
  "$ok\<^sup>> \<sharp> unit_state_rd_merge j"
  "$0:wait\<^sup>< \<sharp> unit_state_rd_merge j"
  "$1:wait\<^sup>< \<sharp> unit_state_rd_merge j"
  "$<:wait\<^sup>< \<sharp> unit_state_rd_merge j"
  "$wait\<^sup>> \<sharp> unit_state_rd_merge j"
  by (pred_auto)+

lemma unit_state_rd_merge_R2m [closure]:
  "unit_state_rd_merge j is R2m"
  by (rule Healthy_intro; pred_auto)

lemma unit_state_rd_merge_RDM [closure]:
  "unit_state_rd_merge j is RDM"
  by (rule RDM_intro; simp add: unit_state_rd_merge_R2m unrest)

subsection \<open> Unit-State Correspondence \<close>

text \<open> We add the unit program state @{term "()"}. The maps preserve
  @{term ok}, @{term wait}, the trace and the extension observation. \<close>

(* Add st = () and preserve all ordinary reactive observations. *)
definition to_unit_state :: "('t::trace, 'a) rp \<Rightarrow> (unit, 't, 'a) rsp" where
  "to_unit_state x \<equiv>
    \<lparr>ok\<^sub>v = ok\<^sub>v x, wait\<^sub>v = wait\<^sub>v x,
      tr\<^sub>v = tr\<^sub>v x, st\<^sub>v = (),
      \<dots> = rea_vars.more x\<rparr>"

(* Remove the unit program state. *)
definition from_unit_state :: "(unit, 't::trace, 'a) rsp \<Rightarrow> ('t, 'a) rp" where
  "from_unit_state x \<equiv>
    \<lparr>ok\<^sub>v = ok\<^sub>v x, wait\<^sub>v = wait\<^sub>v x,
      tr\<^sub>v = tr\<^sub>v x, \<dots> = srea_vars.more x\<rparr>"

lemma from_to_unit_state [simp]:
  "from_unit_state (to_unit_state x) = x"
  by (cases x rule: rea_vars.cases_scheme;
      simp add: to_unit_state_def from_unit_state_def)

lemma to_from_unit_state [simp]:
  "to_unit_state (from_unit_state x) = x"
  by (cases x rule: srea_vars.cases_scheme;
      simp add: to_unit_state_def from_unit_state_def)

lemma unit_state_trace_witness:
  fixes x z :: "('t::trace, 'a) rp"
    and F :: "('t \<times> 'a) \<Rightarrow> bool"
  shows "(tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      (\<exists>t e. t \<le> tr\<^sub>v z - tr\<^sub>v x \<and> F (t,e))) =
    (\<exists>u :: (unit, 't, 'a) rsp.
      tr\<^sub>v x \<le> tr\<^sub>v u \<and> F (tr\<^sub>v u - tr\<^sub>v x, srea_vars.more u) \<and>
      tr\<^sub>v u \<le> tr\<^sub>v z)"
proof
  assume "tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      (\<exists>t e. t \<le> tr\<^sub>v z - tr\<^sub>v x \<and> F (t,e))"
  then obtain t e where hz: "tr\<^sub>v x \<le> tr\<^sub>v z"
    and ht: "t \<le> tr\<^sub>v z - tr\<^sub>v x" and f: "F (t,e)"
    by blast
  show "\<exists>u :: (unit, 't, 'a) rsp.
      tr\<^sub>v x \<le> tr\<^sub>v u \<and> F (tr\<^sub>v u - tr\<^sub>v x, srea_vars.more u) \<and>
      tr\<^sub>v u \<le> tr\<^sub>v z"
    using hz ht f add_left_mono[OF ht, of "tr\<^sub>v x"]
    by (intro exI[where x="\<lparr>ok\<^sub>v=False, wait\<^sub>v=False,
          tr\<^sub>v=tr\<^sub>v x + t, st\<^sub>v=(), \<dots>=e\<rparr>"])
      (simp add: diff_add_cancel_left')
next
  assume "\<exists>u :: (unit, 't, 'a) rsp.
      tr\<^sub>v x \<le> tr\<^sub>v u \<and> F (tr\<^sub>v u - tr\<^sub>v x, srea_vars.more u) \<and>
      tr\<^sub>v u \<le> tr\<^sub>v z"
  then show "tr\<^sub>v x \<le> tr\<^sub>v z \<and>
      (\<exists>t e. t \<le> tr\<^sub>v z - tr\<^sub>v x \<and> F (t,e))"
    using minus_cancel_le[of "tr\<^sub>v x" _ "tr\<^sub>v z"]
      order_trans[of "tr\<^sub>v x" _ "tr\<^sub>v z"]
    by blast
qed

lemma rp_eq_iff:
  fixes x z :: "('t::trace, 'a) rp"
  shows "(x = z) =
    (ok\<^sub>v x = ok\<^sub>v z \<and> wait\<^sub>v x = wait\<^sub>v z \<and>
     tr\<^sub>v x = tr\<^sub>v z \<and> rea_vars.more x = rea_vars.more z)"
  by (cases x rule: rea_vars.cases_scheme;
      cases z rule: rea_vars.cases_scheme; simp)

lemma merge_rdes_unit_state:
  fixes j :: "('t::trace \<times> 'a) merge"
    and x p q z :: "('t, 'a) rp"
  shows "merge_eval (merge_rdes j) x p q z \<longleftrightarrow>
    merge_eval (M\<^sub>R(unit_state_rd_merge j))
      (to_unit_state x) (to_unit_state p) (to_unit_state q) (to_unit_state z)"
proof -
  let ?J = "\<lambda>v. merge_eval j (0, rea_vars.more x)
    (tr\<^sub>v p - tr\<^sub>v x, rea_vars.more p)
    (tr\<^sub>v q - tr\<^sub>v x, rea_vars.more q) v"
  show ?thesis
    by (simp add: merge_rdes_eval
        merge_rd_eval[OF unit_state_rd_merge_RDM] unit_state_rd_merge_eval
        to_unit_state_def rp_eq_iff;
        subst unit_state_trace_witness[of x z ?J, symmetric]; blast)
qed

(* Transport a relation through the bijection on observations. *)
definition unit_state_relation ::
  "('t::trace, 'a) rp_hrel \<Rightarrow> (unit, 't, 'a) rsp_hrel" where
  "unit_state_relation P \<equiv> (\<lambda>(x,z).
    P (from_unit_state x, from_unit_state z))"

lemma rdes_lift_parallel_unit_state:
  fixes P Q :: "('t::trace, 'a) rp_hrel"
    and j :: "('t \<times> 'a) merge"
    and x z :: "('t, 'a) rp"
  shows "(P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) (x,z) \<longleftrightarrow>
    (unit_state_relation P \<parallel>\<^sub>R\<^bsub>unit_state_rd_merge j\<^esub>
      unit_state_relation Q) (to_unit_state x, to_unit_state z)"
  apply (auto simp: par_by_merge_eval unit_state_relation_def
      merge_rdes_unit_state)
   apply (metis from_to_unit_state)
  by (metis to_from_unit_state)

lemma rdes_lift_parallel_unit_state_eq:
  fixes P Q :: "('t::trace, 'a) rp_hrel"
    and j :: "('t \<times> 'a) merge"
  shows "unit_state_relation (P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) =
    unit_state_relation P \<parallel>\<^sub>R\<^bsub>unit_state_rd_merge j\<^esub>
      unit_state_relation Q"
proof (rule ext)
  fix a :: "(unit, 't, 'a) rsp \<times> (unit, 't, 'a) rsp"
  show "unit_state_relation (P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q) a =
    (unit_state_relation P \<parallel>\<^sub>R\<^bsub>unit_state_rd_merge j\<^esub>
      unit_state_relation Q) a"
    using rdes_lift_parallel_unit_state[where P=P and Q=Q and j=j
      and x="from_unit_state (fst a)" and z="from_unit_state (snd a)"]
    by (cases a; simp add: unit_state_relation_def)
qed

end
