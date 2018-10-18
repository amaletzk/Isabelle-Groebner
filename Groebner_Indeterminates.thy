(* Author: Alexander Maletzky *)

theory Groebner_Indeterminates
  imports MPoly_PM Groebner_Bases.Reduced_GB
begin

text \<open>We prove results that hold specifically for Gr\"obner bases in polynomial rings, where the
  polynomials really have @{emph \<open>indeterminates\<close>}.\<close>

definition varnum_wrt :: "'x set \<Rightarrow> ('x::countable \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> nat"
  where "varnum_wrt X t = (if keys t - X = {} then 0 else Suc (Max (elem_index ` (keys t - X))))"

lemma elem_index_less_varnum_wrt:
  assumes "x \<in> keys t"
  obtains "x \<in> X" | "elem_index x < varnum_wrt X t"
proof (cases "x \<in> X")
  case True
  thus ?thesis ..
next
  case False
  with assms have 1: "x \<in> keys t - X" by simp
  hence "keys t - X \<noteq> {}" by blast
  hence eq: "varnum_wrt X t = Suc (Max (elem_index ` (keys t - X)))" by (simp add: varnum_wrt_def)
  hence "elem_index x < varnum_wrt X t" using 1 by (simp add: less_Suc_eq_le)
  thus ?thesis ..
qed

lemma varnum_wrt_eq_zero_iff: "varnum_wrt X t = 0 \<longleftrightarrow> t \<in> .[X]"
  by (auto simp: varnum_wrt_def PPs_def)

lemma varnum_wrt_plus:
  "varnum_wrt X (s + t) = max (varnum_wrt X s) (varnum_wrt X (t::'x::countable \<Rightarrow>\<^sub>0 'b::ninv_comm_monoid_add))"
proof (simp add: varnum_wrt_def keys_plus_ninv_comm_monoid_add image_Un Un_Diff del: Diff_eq_empty_iff, intro impI)
  assume 1: "keys s - X \<noteq> {}" and 2: "keys t - X \<noteq> {}"
  have "finite (elem_index ` (keys s - X))" by simp
  moreover from 1 have "elem_index ` (keys s - X) \<noteq> {}" by simp
  moreover have "finite (elem_index ` (keys t - X))" by simp
  moreover from 2 have "elem_index ` (keys t - X) \<noteq> {}" by simp
  ultimately show "Max (elem_index ` (keys s - X) \<union> elem_index ` (keys t - X)) =
                    max (Max (elem_index ` (keys s - X))) (Max (elem_index ` (keys t - X)))"
    by (rule Max_Un)
qed

lemma dickson_grading_varnum_wrt:
  assumes "finite X"
  shows "dickson_grading ((varnum_wrt X)::('x::countable \<Rightarrow>\<^sub>0 'b::add_wellorder) \<Rightarrow> nat)"
  using varnum_wrt_plus
proof (rule dickson_gradingI)
  fix m::nat
  let ?V = "X \<union> {x. elem_index x < m}"
  have "{t::'x \<Rightarrow>\<^sub>0 'b. varnum_wrt X t \<le> m} \<subseteq> {t. sub_keys ?V t}"
  proof (rule, simp add: sub_keys_def, intro subsetI, simp)
    fix t::"'x \<Rightarrow>\<^sub>0 'b" and x::'x
    assume "varnum_wrt X t \<le> m"
    assume "x \<in> keys t"
    thus "x \<in> X \<or> elem_index x < m"
    proof (rule elem_index_less_varnum_wrt)
      assume "x \<in> X"
      thus ?thesis ..
    next
      assume "elem_index x < varnum_wrt X t"
      hence "elem_index x < m" using \<open>varnum_wrt X t \<le> m\<close> by (rule less_le_trans)
      thus ?thesis ..
    qed
  qed
  thus "almost_full_on (adds) {t::'x \<Rightarrow>\<^sub>0 'b. varnum_wrt X t \<le> m}"
  proof (rule almost_full_on_subset)
    from assms finite_nat_seg have "finite ?V" by (rule finite_UnI)
    thus "almost_full_on (adds) {t::'x \<Rightarrow>\<^sub>0 'b. sub_keys ?V t}" by (rule Dickson_poly_mapping)
  qed
qed

context pm_powerprod
begin

lemma dgrad_set_varnum_wrt: "dgrad_set (varnum_wrt X) 0 = .[X]"
  by (simp add: dgrad_set_def PPs_def varnum_wrt_eq_zero_iff)

lemma dgrad_p_set_varnum_wrt: "punit.dgrad_p_set (varnum_wrt X) 0 = P[X]"
  by (simp add: punit.dgrad_p_set_def dgrad_set_varnum_wrt Polys_def)

lemmas finite_reduced_GB_Polys =
  punit.finite_reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_reduced_GB_Polys =
  punit.reduced_GB_is_reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_GB_Polys =
  punit.reduced_GB_is_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_auto_reduced_Polys =
  punit.reduced_GB_is_auto_reduced_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_monic_set_Polys =
  punit.reduced_GB_is_monic_set_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_nonzero_Polys =
  punit.reduced_GB_nonzero_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_pmdl_Polys =
  punit.reduced_GB_pmdl_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_unique_Polys =
  punit.reduced_GB_unique_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_Polys =
  punit.reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas ideal_eq_UNIV_iff_reduced_GB_eq_one_Polys =
  ideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]

end (* pm_powerprod *)

end (* theory *)
