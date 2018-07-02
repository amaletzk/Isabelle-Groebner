(* Author: Alexander Maletzky *)

section \<open>Signature-Based Algorithms for Computing Gr\"obner Bases\<close>

theory Signature_Based
  imports Syzygy Quasi_PM_Power_Products
begin

(* TODO: Add references. *)

text \<open>This formalization closely follows Sections 4 to 7 of the excellent survey article @{cite Eder2015}.\<close>

subsection \<open>Preliminaries\<close>

lemma (in comm_powerprod) minus_plus': "s adds t \<Longrightarrow> u + (t - s) = (u + t) - s"
  using add_commute minus_plus by auto

context ulcs_powerprod
begin

lemma lcs_alt_2:
  assumes "a + x = b + y"
  shows "lcs x y = (b + y) - gcs a b"
proof -
  have "a + (lcs x y + gcs a b) = lcs (a + x) (a + y) + gcs a b" by (simp only: lcs_plus_left ac_simps)
  also have "... = lcs (b + y) (a + y) + gcs a b" by (simp only: assms)
  also have "... = (lcs a b + y) + gcs a b" by (simp only: lcs_plus_right lcs_comm)
  also have "... = (gcs a b + lcs a b) + y" by (simp only: ac_simps)
  also have "... = a + (b + y)" by (simp only: gcs_plus_lcs, simp add: ac_simps)
  finally have "(lcs x y + gcs a b) - gcs a b = (b + y) - gcs a b" by simp
  thus ?thesis by simp
qed

corollary lcs_alt_1:
  assumes "a + x = b + y"
  shows "lcs x y = (a + x) - gcs a b"
proof -
  have "lcs x y = lcs y x" by (simp only: lcs_comm)
  also from assms[symmetric] have "... = (a + x) - gcs b a" by (rule lcs_alt_2)
  also have "... = (a + x) - gcs a b" by (simp only: gcs_comm)
  finally show ?thesis .
qed

corollary lcs_minus_1:
  assumes "a + x = b + y"
  shows "lcs x y - x = a - gcs a b"
  by (simp add: lcs_alt_1[OF assms] diff_right_commute)

corollary lcs_minus_2:
  assumes "a + x = b + y"
  shows "lcs x y - y = b - gcs a b"
  by (simp add: lcs_alt_2[OF assms] diff_right_commute)

end (* ulcs_powerprod *)

context ord
begin

definition is_le_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_le_rel rel = (rel = (=) \<or> rel = (\<le>) \<or> rel = (<))"

lemma is_le_relI [simp]: "is_le_rel (=)" "is_le_rel (\<le>)" "is_le_rel (<)"
  by (simp_all add: is_le_rel_def)

lemma is_le_relE:
  assumes "is_le_rel rel"
  obtains "rel = (=)" | "rel = (\<le>)" | "rel = (<)"
  using assms unfolding is_le_rel_def by blast

end (* ord *)

context preorder
begin

lemma is_le_rel_le:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> x \<le> y"
  using assms by (rule is_le_relE, auto dest: less_imp_le)

lemma is_le_rel_trans:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> rel y z \<Longrightarrow> rel x z"
  using assms by (rule is_le_relE, auto dest: order_trans less_trans)

lemma is_le_rel_trans_le_left:
  assumes "is_le_rel rel"
  shows "x \<le> y \<Longrightarrow> rel y z \<Longrightarrow> x \<le> z"
  using assms by (rule is_le_relE, auto dest: order_trans le_less_trans less_imp_le)

lemma is_le_rel_trans_le_right:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  using assms by (rule is_le_relE, auto dest: order_trans less_le_trans less_imp_le)

lemma is_le_rel_trans_less_left:
  assumes "is_le_rel rel"
  shows "x < y \<Longrightarrow> rel y z \<Longrightarrow> x < z"
  using assms by (rule is_le_relE, auto dest: less_le_trans less_imp_le)

lemma is_le_rel_trans_less_right:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  using assms by (rule is_le_relE, auto dest: le_less_trans less_imp_le)

end (* preorder *)

context order
begin

lemma is_le_rel_distinct:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x < y"
  using assms by (rule is_le_relE, auto)

lemma is_le_rel_antisym:
  assumes "is_le_rel rel"
  shows "rel x y \<Longrightarrow> rel y x \<Longrightarrow> x = y"
  using assms by (rule is_le_relE, auto)

end (* order *)

lemma poly_mapping_rangeE:
  assumes "c \<in> Poly_Mapping.range p"
  obtains k where "k \<in> keys p" and "c = lookup p k"
  using assms by (transfer, auto)

lemma poly_mapping_range_nonzero: "0 \<notin> Poly_Mapping.range p"
  by (transfer, auto)

context term_powerprod
begin

lemma Keys_range_vectorize_poly: "Keys (Poly_Mapping.range (vectorize_poly p)) = pp_of_term ` keys p"
proof
  show "Keys (Poly_Mapping.range (vectorize_poly p)) \<subseteq> pp_of_term ` keys p"
  proof
    fix t
    assume "t \<in> Keys (Poly_Mapping.range (vectorize_poly p))"
    then obtain q where "q \<in> Poly_Mapping.range (vectorize_poly p)" and "t \<in> keys q" by (rule in_KeysE)
    from this(1) obtain k where q: "q = lookup (vectorize_poly p) k" by (metis DiffE imageE range.rep_eq)
    with \<open>t \<in> keys q\<close> have "term_of_pair (t, k) \<in> keys p"
      by (metis in_keys_iff lookup_proj_poly lookup_vectorize_poly)
    hence "pp_of_term (term_of_pair (t, k)) \<in> pp_of_term ` keys p" by (rule imageI)
    thus "t \<in> pp_of_term ` keys p" by (simp only: pp_of_term_of_pair)
  qed
next
  show "pp_of_term ` keys p \<subseteq> Keys (Poly_Mapping.range (vectorize_poly p))"
  proof
    fix t
    assume "t \<in> pp_of_term ` keys p"
    then obtain x where "x \<in> keys p" and "t = pp_of_term x" ..
    from this(2) have "term_of_pair (t, component_of_term x) = x" by (simp add: term_of_pair_pair)
    with \<open>x \<in> keys p\<close> have "lookup p (term_of_pair (t, component_of_term x)) \<noteq> 0" by simp
    hence "lookup (proj_poly (component_of_term x) p) t \<noteq> 0" by (simp add: lookup_proj_poly)
    hence t: "t \<in> keys (proj_poly (component_of_term x) p)" by simp
    from \<open>x \<in> keys p\<close> have "component_of_term x \<in> keys (vectorize_poly p)"
      by (simp add: keys_vectorize_poly)
    from t show "t \<in> Keys (Poly_Mapping.range (vectorize_poly p))"
    proof (rule in_KeysI)
      have "proj_poly (component_of_term x) p = lookup (vectorize_poly p) (component_of_term x)"
        by (simp only: lookup_vectorize_poly)
      also from \<open>component_of_term x \<in> keys (vectorize_poly p)\<close>
      have "... \<in> Poly_Mapping.range (vectorize_poly p)" by (rule in_keys_lookup_in_range)
      finally show "proj_poly (component_of_term x) p \<in> Poly_Mapping.range (vectorize_poly p)" .
    qed
  qed
qed

end (* term_powerprod *)

context ordered_term
begin

lemma lt_monom_mult_zero:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "lt (monom_mult c 0 p) = lt p"
proof (cases "p = 0")
  case True
  show ?thesis by (simp add: True)
next
  case False
  with assms show ?thesis by (simp add: lt_monom_mult term_simps)
qed

lemma lc_eq_zero_iff: "lc p = 0 \<longleftrightarrow> p = 0"
  using lc_not_0 lc_zero by blast

lemma lt_minus_eqI: "lt p \<prec>\<^sub>t lt q \<Longrightarrow> lt (p - q) = lt q" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  by (metis lt_plus_eqI_2 lt_uminus uminus_add_conv_diff)

lemma lt_minus_eqI_2: "lt q \<prec>\<^sub>t lt p \<Longrightarrow> lt (p - q) = lt p" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  by (metis lt_minus_eqI lt_uminus minus_diff_eq)

lemma lt_minus_lessE: "lt p \<prec>\<^sub>t lt (p - q) \<Longrightarrow> lt p \<prec>\<^sub>t lt q" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  using lt_minus_eqI_2 by fastforce

lemma lt_minus_lessE_2: "lt q \<prec>\<^sub>t lt (p - q) \<Longrightarrow> lt q \<prec>\<^sub>t lt p" for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  using lt_plus_eqI_2 by fastforce

lemma lt_minus_lessI: "p - q \<noteq> 0 \<Longrightarrow> lt q = lt p \<Longrightarrow> lc q = lc p \<Longrightarrow> lt (p - q) \<prec>\<^sub>t lt p"
  for p q :: "'t \<Rightarrow>\<^sub>0 'b::ab_group_add"
  by (metis add_diff_cancel_left leading_monomial_tail lower_id_iff lower_minus tail_def)

end (* ordered_term *)

context gd_term
begin

lemma dgrad_p_set_closed_monom_mult_zero:
  assumes "p \<in> dgrad_p_set d m"
  shows "monom_mult c 0 p \<in> dgrad_p_set d m"
proof (rule dgrad_p_setI)
  fix v
  assume "v \<in> keys (monom_mult c 0 p)"
  hence "pp_of_term v \<in> pp_of_term ` keys (monom_mult c 0 p)" by simp
  then obtain u where "u \<in> keys (monom_mult c 0 p)" and eq: "pp_of_term v = pp_of_term u" ..
  from this(1) have "u \<in> keys p" by (metis keys_monom_multE splus_zero)
  with assms have "d (pp_of_term u) \<le> m" by (rule dgrad_p_setD)
  thus "d (pp_of_term v) \<le> m" by (simp only: eq)
qed

corollary ord_term_minimum_dgrad_set:
  assumes "dickson_grading (+) d" and "x \<in> Q" and "pp_of_term ` Q \<subseteq> dgrad_set d m"
  obtains q where "q \<in> Q" and "\<And>y. y \<prec>\<^sub>t q \<Longrightarrow> y \<notin> Q"
proof -
  from assms(1) have "wfP (dickson_less_v d m)" by (rule wf_dickson_less_v)
  from this assms(2) obtain q where "q \<in> Q" and *: "\<And>y. dickson_less_v d m y q \<Longrightarrow> y \<notin> Q"
    by (rule wfE_min[to_pred], auto)
  from this(1) have "pp_of_term q \<in> pp_of_term ` Q" by (rule imageI)
  with assms(3) have "pp_of_term q \<in> dgrad_set d m" ..
  hence "d (pp_of_term q) \<le> m" by (rule dgrad_setD)
  from \<open>q \<in> Q\<close> show ?thesis
  proof
    fix y
    assume "y \<prec>\<^sub>t q"
    show "y \<notin> Q"
    proof
      assume "y \<in> Q"
      hence "pp_of_term y \<in> pp_of_term ` Q" by (rule imageI)
      with assms(3) have "pp_of_term y \<in> dgrad_set d m" ..
      hence "d (pp_of_term y) \<le> m" by (rule dgrad_setD)
      from this \<open>d (pp_of_term q) \<le> m\<close> \<open>y \<prec>\<^sub>t q\<close> have "dickson_less_v d m y q"
        by (rule dickson_less_vI)
      hence "y \<notin> Q" by (rule *)
      from this \<open>y \<in> Q\<close> show False ..
    qed
  qed
qed

end (* gd_term *)

subsection \<open>Module Polynomials\<close>

context gd_inf_term
begin

lemma in_idealE_rep_dgrad_p_set:
  assumes "hom_grading d" and "B \<subseteq> punit.dgrad_p_set d m" and "p \<in> punit.dgrad_p_set d m" and "p \<in> ideal B"
  obtains r where "keys r \<subseteq> B" and "Poly_Mapping.range r \<subseteq> punit.dgrad_p_set d m" and "p = ideal.rep r"
proof -
  from assms obtain A q where "finite A" and "A \<subseteq> B" and 0: "\<And>b. q b \<in> punit.dgrad_p_set d m"
    and p: "p = (\<Sum>a\<in>A. q a * a)" by (rule punit.in_moduleE_dgrad_p_set[simplified], blast)
  define r where "r = Abs_poly_mapping (\<lambda>k. q k when k \<in> A)"
  have 1: "lookup r = (\<lambda>k. q k when k \<in> A)" unfolding r_def
    by (rule Abs_poly_mapping_inverse, simp add: \<open>finite A\<close>)
  have 2: "keys r \<subseteq> A" by (auto simp: in_keys_iff 1)
  show ?thesis
  proof
    show "Poly_Mapping.range r \<subseteq> punit.dgrad_p_set d m"
    proof
      fix f
      assume "f \<in> Poly_Mapping.range r"
      then obtain b where "b \<in> keys r" and f: "f = lookup r b" by (rule poly_mapping_rangeE)
      from this(1) 2 have "b \<in> A" ..
      hence "f = q b" by (simp add: f 1)
      show "f \<in> punit.dgrad_p_set d m" unfolding \<open>f = q b\<close> by (rule 0)
    qed
  next
    have "p = (\<Sum>a\<in>A. lookup r a * a)" unfolding p by (rule sum.cong, simp_all add: 1)
    also from \<open>finite A\<close> 2 have "... = (\<Sum>a\<in>keys r. lookup r a * a)"
    proof (rule sum.mono_neutral_right)
      show "\<forall>a\<in>A - keys r. lookup r a * a = 0" by simp
    qed
    finally show "p = ideal.rep r" by (simp only: ideal.rep_def)
  next
    from 2 \<open>A \<subseteq> B\<close> show "keys r \<subseteq> B" by (rule subset_trans)
  qed
qed

context fixes fs :: "('a \<Rightarrow>\<^sub>0 'b::field) list"
begin

definition rep_list :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "rep_list r = ideal.rep (pm_of_idx_pm fs (vectorize_poly r))"

(*
definition sig_inv :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "sig_inv r = (keys (vectorize_poly r) \<subseteq> {0..<length fs})"
*)

lemma rep_list_zero: "rep_list 0 = 0"
  by (simp add: rep_list_def vectorize_zero)

lemma rep_list_uminus: "rep_list (- r) = - rep_list r"
  by (simp add: rep_list_def vectorize_uminus pm_of_idx_pm_uminus)

lemma rep_list_plus: "rep_list (r + s) = rep_list r + rep_list s"
  by (simp add: rep_list_def vectorize_plus pm_of_idx_pm_plus ideal.rep_plus)

lemma rep_list_minus: "rep_list (r - s) = rep_list r - rep_list s"
  by (simp add: rep_list_def vectorize_minus pm_of_idx_pm_minus ideal.rep_minus)

lemma vectorize_mult_scalar:
  "vectorize_poly (p \<odot> q) = MPoly_Type_Class.punit.monom_mult p 0 (vectorize_poly q)"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly MPoly_Type_Class.punit.lookup_monom_mult_zero proj_mult_scalar)

lemma rep_list_times: "rep_list (c \<odot> r) = c * rep_list r"
  by (simp add: rep_list_def vectorize_mult_scalar pm_of_idx_pm_monom_mult punit.rep_mult_scalar[simplified])

lemma rep_list_monom_mult: "rep_list (monom_mult c t r) = punit.monom_mult c t (rep_list r)"
  unfolding mult_scalar_monomial[symmetric] times_monomial_left[symmetric] by (rule rep_list_times)

lemma rep_list_monomial:
  assumes "distinct fs"
  shows "rep_list (monomial c u) =
            (punit.monom_mult c (pp_of_term u) (fs ! (component_of_term u))
              when component_of_term u < length fs)"
  by (simp add: rep_list_def vectorize_monomial pm_of_idx_pm_monomial[OF assms] when_def times_monomial_left)

lemma rep_list_in_ideal: "rep_list r \<in> ideal (set fs)"
proof -
  have "rep_list r \<in> ideal (keys (pm_of_idx_pm fs (vectorize_poly r)))"
    unfolding rep_list_def by (rule ideal.rep_in_module)
  also from keys_pm_of_idx_pm_subset have "... \<subseteq> ideal (set fs)" by (rule ideal.module_mono)
  finally show ?thesis .
qed

corollary rep_list_subset_ideal: "rep_list ` B \<subseteq> ideal (set fs)"
  by (auto intro: rep_list_in_ideal)

lemma in_idealE_rep_list:
  assumes "p \<in> ideal (set fs)"
  obtains r where "p = rep_list r"  (*and "sig_inv r"*)
proof -
  from assms obtain r0 where r0: "keys r0 \<subseteq> set fs" and p: "p = ideal.rep r0"
    by (rule ideal.in_moduleE_rep)
  have "p = rep_list (atomize_poly (idx_pm_of_pm fs r0))"
    by (simp add: rep_list_def vectorize_atomize_poly pm_of_idx_pm_of_pm[OF r0] p)
  thus ?thesis ..
qed

lemma keys_rep_list_subset:
  assumes "t \<in> keys (rep_list r)"
  obtains v s where "v \<in> keys r" and "s \<in> Keys (set fs)" and "t = pp_of_term v + s"
proof -
  from assms obtain v0 s where v0: "v0 \<in> Keys (Poly_Mapping.range (pm_of_idx_pm fs (vectorize_poly r)))"
    and s: "s \<in> Keys (keys (pm_of_idx_pm fs (vectorize_poly r)))" and t: "t = v0 + s"
    unfolding rep_list_def by (rule punit.keys_rep_subset[simplified])
  note s
  also from keys_pm_of_idx_pm_subset have "Keys (keys (pm_of_idx_pm fs (vectorize_poly r))) \<subseteq> Keys (set fs)"
    by (rule Keys_mono)
  finally have "s \<in> Keys (set fs)" .
  note v0
  also from range_pm_of_idx_pm_subset'
  have "Keys (Poly_Mapping.range (pm_of_idx_pm fs (vectorize_poly r))) \<subseteq> Keys (Poly_Mapping.range (vectorize_poly r))"
    by (rule Keys_mono)
  also have "... = pp_of_term ` keys r" by (fact Keys_range_vectorize_poly)
  finally obtain v where "v \<in> keys r" and "v0 = pp_of_term v" ..
  from this(2) have "t = pp_of_term v + s" by (simp only: t)
  with \<open>v \<in> keys r\<close> \<open>s \<in> Keys (set fs)\<close> show ?thesis ..
qed

lemma dgrad_p_set_le_rep_list:
  assumes "dickson_grading (+) d" and "dgrad_set_le d (pp_of_term ` keys r) (Keys (set fs))"
  shows "punit.dgrad_p_set_le d {rep_list r} (set fs)"
proof (simp add: punit.dgrad_p_set_le_def Keys_insert, rule dgrad_set_leI)
  fix t
  assume "t \<in> keys (rep_list r)"
  then obtain v s1 where "v \<in> keys r" and "s1 \<in> Keys (set fs)" and t: "t = pp_of_term v + s1"
    by (rule keys_rep_list_subset)
  from this(1) have "pp_of_term v \<in> pp_of_term ` keys r" by fastforce
  with assms(2) obtain s2 where "s2 \<in> Keys (set fs)" and "d (pp_of_term v) \<le> d s2"
    by (rule dgrad_set_leE)
  from assms(1) have "d t = ord_class.max (d (pp_of_term v)) (d s1)" unfolding t
    by (rule dickson_gradingD1)
  hence "d t = d (pp_of_term v) \<or> d t = d s1" by (simp add: ord_class.max_def)
  thus "\<exists>s\<in>Keys (set fs). d t \<le> d s"
  proof
    assume "d t = d (pp_of_term v)"
    with \<open>d (pp_of_term v) \<le> d s2\<close> have "d t \<le> d s2" by simp
    with \<open>s2 \<in> Keys (set fs)\<close> show ?thesis ..
  next
    assume "d t = d s1"
    hence "d t \<le> d s1" by simp
    with \<open>s1 \<in> Keys (set fs)\<close> show ?thesis ..
  qed
qed

corollary dgrad_p_set_le_rep_list_image:
  assumes "dickson_grading (+) d" and "dgrad_set_le d (pp_of_term ` Keys F) (Keys (set fs))"
  shows "punit.dgrad_p_set_le d (rep_list ` F) (set fs)"
proof (rule punit.dgrad_p_set_leI, elim imageE, simp)
  fix f
  assume "f \<in> F"
  have "pp_of_term ` keys f \<subseteq> pp_of_term ` Keys F" by (rule image_mono, rule keys_subset_Keys, fact)
  hence "dgrad_set_le d (pp_of_term ` keys f) (pp_of_term ` Keys F)" by (rule dgrad_set_le_subset)
  hence "dgrad_set_le d (pp_of_term ` keys f) (Keys (set fs))" using assms(2) by (rule dgrad_set_le_trans)
  with assms(1) show "punit.dgrad_p_set_le d {rep_list f} (set fs)" by (rule dgrad_p_set_le_rep_list)
qed

definition dgrad_max :: "('a \<Rightarrow> nat) \<Rightarrow> nat"
  where "dgrad_max d = (MAXIMUM (Keys (set fs)) d)"

abbreviation "dgrad_max_set d \<equiv> dgrad_p_set d (dgrad_max d)"
abbreviation "punit_dgrad_max_set d \<equiv> punit.dgrad_p_set d (dgrad_max d)"

lemma dgrad_max_1: "set fs \<subseteq> punit_dgrad_max_set d"
  unfolding dgrad_max_def using finite_set by (rule punit.dgrad_p_set_exhaust_expl[simplified])

lemma dgrad_max_2:
  assumes "dickson_grading (+) d" and "r \<in> dgrad_max_set d"
  shows "rep_list r \<in> punit_dgrad_max_set d"
proof (rule punit.dgrad_p_setI[simplified])
  fix t
  assume "t \<in> keys (rep_list r)"
  then obtain v s where "v \<in> keys r" and "s \<in> Keys (set fs)" and t: "t = pp_of_term v + s"
    by (rule keys_rep_list_subset)
  from assms(2) \<open>v \<in> keys r\<close> have "d (pp_of_term v) \<le> dgrad_max d" by (rule dgrad_p_setD)
  moreover have "d s \<le> dgrad_max d" by (simp add: \<open>s \<in> Keys (set fs)\<close> dgrad_max_def finite_Keys)
  ultimately show "d t \<le> dgrad_max d" by (simp add: t dickson_gradingD1[OF assms(1)])
qed

corollary dgrad_max_3:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_max_set d"
  shows "rep_list ` F \<subseteq> punit_dgrad_max_set d"
proof (rule, elim imageE, simp)
  fix f
  assume "f \<in> F"
  hence "f \<in> dgrad_p_set d (dgrad_max d)" using assms(2) ..
  with assms(1) show "rep_list f \<in> punit.dgrad_p_set d (dgrad_max d)" by (rule dgrad_max_2)
qed

lemma in_idealE_rep_list_dgrad_max_set:
  assumes "hom_grading d" and "p \<in> punit_dgrad_max_set d" and "p \<in> ideal (set fs)"
  obtains r where "r \<in> dgrad_max_set d" and "p = rep_list r"  (*and "sig_inv r"*)
proof -
  from assms(1) dgrad_max_1 assms(2, 3) obtain r0 where r0: "keys r0 \<subseteq> set fs"
    and 1: "Poly_Mapping.range r0 \<subseteq> punit_dgrad_max_set d" and p: "p = ideal.rep r0"
    by (rule in_idealE_rep_dgrad_p_set)
  show ?thesis
  proof
    show "atomize_poly (idx_pm_of_pm fs r0) \<in> dgrad_max_set d"
    proof
      fix v
      assume "v \<in> keys (atomize_poly (idx_pm_of_pm fs r0))"
      then obtain i where i: "i \<in> keys (idx_pm_of_pm fs r0)"
        and v_in: "v \<in> (\<lambda>t. term_of_pair (t, i)) ` keys (lookup (idx_pm_of_pm fs r0) i)"
        unfolding keys_atomize_poly ..
      from i keys_idx_pm_of_pm_subset[of fs r0] have "i < length fs" by auto
      from v_in obtain t where "t \<in> keys (lookup (idx_pm_of_pm fs r0) i)" and v: "v = term_of_pair (t, i)" ..
      from this(1) \<open>i < length fs\<close> have t: "t \<in> keys (lookup r0 (fs ! i))" by (simp add: lookup_idx_pm_of_pm)
      hence "lookup r0 (fs ! i) \<noteq> 0" by fastforce
      hence "lookup r0 (fs ! i) \<in> Poly_Mapping.range r0" by simp
      hence "lookup r0 (fs ! i) \<in> punit_dgrad_max_set d" using 1 ..
      hence "d t \<le> dgrad_max d" using t by (rule punit.dgrad_p_setD[simplified])
      thus "d (pp_of_term v) \<le> dgrad_max d" by (simp add: v pp_of_term_of_pair)
    qed
  next
    show "p = rep_list (atomize_poly (idx_pm_of_pm fs r0))"
      by (simp add: rep_list_def vectorize_atomize_poly pm_of_idx_pm_of_pm[OF r0] p)
  qed
qed

subsubsection \<open>Signature Reduction\<close>

lemma term_is_le_rel_canc_left:
  assumes "ord_term_lin.is_le_rel rel"
  shows "rel (t \<oplus> u) (t \<oplus> v) \<longleftrightarrow> rel u v"
  using assms
  by (rule ord_term_lin.is_le_relE,
      auto simp: splus_left_canc dest: ord_term_canc ord_term_strict_canc splus_mono splus_mono_strict)

lemma term_is_le_rel_minus:
  assumes "ord_term_lin.is_le_rel rel" and "s adds t"
  shows "rel ((t - s) \<oplus> u) v \<longleftrightarrow> rel (t \<oplus> u) (s \<oplus> v)"
proof -
  from assms(2) have eq: "s + (t - s) = t" unfolding add.commute[of s] by (rule adds_minus)
  from assms(1) have "rel ((t - s) \<oplus> u) v = rel (s \<oplus> ((t - s) \<oplus> u)) (s \<oplus> v)"
    by (simp only: term_is_le_rel_canc_left)
  also have "... = rel (t \<oplus> u) (s \<oplus> v)" by (simp only: splus_assoc[symmetric] eq)
  finally show ?thesis .
qed

lemma term_is_le_rel_minus_minus:
  assumes "ord_term_lin.is_le_rel rel" and "a adds t" and "b adds t"
  shows "rel ((t - a) \<oplus> u) ((t - b) \<oplus> v) \<longleftrightarrow> rel (b \<oplus> u) (a \<oplus> v)"
proof -
  from assms(2) have eq1: "a + (t - a) = t" unfolding add.commute[of a] by (rule adds_minus)
  from assms(3) have eq2: "b + (t - b) = t" unfolding add.commute[of b] by (rule adds_minus)
  from assms(1) have "rel ((t - a) \<oplus> u) ((t - b) \<oplus> v) = rel ((a + b) \<oplus> ((t - a) \<oplus> u)) ((a + b) \<oplus> ((t - b) \<oplus> v))"
    by (simp only: term_is_le_rel_canc_left)
  also have "... = rel ((t + b) \<oplus> u) ((t + a) \<oplus> v)" unfolding splus_assoc[symmetric]
    by (metis (no_types, lifting) add.assoc add.commute eq1 eq2)
  also from assms(1) have "... = rel (b \<oplus> u) (a \<oplus> v)" by (simp only: splus_assoc term_is_le_rel_canc_left)
  finally show ?thesis .
qed

lemma pp_is_le_rel_canc_right:
  assumes "ordered_powerprod_lin.is_le_rel rel"
  shows "rel (s + u) (t + u) \<longleftrightarrow> rel s t"
  using assms
  by (rule ordered_powerprod_lin.is_le_relE, auto dest: ord_canc ord_strict_canc plus_monotone plus_monotone_strict)

lemma pp_is_le_rel_canc_left: "ordered_powerprod_lin.is_le_rel rel \<Longrightarrow> rel (t + u) (t + v) \<longleftrightarrow> rel u v"
  by (simp add: add.commute[of t] pp_is_le_rel_canc_right)

definition sig_red_single :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow> bool"
  where "sig_red_single sing_reg top_tail p q f t \<longleftrightarrow>
                (rep_list f \<noteq> 0 \<and> lookup (rep_list p) (t + punit.lt (rep_list f)) \<noteq> 0 \<and>
                 q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f \<and>
                 ord_term_lin.is_le_rel sing_reg \<and> ordered_powerprod_lin.is_le_rel top_tail \<and>
                 sing_reg (t \<oplus> lt f) (lt p) \<and> top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p)))"

text \<open>The first two parameters of @{const sig_red_single}, \<open>sing_reg\<close> and \<open>top_tail\<close>, specify whether
  the reduction is a singular/regular/arbitrary top/tail/arbitrary signature-reduction.
  * If \<open>sing_reg\<close> is @{const HOL.eq}, the reduction is singular.
  * If \<open>sing_reg\<close> is @{term "(\<prec>\<^sub>t)"}, the reduction is regular.
  * If \<open>sing_reg\<close> is @{term "(\<preceq>\<^sub>t)"}, the reduction is an arbitrary signature-reduction.
  * If \<open>top_tail\<close> is @{const HOL.eq}, it is a top reduction.
  * If \<open>top_tail\<close> is @{term "(\<prec>)"}, it is a tail reduction.
  * If \<open>top_tail\<close> is @{term "(\<preceq>)"}, the reduction is an arbitrary signature-reduction.\<close>

definition sig_red :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "sig_red sing_reg top_tail F p q \<longleftrightarrow> (\<exists>f\<in>F. \<exists>t. sig_red_single sing_reg top_tail p q f t)"

definition is_sig_red :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_sig_red sing_reg top_tail F p \<longleftrightarrow> (\<exists>q. sig_red sing_reg top_tail F p q)"

lemma sig_red_singleI:
  assumes "rep_list f \<noteq> 0" and "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    and "ord_term_lin.is_le_rel sing_reg" and "ordered_powerprod_lin.is_le_rel top_tail"
    and "sing_reg (t \<oplus> lt f) (lt p)"
    and "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
  shows "sig_red_single sing_reg top_tail p q f t"
  unfolding sig_red_single_def using assms by blast

lemma sig_red_singleD1:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "rep_list f \<noteq> 0"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD2:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
  using assms unfolding sig_red_single_def by simp

lemma sig_red_singleD3:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD4:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "ord_term_lin.is_le_rel sing_reg"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD5:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "ordered_powerprod_lin.is_le_rel top_tail"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD6:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "sing_reg (t \<oplus> lt f) (lt p)"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD7:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
  using assms unfolding sig_red_single_def by blast

lemma sig_red_singleD8:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "t \<oplus> lt f \<preceq>\<^sub>t lt p"
proof -
  from assms have "ord_term_lin.is_le_rel sing_reg" and "sing_reg (t \<oplus> lt f) (lt p)"
    by (rule sig_red_singleD4, rule sig_red_singleD6)
  thus ?thesis by (rule ord_term_lin.is_le_rel_le)
qed

lemma sig_red_singleD9:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "t + punit.lt (rep_list f) \<preceq> punit.lt (rep_list p)"
proof -
  from assms have "ordered_powerprod_lin.is_le_rel top_tail"
    and "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
    by (rule sig_red_singleD5, rule sig_red_singleD7)
  thus ?thesis by (rule ordered_powerprod_lin.is_le_rel_le)
qed

lemmas sig_red_singleD = sig_red_singleD1 sig_red_singleD2 sig_red_singleD3 sig_red_singleD4
                         sig_red_singleD5 sig_red_singleD6 sig_red_singleD7 sig_red_singleD8 sig_red_singleD9

lemma sig_red_single_red_single:
  "sig_red_single sing_reg top_tail p q f t \<Longrightarrow> punit.red_single (rep_list p) (rep_list q) (rep_list f) t"
  by (simp add: sig_red_single_def punit.red_single_def rep_list_minus rep_list_monom_mult)

lemma sig_red_single_regular_lt:
  assumes "sig_red_single (\<prec>\<^sub>t) top_tail p q f t"
  shows "lt q = lt p"
proof -
  let ?f = "monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
  from assms have lt: "t \<oplus> lt f \<prec>\<^sub>t lt p" and q: "q = p - ?f"
    by (rule sig_red_singleD6, rule sig_red_singleD3)
  from lt_monom_mult_le lt have "lt ?f \<prec>\<^sub>t lt p" by (rule ord_term_lin.order.strict_trans1)
  thus ?thesis unfolding q by (rule lt_minus_eqI_2)
qed

lemma sig_red_single_regular_lc:
  assumes "sig_red_single (\<prec>\<^sub>t) top_tail p q f t"
  shows "lc q = lc p"
proof -
  from assms have "lt q = lt p" by (rule sig_red_single_regular_lt)
  from assms have lt: "t \<oplus> lt f \<prec>\<^sub>t lt p"
    and q: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ - ?f") by (rule sig_red_singleD6, rule sig_red_singleD3)
  from lt_monom_mult_le lt have "lt ?f \<prec>\<^sub>t lt p" by (rule ord_term_lin.order.strict_trans1)
  hence "lookup ?f (lt p) = 0" using lt_max ord_term_lin.leD by blast
  thus ?thesis unfolding lc_def \<open>lt q = lt p\<close> by (simp add: q lookup_minus)
qed

lemma sig_red_single_singular_lt:
  assumes "sig_red_single (=) top_tail p q f t" and "q \<noteq> 0"
  shows "lt q \<prec>\<^sub>t lt p"
proof -
  from assms(1) have "rep_list f \<noteq> 0" and "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and lt: "t \<oplus> lt f = lt p"
    and q0: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD)+
  from this(2) have "lookup (rep_list p) (t + punit.lt (rep_list f)) \<noteq> 0" by simp
  moreover from \<open>rep_list f \<noteq> 0\<close> have "punit.lc (rep_list f) \<noteq> 0" by (rule punit.lc_not_0)
  ultimately have "- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f) \<noteq> 0"
    (is "?c \<noteq> 0") by simp
  moreover from \<open>rep_list f \<noteq> 0\<close> have "f \<noteq> 0" by (auto simp: rep_list_zero)
  ultimately have "lt (monom_mult ?c t f) = t \<oplus> lt f" by (rule lt_monom_mult)
  hence "lt (monom_mult ?c t f) = lt p" by (simp only: lt)
  moreover have "lc (monom_mult ?c t f) = - lc p" apply simp oops

lemma sig_red_single_singular_top_lt:
  assumes "sig_red_single (=) (=) p q f t" and "q \<noteq> 0"
  shows "lt q \<prec>\<^sub>t lt p"
proof -
  from assms(1) have "rep_list f \<noteq> 0" and "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and lt: "t \<oplus> lt f = lt p" and lt': "t + punit.lt (rep_list f) = punit.lt (rep_list p)"
    and q0: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD)+
  from this(2) have "lookup (rep_list p) (t + punit.lt (rep_list f)) \<noteq> 0" by simp
  moreover from \<open>rep_list f \<noteq> 0\<close> have "punit.lc (rep_list f) \<noteq> 0" by (rule punit.lc_not_0)
  ultimately have "- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f) \<noteq> 0"
    (is "?c \<noteq> 0") by simp
  moreover from \<open>rep_list f \<noteq> 0\<close> have "f \<noteq> 0" by (auto simp: rep_list_zero)
  ultimately have "lt (monom_mult ?c t f) = t \<oplus> lt f" by (rule lt_monom_mult)
  hence "lt (monom_mult ?c t f) = lt p" by (simp only: lt)
  moreover have "lc (monom_mult ?c t f) = - lc p" apply (simp add: lt' punit.lc_def[symmetric]) oops

lemma sig_red_single_lt:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "lt q \<preceq>\<^sub>t lt p"
proof -
  from assms have lt: "t \<oplus> lt f \<preceq>\<^sub>t lt p"
    and "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD8, rule sig_red_singleD3)
  from this(2) have q: "q = p + monom_mult (- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ + ?f") by (simp add: monom_mult_uminus_left)
  from lt_monom_mult_le lt have 1: "lt ?f \<preceq>\<^sub>t lt p" by (rule ord_term_lin.order.trans)
  have "lt q \<preceq>\<^sub>t ord_term_lin.max (lt p) (lt ?f)" unfolding q by (fact lt_plus_le_max)
  also from 1 have "ord_term_lin.max (lt p) (lt ?f) = lt p" by (rule ord_term_lin.max.absorb1)
  finally show ?thesis .
qed

lemma sig_red_single_lt_rep_list:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)"
proof -
  from assms have "punit.red_single (rep_list p) (rep_list q) (rep_list f) t"
    by (rule sig_red_single_red_single)
  hence "punit.ord_strict_p (rep_list q) (rep_list p)" by (rule punit.red_single_ord)
  hence "punit.ord_p (rep_list q) (rep_list p)" by simp
  thus ?thesis by (rule punit.ord_p_lt)
qed

lemma sig_red_single_tail_lt_in_keys_rep_list:
  assumes "sig_red_single sing_reg (\<prec>) p q f t"
  shows "punit.lt (rep_list p) \<in> keys (rep_list q)"
proof -
  from assms have "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD3)
  hence q: "q = p + monom_mult (- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (simp add: monom_mult_uminus_left)
  show ?thesis unfolding q rep_list_plus rep_list_monom_mult
  proof (rule in_keys_plusI1)
    from assms have "t + punit.lt (rep_list f) \<in> keys (rep_list p)" by (rule sig_red_singleD2)
    hence "rep_list p \<noteq> 0" by auto
    thus "punit.lt (rep_list p) \<in> keys (rep_list p)" by (rule punit.lt_in_keys)
  next
    show "punit.lt (rep_list p) \<notin>
      keys (punit.monom_mult (- lookup (rep_list p) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t (rep_list f))"
        (is "_ \<notin> keys ?f")
    proof
      assume "punit.lt (rep_list p) \<in> keys ?f"
      hence "punit.lt (rep_list p) \<preceq> punit.lt ?f" by (rule punit.lt_max_keys)
      also have "... \<preceq> t + punit.lt (rep_list f)" by (fact punit.lt_monom_mult_le[simplified])
      also from assms have "... \<prec> punit.lt (rep_list p)" by (rule sig_red_singleD7)
      finally show False by simp
    qed
  qed
qed

corollary sig_red_single_tail_lt_rep_list:
  assumes "sig_red_single sing_reg (\<prec>) p q f t"
  shows "punit.lt (rep_list q) = punit.lt (rep_list p)"
proof (rule ordered_powerprod_lin.antisym)
  from assms show "punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)" by (rule sig_red_single_lt_rep_list)
next
  from assms have "punit.lt (rep_list p) \<in> keys (rep_list q)" by (rule sig_red_single_tail_lt_in_keys_rep_list)
  thus "punit.lt (rep_list p) \<preceq> punit.lt (rep_list q)" by (rule punit.lt_max_keys)
qed

lemma sig_red_single_tail_lc_rep_list:
  assumes "sig_red_single sing_reg (\<prec>) p q f t"
  shows "punit.lc (rep_list q) = punit.lc (rep_list p)"
proof -
  from assms have *: "punit.lt (rep_list q) = punit.lt (rep_list p)"
    by (rule sig_red_single_tail_lt_rep_list)
  from assms have lt: "t + punit.lt (rep_list f) \<prec> punit.lt (rep_list p)"
    and q: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ - ?f") by (rule sig_red_singleD7, rule sig_red_singleD3)
  from punit.lt_monom_mult_le[simplified] lt have "punit.lt (rep_list ?f) \<prec> punit.lt (rep_list p)"
    unfolding rep_list_monom_mult by (rule ordered_powerprod_lin.order.strict_trans1)
  hence "lookup (rep_list ?f) (punit.lt (rep_list p)) = 0"
    using punit.lt_max ordered_powerprod_lin.leD by blast
  thus ?thesis unfolding punit.lc_def * by (simp add: q lookup_minus rep_list_minus punit.lc_def)
qed

lemma sig_red_single_top_lt_rep_list:
  assumes "sig_red_single sing_reg (=) p q f t" and "rep_list q \<noteq> 0"
  shows "punit.lt (rep_list q) \<prec> punit.lt (rep_list p)"
proof -
  from assms(1) have "rep_list f \<noteq> 0" and in_keys: "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and lt: "t + punit.lt (rep_list f) = punit.lt (rep_list p)"
    and "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    by (rule sig_red_singleD)+
  from this(4) have q: "q = p + monom_mult (- (lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    (is "_ = _ + monom_mult ?c _ _") by (simp add: monom_mult_uminus_left)
  from \<open>rep_list f \<noteq> 0\<close> have "punit.lc (rep_list f) \<noteq> 0" by (rule punit.lc_not_0)
  from assms(2) have *: "rep_list p + punit.monom_mult ?c t (rep_list f) \<noteq> 0"
    by (simp add: q rep_list_plus rep_list_monom_mult)
  from in_keys have "lookup (rep_list p) (t + punit.lt (rep_list f)) \<noteq> 0" by simp
  moreover from \<open>rep_list f \<noteq> 0\<close> have "punit.lc (rep_list f) \<noteq> 0" by (rule punit.lc_not_0)
  ultimately have "?c \<noteq> 0" by simp
  hence "punit.lt (punit.monom_mult ?c t (rep_list f)) = t + punit.lt (rep_list f)"
    using \<open>rep_list f \<noteq> 0\<close> by (rule lp_monom_mult)
  hence "punit.lt (punit.monom_mult ?c t (rep_list f)) = punit.lt (rep_list p)" by (simp only: lt)
  moreover have "punit.lc (punit.monom_mult ?c t (rep_list f)) = - punit.lc (rep_list p)"
    by (simp add: lt punit.lc_def[symmetric] \<open>punit.lc (rep_list f) \<noteq> 0\<close>)
  ultimately show ?thesis unfolding rep_list_plus rep_list_monom_mult q by (rule punit.lt_plus_lessI[OF *])
qed

lemma sig_red_single_monom_mult:
  assumes "sig_red_single sing_reg top_tail p q f t" and "c \<noteq> 0"
  shows "sig_red_single sing_reg top_tail (monom_mult c s p) (monom_mult c s q) f (s + t)"
proof -
  from assms(1) have a: "ord_term_lin.is_le_rel sing_reg" and b: "ordered_powerprod_lin.is_le_rel top_tail"
    by (rule sig_red_singleD4, rule sig_red_singleD5)
  have eq1: "(s + t) \<oplus> lt f = s \<oplus> (t \<oplus> lt f)" by (simp only: splus_assoc)
  from assms(1) have 1: "t + punit.lt (rep_list f) \<in> keys (rep_list p)" by (rule sig_red_singleD2)
  hence "rep_list p \<noteq> 0" by auto
  hence "p \<noteq> 0" by (auto simp: rep_list_zero)
  with assms(2) have eq2: "lt (monom_mult c s p) = s \<oplus> lt p" by (rule lt_monom_mult)
  show ?thesis
  proof (rule sig_red_singleI)
    from assms(1) show "rep_list f \<noteq> 0" by (rule sig_red_singleD1)
  next
    show "s + t + punit.lt (rep_list f) \<in> keys (rep_list (monom_mult c s p))"
      by (auto simp: rep_list_monom_mult punit.keys_monom_mult[OF assms(2)] ac_simps intro: 1)
  next
    from assms(1) have q: "q = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
      by (rule sig_red_singleD3)
    show "monom_mult c s q =
          monom_mult c s p -
            monom_mult (lookup (rep_list (monom_mult c s p)) (s + t + punit.lt (rep_list f)) / punit.lc (rep_list f)) (s + t) f"
      by (simp add: q monom_mult_dist_right_minus ac_simps rep_list_monom_mult
          punit.lookup_monom_mult_plus[simplified] monom_mult_assoc)
  next
    from assms(1) have "sing_reg (t \<oplus> lt f) (lt p)" by (rule sig_red_singleD6)
    thus "sing_reg ((s + t) \<oplus> lt f) (lt (monom_mult c s p))"
      by (simp only: eq1 eq2 term_is_le_rel_canc_left[OF a])
  next
    from assms(1) have "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
      by (rule sig_red_singleD7)
    thus "top_tail (s + t + punit.lt (rep_list f)) (punit.lt (rep_list (monom_mult c s p)))"
      by (simp add: rep_list_monom_mult punit.lt_monom_mult[OF assms(2) \<open>rep_list p \<noteq> 0\<close>] add.assoc pp_is_le_rel_canc_left[OF b])
  qed (fact a, fact b)
qed

lemma sig_red_single_sing_reg_cases:
  "sig_red_single (\<preceq>\<^sub>t) top_tail p q f t = (sig_red_single (=) top_tail p q f t \<or> sig_red_single (\<prec>\<^sub>t) top_tail p q f t)"
  by (auto simp: sig_red_single_def)

corollary sig_red_single_sing_regI:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "sig_red_single (\<preceq>\<^sub>t) top_tail p q f t"
proof -
  from assms have "ord_term_lin.is_le_rel sing_reg" by (rule sig_red_singleD)
  with assms show ?thesis unfolding ord_term_lin.is_le_rel_def
    by (auto simp: sig_red_single_sing_reg_cases)
qed

lemma sig_red_single_top_tail_cases:
  "sig_red_single sing_reg (\<preceq>) p q f t = (sig_red_single sing_reg (=) p q f t \<or> sig_red_single sing_reg (\<prec>) p q f t)"
  by (auto simp: sig_red_single_def)

corollary sig_red_single_top_tailI:
  assumes "sig_red_single sing_reg top_tail p q f t"
  shows "sig_red_single sing_reg (\<preceq>) p q f t"
proof -
  from assms have "ordered_powerprod_lin.is_le_rel top_tail" by (rule sig_red_singleD)
  with assms show ?thesis unfolding ordered_powerprod_lin.is_le_rel_def
    by (auto simp: sig_red_single_top_tail_cases)
qed

lemma dgrad_max_set_closed_sig_red_single:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_max_set d" and "f \<in> dgrad_max_set d"
    and "sig_red_single sing_red top_tail p q f t"
  shows "q \<in> dgrad_max_set d"
proof -
  let ?f = "monom_mult (lookup (rep_list p) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t f"
  from assms(4) have t: "t + punit.lt (rep_list f) \<in> keys (rep_list p)" and q: "q = p - ?f"
    by (rule sig_red_singleD2, rule sig_red_singleD3)
  from assms(1, 2) have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
  show ?thesis unfolding q using assms(2)
  proof (rule dgrad_p_set_closed_minus)
    from assms(1) _ assms(3) show "?f \<in> dgrad_max_set d"
    proof (rule dgrad_p_set_closed_monom_mult)
      from assms(1) have "d t \<le> d (t + punit.lt (rep_list f))" by (simp add: dickson_gradingD1)
      also from \<open>rep_list p \<in> punit_dgrad_max_set d\<close> t have "... \<le> dgrad_max d"
        by (rule punit.dgrad_p_setD[simplified])
      finally show "d t \<le> dgrad_max d" .
    qed
  qed
qed

lemma sig_red_regular_lt: "sig_red (\<prec>\<^sub>t) top_tail F p q \<Longrightarrow> lt q = lt p"
  by (auto simp: sig_red_def intro: sig_red_single_regular_lt)

lemma sig_red_regular_lc: "sig_red (\<prec>\<^sub>t) top_tail F p q \<Longrightarrow> lc q = lc p"
  by (auto simp: sig_red_def intro: sig_red_single_regular_lc)

lemma sig_red_lt: "sig_red sing_reg top_tail F p q \<Longrightarrow> lt q \<preceq>\<^sub>t lt p"
  by (auto simp: sig_red_def intro: sig_red_single_lt)

lemma sig_red_tail_lt_rep_list: "sig_red sing_reg (\<prec>) F p q \<Longrightarrow> punit.lt (rep_list q) = punit.lt (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_tail_lt_rep_list)

lemma sig_red_tail_lc_rep_list: "sig_red sing_reg (\<prec>) F p q \<Longrightarrow> punit.lc (rep_list q) = punit.lc (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_tail_lc_rep_list)

lemma sig_red_top_lt_rep_list:
  "sig_red sing_reg (=) F p q \<Longrightarrow> rep_list q \<noteq> 0 \<Longrightarrow> punit.lt (rep_list q) \<prec> punit.lt (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_top_lt_rep_list)

lemma sig_red_lt_rep_list: "sig_red sing_reg top_tail F p q \<Longrightarrow> punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)"
  by (auto simp: sig_red_def intro: sig_red_single_lt_rep_list)

lemma sig_red_red: "sig_red sing_reg top_tail F p q \<Longrightarrow> punit.red (rep_list ` F) (rep_list p) (rep_list q)"
  by (auto simp: sig_red_def punit.red_def dest: sig_red_single_red_single)

lemma sig_red_monom_mult:
  "sig_red sing_reg top_tail F p q \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> sig_red sing_reg top_tail F (monom_mult c s p) (monom_mult c s q)"
  by (auto simp: sig_red_def punit.red_def dest: sig_red_single_monom_mult)

lemma sig_red_sing_reg_cases:
  "sig_red (\<preceq>\<^sub>t) top_tail F p q = (sig_red (=) top_tail F p q \<or> sig_red (\<prec>\<^sub>t) top_tail F p q)"
  by (auto simp: sig_red_def sig_red_single_sing_reg_cases)

corollary sig_red_sing_regI: "sig_red sing_reg top_tail F p q \<Longrightarrow> sig_red (\<preceq>\<^sub>t) top_tail F p q"
  by (auto simp: sig_red_def intro: sig_red_single_sing_regI)

lemma sig_red_top_tail_cases:
  "sig_red sing_reg (\<preceq>) F p q = (sig_red sing_reg (=) F p q \<or> sig_red sing_reg (\<prec>) F p q)"
  by (auto simp: sig_red_def sig_red_single_top_tail_cases)

corollary sig_red_top_tailI: "sig_red sing_reg top_tail F p q \<Longrightarrow> sig_red sing_reg (\<preceq>) F p q"
  by (auto simp: sig_red_def intro: sig_red_single_top_tailI)

lemma sig_red_wf_dgrad_max_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_max_set d"
  shows "wfP (sig_red sing_reg top_tail F)\<inverse>\<inverse>"
proof -
  from assms have "rep_list ` F \<subseteq> punit_dgrad_max_set d" by (rule dgrad_max_3)
  with assms(1) have "wfP (punit.red (rep_list ` F))\<inverse>\<inverse>" by (rule punit.red_wf_dgrad_p_set)
  hence *: "\<nexists>f. \<forall>i. (punit.red (rep_list ` F))\<inverse>\<inverse> (f (Suc i)) (f i)"
    by (simp add: wf_iff_no_infinite_down_chain[to_pred])
  show ?thesis unfolding wf_iff_no_infinite_down_chain[to_pred]
  proof (rule, elim exE)
    fix seq
    assume "\<forall>i. (sig_red sing_reg top_tail F)\<inverse>\<inverse> (seq (Suc i)) (seq i)"
    hence "sig_red sing_reg top_tail F (seq i) (seq (Suc i))" for i by simp
    hence "punit.red (rep_list ` F) ((rep_list \<circ> seq) i) ((rep_list \<circ> seq) (Suc i))" for i
      by (auto intro: sig_red_red)
    hence "\<forall>i. (punit.red (rep_list ` F))\<inverse>\<inverse> ((rep_list \<circ> seq) (Suc i)) ((rep_list \<circ> seq) i)" by simp
    hence "\<exists>f. \<forall>i. (punit.red (rep_list ` F))\<inverse>\<inverse> (f (Suc i)) (f i)" by blast
    with * show False ..
  qed
qed

lemma dgrad_max_set_closed_sig_red:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_max_set d" and "p \<in> dgrad_max_set d"
    and "sig_red sing_red top_tail F p q"
  shows "q \<in> dgrad_max_set d"
  using assms by (auto simp: sig_red_def intro: dgrad_max_set_closed_sig_red_single)

lemma sig_red_regular_rtrancl_lt:
  assumes "(sig_red (\<prec>\<^sub>t) top_tail F)\<^sup>*\<^sup>* p q"
  shows "lt q = lt p"
  using assms by (induct, auto dest: sig_red_regular_lt)

lemma sig_red_regular_rtrancl_lc:
  assumes "(sig_red (\<prec>\<^sub>t) top_tail F)\<^sup>*\<^sup>* p q"
  shows "lc q = lc p"
  using assms by (induct, auto dest: sig_red_regular_lc)

lemma sig_red_rtrancl_lt:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "lt q \<preceq>\<^sub>t lt p"
  using assms by (induct, auto dest: sig_red_lt)

lemma sig_red_tail_rtrancl_lt_rep_list:
  assumes "(sig_red sing_reg (\<prec>) F)\<^sup>*\<^sup>* p q"
  shows "punit.lt (rep_list q) = punit.lt (rep_list p)"
  using assms by (induct, auto dest: sig_red_tail_lt_rep_list)

lemma sig_red_tail_rtrancl_lc_rep_list:
  assumes "(sig_red sing_reg (\<prec>) F)\<^sup>*\<^sup>* p q"
  shows "punit.lc (rep_list q) = punit.lc (rep_list p)"
  using assms by (induct, auto dest: sig_red_tail_lc_rep_list)

lemma sig_red_rtrancl_lt_rep_list:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "punit.lt (rep_list q) \<preceq> punit.lt (rep_list p)"
  using assms by (induct, auto dest: sig_red_lt_rep_list)

lemma sig_red_red_rtrancl:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "(punit.red (rep_list ` F))\<^sup>*\<^sup>* (rep_list p) (rep_list q)"
  using assms by (induct, auto dest: sig_red_red)

lemma sig_red_rtrancl_monom_mult:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
  shows "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* (monom_mult c s p) (monom_mult c s q)"
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  from assms(1) show ?thesis
  proof induct
    case base
    show ?case ..
  next
    case (step y z)
    from step(2) False have "sig_red sing_reg top_tail F (monom_mult c s y) (monom_mult c s z)"
      by (rule sig_red_monom_mult)
    with step(3) show ?case ..
  qed
qed

lemma sig_red_rtrancl_sing_regI: "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q \<Longrightarrow> (sig_red (\<preceq>\<^sub>t) top_tail F)\<^sup>*\<^sup>* p q"
  by (induct rule: rtranclp_induct, auto dest: sig_red_sing_regI)

lemma sig_red_rtrancl_top_tailI: "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q \<Longrightarrow> (sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* p q"
  by (induct rule: rtranclp_induct, auto dest: sig_red_top_tailI)

lemma dgrad_max_set_closed_sig_red_rtrancl:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_max_set d" and "p \<in> dgrad_max_set d"
    and "(sig_red sing_red top_tail F)\<^sup>*\<^sup>* p q"
  shows "q \<in> dgrad_max_set d"
  using assms(4, 1, 2, 3) by (induct, auto intro: dgrad_max_set_closed_sig_red)

lemma is_sig_red_is_red: "is_sig_red sing_reg top_tail F p \<Longrightarrow> punit.is_red (rep_list ` F) (rep_list p)"
  by (auto simp: is_sig_red_def punit.is_red_alt dest: sig_red_red)

lemma is_sig_red_monom_mult:
  assumes "is_sig_red sing_reg top_tail F p" and "c \<noteq> 0"
  shows "is_sig_red sing_reg top_tail F (monom_mult c s p)"
proof -
  from assms(1) obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  hence "sig_red sing_reg top_tail F (monom_mult c s p) (monom_mult c s q)"
    using assms(2) by (rule sig_red_monom_mult)
  thus ?thesis unfolding is_sig_red_def ..
qed

lemma is_sig_red_sing_reg_cases:
  "is_sig_red (\<preceq>\<^sub>t) top_tail F p = (is_sig_red (=) top_tail F p \<or> is_sig_red (\<prec>\<^sub>t) top_tail F p)"
  by (auto simp: is_sig_red_def sig_red_sing_reg_cases)

corollary is_sig_red_sing_regI: "is_sig_red sing_reg top_tail F p \<Longrightarrow> is_sig_red (\<preceq>\<^sub>t) top_tail F p"
  by (auto simp: is_sig_red_def intro: sig_red_sing_regI)

lemma is_sig_red_top_tail_cases:
  "is_sig_red sing_reg (\<preceq>) F p = (is_sig_red sing_reg (=) F p \<or> is_sig_red sing_reg (\<prec>) F p)"
  by (auto simp: is_sig_red_def sig_red_top_tail_cases)

corollary is_sig_red_top_tailI: "is_sig_red sing_reg top_tail F p \<Longrightarrow> is_sig_red sing_reg (\<preceq>) F p"
  by (auto simp: is_sig_red_def intro: sig_red_top_tailI)

lemma is_sig_redD1:
  assumes "is_sig_red sing_reg top_tail F p"
  shows "ord_term_lin.is_le_rel sing_reg"
proof -
  from assms obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  then obtain f s where "f \<in> F" and "sig_red_single sing_reg top_tail p q f s" unfolding sig_red_def by blast
  from this(2) show ?thesis by (rule sig_red_singleD)
qed

lemma is_sig_redD2:
  assumes "is_sig_red sing_reg top_tail F p"
  shows "ordered_powerprod_lin.is_le_rel top_tail"
proof -
  from assms obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  then obtain f s where "f \<in> F" and "sig_red_single sing_reg top_tail p q f s" unfolding sig_red_def by blast
  from this(2) show ?thesis by (rule sig_red_singleD)
qed

lemma is_sig_red_addsI:
  assumes "f \<in> F" and "t \<in> keys (rep_list p)" and "rep_list f \<noteq> 0" and "punit.lt (rep_list f) adds t"
    and "ord_term_lin.is_le_rel sing_reg" and "ordered_powerprod_lin.is_le_rel top_tail"
    and "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)" and "top_tail t (punit.lt (rep_list p))"
  shows "is_sig_red sing_reg top_tail F p"
  unfolding is_sig_red_def
proof
  let ?q = "p - monom_mult ((lookup (rep_list p) t) / punit.lc (rep_list f)) (t - punit.lt (rep_list f)) f"
  show "sig_red sing_reg top_tail F p ?q" unfolding sig_red_def
  proof (intro bexI exI)
    from assms(4) have eq: "(t - punit.lt (rep_list f)) + punit.lt (rep_list f) = t" by (rule adds_minus)
    from assms(4, 5, 7) have "sing_reg ((t - punit.lt (rep_list f)) \<oplus> lt f) (lt p)"
      by (simp only: term_is_le_rel_minus)
    thus "sig_red_single sing_reg top_tail p ?q f (t - punit.lt (rep_list f))"
      by (simp add: sig_red_single_def assms(1-6, 8) eq)
  qed fact
qed

lemma is_sig_red_addsE:
  assumes "is_sig_red sing_reg top_tail F p"
  obtains f t where "f \<in> F" and "t \<in> keys (rep_list p)" and "rep_list f \<noteq> 0"
    and "punit.lt (rep_list f) adds t"
    and "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    and "top_tail t (punit.lt (rep_list p))"
proof -
  from assms have *: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  from assms obtain q where "sig_red sing_reg top_tail F p q" unfolding is_sig_red_def ..
  then obtain f s where "f \<in> F" and "sig_red_single sing_reg top_tail p q f s" unfolding sig_red_def by blast
  from this(2) have 1: "rep_list f \<noteq> 0" and 2: "s + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and 3: "sing_reg (s \<oplus> lt f) (lt p)" and 4: "top_tail (s + punit.lt (rep_list f)) (punit.lt (rep_list p))"
    by (rule sig_red_singleD)+
  note \<open>f \<in> F\<close> 2 1
  moreover have "punit.lt (rep_list f) adds s + punit.lt (rep_list f)" by simp
  moreover from 3 have "sing_reg ((s + punit.lt (rep_list f)) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (simp add: add.commute[of s] splus_assoc term_is_le_rel_canc_left[OF *])
  moreover from 4 have "top_tail (s + punit.lt (rep_list f)) (punit.lt (rep_list p))" by simp
  ultimately show ?thesis ..
qed

lemma is_sig_red_top_addsI:
  assumes "f \<in> F" and "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and "punit.lt (rep_list f) adds punit.lt (rep_list p)" and "ord_term_lin.is_le_rel sing_reg"
    and "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
  shows "is_sig_red sing_reg (=) F p"
proof -
  note assms(1)
  moreover from assms(3) have "punit.lt (rep_list p) \<in> keys (rep_list p)" by (rule punit.lt_in_keys)
  moreover note assms(2, 4, 5) ordered_powerprod_lin.is_le_relI(1) assms(6) refl
  ultimately show ?thesis by (rule is_sig_red_addsI)
qed

lemma is_sig_red_top_addsE:
  assumes "is_sig_red sing_reg (=) F p"
  obtains f where "f \<in> F" and "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and "punit.lt (rep_list f) adds punit.lt (rep_list p)"
    and "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
proof -
  from assms obtain f t where 1: "f \<in> F" and 2: "t \<in> keys (rep_list p)" and 3: "rep_list f \<noteq> 0"
    and 4: "punit.lt (rep_list f) adds t"
    and 5: "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    and t: "t = punit.lt (rep_list p)" by (rule is_sig_red_addsE)
  note 1 3
  moreover from 2 have "rep_list p \<noteq> 0" by auto
  moreover from 4 have "punit.lt (rep_list f) adds punit.lt (rep_list p)" by (simp only: t)
  moreover from 5 have "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (simp only: t)
  ultimately show ?thesis ..
qed

lemma is_sig_red_top_plusE:
  assumes "is_sig_red sing_reg (=) F p" and "is_sig_red sing_reg (=) F q"
    and "lt p \<preceq>\<^sub>t lt (p + q)" and "lt q \<preceq>\<^sub>t lt (p + q)" and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  assumes 1: "is_sig_red sing_reg (=) F (p + q) \<Longrightarrow> thesis"
  assumes 2: "punit.lt (rep_list p) = punit.lt (rep_list q) \<Longrightarrow> punit.lc (rep_list p) + punit.lc (rep_list q) = 0 \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) obtain f1 where "f1 \<in> F" and "rep_list f1 \<noteq> 0" and "rep_list p \<noteq> 0"
    and a: "punit.lt (rep_list f1) adds punit.lt (rep_list p)"
    and b: "sing_reg (punit.lt (rep_list p) \<oplus> lt f1) (punit.lt (rep_list f1) \<oplus> lt p)"
    by (rule is_sig_red_top_addsE)
  from assms(2) obtain f2 where "f2 \<in> F" and "rep_list f2 \<noteq> 0" and "rep_list q \<noteq> 0"
    and c: "punit.lt (rep_list f2) adds punit.lt (rep_list q)"
    and d: "sing_reg (punit.lt (rep_list q) \<oplus> lt f2) (punit.lt (rep_list f2) \<oplus> lt q)"
    by (rule is_sig_red_top_addsE)
  show ?thesis
  proof (cases "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> punit.lc (rep_list p) + punit.lc (rep_list q) = 0")
    case True
    hence "punit.lt (rep_list p) = punit.lt (rep_list q)" and "punit.lc (rep_list p) + punit.lc (rep_list q) = 0"
      by simp_all
    thus ?thesis by (rule 2)
  next
    case False
    hence disj: "punit.lt (rep_list p) \<noteq> punit.lt (rep_list q) \<or> punit.lc (rep_list p) + punit.lc (rep_list q) \<noteq> 0"
      by simp
    from assms(5) have "ord_term_lin.is_le_rel sing_reg" by (simp add: ord_term_lin.is_le_rel_def)
    have "rep_list (p + q) \<noteq> 0" unfolding rep_list_plus
    proof
      assume eq: "rep_list p + rep_list q = 0"
      have eq2: "punit.lt (rep_list p) = punit.lt (rep_list q)"
      proof (rule ordered_powerprod_lin.linorder_cases)
        assume *: "punit.lt (rep_list p) \<prec> punit.lt (rep_list q)"
        hence "punit.lt (rep_list p + rep_list q) = punit.lt (rep_list q)" by (rule punit.lt_plus_eqI)
        with * zero_min[of "punit.lt (rep_list p)"] show ?thesis by (simp add: eq)
      next
        assume *: "punit.lt (rep_list q) \<prec> punit.lt (rep_list p)"
        hence "punit.lt (rep_list p + rep_list q) = punit.lt (rep_list p)" by (rule punit.lt_plus_eqI_2)
        with * zero_min[of "punit.lt (rep_list q)"] show ?thesis by (simp add: eq)
      qed
      with disj have "punit.lc (rep_list p) + punit.lc (rep_list q) \<noteq> 0" by simp
      thus False by (simp add: punit.lc_def eq2 lookup_add[symmetric] eq)
    qed
    have "punit.lt (rep_list (p + q)) = ordered_powerprod_lin.max (punit.lt (rep_list p)) (punit.lt (rep_list q))"
      unfolding rep_list_plus
    proof (rule punit.lt_plus_eq_maxI)
      assume "punit.lt (rep_list p) = punit.lt (rep_list q)"
      with disj show "punit.lc (rep_list p) + punit.lc (rep_list q) \<noteq> 0" by simp
    qed
    hence "punit.lt (rep_list (p + q)) = punit.lt (rep_list p) \<or> punit.lt (rep_list (p + q)) = punit.lt (rep_list q)"
      by (simp add: ordered_powerprod_lin.max_def)
    thus ?thesis
    proof
      assume eq: "punit.lt (rep_list (p + q)) = punit.lt (rep_list p)"
      show ?thesis
      proof (rule 1, rule is_sig_red_top_addsI)
        from a show "punit.lt (rep_list f1) adds punit.lt (rep_list (p + q))" by (simp only: eq)
      next
        from b have "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f1) (punit.lt (rep_list f1) \<oplus> lt p)"
          by (simp only: eq)
        moreover from assms(3) have "... \<preceq>\<^sub>t punit.lt (rep_list f1) \<oplus> lt (p + q)" by (rule splus_mono)
        ultimately show "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f1) (punit.lt (rep_list f1) \<oplus> lt (p + q))"
          using assms(5) by auto
      qed fact+
    next
      assume eq: "punit.lt (rep_list (p + q)) = punit.lt (rep_list q)"
      show ?thesis
      proof (rule 1, rule is_sig_red_top_addsI)
        from c show "punit.lt (rep_list f2) adds punit.lt (rep_list (p + q))" by (simp only: eq)
      next
        from d have "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f2) (punit.lt (rep_list f2) \<oplus> lt q)"
          by (simp only: eq)
        moreover from assms(4) have "... \<preceq>\<^sub>t punit.lt (rep_list f2) \<oplus> lt (p + q)" by (rule splus_mono)
        ultimately show "sing_reg (punit.lt (rep_list (p + q)) \<oplus> lt f2) (punit.lt (rep_list f2) \<oplus> lt (p + q))"
          using assms(5) by auto
      qed fact+
    qed
  qed
qed

lemma is_sig_red_cong':
  assumes "is_sig_red sing_reg top_tail F p" and "lt p = lt q" and "rep_list p = rep_list q"
  shows "is_sig_red sing_reg top_tail F q"
proof -
  from assms(1) have 1: "ord_term_lin.is_le_rel sing_reg" and 2: "ordered_powerprod_lin.is_le_rel top_tail"
    by (rule is_sig_redD1, rule is_sig_redD2)
  from assms(1) obtain f t where "f \<in> F" and "t \<in> keys (rep_list p)" and "rep_list f \<noteq> 0"
    and "punit.lt (rep_list f) adds t"
    and "sing_reg (t \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    and "top_tail t (punit.lt (rep_list p))" by (rule is_sig_red_addsE)
  from this(1-4) 1 2 this(5, 6) show ?thesis unfolding assms(2, 3) by (rule is_sig_red_addsI)
qed

lemma is_sig_red_cong:
  "lt p = lt q \<Longrightarrow> rep_list p = rep_list q \<Longrightarrow>
      is_sig_red sing_reg top_tail F p \<longleftrightarrow> is_sig_red sing_reg top_tail F q"
  by (auto intro: is_sig_red_cong')

lemma is_sig_red_top_cong:
  assumes "is_sig_red sing_reg (=) F p" and "rep_list q \<noteq> 0" and "lt p = lt q"
    and "punit.lt (rep_list p) = punit.lt (rep_list q)"
  shows "is_sig_red sing_reg (=) F q"
proof -
  from assms(1) have 1: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  from assms(1) obtain f where "f \<in> F" and "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and "punit.lt (rep_list f) adds punit.lt (rep_list p)"
    and "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (rule is_sig_red_top_addsE)
  from this(1, 2) assms(2) this(4) 1 this(5) show ?thesis
    unfolding assms(3, 4) by (rule is_sig_red_top_addsI)
qed

lemma sig_irredE_dgrad_max_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_max_set d"
  obtains q where "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q" and "\<not> is_sig_red sing_reg top_tail F q"
proof -
  let ?Q = "{q. (sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q}"
  from assms have "wfP (sig_red sing_reg top_tail F)\<inverse>\<inverse>" by (rule sig_red_wf_dgrad_max_set)
  moreover have "p \<in> ?Q" by simp
  ultimately obtain q where "q \<in> ?Q" and "\<And>x. (sig_red sing_reg top_tail F)\<inverse>\<inverse> x q \<Longrightarrow> x \<notin> ?Q"
    by (rule wfE_min[to_pred], blast)
  hence 1: "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q"
    and 2: "\<And>x. sig_red sing_reg top_tail F q x \<Longrightarrow> \<not> (sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p x"
    by simp_all
  show ?thesis
  proof
    show "\<not> is_sig_red sing_reg top_tail F q"
    proof
      assume "is_sig_red sing_reg top_tail F q"
      then obtain x where 3: "sig_red sing_reg top_tail F q x" unfolding is_sig_red_def ..
      hence "\<not> (sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p x" by (rule 2)
      moreover from 1 3 have "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p x" ..
      ultimately show False ..
    qed
  qed fact
qed

subsubsection \<open>Signature Gr\"obner Bases\<close>

definition sig_red_zero :: "('t \<Rightarrow>'t \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "sig_red_zero sing_reg F r \<longleftrightarrow> (\<exists>s. (sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s \<and> rep_list s = 0)"

definition is_sig_GB_in :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_sig_GB_in d G u \<longleftrightarrow> (\<forall>r. lt r = u \<longrightarrow> r \<in> dgrad_max_set d \<longrightarrow> sig_red_zero (\<preceq>\<^sub>t) G r)"

definition is_sig_GB_upt :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_sig_GB_upt d G u \<longleftrightarrow>
            (G \<subseteq> dgrad_max_set d \<and> (\<forall>v. v \<prec>\<^sub>t u \<longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<longrightarrow> is_sig_GB_in d G v))"

lemma sig_red_zeroI:
  assumes "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
  shows "sig_red_zero sing_reg F r"
  unfolding sig_red_zero_def using assms by blast

lemma sig_red_zeroE:
  assumes "sig_red_zero sing_reg F r"
  obtains s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
  using assms unfolding sig_red_zero_def by blast

lemma sig_red_zero_sing_regI:
  assumes "sig_red_zero sing_reg G p"
  shows "sig_red_zero (\<preceq>\<^sub>t) G p"
proof -
  from assms obtain s where "(sig_red sing_reg (\<preceq>) G)\<^sup>*\<^sup>* p s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) have "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* p s" by (rule sig_red_rtrancl_sing_regI)
  thus ?thesis using \<open>rep_list s = 0\<close> by (rule sig_red_zeroI)
qed

lemma sig_red_zero_nonzero:
  assumes "sig_red_zero sing_reg F r" and "rep_list r \<noteq> 0" and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  shows "is_sig_red sing_reg (=) F r"
proof -
  from assms(1) obtain s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) assms(2) show ?thesis
  proof (induct rule: converse_rtranclp_induct)
    case base
    thus ?case using \<open>rep_list s = 0\<close> ..
  next
    case (step y z)
    from step(1) obtain f t where "f \<in> F" and *: "sig_red_single sing_reg (\<preceq>) y z f t"
      unfolding sig_red_def by blast
    from this(2) have 1: "rep_list f \<noteq> 0" and 2: "t + punit.lt (rep_list f) \<in> keys (rep_list y)"
      and 3: "z = y - monom_mult (lookup (rep_list y) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t f"
      and 4: "ord_term_lin.is_le_rel sing_reg" and 5: "sing_reg (t \<oplus> lt f) (lt y)"
      by (rule sig_red_singleD)+
    show ?case
    proof (cases "t + punit.lt (rep_list f) = punit.lt (rep_list y)")
      case True
      show ?thesis unfolding is_sig_red_def
      proof
        show "sig_red sing_reg (=) F y z" unfolding sig_red_def
        proof (intro bexI exI)
          from 1 2 3 4 ordered_powerprod_lin.is_le_relI(1) 5 True
          show "sig_red_single sing_reg (=) y z f t" by (rule sig_red_singleI)
        qed fact
      qed
    next
      case False
      from 2 have "t + punit.lt (rep_list f) \<preceq> punit.lt (rep_list y)" by (rule punit.lt_max_keys)
      with False have "t + punit.lt (rep_list f) \<prec> punit.lt (rep_list y)" by simp
      with 1 2 3 4 ordered_powerprod_lin.is_le_relI(3) 5 have "sig_red_single sing_reg (\<prec>) y z f t"
        by (rule sig_red_singleI)
      hence "punit.lt (rep_list y) \<in> keys (rep_list z)"
        and lt_z: "punit.lt (rep_list z) = punit.lt (rep_list y)"
        by (rule sig_red_single_tail_lt_in_keys_rep_list, rule sig_red_single_tail_lt_rep_list)
      from this(1) have "rep_list z \<noteq> 0" by auto
      hence "is_sig_red sing_reg (=) F z" by (rule step(3))
      then obtain g where "g \<in> F" and "rep_list g \<noteq> 0"
        and "punit.lt (rep_list g) adds punit.lt (rep_list z)"
        and a: "sing_reg (punit.lt (rep_list z) \<oplus> lt g) (punit.lt (rep_list g) \<oplus> lt z)"
        by (rule is_sig_red_top_addsE)
      from this(3) have "punit.lt (rep_list g) adds punit.lt (rep_list y)" by (simp only: lt_z)
      with \<open>g \<in> F\<close> \<open>rep_list g \<noteq> 0\<close> step(4) show ?thesis
      proof (rule is_sig_red_top_addsI)
        from \<open>is_sig_red sing_reg (=) F z\<close> show "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
      next
        from \<open>sig_red_single sing_reg (\<prec>) y z f t\<close> have "lt z \<preceq>\<^sub>t lt y" by (rule sig_red_single_lt)
        from assms(3) show "sing_reg (punit.lt (rep_list y) \<oplus> lt g) (punit.lt (rep_list g) \<oplus> lt y)"
        proof
          assume "sing_reg = (\<preceq>\<^sub>t)"
          from a have "punit.lt (rep_list y) \<oplus> lt g \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt z"
            by (simp only: lt_z \<open>sing_reg = (\<preceq>\<^sub>t)\<close>)
          also from \<open>lt z \<preceq>\<^sub>t lt y\<close> have "... \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt y" by (rule splus_mono)
          finally show ?thesis by (simp only: \<open>sing_reg = (\<preceq>\<^sub>t)\<close>)
        next
          assume "sing_reg = (\<prec>\<^sub>t)"
          from a have "punit.lt (rep_list y) \<oplus> lt g \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt z"
            by (simp only: lt_z \<open>sing_reg = (\<prec>\<^sub>t)\<close>)
          also from \<open>lt z \<preceq>\<^sub>t lt y\<close> have "... \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt y" by (rule splus_mono)
          finally show ?thesis by (simp only: \<open>sing_reg = (\<prec>\<^sub>t)\<close>)
        qed
      qed
    qed
  qed
qed

lemma sig_red_weak_cong:
  assumes "sig_red sing_reg top_tail F p p'" and "lt p \<prec>\<^sub>t lt q" and "rep_list q = rep_list p"
    and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  obtains q' where "sig_red sing_reg top_tail F q q'" and "lt p' \<prec>\<^sub>t lt q'" and "rep_list q' = rep_list p'"
proof -
  from assms(1) obtain f t where "f \<in> F" and "sig_red_single sing_reg top_tail p p' f t"
    unfolding sig_red_def by blast
  from this(2) have "rep_list f \<noteq> 0" and t: "t + punit.lt (rep_list f) \<in> keys (rep_list p)"
    and p': "p' = p - monom_mult ((lookup (rep_list p) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
    and 1: "ord_term_lin.is_le_rel sing_reg" and 2: "ordered_powerprod_lin.is_le_rel top_tail"
    and 3: "sing_reg (t \<oplus> lt f) (lt p)" and 4: "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list p))"
    by (rule sig_red_singleD)+

  let ?q = "q - monom_mult ((lookup (rep_list q) (t + punit.lt (rep_list f))) / punit.lc (rep_list f)) t f"
  show ?thesis
  proof
    show "sig_red sing_reg top_tail F q ?q" unfolding sig_red_def
    proof (intro bexI exI)
      note \<open>rep_list f \<noteq> 0\<close>
      moreover from t have "t + punit.lt (rep_list f) \<in> keys (rep_list q)" by (simp only: assms(3))
      moreover note refl 1 2
      moreover from assms(4) have "sing_reg (t \<oplus> lt f) (lt q)"
      proof
        assume a: "sing_reg = (\<preceq>\<^sub>t)"
        from 3 have "t \<oplus> lt f \<preceq>\<^sub>t lt p" by (simp only: a)
        also have "... \<prec>\<^sub>t lt q" by (fact assms(2))
        finally show ?thesis by (simp only: a)
      next
        assume a: "sing_reg = (\<prec>\<^sub>t)"
        from 3 have "t \<oplus> lt f \<prec>\<^sub>t lt p" by (simp only: a)
        also have "... \<prec>\<^sub>t lt q" by (fact assms(2))
        finally show ?thesis by (simp only: a)
      qed
      moreover from 4 have "top_tail (t + punit.lt (rep_list f)) (punit.lt (rep_list q))"
        by (simp only: assms(3))
      ultimately show "sig_red_single sing_reg top_tail q ?q f t" by (rule sig_red_singleI)
    qed fact
  next
    from assms(1) have "lt p' \<preceq>\<^sub>t lt p" by (rule sig_red_lt)
    also have "... \<prec>\<^sub>t lt q" by (fact assms(2))
    also have "... = lt (q + monom_mult (- (lookup (rep_list q) (t + punit.lt (rep_list f)) / punit.lc (rep_list f))) t f)"
    proof (rule HOL.sym, rule lt_plus_eqI_2)
      have "lt (monom_mult (- (lookup (rep_list q) (t + punit.lt (rep_list f)) / punit.lc (rep_list f))) t f) \<preceq>\<^sub>t t \<oplus> lt f"
        by (fact lt_monom_mult_le)
      also from assms(4) 3 have "... \<preceq>\<^sub>t lt p" by auto
      also have "... \<prec>\<^sub>t lt q" by (fact assms(2))
      finally show "lt (monom_mult (- (lookup (rep_list q) (t + punit.lt (rep_list f)) / punit.lc (rep_list f))) t f) \<prec>\<^sub>t lt q" .
    qed
    also have "... = lt ?q" by (simp add: monom_mult_uminus_left)
    finally show "lt p' \<prec>\<^sub>t lt ?q" .
  next
    show "rep_list ?q = rep_list p'" by (simp add: p' rep_list_minus assms(3))
  qed
qed

lemma sig_red_rtrancl_weak_cong:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p p'" and "lt p \<prec>\<^sub>t lt q" and "rep_list q = rep_list p"
    and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  obtains q' where "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* q q'" and "lt p' \<prec>\<^sub>t lt q'" and "rep_list q' = rep_list p'"
  using assms(1, 2, 3)
proof (induct p arbitrary: thesis q rule: converse_rtranclp_induct)
  case base
  from rtrancl_refl[to_pred] base(2, 3) show ?case by (rule base(1))
next
  case (step y z)
  from step(1, 5, 6) assms(4) obtain q0 where "sig_red sing_reg top_tail F q q0"
    and "lt z \<prec>\<^sub>t lt q0" and "rep_list q0 = rep_list z" by (rule sig_red_weak_cong)
  from step(3)[OF _ this(2, 3)] obtain q' where "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* q0 q'"
    and "lt p' \<prec>\<^sub>t lt q'" and "rep_list q' = rep_list p'" by blast
  from \<open>sig_red sing_reg top_tail F q q0\<close> this(1) have "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* q q'" by simp
  thus ?case using \<open>lt p' \<prec>\<^sub>t lt q'\<close> \<open>rep_list q' = rep_list p'\<close> by (rule step(4))
qed

corollary sig_red_zero_weak_cong:
  assumes "sig_red_zero sing_reg G p" and "lt p \<prec>\<^sub>t lt q" and "rep_list q = rep_list p"
    and "sing_reg = (\<preceq>\<^sub>t) \<or> sing_reg = (\<prec>\<^sub>t)"
  shows "sig_red_zero sing_reg G q"
proof -
  from assms(1) obtain s where "(sig_red sing_reg (\<preceq>) G)\<^sup>*\<^sup>* p s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) assms(2, 3, 4) obtain s' where "(sig_red sing_reg (\<preceq>) G)\<^sup>*\<^sup>* q s'"
    and "rep_list s' = rep_list s" by (rule sig_red_rtrancl_weak_cong)
  from this(2) have "rep_list s' = 0" by (simp only: \<open>rep_list s = 0\<close>)
  with \<open>(sig_red sing_reg (\<preceq>) G)\<^sup>*\<^sup>* q s'\<close> show ?thesis by (rule sig_red_zeroI)
qed

lemma is_sig_GB_inI:
  assumes "\<And>r. lt r = u \<Longrightarrow> r \<in> dgrad_max_set d \<Longrightarrow> sig_red_zero (\<preceq>\<^sub>t) G r"
  shows "is_sig_GB_in d G u"
  unfolding is_sig_GB_in_def using assms by blast

lemma is_sig_GB_inD:
  assumes "is_sig_GB_in d G u" and "r \<in> dgrad_max_set d" and "lt r = u"
  shows "sig_red_zero (\<preceq>\<^sub>t) G r"
  using assms unfolding is_sig_GB_in_def by blast

lemma is_sig_GB_inI_triv:
  assumes "\<not> d (pp_of_term u) \<le> dgrad_max d"
  shows "is_sig_GB_in d G u"
proof (rule is_sig_GB_inI)
  fix r::"'t \<Rightarrow>\<^sub>0 'b"
  assume "lt r = u" and "r \<in> dgrad_max_set d"
  show "sig_red_zero (\<preceq>\<^sub>t) G r"
  proof (cases "r = 0")
    case True
    hence "rep_list r = 0" by (simp only: rep_list_zero)
    with rtrancl_refl[to_pred] show ?thesis by (rule sig_red_zeroI)
  next
    case False
    with \<open>r \<in> dgrad_max_set d\<close> have "d (lp r) \<le> dgrad_max d" by (rule dgrad_p_setD_lt)
    with assms show ?thesis unfolding \<open>lt r = u\<close> ..
  qed
qed

lemma is_sig_GB_uptI:
  assumes "G \<subseteq> dgrad_max_set d" and "\<And>v. v \<prec>\<^sub>t u \<Longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<Longrightarrow> is_sig_GB_in d G v"
  shows "is_sig_GB_upt d G u"
  unfolding is_sig_GB_upt_def using assms by blast

lemma is_sig_GB_uptD1:
  assumes "is_sig_GB_upt d G u"
  shows "G \<subseteq> dgrad_max_set d"
  using assms unfolding is_sig_GB_upt_def by blast

lemma is_sig_GB_uptD2:
  assumes "is_sig_GB_upt d G u" and "v \<prec>\<^sub>t u"
  shows "is_sig_GB_in d G v"
  using assms is_sig_GB_inI_triv unfolding is_sig_GB_upt_def by blast

lemma is_sig_GB_uptD3:
  assumes "is_sig_GB_upt d G u" and "r \<in> dgrad_max_set d" and "lt r \<prec>\<^sub>t u"
  shows "sig_red_zero (\<preceq>\<^sub>t) G r"
  by (rule is_sig_GB_inD, rule is_sig_GB_uptD2, fact+, fact refl)

lemma is_sig_GB_imp_is_Groebner_basis:
  assumes "dickson_grading (+) d" and "hom_grading d" and "G \<subseteq> dgrad_max_set d" and "\<And>u. is_sig_GB_in d G u"
  shows "punit.is_Groebner_basis (rep_list ` G)"
  using assms(1)
proof (rule punit.weak_GB_is_strong_GB_dgrad_p_set[simplified])
  from assms(1, 3) show "rep_list ` G \<subseteq> punit_dgrad_max_set d" by (rule dgrad_max_3)
next
  fix f::"'a \<Rightarrow>\<^sub>0 'b"
  assume "f \<in> punit_dgrad_max_set d"
  assume "f \<in> ideal (rep_list ` G)"
  also from rep_list_subset_ideal have "... \<subseteq> ideal (set fs)" by (rule ideal.module_subset_moduleI)
  finally have "f \<in> ideal (set fs)" .
  with assms(2) \<open>f \<in> punit_dgrad_max_set d\<close> obtain r where "r \<in> dgrad_max_set d" and f: "f = rep_list r"
    by (rule in_idealE_rep_list_dgrad_max_set)
  from assms(4) this(1) refl have "sig_red_zero (\<preceq>\<^sub>t) G r" by (rule is_sig_GB_inD)
  then obtain s where "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s" and s: "rep_list s = 0" by (rule sig_red_zeroE)
  from this(1) have "(punit.red (rep_list ` G))\<^sup>*\<^sup>* (rep_list r) (rep_list s)"
    by (rule sig_red_red_rtrancl)
  thus "(punit.red (rep_list ` G))\<^sup>*\<^sup>* f 0" by (simp only: f s)
qed

lemma sig_red_zero_is_red:
  assumes "sig_red_zero sing_reg F r" and "rep_list r \<noteq> 0"
  shows "is_sig_red sing_reg (\<preceq>) F r"
proof -
  from assms(1) obtain s where *: "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(2) assms(2) have "r \<noteq> s" by auto
  with * show ?thesis by (induct rule: converse_rtranclp_induct, auto simp: is_sig_red_def)
qed

lemma sig_regular_reduced_unique:
  assumes "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_max_set d" and "q \<in> dgrad_max_set d"
    and "lt p = lt q" and "lc p = lc q" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q"
  shows "rep_list p = rep_list q"
proof (rule ccontr)
  assume "rep_list p \<noteq> rep_list q"
  hence "rep_list (p - q) \<noteq> 0" by (auto simp: rep_list_minus)
  hence "p - q \<noteq> 0" by (auto simp: rep_list_zero)
  hence "p + (- q) \<noteq> 0" by simp
  moreover from assms(4) have "lt (- q) = lt p" by simp
  moreover from assms(5) have "lc (- q) = - lc p" by simp
  ultimately have "lt (p + (- q)) \<prec>\<^sub>t lt p" by (rule lt_plus_lessI)
  hence "lt (p - q) \<prec>\<^sub>t lt q" using assms(4) by simp
  with assms(1) have "is_sig_GB_in d G (lt (p - q))" by (rule is_sig_GB_uptD2)
  moreover from assms(2, 3) have "p - q \<in> dgrad_max_set d" by (rule dgrad_p_set_closed_minus)
  ultimately have "sig_red_zero (\<preceq>\<^sub>t) G (p - q)" using refl by (rule is_sig_GB_inD)
  hence "is_sig_red (\<preceq>\<^sub>t) (\<preceq>) G (p - q)" using \<open>rep_list (p - q) \<noteq> 0\<close> by (rule sig_red_zero_is_red)
  then obtain g t where "g \<in> G" and t: "t \<in> keys (rep_list (p - q))" and "rep_list g \<noteq> 0"
    and adds: "punit.lt (rep_list g) adds t" and "t \<oplus> lt g \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt (p - q)"
    by (rule is_sig_red_addsE)
  note this(5)
  also from \<open>lt (p - q) \<prec>\<^sub>t lt q\<close> have "punit.lt (rep_list g) \<oplus> lt (p - q) \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt q"
    by (rule splus_mono_strict)
  finally have 1: "t \<oplus> lt g \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt q" .
  hence 2: "t \<oplus> lt g \<prec>\<^sub>t punit.lt (rep_list g) \<oplus> lt p" by (simp only: assms(4))
  from t keys_minus have "t \<in> keys (rep_list p) \<union> keys (rep_list q)" unfolding rep_list_minus ..
  thus False
  proof
    assume t_in: "t \<in> keys (rep_list p)"
    hence "t \<preceq> punit.lt (rep_list p)" by (rule punit.lt_max_keys)
    with \<open>g \<in> G\<close> t_in \<open>rep_list g \<noteq> 0\<close> adds ord_term_lin.is_le_relI(3) ordered_powerprod_lin.is_le_relI(2) 2
    have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" by (rule is_sig_red_addsI)
    with assms(6) show False ..
  next
    assume t_in: "t \<in> keys (rep_list q)"
    hence "t \<preceq> punit.lt (rep_list q)" by (rule punit.lt_max_keys)
    with \<open>g \<in> G\<close> t_in \<open>rep_list g \<noteq> 0\<close> adds ord_term_lin.is_le_relI(3) ordered_powerprod_lin.is_le_relI(2) 1
    have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q" by (rule is_sig_red_addsI)
    with assms(7) show False ..
  qed
qed

corollary sig_regular_reduced_unique':
  assumes "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_max_set d" and "q \<in> dgrad_max_set d"
    and "lt p = lt q" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q"
  shows "punit.monom_mult (lc q) 0 (rep_list p) = punit.monom_mult (lc p) 0 (rep_list q)"
proof (cases "p = 0 \<or> q = 0")
  case True
  thus ?thesis by (auto simp: rep_list_zero)
next
  case False
  hence "p \<noteq> 0" and "q \<noteq> 0" by simp_all
  hence "lc p \<noteq> 0" and "lc q \<noteq> 0" by (simp_all add: lc_not_0)
  let ?p = "monom_mult (lc q) 0 p"
  let ?q = "monom_mult (lc p) 0 q"
  have "lt ?q = lt q" by (simp add: lt_monom_mult[OF \<open>lc p \<noteq> 0\<close> \<open>q \<noteq> 0\<close>] splus_zero)
  with assms(1) have "is_sig_GB_upt d G (lt ?q)" by simp
  moreover from assms(2) have "?p \<in> dgrad_max_set d" by (rule dgrad_p_set_closed_monom_mult_zero)
  moreover from assms(3) have "?q \<in> dgrad_max_set d" by (rule dgrad_p_set_closed_monom_mult_zero)
  moreover from \<open>lt ?q = lt q\<close> have "lt ?p = lt ?q"
    by (simp add: lt_monom_mult[OF \<open>lc q \<noteq> 0\<close> \<open>p \<noteq> 0\<close>] splus_zero assms(4))
  moreover have "lc ?p = lc ?q" by simp
  moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?p"
  proof
    assume "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?p"
    moreover from \<open>lc q \<noteq> 0\<close> have "1 / (lc q) \<noteq> 0" by simp
    ultimately have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G (monom_mult (1 / lc q) 0 ?p)" by (rule is_sig_red_monom_mult)
    hence "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p" by (simp add: monom_mult_assoc \<open>lc q \<noteq> 0\<close>)
    with assms(5) show False ..
  qed
  moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?q"
  proof
    assume "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G ?q"
    moreover from \<open>lc p \<noteq> 0\<close> have "1 / (lc p) \<noteq> 0" by simp
    ultimately have "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G (monom_mult (1 / lc p) 0 ?q)" by (rule is_sig_red_monom_mult)
    hence "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q" by (simp add: monom_mult_assoc \<open>lc p \<noteq> 0\<close>)
    with assms(6) show False ..
  qed
  ultimately have "rep_list ?p = rep_list ?q" by (rule sig_regular_reduced_unique)
  thus ?thesis by (simp only: rep_list_monom_mult)
qed

lemma sig_regular_top_reduced_lt_lc_unique:
  assumes "dickson_grading (+) d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_max_set d" and "q \<in> dgrad_max_set d"
    and "lt p = lt q" and "(p = 0) \<longleftrightarrow> (q = 0)" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  shows "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)"
proof (cases "p = 0")
  case True
  with assms(6) have "q = 0" by simp
  thus ?thesis by (simp add: True)
next
  case False
  with assms(6) have "q \<noteq> 0" by simp
  from False have "lc p \<noteq> 0" by (rule lc_not_0)
  from \<open>q \<noteq> 0\<close> have "lc q \<noteq> 0" by (rule lc_not_0)
  from assms(2) have G_sub: "G \<subseteq> dgrad_max_set d" by (rule is_sig_GB_uptD1)
  with assms(1) obtain p' where p'_red: "(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* p p'" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G p'"
    by (rule sig_irredE_dgrad_max_set)
  from this(1) have lt_p': "lt p' = lt p" and lt_p'': "punit.lt (rep_list p') = punit.lt (rep_list p)"
    and lc_p': "lc p' = lc p" and lc_p'': "punit.lc (rep_list p') = punit.lc (rep_list p)"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_tail_rtrancl_lt_rep_list,
        rule sig_red_regular_rtrancl_lc, rule sig_red_tail_rtrancl_lc_rep_list)
  have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p'"
  proof
    assume a: "is_sig_red (\<prec>\<^sub>t) (=) G p'"
    hence "rep_list p' \<noteq> 0" using is_sig_red_top_addsE by blast
    hence "rep_list p \<noteq> 0" using \<open>(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* p p'\<close>
      by (auto simp: punit.rtrancl_0 dest!: sig_red_red_rtrancl)
    with a have "is_sig_red (\<prec>\<^sub>t) (=) G p" using lt_p' lt_p'' by (rule is_sig_red_top_cong)
    with assms(7) show False ..
  qed
  with \<open>\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G p'\<close> have 1: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G p'" by (simp add: is_sig_red_top_tail_cases)
  from assms(1) G_sub obtain q' where q'_red: "(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* q q'" and "\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G q'"
    by (rule sig_irredE_dgrad_max_set)
  from this(1) have lt_q': "lt q' = lt q" and lt_q'': "punit.lt (rep_list q') = punit.lt (rep_list q)"
    and lc_q': "lc q' = lc q" and lc_q'': "punit.lc (rep_list q') = punit.lc (rep_list q)"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_tail_rtrancl_lt_rep_list,
        rule sig_red_regular_rtrancl_lc, rule sig_red_tail_rtrancl_lc_rep_list)
  have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q'"
  proof
    assume a: "is_sig_red (\<prec>\<^sub>t) (=) G q'"
    hence "rep_list q' \<noteq> 0" using is_sig_red_top_addsE by blast
    hence "rep_list q \<noteq> 0" using \<open>(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* q q'\<close>
      by (auto simp: punit.rtrancl_0 dest!: sig_red_red_rtrancl)
    with a have "is_sig_red (\<prec>\<^sub>t) (=) G q" using lt_q' lt_q'' by (rule is_sig_red_top_cong)
    with assms(8) show False ..
  qed
  with \<open>\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G q'\<close> have 2: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q'" by (simp add: is_sig_red_top_tail_cases)
  from assms(2) have "is_sig_GB_upt d G (lt q')" by (simp only: lt_q')
  moreover from assms(1) G_sub assms(3) p'_red have "p' \<in> dgrad_max_set d"
    by (rule dgrad_max_set_closed_sig_red_rtrancl)
  moreover from assms(1) G_sub assms(4) q'_red have "q' \<in> dgrad_max_set d"
    by (rule dgrad_max_set_closed_sig_red_rtrancl)
  moreover have "lt p' = lt q'" by (simp only: lt_p' lt_q' assms(5))
  ultimately have eq: "punit.monom_mult (lc q') 0 (rep_list p') = punit.monom_mult (lc p') 0 (rep_list q')"
    using 1 2 by (rule sig_regular_reduced_unique')

  have "lc q * punit.lc (rep_list p) = lc q * punit.lc (rep_list p')" by (simp only: lc_p'')
  also from \<open>lc q \<noteq> 0\<close> have "... = punit.lc (punit.monom_mult (lc q') 0 (rep_list p'))"
    by (simp add: lc_q')
  also have "... = punit.lc (punit.monom_mult (lc p') 0 (rep_list q'))" by (simp only: eq)
  also from \<open>lc p \<noteq> 0\<close> have "... = lc p * punit.lc (rep_list q')" by (simp add: lc_p')
  also have "... = lc p * punit.lc (rep_list q)" by (simp only: lc_q'')
  finally have *: "lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)" .

  have "punit.lt (rep_list p) = punit.lt (rep_list p')" by (simp only: lt_p'')
  also from \<open>lc q \<noteq> 0\<close> have "... = punit.lt (punit.monom_mult (lc q') 0 (rep_list p'))"
    by (simp add: lc_q' punit.lt_monom_mult_zero)
  also have "... = punit.lt (punit.monom_mult (lc p') 0 (rep_list q'))" by (simp only: eq)
  also from \<open>lc p \<noteq> 0\<close> have "... = punit.lt (rep_list q')" by (simp add: lc_p' punit.lt_monom_mult_zero)
  also have "... = punit.lt (rep_list q)" by (fact lt_q'')
  finally show ?thesis using * ..
qed

corollary sig_regular_top_reduced_lt_unique:
  assumes "dickson_grading (+) d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_max_set d"
    and "q \<in> dgrad_max_set d" and "lt p = lt q" and "p \<noteq> 0" and "q \<noteq> 0"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  shows "punit.lt (rep_list p) = punit.lt (rep_list q)"
proof -
  from assms(6, 7) have "(p = 0) \<longleftrightarrow> (q = 0)" by simp
  with assms(1, 2, 3, 4, 5)
  have "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)"
    using assms(8, 9) by (rule sig_regular_top_reduced_lt_lc_unique)
  thus ?thesis ..
qed

corollary sig_regular_top_reduced_lc_unique:
  assumes "dickson_grading (+) d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_max_set d" and "q \<in> dgrad_max_set d"
    and "lt p = lt q" and "lc p = lc q" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  shows "punit.lc (rep_list p) = punit.lc (rep_list q)"
proof (cases "p = 0")
  case True
  with assms(6) have "q = 0" by (simp add: lc_eq_zero_iff)
  with True show ?thesis by simp
next
  case False
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  hence "lc q \<noteq> 0" by (simp add: assms(6))
  hence "q \<noteq> 0" by (simp add: lc_eq_zero_iff)
  with False have "(p = 0) \<longleftrightarrow> (q = 0)" by simp
  with assms(1, 2, 3, 4, 5)
  have "punit.lt (rep_list p) = punit.lt (rep_list q) \<and> lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)"
    using assms(7, 8) by (rule sig_regular_top_reduced_lt_lc_unique)
  hence "lc q * punit.lc (rep_list p) = lc p * punit.lc (rep_list q)" ..
  also have "... = lc q * punit.lc (rep_list q)" by (simp only: assms(6))
  finally show ?thesis using \<open>lc q \<noteq> 0\<close> by simp
qed

lemma syzygy_crit:
  assumes "dickson_grading (+) d" and "is_sig_GB_upt d G (lt p)" and "u \<in> dgrad_max_set d"
    and "p \<in> dgrad_max_set d" and "lt u adds\<^sub>t lt p" and "u \<noteq> 0" and "rep_list u = 0"
  shows "sig_red_zero (\<preceq>\<^sub>t) G p"
proof (cases "rep_list p = 0")
  case True
  show ?thesis
  proof (rule sig_red_zeroI)
    show "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* p p" ..
  qed (fact True)
next
  case False
  hence "p \<noteq> 0" by (auto simp: rep_list_zero)
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  moreover from assms(6) have "lc u \<noteq> 0" by (rule lc_not_0)
  ultimately have 1: "- lc p / lc u \<noteq> 0" by simp
  from assms(5) obtain s where lt_p: "lt p = s \<oplus> lt u" by (rule adds_termE)
  let ?u = "monom_mult (- (lc p / lc u)) s u"
  from assms(1) _ assms(3) have "?u \<in> dgrad_max_set d"
  proof (rule dgrad_p_set_closed_monom_mult)
    from assms(4) \<open>p \<noteq> 0\<close> have "d (lp p) \<le> dgrad_max d" by (rule dgrad_p_setD_lt)
    hence "d (s + lp u) \<le> dgrad_max d" by (simp only: lt_p term_simps)
    with assms(1) show "d s \<le> dgrad_max d" by (simp add: dickson_gradingD1)
  qed
  with assms(4) have "p + ?u \<in> dgrad_max_set d" by (rule dgrad_p_set_closed_plus)
  have "rep_list ?u = 0" by (simp add: rep_list_monom_mult assms(7))
  hence "rep_list p = rep_list (p + ?u)" by (simp add: rep_list_plus)
  with False have "rep_list (p + ?u) \<noteq> 0" by simp
  hence "p + ?u \<noteq> 0" by (auto simp: rep_list_zero)
  moreover from 1 assms(6) have "lt ?u = lt p" by (simp add: lt_monom_mult lt_p)
  moreover from \<open>lc u \<noteq> 0\<close> have "lc p + lc ?u = 0" by simp
  ultimately have "lt (p + ?u) \<prec>\<^sub>t lt p" by (rule lt_plus_lessI')
  with assms(2) \<open>p + ?u \<in> dgrad_max_set d\<close> have "sig_red_zero (\<preceq>\<^sub>t) G (p + ?u)" by (rule is_sig_GB_uptD3)
  moreover note \<open>lt (p + ?u) \<prec>\<^sub>t lt p\<close> \<open>rep_list p = rep_list (p + ?u)\<close>
  moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
  ultimately show ?thesis by (rule sig_red_zero_weak_cong)
qed

subsubsection \<open>Rewrite Bases\<close>


subsubsection \<open>S-Pairs\<close>

definition sig_red_zero_or_sing_top_red :: "('t \<Rightarrow>'t \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "sig_red_zero_or_sing_top_red sing_reg F r \<longleftrightarrow>
                (\<exists>s. (sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s \<and> \<not> is_sig_red sing_reg (\<preceq>) F s \<and>
                     (rep_list s = 0 \<or> is_sig_red (=) (=) F s))"

definition spair :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where "spair p q = (let t1 = punit.lt (rep_list p); t2 = punit.lt (rep_list q); l = lcs t1 t2 in
                        (monom_mult (1 / punit.lc (rep_list p)) (l - t1) p) -
                        (monom_mult (1 / punit.lc (rep_list q)) (l - t2) q))"

definition is_regular_spair :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_regular_spair p q \<longleftrightarrow>
                    (rep_list p \<noteq> 0 \<and> rep_list q \<noteq> 0 \<and>
                      (let t1 = punit.lt (rep_list p); t2 = punit.lt (rep_list q); l = lcs t1 t2 in
                        lt (monom_mult (1 / punit.lc (rep_list p)) (l - t1) p) \<noteq>
                        lt (monom_mult (1 / punit.lc (rep_list q)) (l - t2) q)))"

lemma sig_red_zero_or_sing_top_redI:
  assumes "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "\<not> is_sig_red sing_reg (\<preceq>) F s"
    and "rep_list s = 0 \<or> is_sig_red (=) (=) F s"
  shows "sig_red_zero_or_sing_top_red sing_reg F r"
  unfolding sig_red_zero_or_sing_top_red_def using assms by blast

lemma sig_red_zero_or_sing_top_redE:
  assumes "sig_red_zero_or_sing_top_red sing_reg F r"
  obtains s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "\<not> is_sig_red sing_reg (\<preceq>) F s"
    and "rep_list s = 0 \<or> is_sig_red (=) (=) F s"
  using assms unfolding sig_red_zero_or_sing_top_red_def by blast

lemma sig_red_zero_or_sing_top_red_zero:
  assumes "rep_list r = 0"
  shows "sig_red_zero_or_sing_top_red sing_reg F r"
proof (rule sig_red_zero_or_sing_top_redI)
  show "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r r" ..
next
  from assms show "\<not> is_sig_red sing_reg (\<preceq>) F r" using is_sig_red_addsE by fastforce
next
  show "rep_list r = 0 \<or> is_sig_red (=) (=) F r" by (simp add: assms)
qed

lemma sig_red_zero_or_sing_top_red_monom_mult:
  assumes "sig_red_zero_or_sing_top_red sing_reg F r"
  shows "sig_red_zero_or_sing_top_red sing_reg F (monom_mult c 0 r)"
proof (cases "c = 0")
  case True
  hence "rep_list (monom_mult c 0 r) = 0" by (simp add: rep_list_zero)
  thus ?thesis by (rule sig_red_zero_or_sing_top_red_zero)
next
  case False
  from assms obtain s
    where 1: "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and 2: "\<not> is_sig_red sing_reg (\<preceq>) F s"
      and 3: "rep_list s = 0 \<or> is_sig_red (=) (=) F s"
    by (rule sig_red_zero_or_sing_top_redE)
  from 1 have "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* (monom_mult c 0 r) (monom_mult c 0 s)"
    by (rule sig_red_rtrancl_monom_mult)
  thus ?thesis
  proof (rule sig_red_zero_or_sing_top_redI)
    show "\<not> is_sig_red sing_reg (\<preceq>) F (monom_mult c 0 s)"
    proof
      assume "is_sig_red sing_reg (\<preceq>) F (monom_mult c 0 s)"
      moreover from False have "1 / c \<noteq> 0" by simp
      ultimately have "is_sig_red sing_reg (\<preceq>) F (monom_mult (1 / c) 0 (monom_mult c 0 s))"
        by (rule is_sig_red_monom_mult)
      with False have "is_sig_red sing_reg (\<preceq>) F s" by (simp add: monom_mult_assoc)
      with 2 show False ..
    qed
  next
    from 3 show "rep_list (monom_mult c 0 s) = 0 \<or> is_sig_red (=) (=) F (monom_mult c 0 s)"
    proof
      assume "rep_list s = 0"
      thus ?thesis by (simp add: rep_list_monom_mult)
    next
      assume "is_sig_red (=) (=) F s"
      hence "is_sig_red (=) (=) F (monom_mult c 0 s)" using False by (rule is_sig_red_monom_mult)
      thus ?thesis ..
    qed
  qed
qed

lemma singular_crit:
  assumes "dickson_grading (+) d" and "is_sig_GB_upt d G (lt p)" and "p \<in> dgrad_max_set d"
    and "q \<in> dgrad_max_set d" and "p \<noteq> 0" and "sig_red_zero_or_sing_top_red (\<prec>\<^sub>t) G p" and "lt q = lt p"
  shows "sig_red_zero_or_sing_top_red (\<prec>\<^sub>t) G q"
proof (cases "q = 0")
  case True
  hence "rep_list q = 0" by (simp only: rep_list_zero)
  thus ?thesis by (rule sig_red_zero_or_sing_top_red_zero)
next
  case False
  hence "lc q \<noteq> 0" by (rule lc_not_0)
  from assms(5) have "lc p \<noteq> 0" by (rule lc_not_0)
  from assms(2) have "G \<subseteq> dgrad_max_set d" by (rule is_sig_GB_uptD1)
  with assms(1) obtain s' where a: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* q s'" and b: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G s'"
    by (rule sig_irredE_dgrad_max_set)
  from a have lt_s': "lt s' = lt q" and lc_s': "lc s' = lc q"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
  from assms(6) obtain s where 1: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* p s" and 2: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G s"
    and 3: "rep_list s = 0 \<or> is_sig_red (=) (=) G s"
    by (rule sig_red_zero_or_sing_top_redE)
  from 1 have lt_s: "lt s = lt p" and lc_s: "lc s = lc p"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
  with assms(2) have "is_sig_GB_upt d G (lt s)" by simp
  moreover from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> assms(4) a have "s' \<in> dgrad_max_set d"
    by (rule dgrad_max_set_closed_sig_red_rtrancl)
  moreover from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> assms(3) 1 have "s \<in> dgrad_max_set d"
    by (rule dgrad_max_set_closed_sig_red_rtrancl)
  moreover have "lt s' = lt s" by (simp only: lt_s lt_s' assms(7))
  ultimately have eq: "punit.monom_mult (lc s) 0 (rep_list s') = punit.monom_mult (lc s') 0 (rep_list s)"
    using b 2 by (rule sig_regular_reduced_unique')
  from 3 show ?thesis
  proof
    assume "rep_list s = 0"
    with eq have "rep_list s' = 0" by (simp add: punit.monom_mult_eq_zero_iff lc_s \<open>lc p \<noteq> 0\<close>)
    hence "rep_list s' = 0 \<or> is_sig_red (=) (=) G s'" ..
    with a b show ?thesis by (rule sig_red_zero_or_sing_top_redI)
  next
    assume "is_sig_red (=) (=) G s"
    hence "is_sig_red (=) (=) G (monom_mult (lc s') 0 s)" unfolding lc_s' using \<open>lc q \<noteq> 0\<close>
      by (rule is_sig_red_monom_mult)
    moreover from \<open>lc p \<noteq> 0\<close> \<open>lc q \<noteq> 0\<close> have "lt (monom_mult (lc s') 0 s) = lt (monom_mult (lc s) 0 s')"
      by (simp add: lt_monom_mult_zero lc_s lc_s' \<open>lt s' = lt s\<close>)
    moreover have "rep_list (monom_mult (lc s') 0 s) = rep_list (monom_mult (lc s) 0 s')"
      by (simp only: rep_list_monom_mult eq)
    ultimately have "is_sig_red (=) (=) G (monom_mult (lc s) 0 s')" by (rule is_sig_red_cong')
    moreover from \<open>lc p \<noteq> 0\<close> have "1 / lc s \<noteq> 0" by (simp add: lc_s)
    ultimately have "is_sig_red (=) (=) G (monom_mult (1 / lc s) 0 (monom_mult (lc s) 0 s'))"
      by (rule is_sig_red_monom_mult)
    hence "is_sig_red (=) (=) G s'" using \<open>lc p \<noteq> 0\<close> by (simp add: lc_s monom_mult_assoc)
    hence "rep_list s' = 0 \<or> is_sig_red (=) (=) G s'" ..
    with a b show ?thesis by (rule sig_red_zero_or_sing_top_redI)
  qed
qed

lemma rep_list_spair: "rep_list (spair p q) = punit.spoly (rep_list p) (rep_list q)"
  by (simp add: spair_def punit.spoly_def Let_def rep_list_minus rep_list_monom_mult punit.lc_def)

lemma spair_comm: "spair p q = - spair q p"
  by (simp add: spair_def Let_def lcs_comm)

lemma lt_spair:
  assumes "rep_list p \<noteq> 0" and "punit.lt (rep_list p) \<oplus> lt q \<prec>\<^sub>t punit.lt (rep_list q) \<oplus> lt p"
  shows "lt (spair p q) = (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p"
proof -
  define l where "l = lcs (punit.lt (rep_list p)) (punit.lt (rep_list q))"
  have 1: "punit.lt (rep_list p) adds l" and 2: "punit.lt (rep_list q) adds l"
    unfolding l_def by (rule adds_lcs, rule adds_lcs_2)
  have eq1: "spair p q = (monom_mult (1 / punit.lc (rep_list p)) (l - punit.lt (rep_list p)) p) +
                         (monom_mult (- 1 / punit.lc (rep_list q)) (l - punit.lt (rep_list q)) q)"
    by (simp add: spair_def Let_def l_def monom_mult_uminus_left)
  from assms(1) have "punit.lc (rep_list p) \<noteq> 0" by (rule punit.lc_not_0)
  hence "1 / punit.lc (rep_list p) \<noteq> 0" by simp
  moreover from assms(1) have "p \<noteq> 0" by (auto simp: rep_list_zero)
  ultimately have eq2: "lt (monom_mult (1 / punit.lc (rep_list p)) (l - punit.lt (rep_list p)) p) =
                        (l - punit.lt (rep_list p)) \<oplus> lt p"
    by (rule lt_monom_mult)
  have "lt (monom_mult (- 1 / punit.lc (rep_list q)) (l - punit.lt (rep_list q)) q) \<preceq>\<^sub>t
                        (l - punit.lt (rep_list q)) \<oplus> lt q"
    by (fact lt_monom_mult_le)
  also from assms(2) have "... \<prec>\<^sub>t (l - punit.lt (rep_list p)) \<oplus> lt p"
    by (simp add: term_is_le_rel_minus_minus[OF _ 2 1])
  finally show ?thesis unfolding eq2[symmetric] eq1 l_def[symmetric] by (rule lt_plus_eqI_2)
qed

lemma lt_spair':
  assumes "rep_list p \<noteq> 0" and "a + punit.lt (rep_list p) = b + punit.lt (rep_list q)" and "b \<oplus> lt q \<prec>\<^sub>t a \<oplus> lt p"
  shows "lt (spair p q) = (a - gcs a b) \<oplus> lt p"
proof -
  from assms(3) have "punit.lt (rep_list p) \<oplus> (b \<oplus> lt q) \<prec>\<^sub>t punit.lt (rep_list p) \<oplus> (a \<oplus> lt p)"
    by (fact splus_mono_strict)
  hence "(b + punit.lt (rep_list p)) \<oplus> lt q \<prec>\<^sub>t (b + punit.lt (rep_list q)) \<oplus> lt p"
    by (simp only: splus_assoc[symmetric] add.commute assms(2))
  hence "punit.lt (rep_list p) \<oplus> lt q \<prec>\<^sub>t punit.lt (rep_list q) \<oplus> lt p"
    by (simp only: splus_assoc ord_term_strict_canc)
  with assms(1)
  have "lt (spair p q) = (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p"
    by (rule lt_spair)
  with assms(2) show ?thesis by (simp add: lcs_minus_1)
qed

lemma lt_rep_list_spair:
  assumes "rep_list p \<noteq> 0" and "rep_list q \<noteq> 0" and "rep_list (spair p q) \<noteq> 0"
    and "a + punit.lt (rep_list p) = b + punit.lt (rep_list q)"
  shows "punit.lt (rep_list (spair p q)) \<prec> (a - gcs a b) + punit.lt (rep_list p)"
proof -
  from assms(1) have 1: "punit.lc (rep_list p) \<noteq> 0" by (rule punit.lc_not_0)
  from assms(2) have 2: "punit.lc (rep_list q) \<noteq> 0" by (rule punit.lc_not_0)
  define l where "l = lcs (punit.lt (rep_list p)) (punit.lt (rep_list q))"
  have eq: "rep_list (spair p q) = (punit.monom_mult (1 / punit.lc (rep_list p)) (l - punit.lt (rep_list p)) (rep_list p)) +
                               (punit.monom_mult (- 1 / punit.lc (rep_list q)) (l - punit.lt (rep_list q)) (rep_list q))"
    (is "_ = ?a + ?b")
    by (simp add: spair_def Let_def rep_list_minus rep_list_monom_mult punit.monom_mult_uminus_left l_def)
  have "?a + ?b \<noteq> 0" unfolding eq[symmetric] by (fact assms(3))
  moreover from 1 2 assms(1, 2) have "punit.lt ?b = punit.lt ?a"
    by (simp add: lp_monom_mult l_def minus_plus adds_lcs adds_lcs_2)
  moreover have "punit.lc ?b = - punit.lc ?a" by (simp add: 1 2)
  ultimately have "punit.lt (rep_list (spair p q)) \<prec> punit.lt ?a" unfolding eq by (rule punit.lt_plus_lessI)
  also from 1 assms(1) have "... = (l - punit.lt (rep_list p)) + punit.lt (rep_list p)" by (simp add: lp_monom_mult)
  also have "... = l" by (simp add: l_def minus_plus adds_lcs)
  also have "... = (a + punit.lt (rep_list p)) - gcs a b" unfolding l_def using assms(4) by (rule lcs_alt_1)
  also have "... = (a - gcs a b) + punit.lt (rep_list p)" by (simp add: minus_plus gcs_adds)
  finally show ?thesis .
qed

lemma is_regular_spairI:
  assumes "rep_list p \<noteq> 0" and "rep_list q \<noteq> 0"
  and "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q"
  shows "is_regular_spair p q"
proof -
  have *: "(lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p \<noteq>
           (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list q)) \<oplus> lt q"
    (is "?l \<noteq> ?r")
  proof
    assume "?l = ?r"
    hence "punit.lt (rep_list q) \<oplus> lt p = punit.lt (rep_list p) \<oplus> lt q"
      by (simp add: term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
    with assms(3) show False ..
  qed
  from assms(1) have "punit.lc (rep_list p) \<noteq> 0" by (rule punit.lc_not_0)
  moreover from assms(2) have "punit.lc (rep_list q) \<noteq> 0" by (rule punit.lc_not_0)
  ultimately have "1 / punit.lc (rep_list p) \<noteq> 0" and "1 / punit.lc (rep_list q) \<noteq> 0" by simp_all
  moreover from assms(1, 2) have "p \<noteq> 0" and "q \<noteq> 0" by (auto simp: rep_list_zero)
  ultimately have
    "lt (monom_mult (1 / punit.lc (rep_list p)) (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) p) \<noteq>
     lt (monom_mult (1 / punit.lc (rep_list q)) (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list q)) q)"
    using * by (simp add: lt_monom_mult)
  with assms(1, 2) show ?thesis by (simp add: is_regular_spair_def)
qed

lemma is_regular_spairI':
  assumes "rep_list p \<noteq> 0" and "rep_list q \<noteq> 0"
  and "a + punit.lt (rep_list p) = b + punit.lt (rep_list q)" and "a \<oplus> lt p \<noteq> b \<oplus> lt q"
  shows "is_regular_spair p q"
proof -
  have "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q"
  proof
    assume "punit.lt (rep_list q) \<oplus> lt p = punit.lt (rep_list p) \<oplus> lt q"
    hence "a \<oplus> (punit.lt (rep_list q) \<oplus> lt p) = a \<oplus> (punit.lt (rep_list p) \<oplus> lt q)" by (simp only:)
    hence "(a + punit.lt (rep_list q)) \<oplus> lt p = (b + punit.lt (rep_list q)) \<oplus> lt q"
      by (simp add: splus_assoc[symmetric] assms(3))
    hence "punit.lt (rep_list q) \<oplus> (a \<oplus> lt p) = punit.lt (rep_list q) \<oplus> (b \<oplus> lt q)"
      by (simp only: add.commute[of _ "punit.lt (rep_list q)"] splus_assoc)
    hence "a \<oplus> lt p = b \<oplus> lt q" by (simp only: splus_left_canc)
    with assms(4) show False ..
  qed
  with assms(1, 2) show ?thesis by (rule is_regular_spairI)
qed

(* Obsolete? *)
lemma lemma_10:
  assumes "is_sig_GB_upt G u" and "p \<in> G" and "q \<in> G" and "is_regular_spair p q" and "lt (spair p q) adds\<^sub>t u"
  obtains p' q' where "p' \<in> G" and "q' \<in> G" and "is_regular_spair p' q'" and "lt (spair p' q') adds\<^sub>t u"
    and "\<And>r. (sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (spair p' q') r \<Longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r \<Longrightarrow>
            \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp (spair p' q')) r)"
proof -
  define P where "P = (\<lambda>p' q'. \<forall>r. (sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (spair p' q') r \<longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r \<longrightarrow>
            \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp (spair p' q')) r))"
  show ?thesis
  proof (cases "P p q")
    case True
    hence "\<And>r. (sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (spair p q) r \<Longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r \<Longrightarrow>
            \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp (spair p q)) r)"
      unfolding P_def by blast
    with assms(2-5) show ?thesis ..
  next
    case False
    from assms(1) have "finite G" by (rule is_sig_GB_uptD1)
    let ?f = "\<lambda>a. (pp_of_term u - lp a) + punit.lt (rep_list a)"
    define A where "A = (\<Union>p'\<in>G. spair p' ` {q'. q' \<in> G  \<and> is_regular_spair p' q' \<and> lt (spair p' q') adds\<^sub>t u \<and> \<not> P p' q'})"
    define m where "m = ordered_powerprod_lin.MINIMUM A ?f"
    have "finite A" unfolding A_def using \<open>finite G\<close> by simp
    have "spair p q \<in> A" unfolding A_def using assms(2-5) False by blast
    hence "A \<noteq> {}" by blast
    hence "finite (?f ` A)" and "?f ` A \<noteq> {}"
      using \<open>finite A\<close> by simp_all
    hence m_in: "m \<in> ?f ` A" and m_min: "\<And>n. n \<in> ?f ` A \<Longrightarrow> m \<preceq> n"
      by (auto simp: m_def intro: ordered_powerprod_lin.Min_in ordered_powerprod_lin.Min_le)
    from m_in obtain a0 where "a0 \<in> A" and m: "m = ?f a0" ..
    from this(1) obtain p' q' where "p' \<in> G" and "q' \<in> G" and pq'1: "is_regular_spair p' q'"
      and pq'2: "lt (spair p' q') adds\<^sub>t u" and "\<not> P p' q'" and a0: "a0 = spair p' q'"
      unfolding A_def by blast
    from this(4) obtain a where a: "u = a \<oplus> lt (spair p' q')" by (rule adds_termE)
    have *: "P p'' q''"
      if "p'' \<in> G" and "q'' \<in> G" and "is_regular_spair p'' q''" and "lt (spair p'' q'') adds\<^sub>t u"
      and "?f (spair p'' q'') \<prec> a + punit.lt (rep_list (spair p' q'))" for p'' q''
    proof (rule ccontr)
      assume "\<not> P p'' q''"
      with that(1-4) have "spair p'' q'' \<in> A" unfolding A_def by blast
      hence "?f (spair p'' q'') \<in> ?f ` A" by fastforce
      hence "m \<preceq> ?f (spair p'' q'')" by (rule m_min)
      with that(5) show False by (simp add: m a0 a term_simps)
    qed
    from \<open>\<not> P p' q'\<close> obtain r' where r'1: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (spair p' q') r'"
      and r'2: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r'"
      and r'3: "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp (spair p' q')) r')"
      unfolding P_def by blast
    from this(3) have r'4: "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 a r')"
      by (simp add: a term_simps)
    from r'1 have lt_r': "lt r' = lt (spair p' q')" by (rule sig_red_regular_rtrancl_lt)
    also have "... \<prec>\<^sub>t u"
    proof (simp only: ord_term_lin.less_le, intro conjI notI)
      from pq'2 show "lt (spair p' q') \<preceq>\<^sub>t u" by (rule ord_adds_term)
    next
      assume "lt (spair p' q') = u"
      with r'3 have "is_sig_red (\<prec>\<^sub>t) (=) G r'" by simp
      hence "is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r'" by (rule is_sig_red_top_tailI)
      with r'2 show False ..
    qed
    finally have "lt r' \<prec>\<^sub>t u" .
    with assms(1) have "sig_red_zero (\<preceq>\<^sub>t) G r'" by (rule is_sig_GB_uptD3)
    moreover have "rep_list r' \<noteq> 0"
    proof -
      from r'3 have "punit.is_red (rep_list ` G) (rep_list (monom_mult 1 (pp_of_term u - lp (spair p' q')) r'))"
        by (rule is_sig_red_is_red)
      hence "rep_list (monom_mult 1 (pp_of_term u - lp (spair p' q')) r') \<noteq> 0"
        by (auto simp: punit.irred_0)
      thus ?thesis by (auto simp: rep_list_monom_mult)
    qed
    moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
    ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) G r'" by (rule sig_red_zero_nonzero)
    with r'2 have "is_sig_red (=) (=) G r'" by (auto simp: is_sig_red_top_tail_cases is_sig_red_sing_reg_cases)

    (* Construct g0 *)
    then obtain g0 where "g0 \<in> G" and "rep_list g0 \<noteq> 0" and g01: "punit.lt (rep_list g0) adds punit.lt (rep_list r')"
      and g02: "punit.lt (rep_list r') \<oplus> lt g0 = punit.lt (rep_list g0) \<oplus> lt r'" by (rule is_sig_red_top_addsE)
    from this(3) obtain c where eq1: "c + punit.lt (rep_list g0) = punit.lt (rep_list r')" by (metis adds_minus)
    from g02 have eq2: "c \<oplus> lt g0 = lt r'"
      by (simp only: eq1[symmetric] add.commute[of c] splus_assoc splus_left_canc)
    from \<open>rep_list r' \<noteq> 0\<close> have "r' \<noteq> 0" by (auto simp: rep_list_zero)

    (* Construct g1 *)
    from r'3 obtain g1 where "g1 \<in> G" and "rep_list g1 \<noteq> 0"
      and "punit.lt (rep_list g1) adds punit.lt (rep_list (monom_mult 1 (pp_of_term u - lp (spair p' q')) r'))"
      and "punit.lt (rep_list (monom_mult 1 (pp_of_term u - lp (spair p' q')) r')) \<oplus> lt g1 \<prec>\<^sub>t
           punit.lt (rep_list g1) \<oplus> lt (monom_mult 1 (pp_of_term u - lp (spair p' q')) r')"
      by (rule is_sig_red_top_addsE)
    from this(3, 4) have g11: "punit.lt (rep_list g1) adds a + punit.lt (rep_list r')"
      and g12: "(a + punit.lt (rep_list r')) \<oplus> lt g1 \<prec>\<^sub>t (a + punit.lt (rep_list g1)) \<oplus> lt r'"
      by (simp_all add: rep_list_monom_mult \<open>rep_list r' \<noteq> 0\<close> \<open>r' \<noteq> 0\<close> punit.lt_monom_mult lt_monom_mult
          a term_simps ac_simps)
    from this(1) obtain d where eq3: "d + punit.lt (rep_list g1) = a + punit.lt (rep_list r')"
      by (metis adds_minus)
    from g12 have eq4: "d \<oplus> lt g1 \<prec>\<^sub>t a \<oplus> lt r'"
      by (simp only: eq3[symmetric] add.commute[of _ "punit.lt (rep_list g1)"] splus_assoc ord_term_strict_canc)

    define b where "b = gcs (a + c) d"
    have "b adds (a + c)" unfolding b_def by (fact gcs_adds)
    have "b adds d" unfolding b_def by (fact gcs_adds_2)
    let ?q = "spair g0 g1"
    have eq5: "(a + c) + punit.lt (rep_list g0) = d + punit.lt (rep_list g1)" by (simp add: ac_simps eq1 eq3)
    from eq4 have eq6: "d \<oplus> lt g1 \<prec>\<^sub>t (a + c) \<oplus> lt g0" by (simp add: ac_simps eq2)
    have q: "?q = (monom_mult (1 / punit.lc (rep_list g0)) ((a + c) - b) g0) -
                  (monom_mult (1 / punit.lc (rep_list g1)) (d - b) g1)"
      by (simp add: spair_def b_def Let_def lcs_minus_1[OF eq5] lcs_minus_2[OF eq5])
    have lt_q: "lt ?q = ((a + c) - b) \<oplus> lt g0" unfolding b_def using \<open>rep_list g0 \<noteq> 0\<close> eq5 eq6
      by (rule lt_spair')
    have "u = a \<oplus> (c \<oplus> lt g0)" by (simp only: eq2 lt_r' a)
    also have "... = b \<oplus> lt ?q" unfolding lt_q splus_assoc[symmetric]
      by (metis \<open>b adds a + c\<close> add.commute adds_minus)
    finally have eq7: "u = b \<oplus> lt (spair g0 g1)" .
    note \<open>g0 \<in> G\<close> \<open>g1 \<in> G\<close>
    moreover from \<open>rep_list g0 \<noteq> 0\<close> \<open>rep_list g1 \<noteq> 0\<close> eq5 have "is_regular_spair g0 g1"
    proof (rule is_regular_spairI')
      from eq6 show "(a + c) \<oplus> lt g0 \<noteq> d \<oplus> lt g1" by simp
    qed
    moreover from eq7 have "lt ?q adds\<^sub>t u" by (rule adds_termI)
    ultimately show ?thesis
    proof
      fix r
      assume 1: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* ?q r" and 2: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r"
      show "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp ?q) r)"
      proof (cases "rep_list ?q = 0")
        case True
        from 1 have "(punit.red (rep_list ` G))\<^sup>*\<^sup>* (rep_list ?q) (rep_list r)" by (rule sig_red_red_rtrancl)
        hence "(punit.red (rep_list ` G))\<^sup>*\<^sup>* 0 (rep_list r)" by (simp only: True)
        hence "rep_list r = 0" by (rule punit.rtrancl_0)
        hence "rep_list (monom_mult 1 (pp_of_term u - lp ?q) r) = 0" by (simp add: rep_list_monom_mult)
        hence "\<not> punit.is_red (rep_list ` G) (rep_list (monom_mult 1 (pp_of_term u - lp ?q) r))"
          by (simp add: punit.irred_0)
        with is_sig_red_is_red show ?thesis by blast
      next
        case False
        hence "rep_list (spair g1 g0) \<noteq> 0" by (simp add: spair_comm[of g0] rep_list_uminus)
        from \<open>g0 \<in> G\<close> \<open>g1 \<in> G\<close> \<open>is_regular_spair g0 g1\<close> \<open>lt (spair g0 g1) adds\<^sub>t u\<close> have "P g0 g1"
        proof (rule *)
          have "pp_of_term u - lp (spair g0 g1) + punit.lt (rep_list ?q) = b + punit.lt (rep_list ?q)"
            by (simp add: eq7 term_simps)
          thm lt_rep_list_spair
          also have "... \<prec> b + ((d - b) + punit.lt (rep_list g1))"
            unfolding b_def spair_comm[of g0] rep_list_uminus punit.lt_uminus gcs_comm[of "a + c"]
            by (rule plus_monotone_strict_left, rule lt_rep_list_spair, fact+, simp add: ac_simps eq1 eq3)
          thm minus_plus'[OF \<open>b adds d\<close>]
          also have "... = d + punit.lt (rep_list g1)" by (simp add: add.assoc[symmetric] minus_plus'[OF \<open>b adds d\<close>])
          also have "... = a + punit.lt (rep_list r')" by (fact eq3)
          also have "... \<preceq> a + punit.lt (rep_list (spair p' q'))"
            by (rule plus_monotone_left, rule sig_red_rtrancl_lt_rep_list, fact r'1)
          finally show "pp_of_term u - lp (spair g0 g1) + punit.lt (rep_list ?q) \<prec> a + punit.lt (rep_list (spair p' q'))" .
        qed
        thus ?thesis unfolding P_def using 1 2 by blast
      qed
    qed
  qed
qed

(* Obsolete? *)
lemma lemma_9:
  assumes "is_sig_GB_upt G (lt p)"
    and "is_sig_red (=) (=) G (monomial 1 (term_of_pair (0, component_of_term (lt p))))"
    and "p \<noteq> 0" and "\<not> is_sig_red (\<preceq>\<^sub>t) (=) G p"
  obtains p' q' where "p' \<in> G" and "q' \<in> G" and "is_regular_spair p' q'" and "lt (spair p' q') adds\<^sub>t (lt p)"
    and "\<And>r. (sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (spair p' q') r \<Longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r \<Longrightarrow>
            \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (lp p - pp_of_term (lt (spair p' q'))) r)"
proof -
  define u where "u = monomial (lc p) (lt p)"
  from \<open>p \<noteq> 0\<close> have "lc p \<noteq> 0" by (rule lc_not_0)
  hence "lt u = lt p" by (simp add: u_def lt_monomial)
  from assms(2) \<open>lc p \<noteq> 0\<close> have "is_sig_red (=) (=) G
      (monom_mult (lc p) (pp_of_term (lt p)) (monomial 1 (term_of_pair (0, component_of_term (lt p)))))"
    by (rule is_sig_red_monom_mult)
  hence "is_sig_red (=) (=) G u" by (simp add: u_def monom_mult_monomial splus_def term_simps)
  hence "is_sig_red (\<preceq>\<^sub>t) (=) G u" by (rule is_sig_red_sing_regI)
  with assms(4) \<open>lt u = lt p\<close> have "rep_list u \<noteq> rep_list p" by (auto cong: is_sig_red_cong)
  hence "rep_list (p - u) \<noteq> 0" by (simp add: rep_list_minus)
  hence "p - u \<noteq> 0" by (auto simp: rep_list_zero)
  have "lt (p - u) = lt (p + (- u))" by simp
  also have "... \<prec>\<^sub>t lt p" 
  proof (rule lt_plus_lessI')
    from \<open>p - u \<noteq> 0\<close> show "p + - u \<noteq> 0" by simp
  next
    show "lt (- u) = lt p" by (simp add: \<open>lt u = lt p\<close>)
  next
    show "lc p + lc (- u) = 0" by (simp add: u_def)
  qed
  finally have "lt (p - u) \<prec>\<^sub>t lt p" .
  with assms(1) have "is_sig_GB_in G (lt (p - u))" by (rule is_sig_GB_uptD2)
  hence "sig_red_zero (\<preceq>\<^sub>t) G (p - u)" using refl by (rule is_sig_GB_inD)
  moreover note \<open>rep_list (p - u) \<noteq> 0\<close>
  moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
  ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) G (p - u)" by (rule sig_red_zero_nonzero)
  thus ?thesis using \<open>is_sig_red (\<preceq>\<^sub>t) (=) G u\<close>
  proof (rule is_sig_red_top_plusE)
    from \<open>lt (p - u) \<prec>\<^sub>t lt p\<close> show "lt (p - u) \<preceq>\<^sub>t lt (p - u + u)" by simp
  next
    show "lt u \<preceq>\<^sub>t lt (p - u + u)" by (simp add: \<open>lt u = lt p\<close>)
  next
    assume "is_sig_red (\<preceq>\<^sub>t) (=) G (p - u + u)"
    with assms(4) show ?thesis by simp
  next
    assume eq1: "punit.lt (rep_list (p - u)) = punit.lt (rep_list u)"
      and eq2: "punit.lc (rep_list (p - u)) + punit.lc (rep_list u) = 0"

    (* Construct g0 *)
    from \<open>is_sig_red (=) (=) G u\<close> obtain g0 where "g0 \<in> G" and "rep_list g0 \<noteq> 0" and "rep_list u \<noteq> 0"
      and "punit.lt (rep_list g0) adds punit.lt (rep_list u)"
      and g01: "punit.lt (rep_list u) \<oplus> lt g0 = punit.lt (rep_list g0) \<oplus> lt u"
      by (rule is_sig_red_top_addsE)
    from this(4) obtain a where eq3: "a + punit.lt (rep_list g0) = punit.lt (rep_list u)"
      using adds_minus by blast
    from g01 have g02: "a \<oplus> lt g0 = lt p"
      by (simp only: eq3[symmetric] add.commute[of a] splus_assoc \<open>lt u = lt p\<close> splus_left_canc)

    (* Construct g1 *)
    from \<open>is_sig_red (\<preceq>\<^sub>t) (=) G (p - u)\<close> obtain g1 where "g1 \<in> G" and "rep_list g1 \<noteq> 0"
      and "punit.lt (rep_list g1) adds punit.lt (rep_list (p - u))"
      and g11: "punit.lt (rep_list (p - u)) \<oplus> lt g1 \<preceq>\<^sub>t punit.lt (rep_list g1) \<oplus> lt (p - u)"
      by (rule is_sig_red_top_addsE)
    from this(3) obtain b where eq4: "b + punit.lt (rep_list g1) = punit.lt (rep_list (p - u))"
      using adds_minus by blast
    from g11 have g12: "b \<oplus> lt g1 \<preceq>\<^sub>t lt (p - u)"
      by (simp only: eq4[symmetric] add.commute[of b] splus_assoc ord_term_canc)

    define c where "c = gcs a b"
    have "c adds a" unfolding c_def by (fact gcs_adds)
    have "c adds b" unfolding c_def by (fact gcs_adds_2)
    let ?q = "spair g0 g1"
    have eq5: "a + punit.lt (rep_list g0) = b + punit.lt (rep_list g1)" by (simp add: eq1 eq3 eq4)
    from g12 \<open>lt (p - u) \<prec>\<^sub>t lt p\<close> have eq6: "b \<oplus> lt g1 \<prec>\<^sub>t a \<oplus> lt g0" unfolding g02 by simp
    have q: "?q = (monom_mult (1 / punit.lc (rep_list g0)) (a - c) g0) -
                  (monom_mult (1 / punit.lc (rep_list g1)) (b - c) g1)"
      by (simp add: spair_def c_def Let_def lcs_minus_1[OF eq5] lcs_minus_2[OF eq5])
    have lt_q: "lt ?q = (a - c) \<oplus> lt g0" unfolding c_def using \<open>rep_list g0 \<noteq> 0\<close> eq5 eq6
      by (rule lt_spair')
    hence "c \<oplus> lt ?q = a \<oplus> lt g0" using \<open>c adds a\<close> by (metis add.commute adds_minus splus_assoc)
    hence "lt p = c \<oplus> lt ?q" by (simp only: g02)
    hence "lt ?q adds\<^sub>t lt p" by (rule adds_termI)
    note \<open>g0 \<in> G\<close> \<open>g1 \<in> G\<close>
    moreover from \<open>rep_list g0 \<noteq> 0\<close> \<open>rep_list g1 \<noteq> 0\<close> eq5 have "is_regular_spair g0 g1"
    proof (rule is_regular_spairI')
      from eq6 show "a \<oplus> lt g0 \<noteq> b \<oplus> lt g1" by simp
    qed

    from assms(1) \<open>g0 \<in> G\<close> \<open>g1 \<in> G\<close> this \<open>lt ?q adds\<^sub>t lt p\<close>
    obtain p' q' where "p' \<in> G" and "q' \<in> G" and "is_regular_spair p' q'" and "lt (spair p' q') adds\<^sub>t lt p"
      and "\<And>r. (sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (spair p' q') r \<Longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G r \<Longrightarrow>
              \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (lp p - lp (spair p' q')) r)"
      by (rule lemma_10, blast)
    thus ?thesis ..
  qed simp
qed

(* Obsolete? *)
lemma spair_sig_red_zero_is_sig_GB_upt:
  assumes "\<And>p q. is_regular_spair p q \<Longrightarrow> lt (spair p q) \<prec>\<^sub>t u \<Longrightarrow> sig_red_zero_or_sing_top_red (\<preceq>\<^sub>t) G (spair p q)"
    and "\<And>i. i < length fs \<Longrightarrow> term_of_pair (0, i) \<prec>\<^sub>t u \<Longrightarrow> is_sig_red (=) (=) G (monomial 1 (term_of_pair (0, i)))"
  shows "is_sig_GB_upt G u"
  sorry






subsection \<open>Sig-Poly Pairs\<close>

type_synonym ('a, 'b, 't) sig_poly = "('a \<Rightarrow>\<^sub>0 'b) \<times> 't"

definition represents_list :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "represents_list r p \<longleftrightarrow> (ideal.represents (set fs) (pm_of_idx_pm fs (vectorize_poly r)) p)"

lemma represents_list_alt: "represents_list r p \<longleftrightarrow> (rep_list r = p)"
  by (simp add: represents_list_def ideal.represents_def keys_pm_of_idx_pm_subset rep_list_def)

lemma represents_list_zero: "represents_list 0 0"
  unfolding represents_list_def vectorize_zero pm_of_idx_pm_zero by (fact ideal.represents_zero)

lemma represents_list_uminus: "represents_list r p \<Longrightarrow> represents_list (- r) (- p)"
  unfolding represents_list_def vectorize_uminus pm_of_idx_pm_uminus by (rule ideal.represents_uminus)

lemma represents_list_plus:
  assumes "represents_list r p" and "represents_list s q"
  shows "represents_list (r + s) (p + q)"
proof -
  from assms have "ideal.represents (set fs \<union> set fs) (pm_of_idx_pm fs
                      (vectorize_poly r) + pm_of_idx_pm fs (vectorize_poly s)) (p + q)"
    unfolding represents_list_def by (rule ideal.represents_plus)
  thus ?thesis by (simp add: represents_list_def vectorize_plus pm_of_idx_pm_plus)
qed

lemma represents_list_minus:
  assumes "represents_list r p" and "represents_list s q"
  shows "represents_list (r - s) (p - q)"
proof -
  from assms have "ideal.represents (set fs \<union> set fs) (pm_of_idx_pm fs
                      (vectorize_poly r) - pm_of_idx_pm fs (vectorize_poly s)) (p - q)"
    unfolding represents_list_def by (rule ideal.represents_minus)
  thus ?thesis by (simp add: represents_list_def vectorize_minus pm_of_idx_pm_minus)
qed

lemma represents_list_times: "represents_list r p \<Longrightarrow> represents_list (c \<odot> r) (c * p)"
  unfolding represents_list_def vectorize_mult_scalar pm_of_idx_pm_monom_mult by (rule punit.represents_mult_scalar[simplified])

lemma represents_list_monom_mult:
  "represents_list r p \<Longrightarrow> represents_list (monom_mult c t r) (punit.monom_mult c t p)"
  unfolding mult_scalar_monomial[symmetric] times_monomial_left[symmetric] by (rule represents_list_times)

definition sig_inv' :: "('a, 'b, 't) sig_poly \<Rightarrow> bool"
  where "sig_inv' p = (\<exists>r::'t \<Rightarrow>\<^sub>0 'b. represents_list r (fst p) \<and> lt r = snd p)"

subsubsection \<open>Signature Reduction\<close>

text \<open>We only allow @{emph \<open>regular\<close>} signature-reductions here, meaning the signature of the
  result of reduction is the same as the signature of the initial polynomial.\<close>

definition sig_red_single' :: "('a, 'b, 't) sig_poly \<Rightarrow> ('a, 'b, 't) sig_poly \<Rightarrow> ('a, 'b::field, 't) sig_poly \<Rightarrow> 'a \<Rightarrow> bool"
  where "sig_red_single' p q f t \<longleftrightarrow> (punit.red_single (fst p) (fst q) (fst f) t \<and> snd q = snd p \<and> t \<oplus> snd f \<prec>\<^sub>t snd p)"

definition sig_red' :: "('a, 'b, 't) sig_poly set \<Rightarrow> ('a, 'b, 't) sig_poly \<Rightarrow> ('a, 'b::field, 't) sig_poly \<Rightarrow> bool"
  where "sig_red' F p q \<longleftrightarrow> (\<exists>f\<in>F. \<exists>t. sig_red_single' p q f t)"

end

end (* gd_inf_term *)

end (* theory *)
