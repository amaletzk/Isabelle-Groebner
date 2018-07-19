(* Author: Alexander Maletzky *)

section \<open>Signature-Based Algorithms for Computing Gr\"obner Bases\<close>

theory Signature_Based
  imports General_Utils Groebner_Bases.Syzygy Quasi_PM_Power_Products
begin

(* TODO: Add references. *)

text \<open>This formalization closely follows Sections 4 to 7 of the excellent survey article @{cite Eder2015}.\<close>

subsection \<open>Preliminaries\<close>

lemma finite_minimalE:
  assumes "finite A" and "A \<noteq> {}" and "irreflp rel" and "transp rel"
  obtains a where "a \<in> A" and "\<And>b. rel b a \<Longrightarrow> b \<notin> A"
  using assms(1, 2)
proof (induct arbitrary: thesis)
  case empty
  from empty(2) show ?case by simp
next
  case (insert a A)
  show ?case
  proof (cases "A = {}")
    case True
    show ?thesis
    proof (rule insert(4))
      fix b
      assume "rel b a"
      with assms(3) show "b \<notin> insert a A" by (auto simp: True irreflp_def)
    qed simp
  next
    case False
    with insert(3) obtain z where "z \<in> A" and *: "\<And>b. rel b z \<Longrightarrow> b \<notin> A" by blast
    show ?thesis
    proof (cases "rel a z")
      case True
      show ?thesis
      proof (rule insert(4))
        fix b
        assume "rel b a"
        with assms(4) have "rel b z" using \<open>rel a z\<close> by (rule transpD)
        hence "b \<notin> A" by (rule *)
        moreover from \<open>rel b a\<close> assms(3) have "b \<noteq> a" by (auto simp: irreflp_def)
        ultimately show "b \<notin> insert a A" by simp
      qed simp
    next
      case False
      show ?thesis
      proof (rule insert(4))
        fix b
        assume "rel b z"
        hence "b \<notin> A" by (rule *)
        moreover from \<open>rel b z\<close> False have "b \<noteq> a" by blast
        ultimately show "b \<notin> insert a A" by simp
      next
        from \<open>z \<in> A\<close> show "z \<in> insert a A" by simp
      qed
    qed
  qed
qed

lemma wfP_on_finite:
  assumes "irreflp rel" and "transp rel" and "finite A"
  shows "wfP_on A rel"
proof (rule wfP_onI_min)
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> A"
  from this(2) assms(3) have "finite Q" by (rule finite_subset)
  moreover from \<open>x \<in> Q\<close> have "Q \<noteq> {}" by blast
  ultimately obtain z where "z \<in> Q" and "\<And>y. rel y z \<Longrightarrow> y \<notin> Q" using assms(1, 2)
    by (rule finite_minimalE, blast)
  thus "\<exists>z\<in>Q. \<forall>y\<in>A. rel y z \<longrightarrow> y \<notin> Q" by blast
qed

lemma almost_full_on_Int:
  assumes "almost_full_on P1 A1" and "almost_full_on P2 A2"
  shows "almost_full_on (\<lambda>x y. P1 x y \<and> P2 x y) (A1 \<inter> A2)" (is "almost_full_on ?P ?A")
proof (rule almost_full_onI)
  fix f :: "nat \<Rightarrow> 'a"
  assume a: "\<forall>i. f i \<in> ?A"
  define g where "g = (\<lambda>i. (f i, f i))"
  from assms have "almost_full_on (prod_le P1 P2) (A1 \<times> A2)" by (rule almost_full_on_Sigma)
  moreover from a have "\<And>i. g i \<in> A1 \<times> A2" by (simp add: g_def)
  ultimately obtain i j where "i < j" and "prod_le P1 P2 (g i) (g j)" by (rule almost_full_onD)
  from this(2) have "?P (f i) (f j)" by (simp add: g_def prod_le_def)
  with \<open>i < j\<close> show "good ?P f" by (rule goodI)
qed

corollary almost_full_on_same:
  assumes "almost_full_on P1 A" and "almost_full_on P2 A"
  shows "almost_full_on (\<lambda>x y. P1 x y \<and> P2 x y) A"
proof -
  from assms have "almost_full_on (\<lambda>x y. P1 x y \<and> P2 x y) (A \<inter> A)" by (rule almost_full_on_Int)
  thus ?thesis by simp
qed

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

lemma gcs_minus:
  assumes "u adds s" and "u adds t"
  shows "gcs (s - u) (t - u) = gcs s t - u"
proof -
  from assms have "gcs s t = gcs ((s - u) + u) ((t - u) + u)" by (simp add: minus_plus)
  also have "... = gcs (s - u) (t - u) + u" by (simp only: gcs_plus_right)
  finally show ?thesis by simp
qed

corollary gcs_minus_gcs: "gcs (s - (gcs s t)) (t - (gcs s t)) = 0"
  by (simp add: gcs_minus gcs_adds gcs_adds_2)

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

lemma lt_minus_distinct_eq_max:
  assumes "lt p \<noteq> lt (q::'t \<Rightarrow>\<^sub>0 'b::ab_group_add)"
  shows "lt (p - q) = ord_term_lin.max (lt p) (lt q)"
proof (rule ord_term_lin.linorder_cases)
  assume a: "lt p \<prec>\<^sub>t lt q"
  hence "lt (p - q) = lt q" by (rule lt_minus_eqI)
  also from a have "... = ord_term_lin.max (lt p) (lt q)"
    by (simp add: ord_term_lin.max.absorb2)
  finally show ?thesis .
next
  assume a: "lt q \<prec>\<^sub>t lt p"
  hence "lt (p - q) = lt p" by (rule lt_minus_eqI_2)
  also from a have "... = ord_term_lin.max (lt p) (lt q)"
    by (simp add: ord_term_lin.max.absorb1)
  finally show ?thesis .
next
  assume "lt p = lt q"
  with assms show ?thesis ..
qed

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
  assumes "dickson_grading d" and "x \<in> Q" and "pp_of_term ` Q \<subseteq> dgrad_set d m"
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

definition sig_inv_set :: "('t \<Rightarrow>\<^sub>0 'b) set"
  where "sig_inv_set = {r. keys (vectorize_poly r) \<subseteq> {0..<length fs}}"

definition rep_list :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "rep_list r = ideal.rep (pm_of_idx_pm fs (vectorize_poly r))"

lemma sig_inv_setI: "keys (vectorize_poly r) \<subseteq> {0..<length fs} \<Longrightarrow> r \<in> sig_inv_set"
  by (simp add: sig_inv_set_def)

lemma sig_inv_setD: "r \<in> sig_inv_set \<Longrightarrow> keys (vectorize_poly r) \<subseteq> {0..<length fs}"
  by (simp add: sig_inv_set_def)

lemma sig_inv_setI':
  assumes "\<And>v. v \<in> keys r \<Longrightarrow> component_of_term v < length fs"
  shows "r \<in> sig_inv_set"
proof (rule sig_inv_setI, rule)
  fix k
  assume "k \<in> keys (vectorize_poly r)"
  then obtain v where "v \<in> keys r" and k: "k = component_of_term v" unfolding keys_vectorize_poly ..
  from this(1) have "k < length fs" unfolding k by (rule assms)
  thus "k \<in> {0..<length fs}" by simp
qed

lemma sig_inv_setD':
  assumes "r \<in> sig_inv_set" and "v \<in> keys r"
  shows "component_of_term v < length fs"
proof -
  from assms(2) have "component_of_term v \<in> component_of_term ` keys r" by (rule imageI)
  also have "... = keys (vectorize_poly r)" by (simp only: keys_vectorize_poly)
  also from assms(1) have "... \<subseteq> {0..<length fs}" by (rule sig_inv_setD)
  finally show ?thesis by simp
qed

corollary sig_inv_setD_lt:
  assumes "r \<in> sig_inv_set" and "r \<noteq> 0"
  shows "component_of_term (lt r) < length fs"
  by (rule sig_inv_setD', fact, rule lt_in_keys, fact)

lemma sig_inv_set_zero: "0 \<in> sig_inv_set"
  by (rule sig_inv_setI', simp)

lemma sig_inv_set_closed_uminus: "r \<in> sig_inv_set \<Longrightarrow> - r \<in> sig_inv_set"
  by (auto dest!: sig_inv_setD' intro!: sig_inv_setI' simp: keys_uminus)

lemma sig_inv_set_closed_plus:
  assumes "r \<in> sig_inv_set" and "s \<in> sig_inv_set"
  shows "r + s \<in> sig_inv_set"
proof (rule sig_inv_setI')
  fix v
  assume "v \<in> keys (r + s)"
  hence "v \<in> keys r \<union> keys s" using keys_add_subset ..
  thus "component_of_term v < length fs"
  proof
    assume "v \<in> keys r"
    with assms(1) show ?thesis by (rule sig_inv_setD')
  next
    assume "v \<in> keys s"
    with assms(2) show ?thesis by (rule sig_inv_setD')
  qed
qed

lemma sig_inv_set_closed_minus:
  assumes "r \<in> sig_inv_set" and "s \<in> sig_inv_set"
  shows "r - s \<in> sig_inv_set"
proof (rule sig_inv_setI')
  fix v
  assume "v \<in> keys (r - s)"
  hence "v \<in> keys r \<union> keys s" using keys_minus ..
  thus "component_of_term v < length fs"
  proof
    assume "v \<in> keys r"
    with assms(1) show ?thesis by (rule sig_inv_setD')
  next
    assume "v \<in> keys s"
    with assms(2) show ?thesis by (rule sig_inv_setD')
  qed
qed

lemma sig_inv_set_closed_monom_mult:
  assumes "r \<in> sig_inv_set"
  shows "monom_mult c t r \<in> sig_inv_set"
proof (rule sig_inv_setI')
  fix v
  assume "v \<in> keys (monom_mult c t r)"
  hence "v \<in> (\<oplus>) t ` keys r" using keys_monom_mult_subset ..
  then obtain u where "u \<in> keys r" and v: "v = t \<oplus> u" ..
  from assms this(1) have "component_of_term u < length fs" by (rule sig_inv_setD')
  thus "component_of_term v < length fs" by (simp add: v term_simps)
qed

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
  obtains r where "p = rep_list r" and "r \<in> sig_inv_set"
proof -
  from assms obtain r0 where r0: "keys r0 \<subseteq> set fs" and p: "p = ideal.rep r0"
    by (rule ideal.in_moduleE_rep)
  show ?thesis
  proof
    show "p = rep_list (atomize_poly (idx_pm_of_pm fs r0))"
      by (simp add: rep_list_def vectorize_atomize_poly pm_of_idx_pm_of_pm[OF r0] p)
  next
    show "atomize_poly (idx_pm_of_pm fs r0) \<in> sig_inv_set"
      by (rule sig_inv_setI, simp add: vectorize_atomize_poly keys_idx_pm_of_pm_subset)
  qed
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
  assumes "dickson_grading d" and "dgrad_set_le d (pp_of_term ` keys r) (Keys (set fs))"
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
  assumes "dickson_grading d" and "dgrad_set_le d (pp_of_term ` Keys F) (Keys (set fs))"
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
  where "dgrad_max d = (MAXIMUM (insert 0 (Keys (set fs))) d)"

abbreviation "dgrad_max_set d \<equiv> dgrad_p_set d (dgrad_max d)"
abbreviation "punit_dgrad_max_set d \<equiv> punit.dgrad_p_set d (dgrad_max d)"

lemma dgrad_max_0: "d 0 \<le> dgrad_max d"
proof -
  from finite_Keys have "finite (d ` insert 0 (Keys (set fs)))" by auto
  moreover have "d 0 \<in> d ` insert 0 (Keys (set fs))" by blast
  ultimately show ?thesis unfolding dgrad_max_def by (rule Max_ge)
qed

lemma dgrad_max_1: "set fs \<subseteq> punit_dgrad_max_set d"
proof (cases "Keys (set fs) = {}")
  case True
  show ?thesis
  proof (rule, rule punit.dgrad_p_setI[simplified])
    fix f v
    assume "f \<in> set fs" and "v \<in> keys f"
    with True show "d v \<le> dgrad_max d" by (auto simp: Keys_def)
  qed
next
  case False
  show ?thesis
  proof (rule subset_trans)
    from finite_set show "set fs \<subseteq> punit.dgrad_p_set d (MAXIMUM (Keys (set fs)) d)"
      by (rule punit.dgrad_p_set_exhaust_expl[simplified])
  next
    from finite_set have "finite (Keys (set fs))" by (rule finite_Keys)
    hence "finite (d ` Keys (set fs))" by (rule finite_imageI)
    moreover from False have 2: "d ` Keys (set fs) \<noteq> {}" by simp
    ultimately have "dgrad_max d = ord_class.max (d 0) (MAXIMUM (Keys (set fs)) d)"
      by (simp add: dgrad_max_def)
    hence "MAXIMUM (Keys (set fs)) d \<le> dgrad_max d" by simp
    thus "punit.dgrad_p_set d (MAXIMUM (Keys (set fs)) d) \<subseteq> punit_dgrad_max_set d"
      by (rule punit.dgrad_p_set_subset)
  qed
qed

lemma dgrad_max_2:
  assumes "dickson_grading d" and "r \<in> dgrad_max_set d"
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
  assumes "dickson_grading d" and "F \<subseteq> dgrad_max_set d"
  shows "rep_list ` F \<subseteq> punit_dgrad_max_set d"
proof (rule, elim imageE, simp)
  fix f
  assume "f \<in> F"
  hence "f \<in> dgrad_p_set d (dgrad_max d)" using assms(2) ..
  with assms(1) show "rep_list f \<in> punit.dgrad_p_set d (dgrad_max d)" by (rule dgrad_max_2)
qed

definition dgrad_sig_set :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set"
  where "dgrad_sig_set d = dgrad_max_set d \<inter> sig_inv_set"

lemma dgrad_sig_set_closed_uminus: "r \<in> dgrad_sig_set d \<Longrightarrow> - r \<in> dgrad_sig_set d"
  unfolding dgrad_sig_set_def by (auto intro: dgrad_p_set_closed_uminus sig_inv_set_closed_uminus)

lemma dgrad_sig_set_closed_plus: "r \<in> dgrad_sig_set d \<Longrightarrow> s \<in> dgrad_sig_set d \<Longrightarrow> r + s \<in> dgrad_sig_set d"
  unfolding dgrad_sig_set_def by (auto intro: dgrad_p_set_closed_plus sig_inv_set_closed_plus)

lemma dgrad_sig_set_closed_minus: "r \<in> dgrad_sig_set d \<Longrightarrow> s \<in> dgrad_sig_set d \<Longrightarrow> r - s \<in> dgrad_sig_set d"
  unfolding dgrad_sig_set_def by (auto intro: dgrad_p_set_closed_minus sig_inv_set_closed_minus)

lemma dgrad_sig_set_closed_monom_mult:
  assumes "dickson_grading d" and "d t \<le> dgrad_max d"
  shows "p \<in> dgrad_sig_set d \<Longrightarrow> monom_mult c t p \<in> dgrad_sig_set d"
  unfolding dgrad_sig_set_def by (auto intro: assms dgrad_p_set_closed_monom_mult sig_inv_set_closed_monom_mult)

lemma dgrad_sig_set_closed_monom_mult_zero: "p \<in> dgrad_sig_set d \<Longrightarrow> monom_mult c 0 p \<in> dgrad_sig_set d"
  unfolding dgrad_sig_set_def by (auto intro: dgrad_p_set_closed_monom_mult_zero sig_inv_set_closed_monom_mult)

lemma dgrad_sig_set_closed_monomial:
  assumes "d (pp_of_term u) \<le> dgrad_max d" and "component_of_term u < length fs"
  shows "monomial c u \<in> dgrad_sig_set d"
proof (simp add: dgrad_sig_set_def, rule)
  show "monomial c u \<in> dgrad_max_set d"
  proof (rule dgrad_p_setI)
    fix v
    assume "v \<in> keys (monomial c u)"
    also have "... \<subseteq> {u}" by simp
    finally show "d (pp_of_term v) \<le> dgrad_max d" using assms(1) by simp
  qed
next
  show "monomial c u \<in> sig_inv_set"
  proof (rule sig_inv_setI')
    fix v
    assume "v \<in> keys (monomial c u)"
    also have "... \<subseteq> {u}" by simp
    finally show "component_of_term v < length fs" using assms(2) by simp
  qed
qed

lemma in_idealE_rep_list_dgrad_max_set:
  assumes "hom_grading d" and "p \<in> punit_dgrad_max_set d" and "p \<in> ideal (set fs)"
  obtains r where "r \<in> dgrad_sig_set d" and "p = rep_list r"
proof -
  from assms(1) dgrad_max_1 assms(2, 3) obtain r0 where r0: "keys r0 \<subseteq> set fs"
    and 1: "Poly_Mapping.range r0 \<subseteq> punit_dgrad_max_set d" and p: "p = ideal.rep r0"
    by (rule in_idealE_rep_dgrad_p_set)
  show ?thesis
  proof
    show "atomize_poly (idx_pm_of_pm fs r0) \<in> dgrad_sig_set d" unfolding dgrad_sig_set_def
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
      show "atomize_poly (idx_pm_of_pm fs r0) \<in> sig_inv_set"
        by (rule sig_inv_setI, simp add: vectorize_atomize_poly keys_idx_pm_of_pm_subset)
    qed
  next
    show "p = rep_list (atomize_poly (idx_pm_of_pm fs r0))"
      by (simp add: rep_list_def vectorize_atomize_poly pm_of_idx_pm_of_pm[OF r0] p)
  qed
qed

lemma dgrad_sig_setD_lp:
  assumes "p \<in> dgrad_sig_set d"
  shows "d (lp p) \<le> dgrad_max d"
proof (cases "p = 0")
  case True
  show ?thesis by (simp add: True min_term_def pp_of_term_of_pair dgrad_max_0)
next
  case False
  from assms have "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
  thus ?thesis using False by (rule dgrad_p_setD_lt)
qed

lemma dgrad_sig_setD_lt:
  assumes "p \<in> dgrad_sig_set d" and "p \<noteq> 0"
  shows "component_of_term (lt p) < length fs"
proof -
  from assms have "p \<in> sig_inv_set" by (simp add: dgrad_sig_set_def)
  thus ?thesis using assms(2) by (rule sig_inv_setD_lt)
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
  assumes "dickson_grading d" and "p \<in> dgrad_max_set d" and "f \<in> dgrad_max_set d"
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

lemma sig_inv_set_closed_sig_red_single:
  assumes "p \<in> sig_inv_set" and "f \<in> sig_inv_set" and "sig_red_single sing_red top_tail p q f t"
  shows "q \<in> sig_inv_set"
proof -
  let ?f = "monom_mult (lookup (rep_list p) (t + punit.lt (rep_list f)) / punit.lc (rep_list f)) t f"
  from assms(3) have t: "t + punit.lt (rep_list f) \<in> keys (rep_list p)" and q: "q = p - ?f"
    by (rule sig_red_singleD2, rule sig_red_singleD3)
  show ?thesis unfolding q using assms(1)
  proof (rule sig_inv_set_closed_minus)
    from assms(2) show "?f \<in> sig_inv_set" by (rule sig_inv_set_closed_monom_mult)
  qed
qed

corollary dgrad_sig_set_closed_sig_red_single:
  assumes "dickson_grading d" and "p \<in> dgrad_sig_set d" and "f \<in> dgrad_sig_set d"
    and "sig_red_single sing_red top_tail p q f t"
  shows "q \<in> dgrad_sig_set d"
  using assms unfolding dgrad_sig_set_def
  by (auto intro: dgrad_max_set_closed_sig_red_single sig_inv_set_closed_sig_red_single)

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
  assumes "dickson_grading d" and "F \<subseteq> dgrad_max_set d"
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

lemma dgrad_sig_set_closed_sig_red:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_sig_set d" and "p \<in> dgrad_sig_set d"
    and "sig_red sing_red top_tail F p q"
  shows "q \<in> dgrad_sig_set d"
  using assms by (auto simp: sig_red_def intro: dgrad_sig_set_closed_sig_red_single)

lemma sig_red_mono: "sig_red sing_reg top_tail F p q \<Longrightarrow> F \<subseteq> F' \<Longrightarrow> sig_red sing_reg top_tail F' p q"
  by (auto simp: sig_red_def)

lemma sig_red_Un:
  "sig_red sing_reg top_tail (A \<union> B) p q \<longleftrightarrow> (sig_red sing_reg top_tail A p q \<or> sig_red sing_reg top_tail B p q)"
  by (auto simp: sig_red_def)

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

lemma dgrad_sig_set_closed_sig_red_rtrancl:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_sig_set d" and "p \<in> dgrad_sig_set d"
    and "(sig_red sing_red top_tail F)\<^sup>*\<^sup>* p q"
  shows "q \<in> dgrad_sig_set d"
  using assms(4, 1, 2, 3) by (induct, auto intro: dgrad_sig_set_closed_sig_red)

lemma sig_red_rtrancl_mono:
  assumes "(sig_red sing_reg top_tail F)\<^sup>*\<^sup>* p q" and "F \<subseteq> F'"
  shows "(sig_red sing_reg top_tail F')\<^sup>*\<^sup>* p q"
  using assms(1) by (induct rule: rtranclp_induct, auto dest: sig_red_mono[OF _ assms(2)])

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

lemma is_sig_red_singletonI:
  assumes "is_sig_red sing_reg top_tail F r"
  obtains f where "f \<in> F" and "is_sig_red sing_reg top_tail {f} r"
proof -
  from assms obtain r' where "sig_red sing_reg top_tail F r r'" unfolding is_sig_red_def ..
  then obtain f t where "f \<in> F" and t: "sig_red_single sing_reg top_tail r r' f t"
    by (auto simp: sig_red_def)
  have "is_sig_red sing_reg top_tail {f} r" unfolding is_sig_red_def sig_red_def
  proof (intro exI bexI)
    show "f \<in> {f}" by simp
  qed fact
  with \<open>f \<in> F\<close> show ?thesis ..
qed

lemma is_sig_red_singletonD:
  assumes "is_sig_red sing_reg top_tail {f} r" and "f \<in> F"
  shows "is_sig_red sing_reg top_tail F r"
proof -
  from assms(1) obtain r' where "sig_red sing_reg top_tail {f} r r'" unfolding is_sig_red_def ..
  then obtain t where "sig_red_single sing_reg top_tail r r' f t" by (auto simp: sig_red_def)
  show ?thesis unfolding is_sig_red_def sig_red_def by (intro exI bexI, fact+)
qed

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

lemma is_sig_red_singleton_monom_multD:
  assumes "is_sig_red sing_reg top_tail {monom_mult c t f} p"
  shows "is_sig_red sing_reg top_tail {f} p"
proof -
  let ?f = "monom_mult c t f"
  from assms obtain s where "s \<in> keys (rep_list p)" and 2: "rep_list ?f \<noteq> 0"
    and 3: "punit.lt (rep_list ?f) adds s"
    and 4: "sing_reg (s \<oplus> lt ?f) (punit.lt (rep_list ?f) \<oplus> lt p)"
    and "top_tail s (punit.lt (rep_list p))"
    by (auto elim: is_sig_red_addsE)
  from 2 have "c \<noteq> 0" and "rep_list f \<noteq> 0"
    by (simp_all add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  hence "f \<noteq> 0" by (auto simp: rep_list_zero)
  with \<open>c \<noteq> 0\<close> have eq1: "lt ?f = t \<oplus> lt f" by (simp add: lt_monom_mult)
  from \<open>c \<noteq> 0\<close> \<open>rep_list f \<noteq> 0\<close> have eq2: "punit.lt (rep_list ?f) = t + punit.lt (rep_list f)"
    by (simp add: rep_list_monom_mult punit.lt_monom_mult)
  from assms have *: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  show ?thesis
  proof (rule is_sig_red_addsI)
    show "f \<in> {f}" by simp
  next
    have "punit.lt (rep_list f) adds t + punit.lt (rep_list f)" by (rule adds_triv_right)
    also from 3 have "... adds s" by (simp only: eq2)
    finally show "punit.lt (rep_list f) adds s" .
  next
    from 4 have "sing_reg (t \<oplus> (s \<oplus> lt f)) (t \<oplus> (punit.lt (rep_list f) \<oplus> lt p))"
      by (simp add: eq1 eq2 splus_assoc splus_left_commute)
    with * show "sing_reg (s \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
      by (simp add: term_is_le_rel_canc_left)
  next
    from assms show "ordered_powerprod_lin.is_le_rel top_tail" by (rule is_sig_redD2)
  qed fact+
qed

lemma is_sig_red_top_singleton_monom_multI:
  assumes "is_sig_red sing_reg (=) {f} p" and "c \<noteq> 0"
    and "t adds punit.lt (rep_list p) - punit.lt (rep_list f)"
  shows "is_sig_red sing_reg (=) {monom_mult c t f} p"
proof -
  let ?f = "monom_mult c t f"
  from assms have 2: "rep_list f \<noteq> 0" and "rep_list p \<noteq> 0"
    and 3: "punit.lt (rep_list f) adds punit.lt (rep_list p)"
    and 4: "sing_reg (punit.lt (rep_list p) \<oplus> lt f) (punit.lt (rep_list f) \<oplus> lt p)"
    by (auto elim: is_sig_red_top_addsE)
  hence "f \<noteq> 0" by (auto simp: rep_list_zero)
  with \<open>c \<noteq> 0\<close> have eq1: "lt ?f = t \<oplus> lt f" by (simp add: lt_monom_mult)
  from \<open>c \<noteq> 0\<close> \<open>rep_list f \<noteq> 0\<close> have eq2: "punit.lt (rep_list ?f) = t + punit.lt (rep_list f)"
    by (simp add: rep_list_monom_mult punit.lt_monom_mult)
  from assms(1) have *: "ord_term_lin.is_le_rel sing_reg" by (rule is_sig_redD1)
  show ?thesis
  proof (rule is_sig_red_top_addsI)
    show "?f \<in> {?f}" by simp
  next
    from \<open>c \<noteq> 0\<close> \<open>rep_list f \<noteq> 0\<close> show "rep_list ?f \<noteq> 0"
      by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  next
    from assms(3) have "t + punit.lt (rep_list f) adds
                        (punit.lt (rep_list p) - punit.lt (rep_list f)) + punit.lt (rep_list f)"
      by (simp only: adds_canc)
    also from 3 have "... = punit.lt (rep_list p)" by (rule adds_minus)
    finally show "punit.lt (rep_list ?f) adds punit.lt (rep_list p)" by (simp only: eq2)
  next
    from 4 * show "sing_reg (punit.lt (rep_list p) \<oplus> lt ?f) (punit.lt (rep_list ?f) \<oplus> lt p)"
      by (simp add: eq1 eq2 term_is_le_rel_canc_left splus_assoc splus_left_commute)
  qed fact+
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
  assumes "dickson_grading d" and "F \<subseteq> dgrad_max_set d"
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

lemma is_sig_red_mono:
  "is_sig_red sing_reg top_tail F p \<Longrightarrow> F \<subseteq> F' \<Longrightarrow> is_sig_red sing_reg top_tail F' p"
  by (auto simp: is_sig_red_def dest: sig_red_mono)

lemma is_sig_red_Un:
  "is_sig_red sing_reg top_tail (A \<union> B) p \<longleftrightarrow> (is_sig_red sing_reg top_tail A p \<or> is_sig_red sing_reg top_tail B p)"
  by (auto simp: is_sig_red_def sig_red_Un)

lemma is_sig_red_regularD:
  assumes "is_sig_red (\<prec>\<^sub>t) top_tail {f} p"
  shows "lt f \<prec>\<^sub>t lt p"
proof -
  from assms obtain s where "rep_list f \<noteq> 0" and "s \<in> keys (rep_list p)"
    and 1: "punit.lt (rep_list f) adds s" and 2: "s \<oplus> lt f \<prec>\<^sub>t punit.lt (rep_list f) \<oplus> lt p"
    by (auto elim!: is_sig_red_addsE)
  from 1 obtain t where eq: "s = punit.lt (rep_list f) + t" by (rule addsE)
  hence "punit.lt (rep_list f) \<oplus> (t \<oplus> lt f) = s \<oplus> lt f" by (simp add: splus_assoc)
  also note 2
  finally have "t \<oplus> lt f \<prec>\<^sub>t lt p" by (rule ord_term_strict_canc)
  have "0 \<preceq> t" by (fact zero_min)
  hence "0 \<oplus> lt f \<preceq>\<^sub>t t \<oplus> lt f" by (rule splus_mono_left)
  hence "lt f \<preceq>\<^sub>t t \<oplus> lt f" by (simp add: term_simps)
  thus ?thesis using \<open>t \<oplus> lt f \<prec>\<^sub>t lt p\<close> by (rule ord_term_lin.le_less_trans)
qed

lemma sig_irred_regular_self: "\<not> is_sig_red (\<prec>\<^sub>t) top_tail {p} p"
  by (auto dest: is_sig_red_regularD)

subsubsection \<open>Signature Gr\"obner Bases\<close>

definition sig_red_zero :: "('t \<Rightarrow>'t \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "sig_red_zero sing_reg F r \<longleftrightarrow> (\<exists>s. (sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s \<and> rep_list s = 0)"

definition is_sig_GB_in :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_sig_GB_in d G u \<longleftrightarrow> (\<forall>r. lt r = u \<longrightarrow> r \<in> dgrad_sig_set d \<longrightarrow> sig_red_zero (\<preceq>\<^sub>t) G r)"

definition is_sig_GB_upt :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_sig_GB_upt d G u \<longleftrightarrow>
            (G \<subseteq> dgrad_sig_set d \<and> (\<forall>v. v \<prec>\<^sub>t u \<longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<longrightarrow>
                                          component_of_term v < length fs \<longrightarrow> is_sig_GB_in d G v))"

definition is_syz_sig :: "('a \<Rightarrow> nat) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_syz_sig d G u \<longleftrightarrow> (\<exists>r. r \<noteq> 0 \<and> lt r = u \<and> r \<in> dgrad_sig_set d \<and> sig_red_zero (\<prec>\<^sub>t) G r)"

lemma sig_red_zeroI:
  assumes "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
  shows "sig_red_zero sing_reg F r"
  unfolding sig_red_zero_def using assms by blast

lemma sig_red_zeroE:
  assumes "sig_red_zero sing_reg F r"
  obtains s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
  using assms unfolding sig_red_zero_def by blast

lemma sig_red_zero_monom_mult:
  assumes "sig_red_zero sing_reg F r"
  shows "sig_red_zero sing_reg F (monom_mult c t r)"
proof -
  from assms obtain s where "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  from this(1) have "(sig_red sing_reg (\<preceq>) F)\<^sup>*\<^sup>* (monom_mult c t r) (monom_mult c t s)"
    by (rule sig_red_rtrancl_monom_mult)
  moreover have "rep_list (monom_mult c t s) = 0" by (simp add: rep_list_monom_mult \<open>rep_list s = 0\<close>)
  ultimately show ?thesis by (rule sig_red_zeroI)
qed

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

lemma sig_red_zero_mono: "sig_red_zero sing_reg F p \<Longrightarrow> F \<subseteq> F' \<Longrightarrow> sig_red_zero sing_reg F' p"
  by (auto simp: sig_red_zero_def dest: sig_red_rtrancl_mono)

lemma is_sig_GB_inI:
  assumes "\<And>r. lt r = u \<Longrightarrow> r \<in> dgrad_sig_set d \<Longrightarrow> sig_red_zero (\<preceq>\<^sub>t) G r"
  shows "is_sig_GB_in d G u"
  unfolding is_sig_GB_in_def using assms by blast

lemma is_sig_GB_inD:
  assumes "is_sig_GB_in d G u" and "r \<in> dgrad_sig_set d" and "lt r = u"
  shows "sig_red_zero (\<preceq>\<^sub>t) G r"
  using assms unfolding is_sig_GB_in_def by blast

lemma is_sig_GB_inI_triv:
  assumes "\<not> d (pp_of_term u) \<le> dgrad_max d \<or> \<not> component_of_term u < length fs"
  shows "is_sig_GB_in d G u"
proof (rule is_sig_GB_inI)
  fix r::"'t \<Rightarrow>\<^sub>0 'b"
  assume "lt r = u" and "r \<in> dgrad_sig_set d"
  show "sig_red_zero (\<preceq>\<^sub>t) G r"
  proof (cases "r = 0")
    case True
    hence "rep_list r = 0" by (simp only: rep_list_zero)
    with rtrancl_refl[to_pred] show ?thesis by (rule sig_red_zeroI)
  next
    case False
    from \<open>r \<in> dgrad_sig_set d\<close> have "d (lp r) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
    moreover from \<open>r \<in> dgrad_sig_set d\<close> False have "component_of_term (lt r) < length fs"
      by (rule dgrad_sig_setD_lt)
    ultimately show ?thesis using assms by (simp add: \<open>lt r = u\<close>)
  qed
qed

lemma is_sig_GB_in_mono: "is_sig_GB_in d G u \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> is_sig_GB_in d G' u"
  by (auto simp: is_sig_GB_in_def dest: sig_red_zero_mono)

lemma is_sig_GB_uptI:
  assumes "G \<subseteq> dgrad_sig_set d"
    and "\<And>v. v \<prec>\<^sub>t u \<Longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<Longrightarrow> component_of_term v < length fs \<Longrightarrow>
          is_sig_GB_in d G v"
  shows "is_sig_GB_upt d G u"
  unfolding is_sig_GB_upt_def using assms by blast

lemma is_sig_GB_uptD1:
  assumes "is_sig_GB_upt d G u"
  shows "G \<subseteq> dgrad_sig_set d"
  using assms unfolding is_sig_GB_upt_def by blast

lemma is_sig_GB_uptD2:
  assumes "is_sig_GB_upt d G u" and "v \<prec>\<^sub>t u"
  shows "is_sig_GB_in d G v"
  using assms is_sig_GB_inI_triv unfolding is_sig_GB_upt_def by blast

lemma is_sig_GB_uptD3:
  assumes "is_sig_GB_upt d G u" and "r \<in> dgrad_sig_set d" and "lt r \<prec>\<^sub>t u"
  shows "sig_red_zero (\<preceq>\<^sub>t) G r"
  by (rule is_sig_GB_inD, rule is_sig_GB_uptD2, fact+, fact refl)

lemma is_sig_GB_upt_le:
  assumes "is_sig_GB_upt d G u" and "v \<preceq>\<^sub>t u"
  shows "is_sig_GB_upt d G v"
proof (rule is_sig_GB_uptI)
  from assms(1) show "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
next
  fix w
  assume "w \<prec>\<^sub>t v"
  hence "w \<prec>\<^sub>t u" using assms(2) by (rule ord_term_lin.less_le_trans)
  with assms(1) show "is_sig_GB_in d G w" by (rule is_sig_GB_uptD2)
qed

lemma is_sig_GB_upt_mono:
  "is_sig_GB_upt d G u \<Longrightarrow> G \<subseteq> G' \<Longrightarrow> G' \<subseteq> dgrad_sig_set d \<Longrightarrow> is_sig_GB_upt d G' u"
  by (auto simp: is_sig_GB_upt_def dest!: is_sig_GB_in_mono)

lemma is_sig_GB_is_Groebner_basis:
  assumes "dickson_grading d" and "hom_grading d" and "G \<subseteq> dgrad_max_set d" and "\<And>u. is_sig_GB_in d G u"
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
  with assms(2) \<open>f \<in> punit_dgrad_max_set d\<close> obtain r where "r \<in> dgrad_sig_set d" and f: "f = rep_list r"
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
  assumes "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
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
  moreover from assms(2, 3) have "p - q \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_minus)
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
  assumes "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
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
  moreover from assms(2) have "?p \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult_zero)
  moreover from assms(3) have "?q \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult_zero)
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
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
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
  from assms(2) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
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
  from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> obtain q' where q'_red: "(sig_red (\<prec>\<^sub>t) (\<prec>) G)\<^sup>*\<^sup>* q q'"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (\<prec>) G q'" by (rule sig_irredE_dgrad_max_set)
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
  moreover from assms(1) G_sub assms(3) p'_red have "p' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  moreover from assms(1) G_sub assms(4) q'_red have "q' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
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
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d"
    and "q \<in> dgrad_sig_set d" and "lt p = lt q" and "p \<noteq> 0" and "q \<noteq> 0"
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
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
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

lemma sig_red_zero_regularI_adds:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt q)"
    and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d" and "p \<noteq> 0" and "sig_red_zero (\<prec>\<^sub>t) G p"
    and "lt p adds\<^sub>t lt q"
  shows "sig_red_zero (\<prec>\<^sub>t) G q"
proof (cases "q = 0")
  case True
  hence "rep_list q = 0" by (simp only: rep_list_zero)
  with rtrancl_refl[to_pred] show ?thesis by (rule sig_red_zeroI)
next
  case False
  hence "lc q \<noteq> 0" by (rule lc_not_0)
  moreover from assms(5) have "lc p \<noteq> 0" by (rule lc_not_0)
  ultimately have "lc q / lc p \<noteq> 0" by simp
  from assms(7) have eq1: "(lp q - lp p) \<oplus> lt p = lt q"
    by (metis add_diff_cancel_right' adds_termE pp_of_term_splus)
  from assms(7) have "lp p adds lp q" by (simp add: adds_term_def)
  with assms(1) have "d (lp q - lp p) \<le> d (lp q)" by (rule dickson_grading_minus)
  also from assms(4) have "... \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
  finally have "d (lp q - lp p) \<le> dgrad_max d" .
  from assms(2) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set_def)

  let ?mult = "\<lambda>r. monom_mult (lc q / lc p) (lp q - lp p) r"
  from assms(6) obtain p' where p_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* p p'" and "rep_list p' = 0"
    by (rule sig_red_zeroE)
  from p_red have "lt p' = lt p" and "lc p' = lc p"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
  hence "p' \<noteq> 0" using \<open>lc p \<noteq> 0\<close> by auto
  with \<open>lc q / lc p \<noteq> 0\<close> have "?mult p' \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  from \<open>lc q / lc p \<noteq> 0\<close> \<open>p' \<noteq> 0\<close> have "lt (?mult p') = lt q"
    by (simp add: lt_monom_mult \<open>lt p' = lt p\<close> eq1)
  from \<open>lc p \<noteq> 0\<close> have "lc (?mult p') = lc q" by (simp add: \<open>lc p' = lc p\<close>)
  from p_red have mult_p_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (?mult p) (?mult p')"
    by (rule sig_red_rtrancl_monom_mult)
  have "rep_list (?mult p') = 0" by (simp add: rep_list_monom_mult \<open>rep_list p' = 0\<close>)
  hence mult_p'_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G (?mult p')"
    using is_sig_red_addsE by fastforce
  from assms(1) G_sub assms(3) p_red have "p' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  with assms(1) \<open>d (lp q - lp p) \<le> dgrad_max d\<close> have "?mult p' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_monom_mult)

  from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> obtain q' where q_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* q q'"
    and q'_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G q'" by (rule sig_irredE_dgrad_max_set)
  from q_red have "lt q' = lt q" and "lc q' = lc q"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
  hence "q' \<noteq> 0" using \<open>lc q \<noteq> 0\<close> by auto

  from assms(2) have "is_sig_GB_upt d G (lt (?mult p'))" by (simp only: \<open>lt (?mult p') = lt q\<close>)
  moreover from assms(1) G_sub assms(4) q_red have "q' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  moreover note \<open>?mult p' \<in> dgrad_sig_set d\<close>
  moreover have "lt q' = lt (?mult p')" by (simp only: \<open>lt (?mult p') = lt q\<close> \<open>lt q' = lt q\<close>)
  moreover have "lc q' = lc (?mult p')" by (simp only: \<open>lc (?mult p') = lc q\<close> \<open>lc q' = lc q\<close>)
  ultimately have "rep_list q' = rep_list (?mult p')" using q'_irred mult_p'_irred
    by (rule sig_regular_reduced_unique)
  with \<open>rep_list (?mult p') = 0\<close> have "rep_list q' = 0" by simp
  with q_red show ?thesis by (rule sig_red_zeroI)
qed

lemma is_syz_sigI:
  assumes "r \<noteq> 0" and "lt r = u" and "r \<in> dgrad_sig_set d" and "sig_red_zero (\<prec>\<^sub>t) G r"
  shows "is_syz_sig d G u"
  unfolding is_syz_sig_def using assms by blast

lemma is_syz_sigE:
  assumes "is_syz_sig d G u"
  obtains r where "r \<noteq> 0" and "lt r = u" and "r \<in> dgrad_sig_set d" and "sig_red_zero (\<prec>\<^sub>t) G r"
  using assms unfolding is_syz_sig_def by blast

lemma is_syz_sig_dgrad_sig_setE:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_sig_set d" and "is_syz_sig d G u"
  obtains s where "s \<noteq> 0" and "lt s = u" and "s \<in> dgrad_sig_set d" and "rep_list s = 0"
proof -
  from assms(3) obtain r where "r \<noteq> 0" and "lt r = u" and "r \<in> dgrad_sig_set d" and "sig_red_zero (\<prec>\<^sub>t) G r"
    by (rule is_syz_sigE)
  from this(4) obtain s where r_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s" and "rep_list s = 0"
    by (rule sig_red_zeroE)
  show ?thesis
  proof
    from r_red have "lc s = lc r" by (rule sig_red_regular_rtrancl_lc)
    also from \<open>r \<noteq> 0\<close> have "... \<noteq> 0" by (rule lc_not_0)
    finally show "s \<noteq> 0" by (simp add: lc_eq_zero_iff)
  next
    from r_red have "lt s = lt r" by (rule sig_red_regular_rtrancl_lt)
    also have "... = u" by fact
    finally show "lt s = u" .
  next
    from assms(1, 2) \<open>r \<in> dgrad_sig_set d\<close> r_red show "s \<in> dgrad_sig_set d"
      by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  qed fact
qed

lemma is_syz_sig_adds:
  assumes "dickson_grading d" and "is_syz_sig d G u" and "u adds\<^sub>t v"
    and "d (pp_of_term v) \<le> dgrad_max d"
  shows "is_syz_sig d G v"
proof -
  from assms(2) obtain r where "r \<noteq> 0" and "lt r = u" and "r \<in> dgrad_sig_set d"
    and "sig_red_zero (\<prec>\<^sub>t) G r" by (rule is_syz_sigE)
  from assms(3) obtain t where v: "v = t \<oplus> u" by (rule adds_termE)
  show ?thesis
  proof (rule is_syz_sigI)
    from \<open>r \<noteq> 0\<close> show "monom_mult 1 t r \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  next
    from \<open>r \<noteq> 0\<close> show "lt (monom_mult 1 t r) = v" by (simp add: lt_monom_mult v \<open>lt r = u\<close>)
  next
    from assms(4) have "d (t + pp_of_term u) \<le> dgrad_max d" by (simp add: v term_simps)
    with assms(1) have "d t \<le> dgrad_max d" by (simp add: dickson_gradingD1)
    with assms(1) show "monom_mult 1 t r \<in> dgrad_sig_set d" using \<open>r \<in> dgrad_sig_set d\<close>
      by (rule dgrad_sig_set_closed_monom_mult)
  next
    from \<open>sig_red_zero (\<prec>\<^sub>t) G r\<close> show "sig_red_zero (\<prec>\<^sub>t) G (monom_mult 1 t r)"
      by (rule sig_red_zero_monom_mult)
  qed
qed

lemma is_syz_sig_mono: "is_syz_sig d F u \<Longrightarrow> F \<subseteq> F' \<Longrightarrow> is_syz_sig d F' u"
  by (auto simp: is_syz_sig_def dest: sig_red_zero_mono)

lemma is_sig_GB_upt_is_syz_sigD:
  assumes "dickson_grading d" and "is_sig_GB_upt d G u" and "is_syz_sig d G u"
    and "p \<in> dgrad_sig_set d" and "lt p = u"
  shows "sig_red_zero (\<prec>\<^sub>t) G p"
proof -
  from assms(3) obtain r where "r \<noteq> 0" and "lt r = u" and "r \<in> dgrad_sig_set d"
    and "sig_red_zero (\<prec>\<^sub>t) G r" by (rule is_syz_sigE)
  note assms(1)
  moreover from assms(2) have "is_sig_GB_upt d G (lt p)" by (simp only: assms(5))
  moreover note \<open>r \<in> dgrad_sig_set d\<close> assms(4) \<open>r \<noteq> 0\<close> \<open>sig_red_zero (\<prec>\<^sub>t) G r\<close>
  moreover have "lt r adds\<^sub>t lt p" by (simp only: assms(5) \<open>lt r = u\<close> adds_term_refl)
  ultimately show ?thesis by (rule sig_red_zero_regularI_adds)
qed

lemma syzygy_crit:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt p)" and "u \<in> dgrad_sig_set d"
    and "p \<in> dgrad_sig_set d" and "lt u adds\<^sub>t lt p" and "u \<noteq> 0" and "rep_list u = 0"
  shows "sig_red_zero (\<prec>\<^sub>t) G p"
proof -
  note assms(1)
  moreover from assms(6) refl assms(3) have "is_syz_sig d G (lt u)"
  proof (rule is_syz_sigI)
    from rtrancl_refl[to_pred] assms(7) show "sig_red_zero (\<prec>\<^sub>t) G u" by (rule sig_red_zeroI)
  qed
  moreover note assms(5)
  moreover from assms(4) have "d (lp p) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
  ultimately have "is_syz_sig d G (lt p)" by (rule is_syz_sig_adds)
  with assms(1, 2) show ?thesis using assms(4) refl by (rule is_sig_GB_upt_is_syz_sigD)
qed

lemma lemma_21:
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt p)" and "p \<in> dgrad_sig_set d" and "g \<in> G"
    and "rep_list p \<noteq> 0" and "rep_list g \<noteq> 0" and "lt g adds\<^sub>t lt p"
    and "punit.lt (rep_list g) adds punit.lt (rep_list p)"
  shows "is_sig_red (\<preceq>\<^sub>t) (=) G p"
proof -
  let ?lp = "punit.lt (rep_list p)"
  define s where "s = ?lp - punit.lt (rep_list g)"
  from assms(8) have s: "?lp = s + punit.lt (rep_list g)" by (simp add: s_def minus_plus)
  from assms(7) obtain t where lt_p: "lt p = t \<oplus> lt g" by (rule adds_termE)
  show ?thesis
  proof (cases "s \<oplus> lt g \<preceq>\<^sub>t lt p")
    case True
    hence "?lp \<oplus> lt g \<preceq>\<^sub>t punit.lt (rep_list g) \<oplus> lt p"
      by (simp add: s splus_assoc splus_left_commute[of s] splus_mono)
    with assms(4, 6, 5, 8) ord_term_lin.is_le_relI(2) show ?thesis
      by (rule is_sig_red_top_addsI)
  next
    case False
    hence "lt p \<prec>\<^sub>t s \<oplus> lt g" by simp
    hence "t \<prec> s" by (simp add: lt_p ord_term_strict_canc_left)
    hence "t + punit.lt (rep_list g) \<prec> s + punit.lt (rep_list g)" by (rule plus_monotone_strict)
    hence "t + punit.lt (rep_list g) \<prec> ?lp" by (simp only: s)
    from assms(5) have "p \<noteq> 0" by (auto simp: rep_list_zero)
    hence "lc p \<noteq> 0" by (rule lc_not_0)
    from assms(6) have "g \<noteq> 0" by (auto simp: rep_list_zero)
    hence "lc g \<noteq> 0" by (rule lc_not_0)
    with \<open>lc p \<noteq> 0\<close> have 1: "lc p / lc g \<noteq> 0" by simp

    let ?g = "monom_mult (lc p / lc g) t g"
    from 1 \<open>g \<noteq> 0\<close> have "lt ?g = lt p" unfolding lt_p by (rule lt_monom_mult)
    from \<open>lc g \<noteq> 0\<close> have "lc ?g = lc p" by simp
    have "punit.lt (rep_list ?g) = t + punit.lt (rep_list g)"
      unfolding rep_list_monom_mult using 1 assms(6) by (rule punit.lt_monom_mult[simplified])
    also have "... \<prec> ?lp" by fact
    finally have "punit.lt (rep_list ?g) \<prec> ?lp" .
    hence lt_pg: "punit.lt (rep_list (p - ?g)) = ?lp" and "rep_list p \<noteq> rep_list ?g"
      by (auto simp: rep_list_minus punit.lt_minus_eqI_2)
    from this(2) have "rep_list (p - ?g) \<noteq> 0" and "p - ?g \<noteq> 0"
      by (auto simp: rep_list_minus rep_list_zero)

    from assms(2) have "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
    note assms(1)
    moreover have "d t \<le> dgrad_max d"
    proof (rule le_trans)
      have "lp p = t + lp g" by (simp add: lt_p term_simps)
      with assms(1) show "d t \<le> d (lp p)" by (simp add: dickson_grading_adds_imp_le)
    next
      from assms(3) show "d (lp p) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
    qed
    moreover from assms(4) \<open>G \<subseteq> dgrad_sig_set d\<close> have "g \<in> dgrad_sig_set d" ..
    ultimately have "?g \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult)

    note assms(2)
    moreover from assms(3) \<open>?g \<in> dgrad_sig_set d\<close> have "p - ?g \<in> dgrad_sig_set d"
      by (rule dgrad_sig_set_closed_minus)
    moreover from \<open>p - ?g \<noteq> 0\<close> \<open>lt ?g = lt p\<close> \<open>lc ?g = lc p\<close> have "lt (p - ?g) \<prec>\<^sub>t lt p"
      by (rule lt_minus_lessI)
    ultimately have "sig_red_zero (\<preceq>\<^sub>t) G (p - ?g)"
      by (rule is_sig_GB_uptD3)
    moreover note \<open>rep_list (p - ?g) \<noteq> 0\<close>
    moreover have "(\<preceq>\<^sub>t) = (\<preceq>\<^sub>t) \<or> (\<preceq>\<^sub>t) = (\<prec>\<^sub>t)" by simp
    ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) G (p - ?g)" by (rule sig_red_zero_nonzero)
    then obtain g1 where "g1 \<in> G" and "rep_list g1 \<noteq> 0"
      and 2: "punit.lt (rep_list g1) adds punit.lt (rep_list (p - ?g))"
      and 3: "punit.lt (rep_list (p - ?g)) \<oplus> lt g1 \<preceq>\<^sub>t punit.lt (rep_list g1) \<oplus> lt (p - ?g)"
      by (rule is_sig_red_top_addsE)
    from \<open>g1 \<in> G\<close> \<open>rep_list g1 \<noteq> 0\<close> assms(5) show ?thesis
    proof (rule is_sig_red_top_addsI)
      from 2 show "punit.lt (rep_list g1) adds punit.lt (rep_list p)" by (simp only: lt_pg)
    next
      have "?lp \<oplus> lt g1 = punit.lt (rep_list (p - ?g)) \<oplus> lt g1" by (simp only: lt_pg)
      also have "... \<preceq>\<^sub>t punit.lt (rep_list g1) \<oplus> lt (p - ?g)" by (fact 3)
      also from \<open>lt (p - ?g) \<prec>\<^sub>t lt p\<close> have "... \<prec>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p"
        by (rule splus_mono_strict)
      finally show "?lp \<oplus> lt g1 \<preceq>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p" by (rule ord_term_lin.less_imp_le)
    qed simp
  qed
qed

subsubsection \<open>Rewrite Bases\<close>

definition spp_of :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b))"
  where "spp_of r = (lt r, rep_list r)"

text \<open>``spp'' stands for ``sig-poly-pair''.\<close>

definition is_rewrite_ord :: "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_rewrite_ord rword \<longleftrightarrow> (reflp rword \<and> transp rword \<and> (\<forall>a b. rword a b \<or> rword b a) \<and>
                                  (\<forall>a b. rword a b \<longrightarrow> rword b a \<longrightarrow> fst a = fst b) \<and>
                                  (\<forall>d G a b. dickson_grading d \<longrightarrow> is_sig_GB_upt d G (lt b) \<longrightarrow>
                                          a \<in> G \<longrightarrow> b \<in> G \<longrightarrow> a \<noteq> 0 \<longrightarrow> b \<noteq> 0 \<longrightarrow> lt a adds\<^sub>t lt b \<longrightarrow>
                                          \<not> is_sig_red (\<prec>\<^sub>t) (=) G b \<longrightarrow> rword (spp_of a) (spp_of b)))"

definition is_canon_rewriter :: "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_canon_rewriter rword A u p \<longleftrightarrow>
                  (p \<in> A \<and> p \<noteq> 0 \<and> lt p adds\<^sub>t u \<and> (\<forall>a\<in>A. a \<noteq> 0 \<longrightarrow> lt a adds\<^sub>t u \<longrightarrow> rword (spp_of a) (spp_of p)))"

definition is_RB_in :: "('a \<Rightarrow> nat) \<Rightarrow> (('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_RB_in d rword G u \<longleftrightarrow>
            ((\<exists>g\<in>G. is_canon_rewriter rword G u g \<and> \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g)) \<or>
             is_syz_sig d G u)"

definition is_RB_upt :: "('a \<Rightarrow> nat) \<Rightarrow> (('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> 't \<Rightarrow> bool"
  where "is_RB_upt d rword G u \<longleftrightarrow>
            (G \<subseteq> dgrad_sig_set d \<and> (\<forall>v. v \<prec>\<^sub>t u \<longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<longrightarrow>
                                      component_of_term v < length fs \<longrightarrow> is_RB_in d rword G v))"

lemma is_rewrite_ordI:
  assumes "reflp rword" and "transp rword" and "\<And>a b. rword a b \<or> rword b a"
    and "\<And>a b. rword a b \<Longrightarrow> rword b a \<Longrightarrow> fst a = fst b"
    and "\<And>d G a b. dickson_grading d \<Longrightarrow> is_sig_GB_upt d G (lt b) \<Longrightarrow> a \<in> G \<Longrightarrow> b \<in> G \<Longrightarrow>
                   a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t lt b \<Longrightarrow> \<not> is_sig_red (\<prec>\<^sub>t) (=) G b \<Longrightarrow> rword (spp_of a) (spp_of b)"
  shows "is_rewrite_ord rword"
  unfolding is_rewrite_ord_def using assms by blast

lemma is_rewrite_ordD1: "is_rewrite_ord rword \<Longrightarrow> rword a a"
  by (simp add: is_rewrite_ord_def reflpD)

lemma is_rewrite_ordD2: "is_rewrite_ord rword \<Longrightarrow> rword a b \<Longrightarrow> rword b c \<Longrightarrow> rword a c"
  by (auto simp: is_rewrite_ord_def dest: transpD)

lemma is_rewrite_ordD3:
  assumes "is_rewrite_ord rword"
    and "rword a b \<Longrightarrow> thesis"
    and "\<not> rword a b \<Longrightarrow> rword b a \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have disj: "rword a b \<or> rword b a"
    by (simp add: is_rewrite_ord_def del: split_paired_All)
  show ?thesis
  proof (cases "rword a b")
    case True
    thus ?thesis by (rule assms(2))
  next
    case False
    moreover from this disj have "rword b a" by simp
    ultimately show ?thesis by (rule assms(3))
  qed
qed

lemma is_rewrite_ordD4:
  assumes "is_rewrite_ord rword" and "rword a b" and "rword b a"
  shows "fst a = fst b"
  using assms unfolding is_rewrite_ord_def by blast

lemma is_rewrite_ordD4':
  assumes "is_rewrite_ord rword" and "rword (spp_of a) (spp_of b)" and "rword (spp_of b) (spp_of a)"
  shows "lt a = lt b"
proof -
  from assms have "fst (spp_of a) = fst (spp_of b)" by (rule is_rewrite_ordD4)
  thus ?thesis by (simp add: spp_of_def)
qed

lemma is_rewrite_ordD5:
  assumes "is_rewrite_ord rword" and "dickson_grading d" and "is_sig_GB_upt d G (lt b)"
    and "a \<in> G" and "b \<in> G" and "a \<noteq> 0" and "b \<noteq> 0" and "lt a adds\<^sub>t lt b"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G b"
  shows "rword (spp_of a) (spp_of b)"
  using assms unfolding is_rewrite_ord_def by blast

lemma is_canon_rewriterI:
  assumes "p \<in> A" and "p \<noteq> 0" and "lt p adds\<^sub>t u"
    and "\<And>a. a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of p)"
  shows "is_canon_rewriter rword A u p"
  unfolding is_canon_rewriter_def using assms by blast

lemma is_canon_rewriterD1: "is_canon_rewriter rword A u p \<Longrightarrow> p \<in> A"
  by (simp add: is_canon_rewriter_def)

lemma is_canon_rewriterD2: "is_canon_rewriter rword A u p \<Longrightarrow> p \<noteq> 0"
  by (simp add: is_canon_rewriter_def)

lemma is_canon_rewriterD3: "is_canon_rewriter rword A u p \<Longrightarrow> lt p adds\<^sub>t u"
  by (simp add: is_canon_rewriter_def)

lemma is_canon_rewriterD4:
  "is_canon_rewriter rword A u p \<Longrightarrow> a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of p)"
  by (simp add: is_canon_rewriter_def)

lemmas is_canon_rewriterD = is_canon_rewriterD1 is_canon_rewriterD2 is_canon_rewriterD3 is_canon_rewriterD4

lemma is_rewrite_ord_finite_canon_rewriterE:
  assumes "is_rewrite_ord rword" and "finite A" and "a \<in> A" and "a \<noteq> 0" and "lt a adds\<^sub>t u"
    \<comment>\<open>The finiteness condition could be replaced by a condition expressing that @{term u}
        has only finitely many ``adders''.\<close>
  obtains p where "is_canon_rewriter rword A u p"
proof -
  let ?A = "{x. x \<in> A \<and> x \<noteq> 0 \<and> lt x adds\<^sub>t u}"
  let ?rel = "\<lambda>x y. strict rword (spp_of y) (spp_of x)"
  have "finite ?A"
  proof (rule finite_subset)
    show "?A \<subseteq> A" by blast
  qed fact
  moreover have "?A \<noteq> {}"
  proof
    from assms(3, 4, 5) have "a \<in> ?A" by simp
    also assume "?A = {}"
    finally show False by simp
  qed
  moreover have "irreflp ?rel"
  proof -
    from assms(1) have "reflp rword" by (simp add: is_rewrite_ord_def)
    thus ?thesis by (simp add: reflp_def irreflp_def)
  qed
  moreover have "transp ?rel"
  proof -
    from assms(1) have "transp rword" by (simp add: is_rewrite_ord_def)
    thus ?thesis by (auto simp: transp_def simp del: split_paired_All)
  qed
  ultimately obtain p where "p \<in> ?A" and *: "\<And>b. ?rel b p \<Longrightarrow> b \<notin> ?A" by (rule finite_minimalE, blast)
  from this(1) have "p \<in> A" and "p \<noteq> 0" and "lt p adds\<^sub>t u" by simp_all
  show ?thesis
  proof (rule, rule is_canon_rewriterI)
    fix q
    assume "q \<in> A" and "q \<noteq> 0" and "lt q adds\<^sub>t u"
    hence "q \<in> ?A" by simp
    with * have "\<not> ?rel q p" by blast
    hence disj: "\<not> rword (spp_of p) (spp_of q) \<or> rword (spp_of q) (spp_of p)" by simp
    from assms(1) show "rword (spp_of q) (spp_of p)"
    proof (rule is_rewrite_ordD3)
      assume "\<not> rword (spp_of q) (spp_of p)" and "rword (spp_of p) (spp_of q)"
      with disj show ?thesis by simp
    qed
  qed fact+
qed

lemma is_rewrite_ord_canon_rewriterD1:
  assumes "is_rewrite_ord rword" and "is_canon_rewriter rword A u p" and "is_canon_rewriter rword A v q"
    and "lt p adds\<^sub>t v" and "lt q adds\<^sub>t u"
  shows "lt p = lt q"
proof -
  from assms(2) have "p \<in> A" and "p \<noteq> 0"
    and 1: "\<And>a. a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of p)"
    by (rule is_canon_rewriterD)+
  from assms(3) have "q \<in> A" and "q \<noteq> 0"
    and 2: "\<And>a. a \<in> A \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t v \<Longrightarrow> rword (spp_of a) (spp_of q)"
    by (rule is_canon_rewriterD)+
  note assms(1)
  moreover from \<open>p \<in> A\<close> \<open>p \<noteq> 0\<close> assms(4) have "rword (spp_of p) (spp_of q)" by (rule 2)
  moreover from \<open>q \<in> A\<close> \<open>q \<noteq> 0\<close> assms(5) have "rword (spp_of q) (spp_of p)" by (rule 1)
  ultimately show ?thesis by (rule is_rewrite_ordD4')
qed

corollary is_rewrite_ord_canon_rewriterD2:
  assumes "is_rewrite_ord rword" and "is_canon_rewriter rword A u p" and "is_canon_rewriter rword A u q"
  shows "lt p = lt q"
  using assms
proof (rule is_rewrite_ord_canon_rewriterD1)
  from assms(2) show "lt p adds\<^sub>t u" by (rule is_canon_rewriterD)
next
  from assms(3) show "lt q adds\<^sub>t u" by (rule is_canon_rewriterD)
qed

lemma is_rewrite_ord_canon_rewriterD3:
  assumes "is_rewrite_ord rword" and "dickson_grading d" and "is_canon_rewriter rword A u p"
    and "a \<in> A" and "a \<noteq> 0" and "lt a adds\<^sub>t u" and "is_sig_GB_upt d A (lt a)"
    and "lt p adds\<^sub>t lt a" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) A a"
  shows "lt p = lt a"
proof -
  note assms(1)
  moreover from assms(1, 2, 7) _ assms(4) _ assms(5, 8, 9) have "rword (spp_of p) (spp_of a)"
  proof (rule is_rewrite_ordD5)
    from assms(3) show "p \<in> A" and "p \<noteq> 0" by (rule is_canon_rewriterD)+
  qed
  moreover from assms(3, 4, 5, 6) have "rword (spp_of a) (spp_of p)" by (rule is_canon_rewriterD4)
  ultimately show ?thesis by (rule is_rewrite_ordD4')
qed

lemma is_RB_inI1:
  assumes "is_canon_rewriter rword G u g" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g)"
  shows "is_RB_in d rword G u"
  unfolding is_RB_in_def using assms is_canon_rewriterD1 by blast

lemma is_RB_inI2:
  assumes "is_syz_sig d G u"
  shows "is_RB_in d rword G u"
  unfolding is_RB_in_def Let_def using assms by blast

lemma is_RB_inE:
  assumes "is_RB_in d rword G u"
    and "is_syz_sig d G u \<Longrightarrow> thesis"
    and "\<And>g. \<not> is_syz_sig d G u \<Longrightarrow> is_canon_rewriter rword G u g \<Longrightarrow>
            \<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g) \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding is_RB_in_def by blast

lemma is_RB_inD:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_sig_set d" and "is_RB_in d rword G u"
    and "\<not> is_syz_sig d G u" and "d (pp_of_term u) \<le> dgrad_max d"
    and "is_canon_rewriter rword G u g"
  shows "rep_list g \<noteq> 0"
proof
  assume a: "rep_list g = 0"
  from assms(1) have "is_syz_sig d G u"
  proof (rule is_syz_sig_adds)
    show "is_syz_sig d G (lt g)"
    proof (rule is_syz_sigI)
      from assms(6) show "g \<noteq> 0" by (rule is_canon_rewriterD2)
    next
      from assms(6) have "g \<in> G" by (rule is_canon_rewriterD1)
      thus "g \<in> dgrad_sig_set d" using assms(2) ..
    next
      from rtrancl_refl[to_pred] a show "sig_red_zero (\<prec>\<^sub>t) G g" by (rule sig_red_zeroI)
    qed (fact refl)
  next
    from assms(6) show "lt g adds\<^sub>t u" by (rule is_canon_rewriterD3)
  qed fact
  with assms(4) show False ..
qed

lemma is_RB_uptI:
  assumes "G \<subseteq> dgrad_sig_set d"
    and "\<And>v. v \<prec>\<^sub>t u \<Longrightarrow> d (pp_of_term v) \<le> dgrad_max d \<Longrightarrow> component_of_term v < length fs \<Longrightarrow>
            is_RB_in d canon G v"
  shows "is_RB_upt d canon G u"
  unfolding is_RB_upt_def using assms by blast

lemma is_RB_uptD1:
  assumes "is_RB_upt d canon G u"
  shows "G \<subseteq> dgrad_sig_set d"
  using assms unfolding is_RB_upt_def by blast

lemma is_RB_uptD2:
  assumes "is_RB_upt d canon G u" and "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d"
    and "component_of_term v < length fs"
  shows "is_RB_in d canon G v"
  using assms unfolding is_RB_upt_def by blast

lemma is_RB_in_UnI:
  assumes "is_RB_in d rword G u" and "\<And>h. h \<in> H \<Longrightarrow> u \<prec>\<^sub>t lt h"
  shows "is_RB_in d rword (H \<union> G) u"
  using assms(1)
proof (rule is_RB_inE)
  assume "is_syz_sig d G u"
  moreover have "G \<subseteq> H \<union> G" by blast
  ultimately have "is_syz_sig d (H \<union> G) u" by (rule is_syz_sig_mono)
  thus "is_RB_in d rword (H \<union> G) u" by (rule is_RB_inI2)
next
  fix g'
  assume crw: "is_canon_rewriter rword G u g'"
    and irred: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g') g')"
  from crw have "g' \<in> G" and "g' \<noteq> 0" and "lt g' adds\<^sub>t u"
    and max: "\<And>a. a \<in> G \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> lt a adds\<^sub>t u \<Longrightarrow> rword (spp_of a) (spp_of g')"
    by (rule is_canon_rewriterD)+
  show "is_RB_in d rword (H \<union> G) u"
  proof (rule is_RB_inI1)
    show "is_canon_rewriter rword (H \<union> G) u g'"
    proof (rule is_canon_rewriterI)
      from \<open>g' \<in> G\<close> show "g' \<in> H \<union> G" by simp
    next
      fix a
      assume "a \<in> H \<union> G" and "a \<noteq> 0" and "lt a adds\<^sub>t u"
      from this(1) show "rword (spp_of a) (spp_of g')"
      proof
        assume "a \<in> H"
        with \<open>lt a adds\<^sub>t u\<close> have "lt a adds\<^sub>t u" by simp
        hence "lt a \<preceq>\<^sub>t u" by (rule ord_adds_term)
        moreover from \<open>a \<in> H\<close> have "u \<prec>\<^sub>t lt a" by (rule assms(2))
        ultimately show ?thesis by simp
      next
        assume "a \<in> G"
        thus ?thesis using \<open>a \<noteq> 0\<close> \<open>lt a adds\<^sub>t u\<close> by (rule max)
      qed
    qed fact+
  next
    show "\<not> is_sig_red (\<prec>\<^sub>t) (=) (H \<union> G) (monom_mult 1 (pp_of_term u - lp g') g')"
      (is "\<not> is_sig_red _ _ _ ?g")
    proof
      assume "is_sig_red (\<prec>\<^sub>t) (=) (H \<union> G) ?g"
      with irred have "is_sig_red (\<prec>\<^sub>t) (=) H ?g" by (simp add: is_sig_red_Un del: Un_insert_left)
      then obtain h where "h \<in> H" and "is_sig_red (\<prec>\<^sub>t) (=) {h} ?g" by (rule is_sig_red_singletonI)
      from this(2) have "lt h \<prec>\<^sub>t lt ?g" by (rule is_sig_red_regularD)
      also from \<open>g' \<noteq> 0\<close> \<open>lt g' adds\<^sub>t u\<close> have "... = u"
        by (auto simp: lt_monom_mult adds_term_alt pp_of_term_splus)
      finally have "lt h \<prec>\<^sub>t u" .
      moreover from \<open>h \<in> H\<close> have "u \<prec>\<^sub>t lt h" by (rule assms(2))
      ultimately show False by simp
    qed
  qed
qed

corollary is_RB_in_insertI:
  assumes "is_RB_in d rword G u" and "u \<prec>\<^sub>t lt g"
  shows "is_RB_in d rword (insert g G) u"
proof -
  from assms(1) have "is_RB_in d rword ({g} \<union> G) u"
  proof (rule is_RB_in_UnI)
    fix h
    assume "h \<in> {g}"
    with assms(2) show "u \<prec>\<^sub>t lt h" by simp
  qed
  thus ?thesis by simp
qed

corollary is_RB_upt_UnI:
  assumes "is_RB_upt d rword G u" and "H \<subseteq> dgrad_sig_set d" and "\<And>h. h \<in> H \<Longrightarrow> u \<preceq>\<^sub>t lt h"
  shows "is_RB_upt d rword (H \<union> G) u"
proof (rule is_RB_uptI)
  from assms(1) have "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  with assms(2) show "H \<union> G \<subseteq> dgrad_sig_set d" by (rule Un_least)
next
  fix v
  assume "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d" and "component_of_term v < length fs"
  with assms(1) have "is_RB_in d rword G v" by (rule is_RB_uptD2)
  moreover from \<open>v \<prec>\<^sub>t u\<close> assms(3) have "\<And>h. h \<in> H \<Longrightarrow> v \<prec>\<^sub>t lt h" by (rule ord_term_lin.less_le_trans)
  ultimately show "is_RB_in d rword (H \<union> G) v" by (rule is_RB_in_UnI)
qed

corollary is_RB_upt_insertI:
  assumes "is_RB_upt d rword G u" and "g \<in> dgrad_sig_set d" and "u \<preceq>\<^sub>t lt g"
  shows "is_RB_upt d rword (insert g G) u"
proof -
  from assms(1) have "is_RB_upt d rword ({g} \<union> G) u"
  proof (rule is_RB_upt_UnI)
    from assms(2) show "{g} \<subseteq> dgrad_sig_set d" by simp
  next
    fix h
    assume "h \<in> {g}"
    with assms(3) show "u \<preceq>\<^sub>t lt h" by simp
  qed
  thus ?thesis by simp
qed

lemma is_RB_upt_is_sig_GB_upt:
  assumes "dickson_grading d" and "is_RB_upt d rword G u"
  shows "is_sig_GB_upt d G u"
proof (rule ccontr)
  let ?Q = "{v. v \<prec>\<^sub>t u \<and> d (pp_of_term v) \<le> dgrad_max d \<and> component_of_term v < length fs \<and> \<not> is_sig_GB_in d G v}"
  have Q_sub: "pp_of_term ` ?Q \<subseteq> dgrad_set d (dgrad_max d)" by blast
  from assms(2) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
  assume "\<not> is_sig_GB_upt d G u"
  with G_sub obtain v' where "v' \<in> ?Q" unfolding is_sig_GB_upt_def by blast
  with assms(1) obtain v where "v \<in> ?Q" and min: "\<And>y. y \<prec>\<^sub>t v \<Longrightarrow> y \<notin> ?Q" using Q_sub
    by (rule ord_term_minimum_dgrad_set, blast)
  from \<open>v \<in> ?Q\<close> have "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d" and "component_of_term v < length fs"
    and "\<not> is_sig_GB_in d G v" by simp_all
  from assms(2) this(1, 2, 3) have "is_RB_in d rword G v" by (rule is_RB_uptD2)
  from \<open>\<not> is_sig_GB_in d G v\<close> obtain r where "lt r = v" and "r \<in> dgrad_sig_set d" and "\<not> sig_red_zero (\<preceq>\<^sub>t) G r"
    unfolding is_sig_GB_in_def by blast
  from this(3) have "rep_list r \<noteq> 0" by (auto simp: sig_red_zero_def)
  hence "r \<noteq> 0" by (auto simp: rep_list_zero)
  hence "lc r \<noteq> 0" by (rule lc_not_0)

  from G_sub have "is_sig_GB_upt d G v"
  proof (rule is_sig_GB_uptI)
    fix w
    assume dw: "d (pp_of_term w) \<le> dgrad_max d" and cp: "component_of_term w < length fs"
    assume "w \<prec>\<^sub>t v"
    hence "w \<notin> ?Q" by (rule min)
    hence "\<not> w \<prec>\<^sub>t u \<or> is_sig_GB_in d G w" by (simp add: dw cp)
    thus "is_sig_GB_in d G w"
    proof
      assume "\<not> w \<prec>\<^sub>t u"
      moreover from \<open>w \<prec>\<^sub>t v\<close> \<open>v \<prec>\<^sub>t u\<close> have "w \<prec>\<^sub>t u" by (rule ord_term_lin.less_trans)
      ultimately show ?thesis ..
    qed
  qed

  from \<open>is_RB_in d rword G v\<close> have "sig_red_zero (\<preceq>\<^sub>t) G r"
  proof (rule is_RB_inE)
    assume "is_syz_sig d G v"
    have "sig_red_zero (\<prec>\<^sub>t) G r" by (rule is_sig_GB_upt_is_syz_sigD, fact+)
    thus ?thesis by (rule sig_red_zero_sing_regI)
  next
    fix g
    assume a: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g) g)"
    assume "is_canon_rewriter rword G v g"
    hence "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t v" by (rule is_canon_rewriterD)+
    assume "\<not> is_syz_sig d G v"
    from \<open>g \<in> G\<close> G_sub have "g \<in> dgrad_sig_set d" ..
    from \<open>g \<noteq> 0\<close> have "lc g \<noteq> 0" by (rule lc_not_0)
    with \<open>lc r \<noteq> 0\<close> have "lc r / lc g \<noteq> 0" by simp
    from \<open>lt g adds\<^sub>t v\<close> have "lt g adds\<^sub>t lt r" by (simp only: \<open>lt r = v\<close>)
    hence eq1: "(lp r - lp g) \<oplus> lt g = lt r" by (metis add_implies_diff adds_termE pp_of_term_splus)

    let ?h = "monom_mult (lc r / lc g) (lp r - lp g) g"
    from \<open>lc g \<noteq> 0\<close> \<open>lc r \<noteq> 0\<close> \<open>g \<noteq> 0\<close> have "?h \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
    have h_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G ?h"
    proof
      assume "is_sig_red (\<prec>\<^sub>t) (=) G ?h"
      moreover from \<open>lc g \<noteq> 0\<close> \<open>lc r \<noteq> 0\<close> have "lc g / lc r \<noteq> 0" by simp
      ultimately have "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult (lc g / lc r) 0 ?h)" by (rule is_sig_red_monom_mult)
      with \<open>lc g \<noteq> 0\<close> \<open>lc r \<noteq> 0\<close> have "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g) g)"
        by (simp add: monom_mult_assoc \<open>lt r = v\<close>)
      with a show False ..
    qed
    from \<open>lc r / lc g \<noteq> 0\<close> \<open>g \<noteq> 0\<close> have "lt ?h = lt r" by (simp add: lt_monom_mult eq1)
    hence "lt ?h = v" by (simp only: \<open>lt r = v\<close>)
    from \<open>lc g \<noteq> 0\<close> have "lc ?h = lc r" by simp
    from assms(1) _ \<open>g \<in> dgrad_sig_set d\<close> have "?h \<in> dgrad_sig_set d"
    proof (rule dgrad_sig_set_closed_monom_mult)
      from \<open>lt g adds\<^sub>t lt r\<close> have "lp g adds lp r" by (simp add: adds_term_def)
      with assms(1) have "d (lp r - lp g) \<le> d (lp r)" by (rule dickson_grading_minus)
      also from \<open>r \<in> dgrad_sig_set d\<close> have "... \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
      finally show "d (lp r - lp g) \<le> dgrad_max d" .
    qed
    have "rep_list ?h \<noteq> 0"
    proof
      assume "rep_list ?h = 0"
      with rtrancl_refl[to_pred] have "sig_red_zero (\<prec>\<^sub>t) G ?h" by (rule sig_red_zeroI)
      with \<open>?h \<noteq> 0\<close> \<open>lt ?h = v\<close> \<open>?h \<in> dgrad_sig_set d\<close> have "is_syz_sig d G v" by (rule is_syz_sigI)
      with \<open>\<not> is_syz_sig d G v\<close> show False ..
    qed
    hence "rep_list g \<noteq> 0" by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
    hence "punit.lc (rep_list g) \<noteq> 0" by (rule punit.lc_not_0)
    from assms(1) \<open>G \<subseteq> dgrad_max_set d\<close> obtain s where s_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s"
      and s_irred: "\<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) G s" by (rule sig_irredE_dgrad_max_set)
    from s_red have s_red': "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s" by (rule sig_red_rtrancl_sing_regI)
    have "rep_list s \<noteq> 0"
    proof
      assume "rep_list s = 0"
      with s_red' have "sig_red_zero (\<preceq>\<^sub>t) G r" by (rule sig_red_zeroI)
      with \<open>\<not> sig_red_zero (\<preceq>\<^sub>t) G r\<close> show False ..
    qed
    from assms(1) G_sub \<open>r \<in> dgrad_sig_set d\<close> s_red have "s \<in> dgrad_sig_set d"
      by (rule dgrad_sig_set_closed_sig_red_rtrancl)
    from s_red have "lt s = lt r" and "lc s = lc r"
      by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc)
    hence "lt ?h = lt s" and "lc ?h = lc s" and "s \<noteq> 0"
      using \<open>lc r \<noteq> 0\<close> by (auto simp: \<open>lt ?h = lt r\<close> \<open>lc ?h = lc r\<close> simp del: lc_monom_mult)
    from s_irred have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G s" by (simp add: is_sig_red_top_tail_cases)
    from \<open>is_sig_GB_upt d G v\<close> have "is_sig_GB_upt d G (lt s)" by (simp only: \<open>lt s = lt r\<close> \<open>lt r = v\<close>)
    have "punit.lt (rep_list ?h) = punit.lt (rep_list s)"
      by (rule sig_regular_top_reduced_lt_unique, fact+)
    hence eq2: "lp r - lp g + punit.lt (rep_list g) = punit.lt (rep_list s)"
      using \<open>lc r / lc g \<noteq> 0\<close> \<open>rep_list g \<noteq> 0\<close> by (simp add: rep_list_monom_mult punit.lt_monom_mult)
    have "punit.lc (rep_list ?h) = punit.lc (rep_list s)"
      by (rule sig_regular_top_reduced_lc_unique, fact+)
    hence eq3: "lc r / lc g = punit.lc (rep_list s) / punit.lc (rep_list g)"
      using \<open>punit.lc (rep_list g) \<noteq> 0\<close> by (simp add: rep_list_monom_mult field_simps)
    have "sig_red_single (=) (=) s (s - ?h) g (lp r - lp g)"
      by (rule sig_red_singleI, auto simp: eq1 eq2 eq3 punit.lc_def[symmetric] \<open>lt s = lt r\<close>
            \<open>rep_list g \<noteq> 0\<close> \<open>rep_list s \<noteq> 0\<close> intro!: punit.lt_in_keys)
    with \<open>g \<in> G\<close> have "sig_red (=) (=) G s (s - ?h)" unfolding sig_red_def by blast
    hence "sig_red (\<preceq>\<^sub>t) (\<preceq>) G s (s - ?h)" by (auto dest: sig_red_sing_regI sig_red_top_tailI)
    with s_red' have r_red: "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r (s - ?h)" ..
    show ?thesis
    proof (cases "s - ?h = 0")
      case True
      hence "rep_list (s - ?h) = 0" by (simp only: rep_list_zero)
      with r_red show ?thesis by (rule sig_red_zeroI)
    next
      case False
      note \<open>is_sig_GB_upt d G (lt s)\<close>
      moreover from \<open>s \<in> dgrad_sig_set d\<close> \<open>?h \<in> dgrad_sig_set d\<close> have "s - ?h \<in> dgrad_sig_set d"
        by (rule dgrad_sig_set_closed_minus)
      moreover from False \<open>lt ?h = lt s\<close> \<open>lc ?h = lc s\<close> have "lt (s - ?h) \<prec>\<^sub>t lt s" by (rule lt_minus_lessI)
      ultimately have "sig_red_zero (\<preceq>\<^sub>t) G (s - ?h)" by (rule is_sig_GB_uptD3)
      then obtain s' where "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* (s - ?h) s'" and "rep_list s' = 0"
        by (rule sig_red_zeroE)
      from r_red this(1) have "(sig_red (\<preceq>\<^sub>t) (\<preceq>) G)\<^sup>*\<^sup>* r s'" by simp
      thus ?thesis using \<open>rep_list s' = 0\<close> by (rule sig_red_zeroI)
    qed
  qed
  with \<open>\<not> sig_red_zero (\<preceq>\<^sub>t) G r\<close> show False ..
qed

corollary is_RB_upt_is_syz_sigD:
  assumes "dickson_grading d" and "is_RB_upt d rword G u"
    and "is_syz_sig d G u" and "p \<in> dgrad_sig_set d" and "lt p = u"
  shows "sig_red_zero (\<prec>\<^sub>t) G p"
proof -
  note assms(1)
  moreover from assms(1, 2) have "is_sig_GB_upt d G u" by (rule is_RB_upt_is_sig_GB_upt)
  ultimately show ?thesis using assms(3, 4, 5) by (rule is_sig_GB_upt_is_syz_sigD)
qed

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
  assumes "dickson_grading d" and "is_sig_GB_upt d G (lt p)" and "p \<in> dgrad_sig_set d"
    and "q \<in> dgrad_sig_set d" and "p \<noteq> 0" and "sig_red_zero_or_sing_top_red (\<prec>\<^sub>t) G p" and "lt q = lt p"
  shows "sig_red_zero_or_sing_top_red (\<prec>\<^sub>t) G q"
proof (cases "q = 0")
  case True
  hence "rep_list q = 0" by (simp only: rep_list_zero)
  thus ?thesis by (rule sig_red_zero_or_sing_top_red_zero)
next
  case False
  hence "lc q \<noteq> 0" by (rule lc_not_0)
  from assms(5) have "lc p \<noteq> 0" by (rule lc_not_0)
  from assms(2) have "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
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
  moreover from assms(1) \<open>G \<subseteq> dgrad_sig_set d\<close> assms(4) a have "s' \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
  moreover from assms(1) \<open>G \<subseteq> dgrad_sig_set d\<close> assms(3) 1 have "s \<in> dgrad_sig_set d"
    by (rule dgrad_sig_set_closed_sig_red_rtrancl)
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

lemma dgrad_sig_set_closed_spair:
  assumes "dickson_grading d" and "p \<in> dgrad_sig_set d" and "q \<in> dgrad_sig_set d"
  shows "spair p q \<in> dgrad_sig_set d"
proof -
  define t1 where "t1 = punit.lt (rep_list p)"
  define t2 where "t2 = punit.lt (rep_list q)"
  let ?l = "lcs t1 t2"
  have "d t1 \<le> dgrad_max d"
  proof (cases "rep_list p = 0")
    case True
    show ?thesis by (simp add: t1_def True dgrad_max_0)
  next
    case False
    from assms(2) have "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
    with assms(1) have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
    thus ?thesis unfolding t1_def using False by (rule punit.dgrad_p_setD_lt[simplified])
  qed
  moreover have "d t2 \<le> dgrad_max d"
  proof (cases "rep_list q = 0")
    case True
    show ?thesis by (simp add: t2_def True dgrad_max_0)
  next
    case False
    from assms(3) have "q \<in> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
    with assms(1) have "rep_list q \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
    thus ?thesis unfolding t2_def using False by (rule punit.dgrad_p_setD_lt[simplified])
  qed
  ultimately have "ord_class.max (d t1) (d t2) \<le> dgrad_max d" by simp
  moreover from assms(1) have "d ?l \<le> ord_class.max (d t1) (d t2)" by (rule dickson_grading_lcs)
  ultimately have *: "d ?l \<le> dgrad_max d" by auto
  thm dickson_grading_minus
  show ?thesis
  proof (simp add: spair_def Let_def t1_def[symmetric] t2_def[symmetric],
      intro dgrad_sig_set_closed_minus dgrad_sig_set_closed_monom_mult[OF assms(1)])
    from assms(1) adds_lcs have "d (?l - t1) \<le> d ?l" by (rule dickson_grading_minus)
    thus "d (?l - t1) \<le> dgrad_max d" using * by (rule le_trans)
  next
    from assms(1) adds_lcs_2 have "d (?l - t2) \<le> d ?l" by (rule dickson_grading_minus)
    thus "d (?l - t2) \<le> dgrad_max d" using * by (rule le_trans)
  qed fact+
qed

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

lemma is_regular_spair_sym: "is_regular_spair p q \<Longrightarrow> is_regular_spair q p"
  by (auto simp: is_regular_spair_def Let_def lcs_comm)

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

lemma is_regular_spairD1: "is_regular_spair p q \<Longrightarrow> rep_list p \<noteq> 0"
  by (simp add: is_regular_spair_def)

lemma is_regular_spairD2: "is_regular_spair p q \<Longrightarrow> rep_list q \<noteq> 0"
  by (simp add: is_regular_spair_def)

lemma is_regular_spairD3:
  assumes "is_regular_spair p q"
  shows "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q"
proof
  define t1 where "t1 = punit.lt (rep_list p)"
  define t2 where "t2 = punit.lt (rep_list q)"
  assume "t2 \<oplus> lt p = t1 \<oplus> lt q"
  hence eq: "(lcs t1 t2 - t1) \<oplus> lt p = (lcs t1 t2 - t2) \<oplus> lt q"
    by (simp add: term_is_le_rel_minus_minus adds_lcs adds_lcs_2)

  from assms have "rep_list p \<noteq> 0" by (rule is_regular_spairD1)
  hence "punit.lc (rep_list p) \<noteq> 0" and "p \<noteq> 0" by (auto simp: rep_list_zero punit.lc_eq_zero_iff)
  from assms have "rep_list q \<noteq> 0" by (rule is_regular_spairD2)
  hence "punit.lc (rep_list q) \<noteq> 0" and "q \<noteq> 0" by (auto simp: rep_list_zero punit.lc_eq_zero_iff)

  have "(lcs t1 t2 - t1) \<oplus> lt p = lt (monom_mult (1 / punit.lc (rep_list p)) (lcs t1 t2 - t1) p)"
    using \<open>punit.lc (rep_list p) \<noteq> 0\<close> \<open>p \<noteq> 0\<close> by (simp add: lt_monom_mult)
  also from assms have "lt (monom_mult (1 / punit.lc (rep_list p)) (lcs t1 t2 - t1) p) \<noteq>
                        lt (monom_mult (1 / punit.lc (rep_list q)) (lcs t1 t2 - t2) q)"
    by (simp add: is_regular_spair_def Let_def t1_def t2_def)
  also have "lt (monom_mult (1 / punit.lc (rep_list q)) (lcs t1 t2 - t2) q) = (lcs t1 t2 - t2) \<oplus> lt q"
    using \<open>punit.lc (rep_list q) \<noteq> 0\<close> \<open>q \<noteq> 0\<close> by (simp add: lt_monom_mult)
  finally have "(lcs t1 t2 - t1) \<oplus> lt p \<noteq> (lcs t1 t2 - t2) \<oplus> lt q" .
  thus False using eq ..
qed

lemma is_regular_spair_nonzero:
  assumes "is_regular_spair p q"
  shows "spair p q \<noteq> 0"
proof
  assume "spair p q = 0"
  with assms show False by (simp add: is_regular_spair_def spair_def Let_def)
qed

lemma is_regular_spair_lt_ge_1:
  assumes "is_regular_spair p q"
  shows "lt p \<preceq>\<^sub>t lt (spair p q)"
proof -
  from assms have "rep_list p \<noteq> 0" and "rep_list q \<noteq> 0"
    and "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q" (is "?u \<noteq> ?v")
    by (rule is_regular_spairD1, rule is_regular_spairD2, rule is_regular_spairD3)
  let ?l = "lcs (punit.lt (rep_list p)) (punit.lt (rep_list q))"
  show ?thesis
  proof (rule ord_term_lin.linorder_cases)
    assume "?u \<prec>\<^sub>t ?v"
    with \<open>rep_list q \<noteq> 0\<close> have eq: "lt (spair q p) = (?l - punit.lt (rep_list q)) \<oplus> lt q"
      unfolding lcs_comm[of "punit.lt (rep_list p)"] by (rule lt_spair)
    from zero_min splus_mono_left splus_zero have "lt p \<preceq>\<^sub>t (?l - punit.lt (rep_list p)) \<oplus> lt p"
      by fastforce
    also from \<open>?u \<prec>\<^sub>t ?v\<close> have "... \<prec>\<^sub>t (?l - punit.lt (rep_list q)) \<oplus> lt q"
      by (simp add: term_is_le_rel_minus_minus adds_lcs adds_lcs_2)
    also have "... = lt (spair p q)" by (simp add: eq spair_comm[of p])
    finally show ?thesis by simp
  next
    assume "?v \<prec>\<^sub>t ?u"
    with \<open>rep_list p \<noteq> 0\<close> have "lt (spair p q) = (?l - punit.lt (rep_list p)) \<oplus> lt p" by (rule lt_spair)
    with zero_min splus_mono_left splus_zero show ?thesis by fastforce
  next
    assume "?u = ?v"
    with \<open>?u \<noteq> ?v\<close> show ?thesis ..
  qed
qed

corollary is_regular_spair_lt_ge_2:
  assumes "is_regular_spair p q"
  shows "lt q \<preceq>\<^sub>t lt (spair p q)"
proof -
  from assms have "is_regular_spair q p" by (rule is_regular_spair_sym)
  hence "lt q \<preceq>\<^sub>t lt (spair q p)" by (rule is_regular_spair_lt_ge_1)
  also have "... = lt (spair p q)" by (simp add: spair_comm[of q])
  finally show ?thesis .
qed

lemma is_regular_spair_component_lt_cases:
  assumes "is_regular_spair p q"
  shows "component_of_term (lt (spair p q)) = component_of_term (lt p) \<or>
          component_of_term (lt (spair p q)) = component_of_term (lt q)"
proof (rule ord_term_lin.linorder_cases)
  from assms have "rep_list q \<noteq> 0" by (rule is_regular_spairD2)
  moreover assume "punit.lt (rep_list q) \<oplus> lt p \<prec>\<^sub>t punit.lt (rep_list p) \<oplus> lt q"
  ultimately have "lt (spair q p) = (lcs (punit.lt (rep_list q)) (punit.lt (rep_list p)) - punit.lt (rep_list q)) \<oplus> lt q"
    by (rule lt_spair)
  thus ?thesis by (simp add: spair_comm[of p] term_simps)
next
  from assms have "rep_list p \<noteq> 0" by (rule is_regular_spairD1)
  moreover assume "punit.lt (rep_list p) \<oplus> lt q \<prec>\<^sub>t punit.lt (rep_list q) \<oplus> lt p"
  ultimately have "lt (spair p q) = (lcs (punit.lt (rep_list p)) (punit.lt (rep_list q)) - punit.lt (rep_list p)) \<oplus> lt p"
    by (rule lt_spair)
  thus ?thesis by (simp add: term_simps)
next
  from assms have "punit.lt (rep_list q) \<oplus> lt p \<noteq> punit.lt (rep_list p) \<oplus> lt q"
    by (rule is_regular_spairD3)
  moreover assume "punit.lt (rep_list q) \<oplus> lt p = punit.lt (rep_list p) \<oplus> lt q"
  ultimately show ?thesis ..
qed

lemma lemma_9:
  assumes "dickson_grading d" and "is_rewrite_ord rword" and "is_RB_upt d rword G u"
    and "inj_on lt G" and "\<not> is_syz_sig d G u" and "is_canon_rewriter rword G u g1" and "h \<in> G"
    and "is_sig_red (\<prec>\<^sub>t) (=) {h} (monom_mult 1 (pp_of_term u - lp g1) g1)"
    and "d (pp_of_term u) \<le> dgrad_max d"
  shows "spair g1 h = monom_mult (1 / punit.lc (rep_list g1)) (pp_of_term u - lp g1) g1 -
                   monom_mult (1 / punit.lc (rep_list h))
                    (((pp_of_term u - lp g1) + punit.lt (rep_list g1)) - punit.lt (rep_list h)) h"
        (is ?thesis1)
    and "is_regular_spair g1 h" (is ?thesis2)
    and "lt (spair g1 h) = u" (is ?thesis3)
proof -
  from assms(8) have "rep_list (monom_mult 1 (pp_of_term u - lp g1) g1) \<noteq> 0"
    using is_sig_red_top_addsE by fastforce
  hence "rep_list g1 \<noteq> 0" by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  hence "g1 \<noteq> 0" by (auto simp: rep_list_zero)
  from assms(6) have "g1 \<in> G" and "lt g1 adds\<^sub>t u" by (rule is_canon_rewriterD)+
  from assms(3) have "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  with \<open>g1 \<in> G\<close> have "g1 \<in> dgrad_sig_set d" ..
  hence "component_of_term (lt g1) < length fs" using \<open>g1 \<noteq> 0\<close> by (rule dgrad_sig_setD_lt)
  with \<open>lt g1 adds\<^sub>t u\<close> have "component_of_term u < length fs" by (simp add: adds_term_def)

  from \<open>lt g1 adds\<^sub>t u\<close> obtain a where u: "u = a \<oplus> lt g1" by (rule adds_termE)
  hence a: "a = pp_of_term u - lp g1" by (simp add: term_simps)
  from assms(8) have "is_sig_red (\<prec>\<^sub>t) (=) {h} (monom_mult 1 a g1)" by (simp only: a)
  hence "rep_list h \<noteq> 0" and "rep_list (monom_mult 1 a g1) \<noteq> 0" and
      2: "punit.lt (rep_list h) adds punit.lt (rep_list (monom_mult 1 a g1))" and
      3: "punit.lt (rep_list (monom_mult 1 a g1)) \<oplus> lt h \<prec>\<^sub>t punit.lt (rep_list h) \<oplus> lt (monom_mult 1 a g1)"
    by (auto elim: is_sig_red_top_addsE)
  from this(2) have "rep_list g1 \<noteq> 0" by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
  hence "g1 \<noteq> 0" by (auto simp: rep_list_zero)
  from \<open>rep_list h \<noteq> 0\<close> have "h \<noteq> 0" by (auto simp: rep_list_zero)
  from 2 \<open>rep_list g1 \<noteq> 0\<close> have "punit.lt (rep_list h) adds a + punit.lt (rep_list g1)"
    by (simp add: rep_list_monom_mult punit.lt_monom_mult)
  then obtain b where eq1: "a + punit.lt (rep_list g1) = b + punit.lt (rep_list h)"
    by (auto elim: addsE simp: add.commute)
  hence b: "b = ((pp_of_term u - lp g1) + punit.lt (rep_list g1)) - punit.lt (rep_list h)"
    by (simp add: a)
  define g where "g = gcs a b"
  have eq2: "spair g1 h = (monom_mult (1 / punit.lc (rep_list g1)) (a - g) g1) -
                           (monom_mult (1 / punit.lc (rep_list h)) (b - g) h)"
    by (simp only: spair_def Let_def lcs_minus_1[OF eq1] lcs_minus_2[OF eq1] g_def)

  have "g = 0"
  proof (rule ccontr)
    assume "g \<noteq> 0"
    have "g adds a" unfolding g_def by (fact gcs_adds)
    also have "... adds\<^sub>p u" unfolding u by (fact adds_pp_triv)
    finally obtain v where u2: "u = g \<oplus> v" by (rule adds_ppE)
    hence v: "v = u \<ominus> g" by (simp add: term_simps)
    from u2 have "v adds\<^sub>t u" by (rule adds_termI)
    hence "v \<preceq>\<^sub>t u" by (rule ord_adds_term)
    moreover have "v \<noteq> u"
    proof
      assume "v = u"
      hence "g \<oplus> v = 0 \<oplus> v" by (simp add: u2 term_simps)
      hence "g = 0" by (simp only: splus_right_canc)
      with \<open>g \<noteq> 0\<close> show False ..
    qed
    ultimately have "v \<prec>\<^sub>t u" by simp
    note assms(3) \<open>v \<prec>\<^sub>t u\<close>
    moreover have "d (pp_of_term v) \<le> dgrad_max d"
    proof (rule le_trans)
      from assms(1) show "d (pp_of_term v) \<le> d (pp_of_term u)"
        by (simp add: u2 term_simps dickson_gradingD1)
    qed fact
    moreover from \<open>component_of_term u < length fs\<close> have "component_of_term v < length fs"
      by (simp only: v term_simps)
    ultimately have "is_RB_in d rword G v" by (rule is_RB_uptD2)
    thus False
    proof (rule is_RB_inE)
      assume "is_syz_sig d G v"
      with assms(1) have "is_syz_sig d G u" using \<open>v adds\<^sub>t u\<close> assms(9) by (rule is_syz_sig_adds)
      with assms(5) show False ..
    next
      fix g2
      assume *: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g2) g2)"
      assume "is_canon_rewriter rword G v g2"
      hence "g2 \<in> G" and "g2 \<noteq> 0" and "lt g2 adds\<^sub>t v" by (rule is_canon_rewriterD)+
      assume "\<not> is_syz_sig d G v"
      note assms(2) \<open>is_canon_rewriter rword G v g2\<close> assms(6)
      moreover from \<open>lt g2 adds\<^sub>t v\<close> \<open>v adds\<^sub>t u\<close> have "lt g2 adds\<^sub>t u" by (rule adds_term_trans)
      moreover from \<open>g adds a\<close> have "lt g1 adds\<^sub>t v" by (simp add: v u minus_splus[symmetric] adds_termI)
      ultimately have "lt g2 = lt g1" by (rule is_rewrite_ord_canon_rewriterD1)
      with assms(4) have "g2 = g1" using \<open>g2 \<in> G\<close> \<open>g1 \<in> G\<close> by (rule inj_onD)
      have "pp_of_term v - lp g1 = a - g" by (simp add: u v term_simps diff_diff_add)
  
      have "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g2) g2)"
        unfolding \<open>g2 = g1\<close> \<open>pp_of_term v - lp g1 = a - g\<close> using assms(7) \<open>rep_list h \<noteq> 0\<close>
      proof (rule is_sig_red_top_addsI)
        from \<open>rep_list g1 \<noteq> 0\<close> show "rep_list (monom_mult 1 (a - g) g1) \<noteq> 0"
          by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
      next
        have eq3: "(a - g) + punit.lt (rep_list g1) = lcs (punit.lt (rep_list g1)) (punit.lt (rep_list h))"
          by (simp add: g_def lcs_minus_1[OF eq1, symmetric] adds_minus adds_lcs)
        from \<open>rep_list g1 \<noteq> 0\<close>
        show "punit.lt (rep_list h) adds punit.lt (rep_list (monom_mult 1 (a - g) g1))"
          by (simp add: rep_list_monom_mult punit.lt_monom_mult eq3 adds_lcs_2)
      next
        from 3 \<open>rep_list g1 \<noteq> 0\<close> \<open>g1 \<noteq> 0\<close>
        show "punit.lt (rep_list (monom_mult 1 (a - g) g1)) \<oplus> lt h \<prec>\<^sub>t
              punit.lt (rep_list h) \<oplus> lt (monom_mult 1 (a - g) g1)"
          by (auto simp: rep_list_monom_mult punit.lt_monom_mult lt_monom_mult splus_assoc splus_left_commute
                dest!: ord_term_strict_canc intro: splus_mono_strict)
      next
        show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by (fact ord_term_lin.is_le_relI)
      qed
      with * show False ..
    qed
  qed
  hence eq3: "spair g1 h = (monom_mult (1 / punit.lc (rep_list g1)) a g1) -
                           (monom_mult (1 / punit.lc (rep_list h)) b h)" by (simp add: eq2)
  thus ?thesis1 by (simp only: a b)

  from 3 \<open>rep_list g1 \<noteq> 0\<close> \<open>g1 \<noteq> 0\<close> have "b \<oplus> lt h \<prec>\<^sub>t a \<oplus> lt g1"
    by (auto simp: rep_list_monom_mult punit.lt_monom_mult lt_monom_mult eq1 splus_assoc
        splus_left_commute[of b] dest!: ord_term_strict_canc)
  hence "a \<oplus> lt g1 \<noteq> b \<oplus> lt h" by simp
  with \<open>rep_list g1 \<noteq> 0\<close> \<open>rep_list h \<noteq> 0\<close> eq1 show ?thesis2
    by (rule is_regular_spairI')

  have "lt (monom_mult (1 / punit.lc (rep_list h)) b h) = b \<oplus> lt h"
  proof (rule lt_monom_mult)
    from \<open>rep_list h \<noteq> 0\<close> show "1 / punit.lc (rep_list h) \<noteq> 0" by (simp add: punit.lc_eq_zero_iff)
  qed fact
  also have "... \<prec>\<^sub>t a \<oplus> lt g1" by fact
  also have "... = lt (monom_mult (1 / punit.lc (rep_list g1)) a g1)"
  proof (rule HOL.sym, rule lt_monom_mult)
    from \<open>rep_list g1 \<noteq> 0\<close> show "1 / punit.lc (rep_list g1) \<noteq> 0" by (simp add: punit.lc_eq_zero_iff)
  qed fact
  finally have "lt (spair g1 h) = lt (monom_mult (1 / punit.lc (rep_list g1)) a g1)"
    unfolding eq3 by (rule lt_minus_eqI_2)
  also have "... = a \<oplus> lt g1" by (rule HOL.sym, fact)
  finally show ?thesis3 by (simp only: u)
qed

lemma lemma_10:
  assumes "dickson_grading d" and "is_rewrite_ord rword" and "G \<subseteq> dgrad_sig_set d" and "inj_on lt G"
    and "finite G"
    and "\<And>g1 g2. g1 \<in> G \<Longrightarrow> g2 \<in> G \<Longrightarrow> is_regular_spair g1 g2 \<Longrightarrow> lt (spair g1 g2) \<prec>\<^sub>t u \<Longrightarrow>
              is_RB_in d rword G (lt (spair g1 g2))"
    and "\<And>i. i < length fs \<Longrightarrow> term_of_pair (0, i) \<prec>\<^sub>t u \<Longrightarrow> is_RB_in d rword G (term_of_pair (0, i))"
  shows "is_RB_upt d rword G u"
proof (rule ccontr)
  let ?Q = "{v. v \<prec>\<^sub>t u \<and> d (pp_of_term v) \<le> dgrad_max d \<and> component_of_term v < length fs \<and> \<not> is_RB_in d rword G v}"
  have Q_sub: "pp_of_term ` ?Q \<subseteq> dgrad_set d (dgrad_max d)" by blast
  from assms(3) have "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
  assume "\<not> is_RB_upt d rword G u"
  with assms(3) obtain v' where "v' \<in> ?Q" unfolding is_RB_upt_def by blast
  with assms(1) obtain v where "v \<in> ?Q" and min: "\<And>y. y \<prec>\<^sub>t v \<Longrightarrow> y \<notin> ?Q" using Q_sub
    by (rule ord_term_minimum_dgrad_set, blast)
  from \<open>v \<in> ?Q\<close> have "v \<prec>\<^sub>t u" and "d (pp_of_term v) \<le> dgrad_max d" and "component_of_term v < length fs"
    and "\<not> is_RB_in d rword G v" by simp_all
  from this(4)
  have impl: "\<And>g. g \<in> G \<Longrightarrow> is_canon_rewriter rword G v g \<Longrightarrow>
                    is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g) g)"
    and "\<not> is_syz_sig d G v" by (simp_all add: is_RB_in_def Let_def)

  from assms(3) have "is_RB_upt d rword G v"
  proof (rule is_RB_uptI)
    fix w
    assume dw: "d (pp_of_term w) \<le> dgrad_max d" and cp: "component_of_term w < length fs"
    assume "w \<prec>\<^sub>t v"
    hence "w \<notin> ?Q" by (rule min)
    hence "\<not> w \<prec>\<^sub>t u \<or> is_RB_in d rword G w" by (simp add: dw cp)
    thus "is_RB_in d rword G w"
    proof
      assume "\<not> w \<prec>\<^sub>t u"
      moreover from \<open>w \<prec>\<^sub>t v\<close> \<open>v \<prec>\<^sub>t u\<close> have "w \<prec>\<^sub>t u" by (rule ord_term_lin.less_trans)
      ultimately show ?thesis ..
    qed
  qed

  show False
  proof (cases "\<exists>g\<in>G. g \<noteq> 0 \<and> lt g adds\<^sub>t v")
    case False
    hence x: "\<And>g. g \<in> G \<Longrightarrow> lt g adds\<^sub>t v \<Longrightarrow> g = 0" by blast
    let ?w = "term_of_pair (0, component_of_term v)"
    have "?w adds\<^sub>t v" by (simp add: adds_term_def term_simps)
    hence "?w \<preceq>\<^sub>t v" by (rule ord_adds_term)
    also have "... \<prec>\<^sub>t u" by fact
    finally have "?w \<prec>\<^sub>t u" .
    with \<open>component_of_term v < length fs\<close> have "is_RB_in d rword G ?w" by (rule assms(7))
    thus ?thesis
    proof (rule is_RB_inE)
      assume "is_syz_sig d G ?w"
      with assms(1) have "is_syz_sig d G v" using \<open>?w adds\<^sub>t v\<close> \<open>d (pp_of_term v) \<le> dgrad_max d\<close>
        by (rule is_syz_sig_adds)
      with \<open>\<not> is_syz_sig d G v\<close> show ?thesis ..
    next
      fix g1
      assume "is_canon_rewriter rword G ?w g1"
      hence "g1 \<noteq> 0" and "g1 \<in> G" and "lt g1 adds\<^sub>t ?w" by (rule is_canon_rewriterD)+
      from this(3) have "lt g1 adds\<^sub>t v" using \<open>?w adds\<^sub>t v\<close> by (rule adds_term_trans)
      with \<open>g1 \<in> G\<close> have "g1 = 0" by (rule x)
      with \<open>g1 \<noteq> 0\<close> show ?thesis ..
    qed
  next
    case True
    then obtain g' where "g' \<in> G" and "g' \<noteq> 0" and "lt g' adds\<^sub>t v" by blast
    with assms(2, 5) obtain g1 where crw: "is_canon_rewriter rword G v g1"
      by (rule is_rewrite_ord_finite_canon_rewriterE)
    hence "g1 \<in> G" by (rule is_canon_rewriterD1)
    hence "is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term v - lp g1) g1)" using crw by (rule impl)
    then obtain h where "h \<in> G" and "is_sig_red (\<prec>\<^sub>t) (=) {h} (monom_mult 1 (pp_of_term v - lp g1) g1)"
      by (rule is_sig_red_singletonI)
    with assms(1, 2) \<open>is_RB_upt d rword G v\<close> assms(4) \<open>\<not> is_syz_sig d G v\<close> crw
    have "is_regular_spair g1 h" and eq: "lt (spair g1 h) = v"
      using \<open>d (pp_of_term v) \<le> dgrad_max d\<close> by (rule lemma_9)+
    from \<open>v \<prec>\<^sub>t u\<close> have "lt (spair g1 h) \<prec>\<^sub>t u" by (simp only: eq)
    with \<open>g1 \<in> G\<close> \<open>h \<in> G\<close> \<open>is_regular_spair g1 h\<close> have "is_RB_in d rword G (lt (spair g1 h))"
      by (rule assms(6))
    hence "is_RB_in d rword G v" by (simp only: eq)
    with \<open>\<not> is_RB_in d rword G v\<close> show ?thesis ..
  qed
qed

text \<open>Note that the following lemma actually holds for @{emph \<open>all\<close>} regularly reducible power-products
  in @{term "rep_list p"}, not just for the leading power-product.\<close>

lemma lemma_11:
  assumes "dickson_grading d" and "is_rewrite_ord rword" and "is_RB_upt d rword G (lt p)"
    and "p \<in> dgrad_sig_set d" and "is_sig_red (\<prec>\<^sub>t) (=) G p"
  obtains u g where "u \<prec>\<^sub>t lt p" and "d (pp_of_term u) \<le> dgrad_max d" and "component_of_term u < length fs"
    and "\<not> is_syz_sig d G u" and "is_canon_rewriter rword G u g" and "is_sig_red (\<prec>\<^sub>t) (=) {g} p"
proof -
  from assms(3) have G_sub: "G \<subseteq> dgrad_sig_set d" by (rule is_RB_uptD1)
  from assms(5) have "rep_list p \<noteq> 0" using is_sig_red_addsE by fastforce
  hence "p \<noteq> 0" by (auto simp: rep_list_zero)
  let ?lc = "punit.lc (rep_list p)"
  let ?lp = "punit.lt (rep_list p)"
  from \<open>rep_list p \<noteq> 0\<close> have "?lc \<noteq> 0" by (rule punit.lc_not_0)
  from assms(4) have "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
  from assms(4) have "d (lp p) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
  from assms(4) \<open>p \<noteq> 0\<close> have "component_of_term (lt p) < length fs" by (rule dgrad_sig_setD_lt)
  from assms(1) \<open>p \<in> dgrad_max_set d\<close> have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
  hence "d ?lp \<le> dgrad_max d" using \<open>rep_list p \<noteq> 0\<close> by (rule punit.dgrad_p_setD_lt[simplified])

  from assms(5) obtain g0 where "g0 \<in> G" and "is_sig_red (\<prec>\<^sub>t) (=) {g0} p"
    by (rule is_sig_red_singletonI)
  from \<open>g0 \<in> G\<close> G_sub have "g0 \<in> dgrad_sig_set d" ..
  let ?g0 = "monom_mult (?lc / punit.lc (rep_list g0)) (?lp - punit.lt (rep_list g0)) g0"

  define M where "M = {monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g |
                          g. g \<in> dgrad_sig_set d \<and> is_sig_red (\<prec>\<^sub>t) (=) {g} p}"
  from \<open>g0 \<in> dgrad_sig_set d\<close> \<open>is_sig_red (\<prec>\<^sub>t) (=) {g0} p\<close> have "?g0 \<in> M" by (auto simp: M_def)
  have "0 \<notin> rep_list ` M"
  proof
    assume "0 \<in> rep_list ` M"
    then obtain g where 1: "is_sig_red (\<prec>\<^sub>t) (=) {g} p"
      and 2: "rep_list (monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g) = 0"
      unfolding M_def by fastforce
    from 1 have "rep_list g \<noteq> 0" using is_sig_red_addsE by fastforce
    moreover from this have "punit.lc (rep_list g) \<noteq> 0" by (rule punit.lc_not_0)
    ultimately have "rep_list (monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g) \<noteq> 0"
      using \<open>?lc \<noteq> 0\<close> by (simp add: rep_list_monom_mult punit.monom_mult_eq_zero_iff)
    thus False using 2 ..
  qed
  with rep_list_zero have "0 \<notin> M" by auto
  have "M \<subseteq> dgrad_sig_set d"
  proof
    fix m
    assume "m \<in> M"
    then obtain g where "g \<in> dgrad_sig_set d" and 1: "is_sig_red (\<prec>\<^sub>t) (=) {g} p"
      and m: "m = monom_mult (?lc / punit.lc (rep_list g)) (?lp - punit.lt (rep_list g)) g"
      unfolding M_def by fastforce
    from 1 have "punit.lt (rep_list g) adds ?lp" using is_sig_red_top_addsE by fastforce
    note assms(1)
    thm dickson_grading_minus
    moreover have "d (?lp - punit.lt (rep_list g)) \<le> dgrad_max d"
      by (rule le_trans, rule dickson_grading_minus, fact+)
    ultimately show "m \<in> dgrad_sig_set d" unfolding m using \<open>g \<in> dgrad_sig_set d\<close>
      by (rule dgrad_sig_set_closed_monom_mult)
  qed
  hence "M \<subseteq> sig_inv_set" by (simp add: dgrad_sig_set_def)

  let ?M = "lt ` M"
  note assms(1)
  moreover from \<open>?g0 \<in> M\<close> have "lt ?g0 \<in> ?M" by (rule imageI)
  moreover from \<open>M \<subseteq> dgrad_sig_set d\<close> have "pp_of_term ` ?M \<subseteq> dgrad_set d (dgrad_max d)"
    by (auto intro!: dgrad_sig_setD_lp)
  ultimately obtain u where "u \<in> ?M" and min: "\<And>v. v \<prec>\<^sub>t u \<Longrightarrow> v \<notin> ?M"
    by (rule ord_term_minimum_dgrad_set, blast)
  from \<open>u \<in> ?M\<close> obtain m where "m \<in> M" and u': "u = lt m" ..
  from this(1) obtain g1 where "g1 \<in> dgrad_sig_set d" and 1: "is_sig_red (\<prec>\<^sub>t) (=) {g1} p"
    and m: "m = monom_mult (?lc / punit.lc (rep_list g1)) (?lp - punit.lt (rep_list g1)) g1"
    unfolding M_def by fastforce
  from 1 have adds: "punit.lt (rep_list g1) adds ?lp" and "?lp \<oplus> lt g1 \<prec>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p"
    and "rep_list g1 \<noteq> 0" using is_sig_red_top_addsE by fastforce+
  from this(3) have lc_g1: "punit.lc (rep_list g1) \<noteq> 0" by (rule punit.lc_not_0)
  from \<open>m \<in> M\<close> \<open>0 \<notin> rep_list ` M\<close> have "rep_list m \<noteq> 0" by fastforce
  from \<open>m \<in> M\<close> \<open>0 \<notin> M\<close> have "m \<noteq> 0" by blast
  hence "lc m \<noteq> 0" by (rule lc_not_0)
  from lc_g1 have eq0: "punit.lc (rep_list m) = ?lc" by (simp add: m rep_list_monom_mult)
  from \<open>?lc \<noteq> 0\<close> \<open>rep_list g1 \<noteq> 0\<close> adds have eq1: "punit.lt (rep_list m) = ?lp"
    by (simp add: m rep_list_monom_mult punit.lt_monom_mult punit.lc_eq_zero_iff adds_minus)
  from \<open>m \<in> M\<close> \<open>M \<subseteq> dgrad_sig_set d\<close> have "m \<in> dgrad_sig_set d" ..

  from \<open>rep_list g1 \<noteq> 0\<close> have "punit.lc (rep_list g1) \<noteq> 0" and "g1 \<noteq> 0"
    by (auto simp: rep_list_zero punit.lc_eq_zero_iff)
  with \<open>?lc \<noteq> 0\<close> have u: "u = (?lp - punit.lt (rep_list g1)) \<oplus> lt g1"
    by (simp add: u' m lt_monom_mult lc_eq_zero_iff)
  hence "punit.lt (rep_list g1) \<oplus> u = punit.lt (rep_list g1) \<oplus> ((?lp - punit.lt (rep_list g1)) \<oplus> lt g1)"
    by simp
  also from adds have "... = ?lp \<oplus> lt g1"
    by (simp only: splus_assoc[symmetric], metis add.commute adds_minus)
  also have "... \<prec>\<^sub>t punit.lt (rep_list g1) \<oplus> lt p" by fact
  finally have "u \<prec>\<^sub>t lt p" by (rule ord_term_strict_canc)

  from \<open>u \<in> ?M\<close> have "pp_of_term u \<in> pp_of_term ` ?M" by (rule imageI)
  also have "... \<subseteq> dgrad_set d (dgrad_max d)" by fact
  finally have "d (pp_of_term u) \<le> dgrad_max d" by (rule dgrad_setD)

  from \<open>u \<in> ?M\<close> have "component_of_term u \<in> component_of_term ` ?M" by (rule imageI)
  also from \<open>M \<subseteq> sig_inv_set\<close> \<open>0 \<notin> M\<close> sig_inv_setD_lt have "... \<subseteq> {0..<length fs}" by fastforce
  finally have "component_of_term u < length fs" by simp

  have "\<not> is_syz_sig d G u"
  proof
    assume "is_syz_sig d G u"
    with assms(1) G_sub obtain s where "s \<noteq> 0" and "lt s = u" and "s \<in> dgrad_sig_set d" and "rep_list s = 0"
      by (rule is_syz_sig_dgrad_sig_setE)
    let ?s = "monom_mult (lc m / lc s) 0 s"
    have "rep_list ?s = 0" by (simp add: rep_list_monom_mult \<open>rep_list s = 0\<close>)
    from \<open>s \<noteq> 0\<close> have "lc s \<noteq> 0" by (rule lc_not_0)
    hence "lc m / lc s \<noteq> 0" using \<open>lc m \<noteq> 0\<close> by simp
    have "m - ?s \<noteq> 0"
    proof
      assume "m - ?s = 0"
      hence "m = ?s" by simp
      with \<open>rep_list ?s = 0\<close> have "rep_list m = 0" by simp
      with \<open>rep_list m \<noteq> 0\<close> show False ..
    qed
    moreover from \<open>lc m / lc s \<noteq> 0\<close> have "lt ?s = lt m" by (simp add: lt_monom_mult_zero \<open>lt s = u\<close> u')
    moreover from \<open>lc s \<noteq> 0\<close> have "lc ?s = lc m" by simp
    ultimately have "lt (m - ?s) \<prec>\<^sub>t u" unfolding u' by (rule lt_minus_lessI)
    hence "lt (m - ?s) \<notin> ?M" by (rule min)
    hence "m - ?s \<notin> M" by blast
    moreover have "m - ?s \<in> M"
    proof -
      have "?s = monom_mult (?lc / lc s) 0 (monom_mult (lc g1 / punit.lc (rep_list g1)) 0 s)"
        by (simp add: m monom_mult_assoc mult.commute)
      define m' where "m' = m - ?s"
      have eq: "rep_list m' = rep_list m" by (simp add: m'_def rep_list_minus \<open>rep_list ?s = 0\<close>)
      from \<open>?lc \<noteq> 0\<close> have "m' = monom_mult (?lc / punit.lc (rep_list m')) (?lp - punit.lt (rep_list m')) m'"
        by (simp add: eq eq0 eq1)
      also have "... \<in> M" unfolding M_def
      proof (rule, intro exI conjI)
        from \<open>s \<in> dgrad_sig_set d\<close> have "?s \<in> dgrad_sig_set d"
          by (rule dgrad_sig_set_closed_monom_mult_zero)
        with \<open>m \<in> dgrad_sig_set d\<close> show "m' \<in> dgrad_sig_set d" unfolding m'_def
          by (rule dgrad_sig_set_closed_minus)
      next
        show "is_sig_red (\<prec>\<^sub>t) (=) {m'} p"
        proof (rule is_sig_red_top_addsI)
          show "m' \<in> {m'}" by simp
        next
          from \<open>rep_list m \<noteq> 0\<close> show "rep_list m' \<noteq> 0" by (simp add: eq)
        next
          show "punit.lt (rep_list m') adds punit.lt (rep_list p)" by (simp add: eq eq1)
        next
          have "punit.lt (rep_list p) \<oplus> lt m' \<prec>\<^sub>t punit.lt (rep_list p) \<oplus> u"
            by (rule splus_mono_strict, simp only: m'_def \<open>lt (m - ?s) \<prec>\<^sub>t u\<close>)
          also have "... \<prec>\<^sub>t punit.lt (rep_list m') \<oplus> lt p"
            unfolding eq eq1 using \<open>u \<prec>\<^sub>t lt p\<close> by (rule splus_mono_strict)
          finally show "punit.lt (rep_list p) \<oplus> lt m' \<prec>\<^sub>t punit.lt (rep_list m') \<oplus> lt p" .
        next
          show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by simp
        qed fact
      qed (fact refl)
      finally show ?thesis by (simp only: m'_def)
    qed
    ultimately show False ..
  qed

  have "is_RB_in d rword G u" by (rule is_RB_uptD2, fact+)
  thus ?thesis
  proof (rule is_RB_inE)
    assume "is_syz_sig d G u"
    with \<open>\<not> is_syz_sig d G u\<close> show ?thesis ..
  next
    fix g
    assume "is_canon_rewriter rword G u g"
    hence "g \<in> G" and "g \<noteq> 0" and adds': "lt g adds\<^sub>t u" by (rule is_canon_rewriterD)+
    assume irred: "\<not> is_sig_red (\<prec>\<^sub>t) (=) G (monom_mult 1 (pp_of_term u - lp g) g)"

    define b where "b = monom_mult 1 (pp_of_term u - lp g) g"
    note assms(1)
    moreover have "is_sig_GB_upt d G (lt m)" unfolding u'[symmetric]
      by (rule is_sig_GB_upt_le, rule is_RB_upt_is_sig_GB_upt, fact+, rule ord_term_lin.less_imp_le, fact)
    moreover from assms(1) have "b \<in> dgrad_sig_set d" unfolding b_def
    proof (rule dgrad_sig_set_closed_monom_mult)
      from adds' have "lp g adds pp_of_term u" by (simp add: adds_term_def)
      with assms(1) have "d (pp_of_term u - lp g) \<le> d (pp_of_term u)" by (rule dickson_grading_minus)
      thus "d (pp_of_term u - lp g) \<le> dgrad_max d" using \<open>d (pp_of_term u) \<le> dgrad_max d\<close>
        by (rule le_trans)
    next
      from \<open>g \<in> G\<close> G_sub show "g \<in> dgrad_sig_set d" ..
    qed
    moreover note \<open>m \<in> dgrad_sig_set d\<close>
    moreover from \<open>g \<noteq> 0\<close> have "lt b = lt m"
      by (simp add: b_def u'[symmetric] lt_monom_mult,
          metis adds' add_diff_cancel_right' adds_termE pp_of_term_splus)
    moreover from \<open>g \<noteq> 0\<close> have "b \<noteq> 0" by (simp add: b_def monom_mult_eq_zero_iff)
    moreover note \<open>m \<noteq> 0\<close>
    moreover from irred have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G b" by (simp add: b_def)
    moreover have "\<not> is_sig_red (\<prec>\<^sub>t) (=) G m"
    proof
      assume "is_sig_red (\<prec>\<^sub>t) (=) G m"
      then obtain g2 where 1: "g2 \<in> G" and 2: "rep_list g2 \<noteq> 0"
        and 3: "punit.lt (rep_list g2) adds punit.lt (rep_list m)"
        and 4: "punit.lt (rep_list m) \<oplus> lt g2 \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> lt m"
        by (rule is_sig_red_top_addsE)
      from 2 have "g2 \<noteq> 0" and "punit.lc (rep_list g2) \<noteq> 0" by (auto simp: rep_list_zero punit.lc_eq_zero_iff)
      with 3 4 have "lt (monom_mult (?lc / punit.lc (rep_list g2)) (?lp - punit.lt (rep_list g2)) g2) \<prec>\<^sub>t u"
        (is "lt ?g2 \<prec>\<^sub>t u")
        using \<open>?lc \<noteq> 0\<close> by (simp add: term_is_le_rel_minus u' eq1 lt_monom_mult)
      hence "lt ?g2 \<notin> ?M" by (rule min)
      hence "?g2 \<notin> M" by blast
      hence "g2 \<notin> dgrad_sig_set d \<or> \<not> is_sig_red (\<prec>\<^sub>t) (=) {g2} p" by (simp add: M_def)
      thus False
      proof
        assume "g2 \<notin> dgrad_sig_set d"
        moreover from \<open>g2 \<in> G\<close> G_sub have "g2 \<in> dgrad_sig_set d" ..
        ultimately show ?thesis ..
      next
        assume "\<not> is_sig_red (\<prec>\<^sub>t) (=) {g2} p"
        moreover have "is_sig_red (\<prec>\<^sub>t) (=) {g2} p"
        proof (rule is_sig_red_top_addsI)
          show "g2 \<in> {g2}" by simp
        next
          from 3 show "punit.lt (rep_list g2) adds punit.lt (rep_list p)" by (simp only: eq1)
        next
          from 4 have "?lp \<oplus> lt g2 \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> u" by (simp only: eq1 u')
          also from \<open>u \<prec>\<^sub>t lt p\<close> have "... \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> lt p" by (rule splus_mono_strict)
          finally show "?lp \<oplus> lt g2 \<prec>\<^sub>t punit.lt (rep_list g2) \<oplus> lt p" .
        next
          show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by simp
        qed fact+
        ultimately show ?thesis ..
      qed
    qed
    ultimately have eq2: "punit.lt (rep_list b) = punit.lt (rep_list m)"
      by (rule sig_regular_top_reduced_lt_unique)
    have "is_sig_red (\<prec>\<^sub>t) (=) {b} p"
    proof (rule is_sig_red_top_addsI)
      show "b \<in> {b}" by simp
    next
      have "rep_list g \<noteq> 0" by (rule is_RB_inD, fact+)
      thus "rep_list b \<noteq> 0" by (simp add: b_def rep_list_monom_mult punit.monom_mult_eq_zero_iff)
    next
      show "punit.lt (rep_list b) adds punit.lt (rep_list p)" by (simp add: eq1 eq2)
    next
      show "punit.lt (rep_list p) \<oplus> lt b \<prec>\<^sub>t punit.lt (rep_list b) \<oplus> lt p"
        by (simp add: eq1 eq2 \<open>lt b = lt m\<close> u'[symmetric] \<open>u \<prec>\<^sub>t lt p\<close> splus_mono_strict)
    next
      show "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by simp
    qed fact
    hence "is_sig_red (\<prec>\<^sub>t) (=) {g} p" unfolding b_def by (rule is_sig_red_singleton_monom_multD)
    show ?thesis by (rule, fact+)
  qed
qed

subsubsection \<open>Termination\<close>

definition term_pp_rel :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<times> 'a) \<Rightarrow> ('t \<times> 'a) \<Rightarrow> bool"
  where "term_pp_rel r a b \<longleftrightarrow> r (snd b \<oplus> fst a) (snd a \<oplus> fst b)"

definition canon_term_pp_pair :: "('t \<times> 'a) \<Rightarrow> bool"
  where "canon_term_pp_pair a \<longleftrightarrow> (gcs (pp_of_term (fst a)) (snd a) = 0)"

definition cancel_term_pp_pair :: "('t \<times> 'a) \<Rightarrow> ('t \<times> 'a)"
  where "cancel_term_pp_pair a = (fst a \<ominus> (gcs (pp_of_term (fst a)) (snd a)), snd a - (gcs (pp_of_term (fst a)) (snd a)))"

lemma term_pp_rel_refl: "reflp r \<Longrightarrow> term_pp_rel r a a"
  by (simp add: term_pp_rel_def reflp_def)

lemma term_pp_rel_irrefl: "irreflp r \<Longrightarrow> \<not> term_pp_rel r a a"
  by (simp add: term_pp_rel_def irreflp_def)

lemma term_pp_rel_sym: "symp r \<Longrightarrow> term_pp_rel r a b \<Longrightarrow> term_pp_rel r b a"
  by (auto simp: term_pp_rel_def symp_def)

lemma term_pp_rel_trans:
  assumes "ord_term_lin.is_le_rel r" and "term_pp_rel r a b" and "term_pp_rel r b c"
  shows "term_pp_rel r a c"
proof -
  from assms(1) have "transp r" by (rule ord_term_lin.is_le_relE, auto)
  from assms(2) have 1: "r (snd b \<oplus> fst a) (snd a \<oplus> fst b)" by (simp only: term_pp_rel_def)
  from assms(3) have 2: "r (snd c \<oplus> fst b) (snd b \<oplus> fst c)" by (simp only: term_pp_rel_def)
  have "snd b \<oplus> (snd c \<oplus> fst a) = snd c \<oplus> (snd b \<oplus> fst a)" by (rule splus_left_commute)
  also from assms(1) 1 have "r ... (snd a \<oplus> (snd c \<oplus> fst b))"
    by (simp add: splus_left_commute[of "snd a"] term_is_le_rel_canc_left)
  also from assms(1) 2 have "r ... (snd b \<oplus> (snd a \<oplus> fst c))"
    by (simp add: splus_left_commute[of "snd b"] term_is_le_rel_canc_left)
  finally(transpD[OF \<open>transp r\<close>]) show ?thesis using assms(1)
    by (simp only: term_pp_rel_def term_is_le_rel_canc_left)
qed

lemma term_pp_rel_trans_eq_left:
  assumes "ord_term_lin.is_le_rel r" and "term_pp_rel (=) a b" and "term_pp_rel r b c"
  shows "term_pp_rel r a c"
proof -
  from assms(1) have "transp r" by (rule ord_term_lin.is_le_relE, auto)
  from assms(2) have 1: "snd b \<oplus> fst a = snd a \<oplus> fst b" by (simp only: term_pp_rel_def)
  from assms(3) have 2: "r (snd c \<oplus> fst b) (snd b \<oplus> fst c)" by (simp only: term_pp_rel_def)
  have "snd b \<oplus> (snd c \<oplus> fst a) = snd c \<oplus> (snd b \<oplus> fst a)" by (rule splus_left_commute)
  also from assms(1) 1 have "... = (snd a \<oplus> (snd c \<oplus> fst b))"
    by (simp add: splus_left_commute[of "snd a"])
  finally have eq: "snd b \<oplus> (snd c \<oplus> fst a) = snd a \<oplus> (snd c \<oplus> fst b)" .
  from assms(1) 2 have "r (snd b \<oplus> (snd c \<oplus> fst a)) (snd b \<oplus> (snd a \<oplus> fst c))"
    unfolding eq by (simp add: splus_left_commute[of "snd b"] term_is_le_rel_canc_left)
  thus ?thesis using assms(1) by (simp only: term_pp_rel_def term_is_le_rel_canc_left)
qed

lemma term_pp_rel_trans_eq_right:
  assumes "ord_term_lin.is_le_rel r" and "term_pp_rel r a b" and "term_pp_rel (=) b c"
  shows "term_pp_rel r a c"
proof -
  from assms(1) have "transp r" by (rule ord_term_lin.is_le_relE, auto)
  from assms(2) have 1: "r (snd b \<oplus> fst a) (snd a \<oplus> fst b)" by (simp only: term_pp_rel_def)
  from assms(3) have 2: "snd c \<oplus> fst b = snd b \<oplus> fst c" by (simp only: term_pp_rel_def)
  have "snd b \<oplus> (snd a \<oplus> fst c) = snd a \<oplus> (snd b \<oplus> fst c)" by (rule splus_left_commute)
  also from assms(1) 2 have "... = (snd a \<oplus> (snd c \<oplus> fst b))"
    by (simp add: splus_left_commute[of "snd a"])
  finally have eq: "snd b \<oplus> (snd a \<oplus> fst c) = snd a \<oplus> (snd c \<oplus> fst b)" .
  from assms(1) 1 have "r (snd b \<oplus> (snd c \<oplus> fst a)) (snd b \<oplus> (snd a \<oplus> fst c))"
    unfolding eq by (simp add: splus_left_commute[of _ "snd c"] term_is_le_rel_canc_left)
  thus ?thesis using assms(1) by (simp only: term_pp_rel_def term_is_le_rel_canc_left)
qed

lemma canon_term_pp_cancel: "canon_term_pp_pair (cancel_term_pp_pair a)"
  by (simp add: cancel_term_pp_pair_def canon_term_pp_pair_def gcs_minus_gcs term_simps)

lemma term_pp_rel_cancel:
  assumes "reflp r"
  shows "term_pp_rel r a (cancel_term_pp_pair a)"
proof -
  obtain u s where a: "a = (u, s)" by (rule prod.exhaust)
  show ?thesis
  proof (simp add: a cancel_term_pp_pair_def)
    let ?g = "gcs (pp_of_term u) s"
    have "?g adds s" by (fact gcs_adds_2)
    hence "(s - ?g) \<oplus> (u \<ominus> 0) = s \<oplus> u \<ominus> (?g + 0)" using zero_adds_pp
      by (rule minus_splus_sminus)
    also have "... = s \<oplus> (u \<ominus> ?g)"
      by (metis add.left_neutral add.right_neutral adds_pp_def diff_zero gcs_adds_2 gcs_comm
          minus_splus_sminus zero_adds)
    finally have "r ((s - ?g) \<oplus> u) (s \<oplus> (u \<ominus> ?g))" using assms by (simp add: term_simps reflp_def)
    thus "term_pp_rel r (u, s) (u \<ominus> ?g, s - ?g)" by (simp add: a term_pp_rel_def)
  qed
qed

lemma canon_term_pp_rel_id:
  assumes "term_pp_rel (=) a b" and "canon_term_pp_pair a" and "canon_term_pp_pair b"
  shows "a = b"
proof -
  obtain u s where a: "a = (u, s)" by (rule prod.exhaust)
  obtain v t where b: "b = (v, t)" by (rule prod.exhaust)
  from assms(1) have "t \<oplus> u = s \<oplus> v" by (simp add: term_pp_rel_def a b)
  hence 1: "t + pp_of_term u = s + pp_of_term v" by (metis pp_of_term_splus)
  from assms(2) have 2: "gcs (pp_of_term u) s = 0" by (simp add: canon_term_pp_pair_def a)
  from assms(3) have 3: "gcs (pp_of_term v) t = 0" by (simp add: canon_term_pp_pair_def b)
  have "t = t + gcs (pp_of_term u) s" by (simp add: 2)
  also have "... = gcs (t + pp_of_term u) (t + s)" by (simp only: gcs_plus_left)
  also have "... = gcs (s + pp_of_term v) (s + t)" by (simp only: 1 add.commute)
  also have "... = s + gcs (pp_of_term v) t" by (simp only: gcs_plus_left)
  also have "... = s" by (simp add: 3)
  finally have "t = s" .
  moreover from \<open>t \<oplus> u = s \<oplus> v\<close> have "u = v" by (simp only: \<open>t = s\<close> splus_left_canc)
  ultimately show ?thesis by (simp add: a b)
qed

lemma min_set_finite:
  fixes seq :: "nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)"
  assumes "dickson_grading d" and "range seq \<subseteq> dgrad_sig_set d" and "0 \<notin> rep_list ` range seq"
    and "\<And>i j. i < j \<Longrightarrow> lt (seq i) \<prec>\<^sub>t lt (seq j)"
  shows "finite {i. \<not> (\<exists>j<i. lt (seq j) adds\<^sub>t lt (seq i) \<and>
                             punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq i)))}"
proof -
  have "inj (\<lambda>i. lt (seq i))"
  proof
    fix i j
    assume eq: "lt (seq i) = lt (seq j)"
    show "i = j"
    proof (rule linorder_cases)
      assume "i < j"
      hence "lt (seq i) \<prec>\<^sub>t lt (seq j)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    next
      assume "j < i"
      hence "lt (seq j) \<prec>\<^sub>t lt (seq i)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    qed
  qed
  hence "inj seq" unfolding comp_def[symmetric] by (rule inj_on_imageI2)

  let ?P1 = "\<lambda>p q. lt p adds\<^sub>t lt q"
  let ?P2 = "\<lambda>p q. punit.lt (rep_list p) adds punit.lt (rep_list q)"
  let ?P = "\<lambda>p q. ?P1 p q \<and> ?P2 p q"
  have "reflp ?P" by (simp add: reflp_def adds_term_refl)
  have "almost_full_on ?P1 (range seq)"
  proof (rule almost_full_on_map)
    let ?B = "{t. pp_of_term t \<in> dgrad_set d (dgrad_max d) \<and> component_of_term t \<in> {0..<length fs}}"
    from assms(1) finite_atLeastLessThan show "almost_full_on (adds\<^sub>t) ?B" by (rule Dickson_term)
    show "lt ` range seq \<subseteq> ?B"
    proof
      fix v
      assume "v \<in> lt ` range seq"
      then obtain p where "p \<in> range seq" and v: "v = lt p" ..
      from this(1) assms(3) have "rep_list p \<noteq> 0" by auto
      hence "p \<noteq> 0" by (auto simp: rep_list_zero)
      from \<open>p \<in> range seq\<close> assms(2) have "p \<in> dgrad_sig_set d" ..
      hence "d (lp p) \<le> dgrad_max d" by (rule dgrad_sig_setD_lp)
      hence "lp p \<in> dgrad_set d (dgrad_max d)" by (simp add: dgrad_set_def)
      moreover from \<open>p \<in> dgrad_sig_set d\<close> \<open>p \<noteq> 0\<close> have "component_of_term (lt p) < length fs"
        by (rule dgrad_sig_setD_lt)
      ultimately show "v \<in> ?B" by (simp add: v)
    qed
  qed
  moreover have "almost_full_on ?P2 (range seq)"
  proof (rule almost_full_on_map)
    let ?B = "dgrad_set d (dgrad_max d)"
    from assms(1) show "almost_full_on (adds) ?B" by (rule dickson_gradingD_dgrad_set)
    show "(\<lambda>p. punit.lt (rep_list p)) ` range seq \<subseteq> ?B"
    proof
      fix t
      assume "t \<in> (\<lambda>p. punit.lt (rep_list p)) ` range seq"
      then obtain p where "p \<in> range seq" and t: "t = punit.lt (rep_list p)" ..
      from this(1) assms(3) have "rep_list p \<noteq> 0" by auto
      from \<open>p \<in> range seq\<close> assms(2) have "p \<in> dgrad_sig_set d" ..
      hence "p \<in> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
      with assms(1) have "rep_list p \<in> punit_dgrad_max_set d" by (rule dgrad_max_2)
      from this \<open>rep_list p \<noteq> 0\<close> have "d (punit.lt (rep_list p)) \<le> dgrad_max d"
        by (rule punit.dgrad_p_setD_lt[simplified])
      thus "t \<in> ?B" by (simp add: t dgrad_set_def)
    qed
  qed
  ultimately have "almost_full_on ?P (range seq)" by (rule almost_full_on_same)
  with \<open>reflp ?P\<close> obtain T where "finite T" and "T \<subseteq> range seq" and *: "\<And>p. p \<in> range seq \<Longrightarrow> (\<exists>q\<in>T. ?P q p)"
    by (rule almost_full_on_finite_subsetE, blast)
  from \<open>T \<subseteq> range seq\<close> obtain I where T: "T = seq ` I" by (meson subset_image_iff)
  have "{i. \<not> (\<exists>j<i. ?P (seq j) (seq i))} \<subseteq> I"
  proof
    fix i
    assume "i \<in> {i. \<not> (\<exists>j<i. ?P (seq j) (seq i))}"
    hence x: "\<not> (\<exists>j<i. ?P (seq j) (seq i))" by simp
    obtain j where "j \<in> I" and "?P (seq j) (seq i)"
    proof -
      have "seq i \<in> range seq" by simp
      hence "\<exists>q\<in>T. ?P q (seq i)" by (rule *)
      then obtain q where "q \<in> T" and "?P q (seq i)" ..
      from this(1) obtain j where "j \<in> I" and "q = seq j" unfolding T ..
      from this(1) \<open>?P q (seq i)\<close> show ?thesis unfolding \<open>q = seq j\<close> ..
    qed
    from this(2) x have "i \<le> j" by auto
    moreover have "\<not> i < j"
    proof
      assume "i < j"
      hence "lt (seq i) \<prec>\<^sub>t lt (seq j)" by (rule assms(4))
      hence "\<not> ?P1 (seq j) (seq i)" using ord_adds_term ord_term_lin.leD by blast
      with \<open>?P (seq j) (seq i)\<close> show False by simp
    qed
    ultimately show "i \<in> I" using \<open>j \<in> I\<close> by simp
  qed
  moreover from \<open>inj seq\<close> \<open>finite T\<close> have "finite I" by (simp add: finite_image_iff inj_on_subset T)
  ultimately show ?thesis by (rule finite_subset)
qed

lemma theorem_20:
  fixes seq :: "nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)"
  assumes "dickson_grading d" and "range seq \<subseteq> dgrad_sig_set d" and "0 \<notin> rep_list ` range seq"
    and "\<And>i j. i < j \<Longrightarrow> lt (seq i) \<prec>\<^sub>t lt (seq j)"
    and "\<And>i. \<not> is_sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<i}) (seq i)"
    and "\<And>i. (\<exists>j<length fs. (sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<i}))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) (seq i)) \<or>
              (\<exists>j k. is_regular_spair (seq j) (seq k) \<and> (sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<i}))\<^sup>*\<^sup>* (spair (seq j) (seq k)) (seq i))"
    and "\<And>i. is_sig_GB_upt d (seq ` {0..<i}) (lt (seq i))"
  shows thesis
proof -
  from assms(3) have "0 \<notin> range seq" using rep_list_zero by auto
  have "ord_term_lin.is_le_rel (=)" and "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" by (rule ord_term_lin.is_le_relI)+
  have "reflp (=)" and "symp (=)" by (simp_all add: symp_def)
  have "irreflp (\<prec>\<^sub>t)" by (simp add: irreflp_def)
  have "inj (\<lambda>i. lt (seq i))"
  proof
    fix i j
    assume eq: "lt (seq i) = lt (seq j)"
    show "i = j"
    proof (rule linorder_cases)
      assume "i < j"
      hence "lt (seq i) \<prec>\<^sub>t lt (seq j)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    next
      assume "j < i"
      hence "lt (seq j) \<prec>\<^sub>t lt (seq i)" by (rule assms(4))
      thus ?thesis by (simp add: eq)
    qed
  qed
  hence "inj seq" unfolding comp_def[symmetric] by (rule inj_on_imageI2)

  define R where "R = (\<lambda>x. {i. term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) x})"
  let ?A = "{x. canon_term_pp_pair x \<and> R x \<noteq> {}}"

  have "finite ?A"
  proof -
    define min_set where "min_set = {i. \<not> (\<exists>j<i. lt (seq j) adds\<^sub>t lt (seq i) \<and>
                                      punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq i)))}"
    have "?A \<subseteq> (\<lambda>i. cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i)))) ` min_set"
    proof
      fix u t
      assume "(u, t) \<in> ?A"
      hence "canon_term_pp_pair (u, t)" and "R (u, t) \<noteq> {}" by simp_all
      from this(2) obtain i where x: "term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) (u, t)"
        by (auto simp: R_def)
      let ?equiv = "(\<lambda>i j. term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) (lt (seq j), punit.lt (rep_list (seq j))))"
      obtain j where "j \<in> min_set" and "?equiv j i"
      proof (cases "i \<in> min_set")
        case True
        moreover have "?equiv i i" by (simp add: term_pp_rel_refl)
        ultimately show ?thesis ..
      next
        case False
        let ?Q = "{seq j | j. j < i \<and> is_sig_red (=) (=) {seq j} (seq i)}"
        have "?Q \<subseteq> range seq" by blast
        also have "... \<subseteq> dgrad_sig_set d" by (fact assms(2))
        finally have "?Q \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
        moreover from \<open>?Q \<subseteq> range seq\<close> \<open>0 \<notin> range seq\<close> have "0 \<notin> ?Q" by blast
        ultimately have Q_sub: "pp_of_term ` lt ` ?Q \<subseteq> dgrad_set d (dgrad_max d)"
          unfolding image_image by (smt CollectI dgrad_p_setD_lt dgrad_set_def image_subset_iff subsetCE)
        have *: "\<exists>g\<in>seq ` {0..<k}. is_sig_red (=) (=) {g} (seq k)" if "k \<notin> min_set" for k
          proof -
          from that obtain j where "j < k" and a: "lt (seq j) adds\<^sub>t lt (seq k)"
            and b: "punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq k))" by (auto simp: min_set_def)
          note assms(1, 7)
          moreover from assms(2) have "seq k \<in> dgrad_sig_set d" by fastforce
          moreover from \<open>j < k\<close> have "seq j \<in> seq ` {0..<k}" by simp
          moreover from assms(3) have "rep_list (seq k) \<noteq> 0" and "rep_list (seq j) \<noteq> 0" by fastforce+
          ultimately have "is_sig_red (\<preceq>\<^sub>t) (=) (seq ` {0..<k}) (seq k)" using a b by (rule lemma_21)
          moreover from assms(5)[of k] have "\<not> is_sig_red (\<prec>\<^sub>t) (=) (seq ` {0..<k}) (seq k)"
            by (simp add: is_sig_red_top_tail_cases)
          ultimately have "is_sig_red (=) (=) (seq ` {0..<k}) (seq k)"
            by (simp add: is_sig_red_sing_reg_cases)
          then obtain g0 where "g0 \<in> seq ` {0..<k}" and "is_sig_red (=) (=) {g0} (seq k)"
            by (rule is_sig_red_singletonI)
          thus ?thesis ..
        qed

        from this[OF False] obtain g0 where "g0 \<in> seq ` {0..<i}" and "is_sig_red (=) (=) {g0} (seq i)" ..
        hence "g0 \<in> ?Q" by fastforce
        hence "lt g0 \<in> lt ` ?Q" by (rule imageI)
        with assms(1) obtain v where "v \<in> lt ` ?Q" and min: "\<And>v'. v' \<prec>\<^sub>t v \<Longrightarrow> v' \<notin> lt ` ?Q"
          using Q_sub by (rule ord_term_minimum_dgrad_set, blast)
        from this(1) obtain j where "j < i" and "is_sig_red (=) (=) {seq j} (seq i)"
          and v: "v = lt (seq j)" by fastforce
        hence 1: "punit.lt (rep_list (seq j)) adds punit.lt (rep_list (seq i))"
          and 2: "punit.lt (rep_list (seq i)) \<oplus> lt (seq j) = punit.lt (rep_list (seq j)) \<oplus> lt (seq i)"
          by (auto elim: is_sig_red_top_addsE)
        show ?thesis
        proof
          show "?equiv j i" by (simp add: term_pp_rel_def 2)
        next
          show "j \<in> min_set"
          proof (rule ccontr)
            assume "j \<notin> min_set"
            from *[OF this] obtain g1 where "g1 \<in> seq ` {0..<j}" and red: "is_sig_red (=) (=) {g1} (seq j)" ..
            from this(1) obtain j0 where "j0 < j" and "g1 = seq j0" by fastforce+

            from red have 3: "punit.lt (rep_list (seq j0)) adds punit.lt (rep_list (seq j))"
              and 4: "punit.lt (rep_list (seq j)) \<oplus> lt (seq j0) = punit.lt (rep_list (seq j0)) \<oplus> lt (seq j)"
              by (auto simp: \<open>g1 = seq j0\<close> elim: is_sig_red_top_addsE)

            from \<open>j0 < j\<close> \<open>j < i\<close> have "j0 < i" by simp
            from \<open>j0 < j\<close> have "lt (seq j0) \<prec>\<^sub>t v" unfolding v by (rule assms(4))
            hence "lt (seq j0) \<notin> lt `?Q" by (rule min)
            with \<open>j0 < i\<close> have "\<not> is_sig_red (=) (=) {seq j0} (seq i)" by blast
            moreover have "is_sig_red (=) (=) {seq j0} (seq i)"
            proof (rule is_sig_red_top_addsI)
              from assms(3) show "rep_list (seq j0) \<noteq> 0" by fastforce
            next
              from assms(3) show "rep_list (seq i) \<noteq> 0" by fastforce
            next
              from 3 1 show "punit.lt (rep_list (seq j0)) adds punit.lt (rep_list (seq i))"
                by (rule adds_trans)
            next
              from 4 have "?equiv j0 j" by (simp add: term_pp_rel_def)
              also from 2 have "?equiv j i" by (simp add: term_pp_rel_def)
              finally(term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (=)\<close>])
              show "punit.lt (rep_list (seq i)) \<oplus> lt (seq j0) = punit.lt (rep_list (seq j0)) \<oplus> lt (seq i)"
                by (simp add: term_pp_rel_def)
            next
              show "ord_term_lin.is_le_rel (=)" by simp
            qed simp_all
            ultimately show False ..
          qed
        qed
      qed
      have "term_pp_rel (=) (cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j)))) (lt (seq j), punit.lt (rep_list (seq j)))"
        by (rule term_pp_rel_sym, fact \<open>symp (=)\<close>, rule term_pp_rel_cancel, fact \<open>reflp (=)\<close>)
      also note \<open>?equiv j i\<close>
      also(term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (=)\<close>]) note x
      finally(term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (=)\<close>])
      have "term_pp_rel (=) (cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j)))) (u, t)" .
      with \<open>symp (=)\<close> have "term_pp_rel (=) (u, t) (cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j))))"
        by (rule term_pp_rel_sym)
      hence "(u, t) = cancel_term_pp_pair (lt (seq j), punit.lt (rep_list (seq j)))"
        using \<open>canon_term_pp_pair (u, t)\<close> canon_term_pp_cancel by (rule canon_term_pp_rel_id)
      with \<open>j \<in> min_set\<close> show "(u, t) \<in> (\<lambda>i. cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i)))) ` min_set"
        by fastforce
    qed
    moreover have "finite ((\<lambda>i. cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i)))) ` min_set)"
    proof (rule finite_imageI)
      show "finite min_set" unfolding min_set_def using assms(1-4) by (rule min_set_finite)
    qed
    ultimately show ?thesis by (rule finite_subset)
  qed

  have "range seq \<subseteq> seq ` (UNION ?A R)"
  proof (rule image_mono, rule)
    fix i
    show "i \<in> UNION ?A R"
    proof
      show "i \<in> R (cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i))))"
        by (simp add: R_def term_pp_rel_cancel)
      thus "cancel_term_pp_pair (lt (seq i), punit.lt (rep_list (seq i))) \<in> ?A"
        using canon_term_pp_cancel by blast
    qed
  qed
  moreover from \<open>inj seq\<close> have "infinite (range seq)" by (rule range_inj_infinite)
  ultimately have "infinite (seq ` UNION ?A R)" by (rule infinite_super)
  moreover have "finite (seq ` UNION ?A R)"
  proof (rule finite_imageI, rule finite_UN_I)
    fix x
    assume "x \<in> ?A"
    let ?rel = "term_pp_rel (\<prec>\<^sub>t)"
    have "irreflp ?rel" by (rule irreflpI, rule term_pp_rel_irrefl, fact)
    moreover have "transp ?rel" by (rule transpI, drule term_pp_rel_trans[OF \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>])
    ultimately have "wfP_on ?A ?rel" using \<open>finite ?A\<close> by (rule wfP_on_finite)
    thus "finite (R x)" using \<open>x \<in> ?A\<close>
    proof (induct rule: wfP_on_induct)
      case (step x)
      from step(1) have "canon_term_pp_pair x" by simp
      define R' where "R' = UNION (?A \<inter> {z. term_pp_rel (\<prec>\<^sub>t) z x}) R"
      define red_set where "red_set = (\<lambda>p. {k. (sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<k}))\<^sup>*\<^sup>* p (seq k)})"
      have finite_red_set: "finite (red_set p)" for p
      proof (cases "red_set p = {}")
        case True
        thus ?thesis by simp
      next
        case False
        then obtain k where "(sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<k}))\<^sup>*\<^sup>* p (seq k)"
          by (auto simp: red_set_def)
        hence lt_k: "lt (seq k) = lt p" by (rule sig_red_regular_rtrancl_lt)
        have "red_set p \<subseteq> {k}"
        proof
          fix k'
          assume "k' \<in> red_set p"
          hence "(sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<k'}))\<^sup>*\<^sup>* p (seq k')"
            by (simp add: red_set_def)
          hence "lt (seq k') = lt (seq k)" unfolding lt_k by (rule sig_red_regular_rtrancl_lt)
          with \<open>inj (\<lambda>i. lt (seq i))\<close> have "k' = k" by (rule injD)
          thus "k' \<in> {k}" by simp
        qed
        thus ?thesis using infinite_super by auto
      qed

      have "R x \<subseteq> (\<Union>i\<in>R'. \<Union>j\<in>R'. red_set (spair (seq i) (seq j))) \<union>
                   (UNION {0..<length fs} (\<lambda>j. red_set (monomial 1 (term_of_pair (0, j)))))"
        (is "_ \<subseteq> ?B \<union> ?C")
      proof
        fix i
        assume "i \<in> R x"
        hence i_x: "term_pp_rel (=) (lt (seq i), punit.lt (rep_list (seq i))) x"
          by (simp add: R_def term_pp_rel_def)
        from assms(6)[of i] show "i \<in> ?B \<union> ?C"
        proof (elim disjE exE conjE)
          fix j
          assume "j < length fs"
          hence "j \<in> {0..<length fs}" by simp
          assume "(sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<i}))\<^sup>*\<^sup>* (monomial 1 (term_of_pair (0, j))) (seq i)"
          hence "i \<in> red_set (monomial 1 (term_of_pair (0, j)))" by (simp add: red_set_def)
          with \<open>j \<in> {0..<length fs}\<close> have "i \<in> ?C" ..
          thus ?thesis ..
        next
          fix j k
          let ?li = "punit.lt (rep_list (seq i))"
          let ?lj = "punit.lt (rep_list (seq j))"
          let ?lk = "punit.lt (rep_list (seq k))"
          assume spair_red: "(sig_red (\<prec>\<^sub>t) (\<preceq>) (seq ` {0..<i}))\<^sup>*\<^sup>* (spair (seq j) (seq k)) (seq i)"
          hence "i \<in> red_set (spair (seq j) (seq k))" by (simp add: red_set_def)
          from spair_red have lt_i: "lt (seq i) = lt (spair (seq j) (seq k))"
            by (rule sig_red_regular_rtrancl_lt)
          from spair_red have lt_i': "?li \<preceq> punit.lt (rep_list (spair (seq j) (seq k)))"
            by (rule sig_red_rtrancl_lt_rep_list)
          from assms(3) have i_0: "rep_list (seq i) \<noteq> 0" and j_0: "rep_list (seq j) \<noteq> 0"
            and k_0: "rep_list (seq k) \<noteq> 0" by fastforce+
          from spair_red this(1) have spair_0: "rep_list (spair (seq j) (seq k)) \<noteq> 0"
            using punit.rtrancl_0 sig_red_red_rtrancl by force

          have R'I: "a \<in> R'" if "term_pp_rel (\<prec>\<^sub>t) (lt (seq a), punit.lt (rep_list (seq a))) x" for a
          proof -
            let ?x = "cancel_term_pp_pair (lt (seq a), punit.lt (rep_list (seq a)))"
            show ?thesis unfolding R'_def
            proof (rule UN_I, simp, intro conjI)
              show "a \<in> R ?x" by (simp add: R_def term_pp_rel_cancel)
              thus "R ?x \<noteq> {}" by blast
            next
              note \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>
              moreover have "term_pp_rel (=) ?x (lt (seq a), punit.lt (rep_list (seq a)))"
                by (rule term_pp_rel_sym, fact, rule term_pp_rel_cancel, fact)
              ultimately show "term_pp_rel (\<prec>\<^sub>t) ?x x" using that by (rule term_pp_rel_trans_eq_left)
            qed (fact canon_term_pp_cancel)
          qed

          assume "is_regular_spair (seq j) (seq k)"
          hence "?lk \<oplus> lt (seq j) \<noteq> ?lj \<oplus> lt (seq k)" by (rule is_regular_spairD3)
          hence "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) x \<and> term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) x"
          proof (rule ord_term_lin.neqE)
            assume c: "?lk \<oplus> lt (seq j) \<prec>\<^sub>t ?lj \<oplus> lt (seq k)"
            hence j_k: "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) (lt (seq k), ?lk)"
              by (simp add: term_pp_rel_def)
            note \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>
            moreover have "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) (lt (seq i), ?li)"
            proof (simp add: term_pp_rel_def)
              from lt_i' have "?li \<oplus> lt (seq k) \<preceq>\<^sub>t
                                punit.lt (rep_list (spair (seq j) (seq k))) \<oplus> lt (seq k)"
                by (rule splus_mono_left)
              also have "... \<prec>\<^sub>t (?lk - gcs ?lk ?lj + ?lj) \<oplus> lt (seq k)"
                by (rule splus_mono_strict_left, rule lt_rep_list_spair, fact+, simp only: add.commute)
              also have "... = ((?lk + ?lj) - gcs ?lj ?lk) \<oplus> lt (seq k)"
                by (simp add: minus_plus gcs_adds_2 gcs_comm)
              also have "... = ?lk \<oplus> ((?lj - gcs ?lj ?lk) \<oplus> lt (seq k))"
                by (simp add: minus_plus' gcs_adds splus_assoc[symmetric])
              also have "... = ?lk \<oplus> lt (seq i)"
                by (simp add: lt_spair'[OF k_0 _ c] add.commute spair_comm[of "seq j"] lt_i)
              finally show "?li \<oplus> lt (seq k) \<prec>\<^sub>t ?lk \<oplus> lt (seq i)" .
            qed
            ultimately have "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) x" using i_x
              by (rule term_pp_rel_trans_eq_right)
            moreover from \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close> j_k this
            have "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) x" by (rule term_pp_rel_trans)
            ultimately show ?thesis by simp
          next
            assume c: "?lj \<oplus> lt (seq k) \<prec>\<^sub>t ?lk \<oplus> lt (seq j)"
            hence j_k: "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) (lt (seq j), ?lj)"
              by (simp add: term_pp_rel_def)
            note \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close>
            moreover have "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) (lt (seq i), ?li)"
            proof (simp add: term_pp_rel_def)
              from lt_i' have "?li \<oplus> lt (seq j) \<preceq>\<^sub>t
                                punit.lt (rep_list (spair (seq j) (seq k))) \<oplus> lt (seq j)"
                by (rule splus_mono_left)
              thm lt_rep_list_spair
              also have "... \<prec>\<^sub>t (?lk - gcs ?lk ?lj + ?lj) \<oplus> lt (seq j)"
                by (rule splus_mono_strict_left, rule lt_rep_list_spair, fact+, simp only: add.commute)
              also have "... = ((?lk + ?lj) - gcs ?lk ?lj) \<oplus> lt (seq j)"
                by (simp add: minus_plus gcs_adds_2 gcs_comm)
              also have "... = ?lj \<oplus> ((?lk - gcs ?lk ?lj) \<oplus> lt (seq j))"
                by (simp add: minus_plus' gcs_adds splus_assoc[symmetric] add.commute)
              also have "... = ?lj \<oplus> lt (seq i)" by (simp add: lt_spair'[OF j_0 _ c] lt_i add.commute)
              finally show "?li \<oplus> lt (seq j) \<prec>\<^sub>t ?lj \<oplus> lt (seq i)" .
            qed
            ultimately have "term_pp_rel (\<prec>\<^sub>t) (lt (seq j), ?lj) x" using i_x
              by (rule term_pp_rel_trans_eq_right)
            moreover from \<open>ord_term_lin.is_le_rel (\<prec>\<^sub>t)\<close> j_k this
            have "term_pp_rel (\<prec>\<^sub>t) (lt (seq k), ?lk) x" by (rule term_pp_rel_trans)
            ultimately show ?thesis by simp
          qed
          with \<open>i \<in> red_set (spair (seq j) (seq k))\<close> have "i \<in> ?B" using R'I by blast
          thus ?thesis ..
        qed
      qed
      moreover have "finite (?B \<union> ?C)"
      proof (rule finite_UnI)
        have "finite R'" unfolding R'_def
        proof (rule finite_UN_I)
          from \<open>finite ?A\<close> show "finite (?A \<inter> {z. term_pp_rel (\<prec>\<^sub>t) z x})" by simp
        next
          fix y
          assume "y \<in> ?A \<inter> {z. term_pp_rel (\<prec>\<^sub>t) z x}"
          hence "y \<in> ?A" and "term_pp_rel (\<prec>\<^sub>t) y x" by simp_all
          thus "finite (R y)" by (rule step(2))
        qed
        show "finite ?B" by (intro finite_UN_I \<open>finite R'\<close> finite_red_set)
      next
        show "finite ?C" by (intro finite_UN_I finite_atLeastLessThan finite_red_set)
      qed
      ultimately show ?case by (rule finite_subset)
    qed
  qed fact
  ultimately show ?thesis ..
qed

subsubsection \<open>Concrete Rewrite Orders\<close>

definition is_strict_rewrite_ord :: "(('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_strict_rewrite_ord rel \<longleftrightarrow>
              (\<forall>x y. rel x y \<longrightarrow> \<not> rel y x) \<and>
              (\<exists>rel'. is_rewrite_ord rel' \<and> rel \<le> rel' \<and> (\<forall>x y. rel' x y \<longrightarrow> fst x \<noteq> fst y \<longrightarrow> rel x y))"

lemma is_strict_rewrite_ordI:
  assumes "\<And>x y. rel x y \<Longrightarrow> rel y x \<Longrightarrow> False" and "is_rewrite_ord rel'" and "rel \<le> rel'"
    and "\<And>x y. rel' x y \<Longrightarrow> fst x \<noteq> fst y \<Longrightarrow> rel x y"
  shows "is_strict_rewrite_ord rel"
  unfolding is_strict_rewrite_ord_def using assms by blast

lemma is_strict_rewrite_ordE:
  assumes "is_strict_rewrite_ord rel"
  obtains rel' where "is_rewrite_ord rel'" and "rel \<le> rel'"
    and "\<And>x y. rel' x y \<Longrightarrow> fst x \<noteq> fst y \<Longrightarrow> rel x y"
  using assms unfolding is_strict_rewrite_ord_def by blast

lemma is_strict_rewrite_ord_asym: "is_strict_rewrite_ord rel \<Longrightarrow> rel p q \<Longrightarrow> \<not> rel q p"
  unfolding is_strict_rewrite_ord_def by blast

lemma is_strict_rewrite_ord_irrefl: "is_strict_rewrite_ord rel \<Longrightarrow> \<not> rel p p"
  using is_strict_rewrite_ord_asym by blast

definition rw_rat :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_rat p q \<longleftrightarrow> (let u = punit.lt (snd q) \<oplus> fst p; v = punit.lt (snd p) \<oplus> fst q in
                          u \<prec>\<^sub>t v \<or> (u = v \<and> fst p \<preceq>\<^sub>t fst q))"

definition rw_rat_strict :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_rat_strict p q \<longleftrightarrow> (let u = punit.lt (snd q) \<oplus> fst p; v = punit.lt (snd p) \<oplus> fst q in
                          u \<prec>\<^sub>t v \<or> (u = v \<and> fst p \<prec>\<^sub>t fst q))"

definition rw_add :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_add p q \<longleftrightarrow> (fst p \<preceq>\<^sub>t fst q)"

definition rw_add_strict :: "('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> bool"
  where "rw_add_strict p q \<longleftrightarrow> (fst p \<prec>\<^sub>t fst q)"

lemma rw_rat_alt:
  "rw_rat p q \<longleftrightarrow> (term_pp_rel (\<prec>\<^sub>t) (fst p, punit.lt (snd p)) (fst q, punit.lt (snd q)) \<or>
                    (term_pp_rel (=) (fst p, punit.lt (snd p)) (fst q, punit.lt (snd q)) \<and> fst p \<preceq>\<^sub>t fst q))"
  by (simp add: rw_rat_def term_pp_rel_def Let_def)

lemma rw_rat_is_rewrite_ord: "is_rewrite_ord rw_rat"
proof (rule is_rewrite_ordI)
  show "reflp rw_rat" by (simp add: reflp_def rw_rat_def)
next
  have 1: "ord_term_lin.is_le_rel (\<prec>\<^sub>t)" and 2: "ord_term_lin.is_le_rel (=)"
    by (rule ord_term_lin.is_le_relI)+
  show "transp rw_rat"
    by (auto simp: transp_def rw_rat_alt dest: term_pp_rel_trans[OF 1] term_pp_rel_trans_eq_left[OF 1]
        term_pp_rel_trans_eq_right[OF 1] term_pp_rel_trans[OF 2])
next
  fix p q
  show "rw_rat p q \<or> rw_rat q p" by (auto simp: rw_rat_def Let_def)
next
  fix p q
  assume "rw_rat p q" and "rw_rat q p"
  thus "fst p = fst q" by (auto simp: rw_rat_def Let_def)
next
  fix d G p q
  assume d: "dickson_grading d" and gb: "is_sig_GB_upt d G (lt q)" and "p \<in> G" and "q \<in> G"
    and "p \<noteq> 0" and "q \<noteq> 0" and "lt p adds\<^sub>t lt q" and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G q"
  let ?u = "punit.lt (rep_list q) \<oplus> lt p"
  let ?v = "punit.lt (rep_list p) \<oplus> lt q"
  from \<open>lt p adds\<^sub>t lt q\<close> obtain t where lt_q: "lt q = t \<oplus> lt p" by (rule adds_termE)
  from gb have "G \<subseteq> dgrad_sig_set d" by (rule is_sig_GB_uptD1)
  hence "G \<subseteq> dgrad_max_set d" by (simp add: dgrad_sig_set_def)
  with d obtain p' where red: "(sig_red (\<prec>\<^sub>t) (=) G)\<^sup>*\<^sup>* (monom_mult 1 t p) p'"
    and "\<not> is_sig_red (\<prec>\<^sub>t) (=) G p'" by (rule sig_irredE_dgrad_max_set)
  from red have "lt p' = lt (monom_mult 1 t p)" and "lc p' = lc (monom_mult 1 t p)"
    and 2: "punit.lt (rep_list p') \<preceq> punit.lt (rep_list (monom_mult 1 t p))"
    by (rule sig_red_regular_rtrancl_lt, rule sig_red_regular_rtrancl_lc, rule sig_red_rtrancl_lt_rep_list)
  with \<open>p \<noteq> 0\<close> have "lt p' = lt q" and "lc p' = lc p" by (simp_all add: lt_q lt_monom_mult)
  from 2 punit.lt_monom_mult_le[simplified] have 3: "punit.lt (rep_list p') \<preceq> t + punit.lt (rep_list p)"
    unfolding rep_list_monom_mult by (rule ordered_powerprod_lin.order_trans)
  have "punit.lt (rep_list p') = punit.lt (rep_list q)"
  proof (rule sig_regular_top_reduced_lt_unique)
    show "p' \<in> dgrad_sig_set d"
    proof (rule dgrad_sig_set_closed_sig_red_rtrancl)
      note d
      moreover have "d t \<le> dgrad_max d"
      proof (rule le_trans)
        have "t adds lp q" by (simp add: lt_q term_simps)
        with d show "d t \<le> d (lp q)" by (rule dickson_grading_adds_imp_le)
      next
        from \<open>q \<in> G\<close> \<open>G \<subseteq> dgrad_max_set d\<close> have "q \<in> dgrad_max_set d" ..
        thus "d (lp q) \<le> dgrad_max d" using \<open>q \<noteq> 0\<close> by (rule dgrad_p_setD_lt)
      qed
      moreover from \<open>p \<in> G\<close> \<open>G \<subseteq> dgrad_sig_set d\<close> have "p \<in> dgrad_sig_set d" ..
      ultimately show "monom_mult 1 t p \<in> dgrad_sig_set d" by (rule dgrad_sig_set_closed_monom_mult)
    qed fact+
  next
    from \<open>q \<in> G\<close> \<open>G \<subseteq> dgrad_sig_set d\<close> show "q \<in> dgrad_sig_set d" ..
  next
    from \<open>p \<noteq> 0\<close> \<open>lc p' = lc p\<close> show "p' \<noteq> 0" by (auto simp: lc_eq_zero_iff)
  qed fact+
  with 3 have "punit.lt (rep_list q) \<preceq> t + punit.lt (rep_list p)" by simp
  hence "?u \<preceq>\<^sub>t (t + punit.lt (rep_list p)) \<oplus> lt p" by (rule splus_mono_left)
  also have "... = ?v" by (simp add: lt_q splus_assoc splus_left_commute)
  finally have "?u \<preceq>\<^sub>t ?v" by (simp only: rel_def)
  moreover from \<open>lt p adds\<^sub>t lt q\<close> have "lt p \<preceq>\<^sub>t lt q" by (rule ord_adds_term)
  ultimately show "rw_rat (spp_of p) (spp_of q)" by (auto simp: rw_rat_def Let_def spp_of_def)
qed

lemma rw_rat_strict_is_strict_rewrite_ord: "is_strict_rewrite_ord rw_rat_strict"
proof (rule is_strict_rewrite_ordI)
  fix p q
  assume "rw_rat_strict p q" and "rw_rat_strict q p"
  thus False by (auto simp: rw_rat_strict_def Let_def)
next
  show "rw_rat_strict \<le> rw_rat" by (auto simp: rw_rat_strict_def rw_rat_def Let_def)
next
  fix p q
  assume "rw_rat p q" and "fst p \<noteq> fst q"
  thus "rw_rat_strict p q" by (auto simp: rw_rat_strict_def rw_rat_def Let_def)
qed (fact rw_rat_is_rewrite_ord)

lemma rw_add_is_rewrite_ord: "is_rewrite_ord rw_add"
proof (rule is_rewrite_ordI)
  show "reflp rw_add" by (simp add: reflp_def rw_add_def)
next
  show "transp rw_add" by (auto simp: transp_def rw_add_def)
next
  fix p q
  show "rw_add p q \<or> rw_add q p" by (simp only: rw_add_def ord_term_lin.linear)
next
  fix p q
  assume "rw_add p q" and "rw_add q p"
  thus "fst p = fst q" unfolding rw_add_def by (rule ord_term_lin.antisym)
next
  fix p q :: "'t \<Rightarrow>\<^sub>0 'b"
  assume "lt p adds\<^sub>t lt q"
  thus "rw_add (spp_of p) (spp_of q)" unfolding rw_add_def spp_of_def fst_conv by (rule ord_adds_term)
qed

lemma rw_add_strict_is_strict_rewrite_ord: "is_strict_rewrite_ord rw_add_strict"
proof (rule is_strict_rewrite_ordI)
  fix p q
  assume "rw_add_strict p q" and "rw_add_strict q p"
  thus False by (simp add: rw_add_strict_def)
next
  show "rw_add_strict \<le> rw_add" by (rule, simp add: rw_add_strict_def rw_add_def)
next
  fix p q
  assume "rw_add p q" and "fst p \<noteq> fst q"
  thus "rw_add_strict p q" by (simp add: rw_add_strict_def rw_add_def)
qed (fact rw_add_is_rewrite_ord)

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
