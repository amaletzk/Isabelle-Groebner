section \<open>Multivariate Polynomials with Power-Products Represented by Polynomial Mappings\<close>

theory MPoly_PM
  imports Signature_Groebner.Quasi_PM_Power_Products
begin

text \<open>Many notions introduced in this theory for type @{typ "('x \<Rightarrow>\<^sub>0 'a) \<Rightarrow>\<^sub>0 'b"} closely resemble
  those introduced in @{theory Polynomials.MPoly_Type} for type @{typ "'a mpoly"}.\<close>

lemma monomial_single_power:
  "(monomial c (Poly_Mapping.single x k)) ^ n = monomial (c ^ n) (Poly_Mapping.single x (k * n))"
proof -
  have eq: "(\<Sum>i = 0..<n. Poly_Mapping.single x k) = Poly_Mapping.single x (k * n)"
    by (induct n, simp_all add: add.commute single_add)
  show ?thesis by (simp add: punit.monomial_power eq)
qed

lemma times_canc_left:
  assumes "h * p = h * q" and "h \<noteq> (0::('x::linorder \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::ring_no_zero_divisors)"
  shows "p = q"
proof (rule ccontr)
  assume "p \<noteq> q"
  hence "p - q \<noteq> 0" by simp
  with assms(2) have "h * (p - q) \<noteq> 0" by simp
  hence "h * p \<noteq> h * q" by (simp add: algebra_simps)
  thus False using assms(1) ..
qed

lemma times_canc_right:
  assumes "p * h = q * h" and "h \<noteq> (0::('x::linorder \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::ring_no_zero_divisors)"
  shows "p = q"
proof (rule ccontr)
  assume "p \<noteq> q"
  hence "p - q \<noteq> 0" by simp
  hence "(p - q) * h \<noteq> 0" using assms(2) by simp
  hence "p * h \<noteq> q * h" by (simp add: algebra_simps)
  thus False using assms(1) ..
qed

subsection \<open>More General Facts about Ideals\<close>

lemma ideal_eq_zero_iff [iff]: "ideal F = {0} \<longleftrightarrow> F \<subseteq> {0}"
  by (metis empty_subsetI ideal.span_empty ideal.span_eq)

lemma ideal_field_cases:
  obtains "ideal B = {0}" | "ideal (B::'a::field set) = UNIV"
proof (cases "ideal B = {0}")
  case True
  thus ?thesis ..
next
  case False
  hence "\<not> B \<subseteq> {0}" by simp
  then obtain b where "b \<in> B" and "b \<noteq> 0" by blast
  from this(1) have "b \<in> ideal B" by (rule ideal.span_base)
  hence "inverse b * b \<in> ideal B" by (rule ideal.span_scale)
  with \<open>b \<noteq> 0\<close> have "ideal B = UNIV" by (simp add: ideal_eq_UNIV_iff_contains_one)
  thus ?thesis ..
qed

corollary ideal_field_disj: "ideal B = {0} \<or> ideal (B::'a::field set) = UNIV"
  by (rule ideal_field_cases) blast+

lemma image_ideal_subset:
  assumes "\<And>x y. h (x + y) = h x + h y" and "\<And>x y. h (x * y) = h x * h y"
  shows "h ` ideal F \<subseteq> ideal (h ` F)"
proof (intro subsetI, elim imageE)
  fix g f
  assume g: "g = h f"
  assume "f \<in> ideal F"
  thus "g \<in> ideal (h ` F)" unfolding g
  proof (induct f rule: ideal.span_induct_alt)
    case base
    have "h 0 = h (0 + 0)" by simp
    also have "\<dots> = h 0 + h 0" by (simp only: assms(1))
    finally show ?case by (simp add: ideal.span_zero)
  next
    case (step c f g)
    from step.hyps(1) have "h f \<in> ideal (h ` F)"
      by (intro ideal.span_base imageI)
    hence "h c * h f \<in> ideal (h ` F)" by (rule ideal.span_scale)
    hence "h c * h f + h g \<in> ideal (h ` F)"
      using step.hyps(2) by (rule ideal.span_add)
    thus ?case by (simp only: assms)
  qed
qed

lemma image_ideal_eq_surj:
  assumes "\<And>x y. h (x + y) = h x + h y" and "\<And>x y. h (x * y) = h x * h y" and "surj h"
  shows "h ` ideal B = ideal (h ` B)"
proof
  from assms(1, 2) show "h ` ideal B \<subseteq> ideal (h ` B)" by (rule image_ideal_subset)
next
  show "ideal (h ` B) \<subseteq> h ` ideal B"
  proof
    fix b
    assume "b \<in> ideal (h ` B)"
    thus "b \<in> h ` ideal B"
    proof (induct b rule: ideal.span_induct_alt)
      case base
      have "h 0 = h (0 + 0)" by simp
      also have "\<dots> = h 0 + h 0" by (simp only: assms(1))
      finally have "0 = h 0" by simp
      with ideal.span_zero show ?case by (rule rev_image_eqI)
    next
      case (step c b a)
      from assms(3) obtain c' where c: "c = h c'" by (rule surjE)
      from step.hyps(2) obtain a' where "a' \<in> ideal B" and a: "a = h a'" ..
      from step.hyps(1) obtain b' where "b' \<in> B" and b: "b = h b'" ..
      from this(1) have "b' \<in> ideal B" by (rule ideal.span_base)
      hence "c' * b' \<in> ideal B" by (rule ideal.span_scale)
      hence "c' * b' + a' \<in> ideal B" using \<open>a' \<in> _\<close> by (rule ideal.span_add)
      moreover have "c * b + a = h (c' * b' + a')"
        by (simp add: c b a assms(1, 2))
      ultimately show ?case by (rule rev_image_eqI)
    qed
  qed
qed

context
  fixes h :: "'a \<Rightarrow> 'a::comm_ring_1"
  assumes h_plus: "h (x + y) = h x + h y"
  assumes h_times: "h (x * y) = h x * h y"
  assumes h_idem: "h (h x) = h x"
begin

lemma in_idealE_homomorphism_finite:
  assumes "finite B" and "B \<subseteq> range h" and "p \<in> range h" and "p \<in> ideal B"
  obtains q where "\<And>b. q b \<in> range h" and "p = (\<Sum>b\<in>B. q b * b)"
proof -
  from assms(1, 4) obtain q0 where p: "p = (\<Sum>b\<in>B. q0 b * b)" by (rule ideal.span_finiteE)
  define q where "q = (\<lambda>b. h (q0 b))"
  show ?thesis
  proof
    fix b
    show "q b \<in> range h" unfolding q_def by (rule rangeI)
  next
    from assms(3) obtain p' where "p = h p'" ..
    hence "p = h p" by (simp only: h_idem)
    also from \<open>finite B\<close> have "\<dots> = (\<Sum>b\<in>B. q b * h b)" unfolding p
    proof (induct B)
      case empty
      have "h 0 = h (0 + 0)" by simp
      also have "\<dots> = h 0 + h 0" by (simp only: h_plus)
      finally show ?case by simp
    next
      case (insert b B)
      thus ?case by (simp add: h_plus h_times q_def)
    qed
    also from refl have "\<dots> = (\<Sum>b\<in>B. q b * b)"
    proof (rule sum.cong)
      fix b
      assume "b \<in> B"
      hence "b \<in> range h" using assms(2) ..
      then obtain b' where "b = h b'" ..
      thus "q b * h b = q b * b" by (simp only: h_idem)
    qed
    finally show "p = (\<Sum>b\<in>B. q b * b)" .
  qed
qed

corollary in_idealE_homomorphism:
  assumes "B \<subseteq> range h" and "p \<in> range h" and "p \<in> ideal B"
  obtains A q where "finite A" and "A \<subseteq> B" and "\<And>b. q b \<in> range h" and "p = (\<Sum>b\<in>A. q b * b)"
proof -
  from assms(3) obtain A where "finite A" and "A \<subseteq> B" and "p \<in> ideal A"
    by (rule ideal.span_finite_subset)
  from this(2) assms(1) have "A \<subseteq> range h" by (rule subset_trans)
  with \<open>finite A\<close> obtain q where "\<And>b. q b \<in> range h" and "p = (\<Sum>b\<in>A. q b * b)"
    using assms(2) \<open>p \<in> ideal A\<close> by (rule in_idealE_homomorphism_finite) blast
  with \<open>finite A\<close> \<open>A \<subseteq> B\<close> show ?thesis ..
qed

lemma ideal_induct_homomorphism [consumes 3, case_names 0 plus]:
  assumes "B \<subseteq> range h" and "p \<in> range h" and "p \<in> ideal B"
  assumes "P 0" and "\<And>c b a. c \<in> range h \<Longrightarrow> b \<in> B \<Longrightarrow> P a \<Longrightarrow> a \<in> range h \<Longrightarrow> P (c * b + a)"
  shows "P p"
proof -
  from assms(1-3) obtain A q where "finite A" and "A \<subseteq> B" and rl: "\<And>f. q f \<in> range h"
    and p: "p = (\<Sum>f\<in>A. q f * f)" by (rule in_idealE_homomorphism) blast
  show ?thesis unfolding p using \<open>finite A\<close> \<open>A \<subseteq> B\<close>
  proof (induct A)
    case empty
    from assms(4) show ?case by simp
  next
    case (insert a A)
    from insert.hyps(1, 2) have "(\<Sum>f\<in>insert a A. q f * f) = q a * a + (\<Sum>f\<in>A. q f * f)" by simp
    also from rl have "P \<dots>"
    proof (rule assms(5))
      have "a \<in> insert a A" by simp
      thus "a \<in> B" using insert.prems ..
    next
      from insert.prems have "A \<subseteq> B" by simp
      thus "P (\<Sum>f\<in>A. q f * f)" by (rule insert.hyps)
    next
      from insert.prems have "A \<subseteq> B" by simp
      hence "A \<subseteq> range h" using assms(1) by (rule subset_trans)
      with \<open>finite A\<close> show "(\<Sum>f\<in>A. q f * f) \<in> range h"
      proof (induct A)
        case empty
        have "h 0 = h (0 + 0)" by simp
        also have "\<dots> = h 0 + h 0" by (simp only: h_plus)
        finally have "(\<Sum>f\<in>{}. q f * f) = h 0" by simp
        thus ?case by (rule image_eqI) simp
      next
        case (insert a A)
        from insert.prems have "a \<in> range h" and "A \<subseteq> range h" by simp_all
        from this(1) obtain a' where a: "a = h a'" ..
        from \<open>q a \<in> range h\<close> obtain q' where q: "q a = h q'" ..
        from \<open>A \<subseteq> _\<close> have "(\<Sum>f\<in>A. q f * f) \<in> range h" by (rule insert.hyps)
        then obtain m where eq: "(\<Sum>f\<in>A. q f * f) = h m" ..
        from insert.hyps(1, 2) have "(\<Sum>f\<in>insert a A. q f * f) = q a * a + (\<Sum>f\<in>A. q f * f)" by simp
        also have "\<dots> = h (q' * a' + m)" unfolding q by (simp add: a eq h_plus h_times)
        also have "\<dots> \<in> range h" by (rule rangeI)
        finally show ?case .
      qed
    qed
    finally show ?case .
  qed
qed

lemma image_ideal_eq_Int: "h ` ideal B = ideal (h ` B) \<inter> range h"
proof
  from h_plus h_times have "h ` ideal B \<subseteq> ideal (h ` B)" by (rule image_ideal_subset)
  thus "h ` ideal B \<subseteq> ideal (h ` B) \<inter> range h" by blast
next
  show "ideal (h ` B) \<inter> range h \<subseteq> h ` ideal B"
  proof
    fix b
    assume "b \<in> ideal (h ` B) \<inter> range h"
    hence "b \<in> ideal (h ` B)" and "b \<in> range h" by simp_all
    have "h ` B \<subseteq> range h" by blast
    thus "b \<in> h ` ideal B" using \<open>b \<in> range h\<close> \<open>b \<in> ideal (h ` B)\<close>
    proof (induct b rule: ideal_induct_homomorphism)
      case 0
      have "h 0 = h (0 + 0)" by simp
      also have "\<dots> = h 0 + h 0" by (simp only: h_plus)
      finally have "0 = h 0" by simp
      with ideal.span_zero show ?case by (rule rev_image_eqI)
    next
      case (plus c b a)
      from plus.hyps(1) obtain c' where c: "c = h c'" ..
      from plus.hyps(3) obtain a' where "a' \<in> ideal B" and a: "a = h a'" ..
      from plus.hyps(2) obtain b' where "b' \<in> B" and b: "b = h b'" ..
      from this(1) have "b' \<in> ideal B" by (rule ideal.span_base)
      hence "c' * b' \<in> ideal B" by (rule ideal.span_scale)
      hence "c' * b' + a' \<in> ideal B" using \<open>a' \<in> _\<close> by (rule ideal.span_add)
      moreover have "c * b + a = h (c' * b' + a')" by (simp add: a b c h_plus h_times)
      ultimately show ?case by (rule rev_image_eqI)
    qed
  qed
qed

end

subsection \<open>Order relation on polynomial mappings\<close>

definition le_pm :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::{ord,zero}) \<Rightarrow> bool" (infixl "\<unlhd>" 50)
  where "le_pm s t \<longleftrightarrow> lookup s \<le> lookup t"

lemma le_pmI: "(\<And>x. lookup s x \<le> lookup t x) \<Longrightarrow> s \<unlhd> t"
  unfolding le_pm_def le_fun_def ..

lemma le_pmD: "s \<unlhd> t \<Longrightarrow> lookup s x \<le> lookup t x"
  by (simp add: le_pm_def le_fun_def)

lemma le_pm_refl [simp]: "s \<unlhd> (s::_ \<Rightarrow>\<^sub>0 _::preorder)"
  by (simp add: le_pm_def)

lemma le_pm_antisym: "s \<unlhd> t \<Longrightarrow> t \<unlhd> s \<Longrightarrow> s = (t::_ \<Rightarrow>\<^sub>0 _::order)"
  by (simp add: le_pm_def poly_mapping_eq_iff)

lemma le_pm_trans [trans]: "s \<unlhd> t \<Longrightarrow> t \<unlhd> u \<Longrightarrow> s \<unlhd> (u::_ \<Rightarrow>\<^sub>0 _::preorder)"
  by (auto simp: le_pm_def dest: order_trans)

lemma le_pm_mono_plus_right: "s \<unlhd> t \<Longrightarrow> s + u \<unlhd> t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add)"
  by (simp add: le_pm_def lookup_plus_fun le_fun_def add_right_mono)

lemma le_pm_mono_plus_left: "s \<unlhd> t \<Longrightarrow> u + s \<unlhd> u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add)"
  by (simp add: le_pm_def lookup_plus_fun le_fun_def add_left_mono)

lemma le_pm_mono_plus: "s \<unlhd> t \<Longrightarrow> u \<unlhd> v \<Longrightarrow> s + u \<unlhd> t + (v::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add)"
  by (simp add: le_pm_def lookup_plus_fun le_fun_def add_mono)

lemma le_pm_increasing: "0 \<unlhd> u \<Longrightarrow> s \<unlhd> t \<Longrightarrow> s \<unlhd> u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  using le_pm_mono_plus[of 0 u s t] by simp

lemma le_pm_increasing2: "0 \<unlhd> u \<Longrightarrow> s \<unlhd> t \<Longrightarrow> s \<unlhd> t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  by (simp add: le_pm_increasing add.commute[of t])

lemma le_pm_decreasing: "u \<unlhd> 0 \<Longrightarrow> s \<unlhd> t \<Longrightarrow> u + s \<unlhd> (t::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  using le_pm_mono_plus[of u 0 s t] by simp

lemma le_pm_decreasing2: "u \<unlhd> 0 \<Longrightarrow> s \<unlhd> t \<Longrightarrow> s + u \<unlhd> (t::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  using le_pm_mono_plus[of s t u 0] by simp

lemma zero_le_pm: "0 \<unlhd> (t::_ \<Rightarrow>\<^sub>0 _::add_linorder_min)"
  by (simp add: le_pmI)

lemma le_pm_mono_minus: "s \<unlhd> t \<Longrightarrow> s - u \<unlhd> t - (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_group_add)"
  by (simp add: le_pm_def lookup_minus_fun)

lemma adds_pmI: "s \<unlhd> t \<Longrightarrow> s adds (t::'a \<Rightarrow>\<^sub>0 'b::add_linorder)"
  by (simp add: le_pm_def, intro adds_poly_mappingI)

lemma adds_pm: "s adds t \<longleftrightarrow> s \<unlhd> (t::'a \<Rightarrow>\<^sub>0 'b::add_linorder_min)"
  by (simp add: adds_poly_mapping le_pm_def)

lemma gcs_le_pm:
  shows "gcs s t \<unlhd> s" and "gcs s t \<unlhd> t"
  by (simp_all add: gcs_leq_fun_1 gcs_leq_fun_2 le_pm_def lookup_gcs_fun)

lemma gcs_ge_pm: "u \<unlhd> s \<Longrightarrow> u \<unlhd> t \<Longrightarrow> u \<unlhd> gcs s t"
  by (simp add: leq_gcs_fun le_pm_def lookup_gcs_fun)

lemma lcs_ge_pm:
  shows "s \<unlhd> lcs s t" and "t \<unlhd> lcs s t"
  by (simp_all add: leq_lcs_fun_1 leq_lcs_fun_2 le_pm_def lookup_lcs_fun)

lemma lcs_le_pm: "s \<unlhd> u \<Longrightarrow> t \<unlhd> u \<Longrightarrow> lcs s t \<unlhd> u"
  by (simp add: lcs_leq_fun le_pm_def lookup_lcs_fun)

lemma gcs_add_distrib_left: "gcs s t + u = gcs (s + u) (t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_gcs_fun lookup_add gcs_fun min_add_distrib_left)

lemma gcs_add_distrib_right: "u + gcs s t = gcs (u + s) (u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_gcs_fun lookup_add gcs_fun min_add_distrib_right)

lemma lcs_add_distrib_left: "lcs s t + u = lcs (s + u) (t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_lcs_fun lookup_add lcs_fun_def max_add_distrib_left)

lemma lcs_add_distrib_right: "u + lcs s t = lcs (u + s) (u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_lcs_fun lookup_add lcs_fun_def max_add_distrib_right)

lemma gcs_diff_distrib_left: "gcs s t - u = gcs (s - u) (t - (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_group_add))"
  by (rule poly_mapping_eqI) (simp only: lookup_gcs_fun lookup_minus gcs_fun min_diff_distrib_left)

lemma lcs_diff_distrib_left: "lcs s t - u = lcs (s - u) (t - (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_group_add))"
  by (rule poly_mapping_eqI) (simp only: lookup_lcs_fun lookup_minus lcs_fun_def max_diff_distrib_left)

lemma deg_pm_mono_le: "s \<unlhd> t \<Longrightarrow> deg_pm s \<le> deg_pm (t::'a \<Rightarrow>\<^sub>0 'b::add_linorder)"
  unfolding le_pm_def by (transfer) (auto intro!: deg_fun_leq simp: supp_fun_def)

lemma le_deg_pm_antisym:
  assumes "s \<unlhd> t" and "deg_pm t \<le> deg_pm (s::'a \<Rightarrow>\<^sub>0 'b::add_linorder)"
  shows "s = t"
proof (rule ccontr)
  assume "s \<noteq> t"
  have fin: "finite (keys s \<union> keys t)" by simp
  with _ have "deg_pm s = (\<Sum>x\<in>keys s \<union> keys t. lookup s x)" by (rule deg_pm_superset) simp
  also from fin have "\<dots> < (\<Sum>x\<in>keys s \<union> keys t. lookup t x)"
  proof (rule sum_strict_mono_ex1)
    from assms(1) show "\<forall>x\<in>keys s \<union> keys t. lookup s x \<le> lookup t x"
      by (auto dest: le_pmD)
  next
    from \<open>s \<noteq> t\<close> obtain x where neq: "lookup s x \<noteq> lookup t x" by (auto simp: poly_mapping_eq_iff)
    moreover from assms(1) have "lookup s x \<le> lookup t x" by (rule le_pmD)
    ultimately have "lookup s x < lookup t x" by simp
    moreover from neq have "x \<in> keys s \<union> keys t" by auto
    ultimately show "\<exists>x\<in>keys s \<union> keys t. lookup s x < lookup t x" ..
  qed
  also from _ fin have "\<dots> = deg_pm t" by (rule deg_pm_superset[symmetric]) simp
  finally have "deg_pm s < deg_pm t" .
  with assms(2) show False by simp
qed

subsection \<open>Degree\<close>

lemma plus_minus_assoc_pm_nat_1: "s + t - u = (s - (u - t)) + (t - (u::_ \<Rightarrow>\<^sub>0 nat))"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_minus)

lemma plus_minus_assoc_pm_nat_2:
  "s + (t - u) = (s + (except (u - t) (- keys s))) + t - (u::_ \<Rightarrow>\<^sub>0 nat)"
proof (rule poly_mapping_eqI)
  fix x
  show "lookup (s + (t - u)) x = lookup (s + except (u - t) (- keys s) + t - u) x"
  proof (cases "x \<in> keys s")
    case True
    thus ?thesis
      by (simp add: plus_minus_assoc_pm_nat_1 lookup_add lookup_minus lookup_except)
  next
    case False
    hence "lookup s x = 0" by simp
    with False show ?thesis
      by (simp add: lookup_add lookup_minus lookup_except del: not_in_keys_iff_lookup_eq_zero)
  qed
qed

lemma deg_pm_sum: "deg_pm (sum t A) = (\<Sum>a\<in>A. deg_pm (t a))"
  by (induct A rule: infinite_finite_induct) (auto simp: deg_pm_plus)

lemma deg_pm_mono: "s adds t \<Longrightarrow> deg_pm s \<le> deg_pm (t::_ \<Rightarrow>\<^sub>0 _::add_linorder_min)"
  by (simp add: adds_pm deg_pm_mono_le)

lemma adds_deg_pm_antisym: "s adds t \<Longrightarrow> deg_pm t \<le> deg_pm (s::_ \<Rightarrow>\<^sub>0 _::add_linorder_min) \<Longrightarrow> s = t"
  by (simp add: adds_pm le_deg_pm_antisym)

lemma deg_pm_minus:
  assumes "s adds (t::_ \<Rightarrow>\<^sub>0 _::comm_monoid_add)"
  shows "deg_pm (t - s) = deg_pm t - deg_pm s"
proof -
  from assms have "(t - s) + s = t" by (rule adds_minus)
  hence "deg_pm t = deg_pm ((t - s) + s)" by simp
  also have "\<dots> = deg_pm (t - s) + deg_pm s" by (simp only: deg_pm_plus)
  finally show ?thesis by simp
qed

lemma adds_group [simp]: "s adds (t::'a \<Rightarrow>\<^sub>0 'b::ab_group_add)"
proof (rule addsI)
  show "t = s + (t - s)" by simp
qed

lemmas deg_pm_minus_group = deg_pm_minus[OF adds_group]

lemma deg_pm_minus_le: "deg_pm (t - s) \<le> deg_pm (t::_ \<Rightarrow>\<^sub>0 nat)"
proof -
  have "keys (t - s) \<subseteq> keys t" by (rule, simp add: lookup_minus in_keys_iff)
  hence "deg_pm (t - s) = (\<Sum>x\<in>keys t. lookup (t - s) x)" using finite_keys by (rule deg_pm_superset)
  also have "\<dots> \<le> (\<Sum>x\<in>keys t. lookup t x)" by (rule sum_mono) (simp add: lookup_minus)
  also have "\<dots> = deg_pm t" by (rule sym, rule deg_pm_superset, fact subset_refl, fact finite_keys)
  finally show ?thesis .
qed

lemma minus_id_iff: "t - s = t \<longleftrightarrow> keys t \<inter> keys (s::_ \<Rightarrow>\<^sub>0 nat) = {}"
proof
  assume "t - s = t"
  {
    fix x
    assume "x \<in> keys t" and "x \<in> keys s"
    hence "0 < lookup t x" and "0 < lookup s x" by (simp_all add: in_keys_iff)
    hence "lookup (t - s) x \<noteq> lookup t x" by (simp add: lookup_minus)
    with \<open>t - s = t\<close> have False by simp
  }
  thus "keys t \<inter> keys s = {}" by blast
next
  assume *: "keys t \<inter> keys s = {}"
  show "t - s = t"
  proof (rule poly_mapping_eqI)
    fix x
    have "lookup t x - lookup s x = lookup t x"
    proof (cases "x \<in> keys t")
      case True
      with * have "x \<notin> keys s" by blast
      thus ?thesis by simp
    next
      case False
      thus ?thesis by simp
    qed
    thus "lookup (t - s) x = lookup t x" by (simp only: lookup_minus)
  qed
qed

lemma deg_pm_minus_id_iff: "deg_pm (t - s) = deg_pm t \<longleftrightarrow> keys t \<inter> keys (s::_ \<Rightarrow>\<^sub>0 nat) = {}"
proof
  assume eq: "deg_pm (t - s) = deg_pm t"
  {
    fix x
    assume "x \<in> keys t" and "x \<in> keys s"
    hence "0 < lookup t x" and "0 < lookup s x" by (simp_all add: in_keys_iff)
    hence *: "lookup (t - s) x < lookup t x" by (simp add: lookup_minus)
    have "keys (t - s) \<subseteq> keys t" by (rule, simp add: lookup_minus in_keys_iff)
    hence "deg_pm (t - s) = (\<Sum>x\<in>keys t. lookup (t - s) x)" using finite_keys by (rule deg_pm_superset)
    also from finite_keys have "\<dots> < (\<Sum>x\<in>keys t. lookup t x)"
    proof (rule sum_strict_mono_ex1)
      show "\<forall>x\<in>keys t. lookup (t - s) x \<le> lookup t x" by (simp add: lookup_minus)
    next
      from \<open>x \<in> keys t\<close> * show "\<exists>x\<in>keys t. lookup (t - s) x < lookup t x" ..
    qed
    also have "\<dots> = deg_pm t" by (rule sym, rule deg_pm_superset, fact subset_refl, fact finite_keys)
    finally have False by (simp add: eq)
  }
  thus "keys t \<inter> keys s = {}" by blast
next
  assume "keys t \<inter> keys s = {}"
  hence "t - s = t" by (simp only: minus_id_iff)
  thus "deg_pm (t - s) = deg_pm t" by (simp only:)
qed

definition poly_deg :: "(('x \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a" where
  "poly_deg p = (if keys p = {} then 0 else Max (deg_pm ` keys p))"

definition maxdeg :: "(('x \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> 'a" where
  "maxdeg A = Max (poly_deg ` A)"
  
definition mindeg :: "(('x \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> 'a" where
  "mindeg A = Min (poly_deg ` A)"

lemma poly_deg_monomial: "poly_deg (monomial c t) = (if c = 0 then 0 else deg_pm t)"
  by (simp add: poly_deg_def)

lemma poly_deg_monomial_zero [simp]: "poly_deg (monomial c 0) = 0"
  by (simp add: poly_deg_monomial)

lemma poly_deg_zero [simp]: "poly_deg 0 = 0"
  by (simp only: single_zero[of 0, symmetric] poly_deg_monomial_zero)

lemma poly_deg_one [simp]: "poly_deg 1 = 0"
  by (simp only: single_one[symmetric] poly_deg_monomial_zero)

lemma poly_degE:
  assumes "p \<noteq> 0"
  obtains t where "t \<in> keys p" and "poly_deg p = deg_pm t"
proof -
  from assms have "poly_deg p = Max (deg_pm ` keys p)" by (simp add: poly_deg_def)
  also have "\<dots> \<in> deg_pm ` keys p"
  proof (rule Max_in)
    from assms show "deg_pm ` keys p \<noteq> {}" by simp
  qed simp
  finally obtain t where "t \<in> keys p" and "poly_deg p = deg_pm t" ..
  thus ?thesis ..
qed

lemma poly_deg_max_keys: "t \<in> keys p \<Longrightarrow> deg_pm t \<le> poly_deg p"
  using finite_keys by (auto simp: poly_deg_def)

lemma poly_deg_leI: "(\<And>t. t \<in> keys p \<Longrightarrow> deg_pm t \<le> (d::'a::add_linorder_min)) \<Longrightarrow> poly_deg p \<le> d"
  using finite_keys by (auto simp: poly_deg_def)

lemma poly_deg_lessI:
  "p \<noteq> 0 \<Longrightarrow> (\<And>t. t \<in> keys p \<Longrightarrow> deg_pm t < (d::'a::add_linorder_min)) \<Longrightarrow> poly_deg p < d"
  using finite_keys by (auto simp: poly_deg_def)

lemma poly_deg_zero_imp_monomial:
  assumes "poly_deg p = (0::'a::add_linorder_min)"
  shows "monomial (lookup p 0) 0 = p"
proof (rule keys_subset_singleton_imp_monomial, rule)
  fix t
  assume "t \<in> keys p"
  have "t = 0"
  proof (rule ccontr)
    assume "t \<noteq> 0"
    hence "deg_pm t \<noteq> 0" by simp
    hence "0 < deg_pm t" using not_gr_zero by blast
    also from \<open>t \<in> keys p\<close> have "... \<le> poly_deg p" by (rule poly_deg_max_keys)
    finally have "poly_deg p \<noteq> 0" by simp
    from this assms show False ..
  qed
  thus "t \<in> {0}" by simp
qed

lemma poly_deg_plus_le:
  "poly_deg (p + q) \<le> max (poly_deg p) (poly_deg (q::(_ \<Rightarrow>\<^sub>0 'a::add_linorder_min) \<Rightarrow>\<^sub>0 _))"
proof (rule poly_deg_leI)
  fix t
  assume "t \<in> keys (p + q)"
  also have "... \<subseteq> keys p \<union> keys q" by (fact keys_add_subset)
  finally show "deg_pm t \<le> max (poly_deg p) (poly_deg q)"
  proof
    assume "t \<in> keys p"
    hence "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
    thus ?thesis by (simp add: le_max_iff_disj)
  next
    assume "t \<in> keys q"
    hence "deg_pm t \<le> poly_deg q" by (rule poly_deg_max_keys)
    thus ?thesis by (simp add: le_max_iff_disj)
  qed
qed

lemma poly_deg_uminus [simp]: "poly_deg (-p) = poly_deg p"
  by (simp add: poly_deg_def keys_uminus)

lemma poly_deg_minus_le:
  "poly_deg (p - q) \<le> max (poly_deg p) (poly_deg (q::(_ \<Rightarrow>\<^sub>0 'a::add_linorder_min) \<Rightarrow>\<^sub>0 _))"
proof (rule poly_deg_leI)
  fix t
  assume "t \<in> keys (p - q)"
  also have "... \<subseteq> keys p \<union> keys q" by (fact keys_minus)
  finally show "deg_pm t \<le> max (poly_deg p) (poly_deg q)"
  proof
    assume "t \<in> keys p"
    hence "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
    thus ?thesis by (simp add: le_max_iff_disj)
  next
    assume "t \<in> keys q"
    hence "deg_pm t \<le> poly_deg q" by (rule poly_deg_max_keys)
    thus ?thesis by (simp add: le_max_iff_disj)
  qed
qed

lemma poly_deg_times_le:
  "poly_deg (p * q) \<le> poly_deg p + poly_deg (q::(_ \<Rightarrow>\<^sub>0 'a::add_linorder_min) \<Rightarrow>\<^sub>0 _)"
proof (rule poly_deg_leI)
  fix t
  assume "t \<in> keys (p * q)"
  then obtain u v where "u \<in> keys p" and "v \<in> keys q" and "t = u + v" by (rule in_keys_timesE)
  from \<open>u \<in> keys p\<close> have "deg_pm u \<le> poly_deg p" by (rule poly_deg_max_keys)
  moreover from \<open>v \<in> keys q\<close> have "deg_pm v \<le> poly_deg q" by (rule poly_deg_max_keys)
  ultimately show "deg_pm t \<le> poly_deg p + poly_deg q" by (simp add: \<open>t = u + v\<close> deg_pm_plus add_mono)
qed

lemma poly_deg_times:
  assumes "p \<noteq> 0" and "q \<noteq> (0::('x::linorder \<Rightarrow>\<^sub>0 'a::add_linorder_min) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "poly_deg (p * q) = poly_deg p + poly_deg q"
  using poly_deg_times_le
proof (rule antisym)
  let ?A = "\<lambda>f. {u. deg_pm u < poly_deg f}"
  define p1 where "p1 = except p (?A p)"
  define p2 where "p2 = except p (- ?A p)"
  define q1 where "q1 = except q (?A q)"
  define q2 where "q2 = except q (- ?A q)"
  have deg_p1: "deg_pm t = poly_deg p" if "t \<in> keys p1" for t
  proof -
    from that have "t \<in> keys p" and "poly_deg p \<le> deg_pm t"
      by (simp_all add: p1_def keys_except not_less)
    from this(1) have "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
    thus ?thesis using \<open>poly_deg p \<le> deg_pm t\<close> by (rule antisym)
  qed
  have deg_p2: "t \<in> keys p2 \<Longrightarrow> deg_pm t < poly_deg p" for t by (simp add: p2_def keys_except)
  have deg_q1: "deg_pm t = poly_deg q" if "t \<in> keys q1" for t
  proof -
    from that have "t \<in> keys q" and "poly_deg q \<le> deg_pm t"
      by (simp_all add: q1_def keys_except not_less)
    from this(1) have "deg_pm t \<le> poly_deg q" by (rule poly_deg_max_keys)
    thus ?thesis using \<open>poly_deg q \<le> deg_pm t\<close> by (rule antisym)
  qed
  have deg_q2: "t \<in> keys q2 \<Longrightarrow> deg_pm t < poly_deg q" for t by (simp add: q2_def keys_except)
  have p: "p = p1 + p2" unfolding p1_def p2_def by (fact except_decomp)
  have "p1 \<noteq> 0"
  proof -
    from assms(1) obtain t where "t \<in> keys p" and "poly_deg p = deg_pm t" by (rule poly_degE)
    hence "t \<in> keys p1" by (simp add: p1_def keys_except)
    thus ?thesis by auto
  qed
  have q: "q = q1 + q2" unfolding q1_def q2_def by (fact except_decomp)
  have "q1 \<noteq> 0"
  proof -
    from assms(2) obtain t where "t \<in> keys q" and "poly_deg q = deg_pm t" by (rule poly_degE)
    hence "t \<in> keys q1" by (simp add: q1_def keys_except)
    thus ?thesis by auto
  qed
  with \<open>p1 \<noteq> 0\<close> have "p1 * q1 \<noteq> 0" by simp
  hence "keys (p1 * q1) \<noteq> {}" by simp
  then obtain u where "u \<in> keys (p1 * q1)" by blast
  then obtain s t where "s \<in> keys p1" and "t \<in> keys q1" and u: "u = s + t" by (rule in_keys_timesE)
  from \<open>s \<in> keys p1\<close> have "deg_pm s = poly_deg p" by (rule deg_p1)
  moreover from \<open>t \<in> keys q1\<close> have "deg_pm t = poly_deg q" by (rule deg_q1)
  ultimately have eq: "poly_deg p + poly_deg q = deg_pm u" by (simp only: u deg_pm_plus)
  also have "\<dots> \<le> poly_deg (p * q)"
  proof (rule poly_deg_max_keys)
    have "u \<notin> keys (p1 * q2 + p2 * q)"
    proof
      assume "u \<in> keys (p1 * q2 + p2 * q)"
      also have "\<dots> \<subseteq> keys (p1 * q2) \<union> keys (p2 * q)" by (rule keys_add_subset)
      finally have "deg_pm u < poly_deg p + poly_deg q"
      proof
        assume "u \<in> keys (p1 * q2)"
        then obtain s' t' where "s' \<in> keys p1" and "t' \<in> keys q2" and u: "u = s' + t'"
          by (rule in_keys_timesE)
        from \<open>s' \<in> keys p1\<close> have "deg_pm s' = poly_deg p" by (rule deg_p1)
        moreover from \<open>t' \<in> keys q2\<close> have "deg_pm t' < poly_deg q" by (rule deg_q2)
        ultimately show ?thesis by (simp add: u deg_pm_plus)
      next
        assume "u \<in> keys (p2 * q)"
        then obtain s' t' where "s' \<in> keys p2" and "t' \<in> keys q" and u: "u = s' + t'"
          by (rule in_keys_timesE)
        from \<open>s' \<in> keys p2\<close> have "deg_pm s' < poly_deg p" by (rule deg_p2)
        moreover from \<open>t' \<in> keys q\<close> have "deg_pm t' \<le> poly_deg q" by (rule poly_deg_max_keys)
        ultimately show ?thesis by (simp add: u deg_pm_plus add_less_le_mono)
      qed
      thus False by (simp only: eq)
    qed
    with \<open>u \<in> keys (p1 * q1)\<close> have "u \<in> keys (p1 * q1 + (p1 * q2 + p2 * q))" by (rule in_keys_plusI1)
    thus "u \<in> keys (p * q)" by (simp only: p q algebra_simps)
  qed
  finally show "poly_deg p + poly_deg q \<le> poly_deg (p * q)" .
qed

corollary poly_deg_monom_mult_le:
  "poly_deg (punit.monom_mult c (t::_ \<Rightarrow>\<^sub>0 'a::add_linorder_min) p) \<le> deg_pm t + poly_deg p"
proof -
  have "poly_deg (punit.monom_mult c t p) \<le> poly_deg (monomial c t) + poly_deg p"
    by (simp only: times_monomial_left[symmetric] poly_deg_times_le)
  also have "... \<le> deg_pm t + poly_deg p" by (simp add: poly_deg_monomial)
  finally show ?thesis .
qed

lemma poly_deg_monom_mult:
  assumes "c \<noteq> 0" and "p \<noteq> (0::(_ \<Rightarrow>\<^sub>0 'a::add_linorder_min) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "poly_deg (punit.monom_mult c t p) = deg_pm t + poly_deg p"
proof (rule order.antisym, fact poly_deg_monom_mult_le)
  from assms(2) obtain s where "s \<in> keys p" and "poly_deg p = deg_pm s" by (rule poly_degE)
  have "deg_pm t + poly_deg p = deg_pm (t + s)" by (simp add: \<open>poly_deg p = deg_pm s\<close> deg_pm_plus)
  also have "... \<le> poly_deg (punit.monom_mult c t p)"
  proof (rule poly_deg_max_keys)
    from \<open>s \<in> keys p\<close> show "t + s \<in> keys (punit.monom_mult c t p)"
      unfolding punit.keys_monom_mult[OF assms(1)] by fastforce
  qed
  finally show "deg_pm t + poly_deg p \<le> poly_deg (punit.monom_mult c t p)" .
qed

lemma poly_deg_map_scale:
  "poly_deg (c \<cdot> p) = (if c = (0::_::semiring_no_zero_divisors) then 0 else poly_deg p)"
  by (simp add: poly_deg_def keys_map_scale)

lemma poly_deg_sum_le: "((poly_deg (sum f A))::'a::add_linorder_min) \<le> Max (poly_deg ` f ` A)"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    show ?case by simp
  next
    case (insert a A)
    show ?case
    proof (cases "A = {}")
      case True
      thus ?thesis by simp
    next
      case False
      have "poly_deg (sum f (insert a A)) \<le> max (poly_deg (f a)) (poly_deg (sum f A))"
        by (simp only: comm_monoid_add_class.sum.insert[OF insert(1) insert(2)] poly_deg_plus_le)
      also have "... \<le> max (poly_deg (f a)) (Max (poly_deg ` f ` A))"
        using insert(3) max.mono by blast
      also have "... = (Max (poly_deg ` f ` (insert a A)))" using False by (simp add: insert(1))
      finally show ?thesis .
    qed
  qed
next
  case False
  thus ?thesis by simp
qed

lemma poly_deg_prod_le: "((poly_deg (prod f A))::'a::add_linorder_min) \<le> (\<Sum>a\<in>A. poly_deg (f a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    show ?case by simp
  next
    case (insert a A)
    have "poly_deg (prod f (insert a A)) \<le> (poly_deg (f a)) + (poly_deg (prod f A))"
      by (simp only: comm_monoid_mult_class.prod.insert[OF insert(1) insert(2)] poly_deg_times_le)
    also have "... \<le> (poly_deg (f a)) + (\<Sum>a\<in>A. poly_deg (f a))"
      using insert(3) add_le_cancel_left by blast
    also have "... = (\<Sum>a\<in>insert a A. poly_deg (f a))" by (simp add: insert(1) insert(2))
    finally show ?case .
  qed
next
  case False
  thus ?thesis by simp
qed

lemma maxdeg_max:
  assumes "finite A" and "p \<in> A"
  shows "poly_deg p \<le> maxdeg A"
  unfolding maxdeg_def using assms by auto

lemma mindeg_min:
  assumes "finite A" and "p \<in> A"
  shows "mindeg A \<le> poly_deg p"
  unfolding mindeg_def using assms by auto

subsection \<open>Scalar Multiplication of Polynomial Mappings\<close>

lemma map_scale_eq_0_iff: "c \<cdot> t = 0 \<longleftrightarrow> ((c::_::semiring_no_zero_divisors) = 0 \<or> t = 0)"
  by (metis aux lookup_map_scale mult_eq_0_iff)

lemma monomial_power_map_scale: "(monomial c t) ^ n = monomial (c ^ n) (n \<cdot> t)"
proof -
  have "(\<Sum>i = 0..<n. t) = (\<Sum>i = 0..<n. 1) \<cdot> t"
    by (simp only: map_scale_sum_distrib_right map_scale_one_left)
  thus ?thesis by (simp add: punit.monomial_power)
qed

lemma times_le_interval:
  assumes "x \<le> y + a * z" and "x \<le> y + b * z" and "a \<le> c" and "c \<le> (b::'b::{linorder,ordered_ring})"
  shows "x \<le> y + c * z"
proof (cases "0 \<le> z")
  case True
  from assms(3) True have "y + a * z \<le> y + c * z" by (simp add: add_left_mono mult_right_mono)
  with assms(1) show ?thesis by (rule order_trans)
next
  case False
  hence "z \<le> 0" by simp
  with assms(4) have "y + b * z \<le> y + c * z" by (simp add: add_left_mono mult_right_mono_neg)
  with assms(2) show ?thesis by (rule order_trans)
qed

corollary times_le_interval':
  "x \<le> a * z \<Longrightarrow> x \<le> b * z \<Longrightarrow> a \<le> c \<Longrightarrow> c \<le> (b::'b::{linorder,ordered_ring}) \<Longrightarrow> x \<le> c * z"
  using times_le_interval[of x 0 a z b c] by simp

lemma map_scale_le_interval:
  assumes "x \<unlhd> y + a \<cdot> z" and "x \<unlhd> y + b \<cdot> z" and "a \<le> c" and "c \<le> (b::'b::{linorder,ordered_ring})"
  shows "x \<unlhd> y + c \<cdot> z"
proof (rule le_pmI)
  fix k
  from assms(1) have "lookup x k \<le> lookup (y + a \<cdot> z) k" by (rule le_pmD)
  hence *: "lookup x k \<le> lookup y k + a * lookup z k" by (simp add: lookup_add)
  from assms(2) have "lookup x k \<le> lookup (y + b \<cdot> z) k" by (rule le_pmD)
  hence "lookup x k \<le> lookup y k + b * lookup z k" by (simp add: lookup_add)
  with * have "lookup x k \<le> lookup y k + c * lookup z k" using assms(3, 4) by (rule times_le_interval)
  thus "lookup x k \<le> lookup (y + c \<cdot> z) k" by (simp add: lookup_add)
qed

corollary map_scale_le_interval':
  "x \<unlhd> a \<cdot> z \<Longrightarrow> x \<unlhd> b \<cdot> z \<Longrightarrow> a \<le> c \<Longrightarrow> c \<le> (b::'b::{linorder,ordered_ring}) \<Longrightarrow> x \<unlhd> c \<cdot> z"
  using map_scale_le_interval[of x 0 a z b c] by simp

subsection \<open>Indeterminates\<close>

definition indets :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'x set"
  where "indets p = UNION (keys p) keys"

definition PPs :: "'x set \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) set"  (".[(_)]")
  where "PPs X = {t. keys t \<subseteq> X}"

definition Polys :: "'x set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) set"  ("P[(_)]")
  where "Polys X = {p. keys p \<subseteq> .[X]}"

subsubsection \<open>@{const indets}\<close>

lemma in_indetsI:
  assumes "x \<in> keys t" and "t \<in> keys p"
  shows "x \<in> indets p"
  using assms by (auto simp add: indets_def)

lemma in_indetsE:
  assumes "x \<in> indets p"
  obtains t where "t \<in> keys p" and "x \<in> keys t"
  using assms by (auto simp add: indets_def)

lemma keys_subset_indets: "t \<in> keys p \<Longrightarrow> keys t \<subseteq> indets p"
  by (auto dest: in_indetsI)

lemma indets_empty_imp_monomial:
  assumes "indets p = {}"
  shows "monomial (lookup p 0) 0 = p"
proof (rule keys_subset_singleton_imp_monomial, rule)
  fix t
  assume "t \<in> keys p"
  have "t = 0"
  proof (rule ccontr)
    assume "t \<noteq> 0"
    hence "keys t \<noteq> {}" by simp
    then obtain x where "x \<in> keys t" by blast
    from this \<open>t \<in> keys p\<close> have "x \<in> indets p" by (rule in_indetsI)
    with assms show False by simp
  qed
  thus "t \<in> {0}" by simp
qed

lemma finite_indets: "finite (indets p)"
  by (simp only: indets_def, rule finite_UN_I, (rule finite_keys)+)

lemma indets_zero [simp]: "indets 0 = {}"
  by (simp add: indets_def)

lemma indets_one [simp]: "indets 1 = {}"
  by (simp add: indets_def)

lemma indets_monomial_single_subset: "indets (monomial c (Poly_Mapping.single v k)) \<subseteq> {v}"
proof
  fix x assume "x \<in> indets (monomial c (Poly_Mapping.single v k))"
  then have "x = v" unfolding indets_def
    by (metis UN_E lookup_eq_zero_in_keys_contradict lookup_single_not_eq)
  thus "x \<in> {v}" by simp
qed

lemma indets_monomial_single:
  assumes "c \<noteq> 0" and "k \<noteq> 0"
  shows "indets (monomial c (Poly_Mapping.single v k)) = {v}"
proof (rule, fact indets_monomial_single_subset, simp)
  from assms show "v \<in> indets (monomial c (monomial k v))" by (simp add: indets_def)
qed

lemma indets_monomial:
  assumes "c \<noteq> 0"
  shows "indets (monomial c t) = keys t"
proof (rule antisym; rule subsetI)
  fix x
  assume "x \<in> indets (monomial c t)"
  then have "lookup t x \<noteq> 0" unfolding indets_def
    by (metis UN_E lookup_eq_zero_in_keys_contradict lookup_single_not_eq)
  thus "x \<in> keys t" by (meson lookup_not_eq_zero_eq_in_keys)
next
  fix x
  assume "x \<in> keys t"
  then have "lookup t x \<noteq> 0" by (meson lookup_not_eq_zero_eq_in_keys)
  thus "x \<in> indets (monomial c t)" unfolding indets_def using assms
    by (metis UN_iff lookup_not_eq_zero_eq_in_keys lookup_single_eq)
qed

lemma indets_monomial_subset: "indets (monomial c t) \<subseteq> keys t"
  by (cases "c = 0", simp_all add: indets_def)

lemma indets_monomial_zero [simp]: "indets (monomial c 0) = {}"
  by (simp add: indets_def)

lemma indets_plus_subset: "indets (p + q) \<subseteq> indets p \<union> indets q"
proof
  fix x
  assume "x \<in> indets (p + q)"
  then obtain t where "x \<in> keys t" and "t \<in> keys (p + q)" by (metis UN_E indets_def)
  hence "t \<in> keys p \<union> keys q" by (metis keys_add_subset subsetCE)
  thus "x \<in> indets p \<union> indets q" using indets_def \<open>x \<in> keys t\<close> by fastforce
qed

lemma indets_uminus [simp]: "indets (-p) = indets p"
  by (simp add: indets_def keys_uminus)

lemma indets_minus_subset: "indets (p - q) \<subseteq> indets p \<union> indets q"
proof
  fix x
  assume "x \<in> indets (p - q)"
  then obtain t where "x \<in> keys t" and "t \<in> keys (p - q)" by (metis UN_E indets_def)
  hence "t \<in> keys p \<union> keys q" by (metis keys_minus subsetCE)
  thus "x \<in> indets p \<union> indets q" using indets_def \<open>x \<in> keys t\<close> by fastforce
qed

lemma indets_times_subset: "indets (p * q) \<subseteq> indets p \<union> indets (q::(_ \<Rightarrow>\<^sub>0 _::cancel_comm_monoid_add) \<Rightarrow>\<^sub>0 _)"
proof
  fix x
  assume "x \<in> indets (p * q)"
  then obtain t where "t \<in> keys (p * q)" and "x \<in> keys t" unfolding indets_def by blast
  from this(1) obtain u v where "u \<in> keys p" "v \<in> keys q" and "t = u + v" by (rule in_keys_timesE)
  hence "x \<in> keys u \<union> keys v" by (metis \<open>x \<in> keys t\<close> keys_add_subset subsetCE)
  thus "x \<in> indets p \<union> indets q" unfolding indets_def using \<open>u \<in> keys p\<close> \<open>v \<in> keys q\<close> by blast
qed

corollary indets_monom_mult_subset: "indets (punit.monom_mult c t p) \<subseteq> keys t \<union> indets p"
proof -
  have "indets (punit.monom_mult c t p) \<subseteq> indets (monomial c t) \<union> indets p"
    by (simp only: times_monomial_left[symmetric] indets_times_subset)
  also have "... \<subseteq> keys t \<union> indets p" using indets_monomial_subset[of t c] by blast
  finally show ?thesis .
qed

lemma indets_monom_mult:
  assumes "c \<noteq> 0" and "p \<noteq> (0::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "indets (punit.monom_mult c t p) = keys t \<union> indets p"
proof (rule, fact indets_monom_mult_subset, rule)
  fix x
  assume "x \<in> keys t \<union> indets p"
  thus "x \<in> indets (punit.monom_mult c t p)"
  proof
    assume "x \<in> keys t"
    from assms(2) have "keys p \<noteq> {}" by simp
    then obtain s where "s \<in> keys p" by blast
    hence "t + s \<in> (+) t ` keys p" by fastforce
    also from assms(1) have "... = keys (punit.monom_mult c t p)" by (simp add: punit.keys_monom_mult)
    finally have "t + s \<in> keys (punit.monom_mult c t p)" .
    show ?thesis
    proof (rule in_indetsI)
      from \<open>x \<in> keys t\<close> show "x \<in> keys (t + s)" by (simp add: keys_plus_ninv_comm_monoid_add)
    qed fact
  next
    assume "x \<in> indets p"
    then obtain s where "s \<in> keys p" and "x \<in> keys s" by (rule in_indetsE)
    from this(1) have "t + s \<in> (+) t ` keys p" by fastforce
    also from assms(1) have "... = keys (punit.monom_mult c t p)" by (simp add: punit.keys_monom_mult)
    finally have "t + s \<in> keys (punit.monom_mult c t p)" .
    show ?thesis
    proof (rule in_indetsI)
      from \<open>x \<in> keys s\<close> show "x \<in> keys (t + s)" by (simp add: keys_plus_ninv_comm_monoid_add)
    qed fact
  qed
qed

lemma indets_sum_subset: "indets (sum f A) \<subseteq> (\<Union>a\<in>A. indets (f a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    show ?case by simp
  next
    case (insert a A)
    have "indets (sum f (insert a A)) \<subseteq> indets (f a) \<union> indets (sum f A)"
      by (simp only: comm_monoid_add_class.sum.insert[OF insert(1) insert(2)] indets_plus_subset)
    also have "... \<subseteq> indets (f a) \<union> (\<Union>a\<in>A. indets (f a))" using insert(3) by blast
    also have "... = (\<Union>a\<in>insert a A. indets (f a))" by simp
    finally show ?case .
  qed
next
  case False
  thus ?thesis by simp
qed

lemma indets_prod_subset:
  "indets (prod (f::_ \<Rightarrow> ((_ \<Rightarrow>\<^sub>0 _::cancel_comm_monoid_add) \<Rightarrow>\<^sub>0 _)) A) \<subseteq> (\<Union>a\<in>A. indets (f a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    show ?case by simp
  next
    case (insert a A)
    have "indets (prod f (insert a A)) \<subseteq> indets (f a) \<union> indets (prod f A)"
      by (simp only: comm_monoid_mult_class.prod.insert[OF insert(1) insert(2)] indets_times_subset)
    also have "... \<subseteq> indets (f a) \<union> (\<Union>a\<in>A. indets (f a))" using insert(3) by blast
    also have "... = (\<Union>a\<in>insert a A. indets (f a))" by simp
    finally show ?case .
  qed
next
  case False
  thus ?thesis by simp
qed

lemma indets_power_subset: "indets (p ^ n) \<subseteq> indets (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)"
proof -
  have "p ^ n = (\<Prod>i=0..<n. p)" by simp
  also have "indets ... \<subseteq> (\<Union>i\<in>{0..<n}. indets p)" by (fact indets_prod_subset)
  also have "... \<subseteq> indets p" by simp
  finally show ?thesis .
qed

lemma indets_empty_iff_poly_deg_zero: "indets p = {} \<longleftrightarrow> poly_deg p = 0"
proof
  assume "indets p = {}"
  hence "monomial (lookup p 0) 0 = p" by (rule indets_empty_imp_monomial)
  moreover have "poly_deg (monomial (lookup p 0) 0) = 0" by simp
  ultimately show "poly_deg p = 0" by metis
next
  assume "poly_deg p = 0"
  hence "monomial (lookup p 0) 0 = p" by (rule poly_deg_zero_imp_monomial)
  moreover have "indets (monomial (lookup p 0) 0) = {}" by simp
  ultimately show "indets p = {}" by metis
qed

subsubsection \<open>@{const PPs}\<close>

lemma PPsI: "keys t \<subseteq> X \<Longrightarrow> t \<in> .[X]"
  by (simp add: PPs_def)

lemma PPsD: "t \<in> .[X] \<Longrightarrow> keys t \<subseteq> X"
  by (simp add: PPs_def)

lemma PPs_empty [simp]: ".[{}] = {0}"
  by (simp add: PPs_def)

lemma PPs_UNIV [simp]: ".[UNIV] = UNIV"
  by (simp add: PPs_def)

lemma PPs_singleton: ".[{x}] = range (Poly_Mapping.single x)"
proof (rule set_eqI)
  fix t
  show "t \<in> .[{x}] \<longleftrightarrow> t \<in> range (Poly_Mapping.single x)"
  proof
    assume "t \<in> .[{x}]"
    hence "keys t \<subseteq> {x}" by (rule PPsD)
    hence "Poly_Mapping.single x (lookup t x) = t" by (rule keys_subset_singleton_imp_monomial)
    from this[symmetric] UNIV_I show "t \<in> range (Poly_Mapping.single x)" ..
  next
    assume "t \<in> range (Poly_Mapping.single x)"
    then obtain e where "t = Poly_Mapping.single x e" ..
    thus "t \<in> .[{x}]" by (simp add: PPs_def)
  qed
qed

lemma zero_in_PPs: "0 \<in> .[X]"
  by (simp add: PPs_def)

lemma PPs_mono: "X \<subseteq> Y \<Longrightarrow> .[X] \<subseteq> .[Y]"
  by (auto simp: PPs_def)

lemma PPs_closed_single:
  assumes "x \<in> X"
  shows "Poly_Mapping.single x e \<in> .[X]"
proof (rule PPsI)
  have "keys (Poly_Mapping.single x e) \<subseteq> {x}" by simp
  also from assms have "... \<subseteq> X" by simp
  finally show "keys (Poly_Mapping.single x e) \<subseteq> X" .
qed

lemma PPs_closed_plus:
  assumes "s \<in> .[X]" and "t \<in> .[X]"
  shows "s + t \<in> .[X]"
proof -
  have "keys (s + t) \<subseteq> keys s \<union> keys t" by (fact keys_add_subset)
  also from assms have "... \<subseteq> X" by (simp add: PPs_def)
  finally show ?thesis by (rule PPsI)
qed

lemma PPs_closed_minus:
  assumes "s \<in> .[X]"
  shows "s - t \<in> .[X]"
proof -
  have "keys (s - t) \<subseteq> keys s" by (metis lookup_minus lookup_not_eq_zero_eq_in_keys subsetI zero_diff)
  also from assms have "... \<subseteq> X" by (rule PPsD)
  finally show ?thesis by (rule PPsI)
qed

lemma PPs_closed_adds:
  assumes "s \<in> .[X]" and "t adds s"
  shows "t \<in> .[X]"
proof -
  from assms(2) have "s - (s - t) = t" by (metis add_minus_2 adds_minus)
  moreover from assms(1) have "s - (s - t) \<in> .[X]" by (rule PPs_closed_minus)
  ultimately show ?thesis by simp
qed

lemma PPs_closed_gcs:
  assumes "s \<in> .[X]"
  shows "gcs s t \<in> .[X]"
  using assms gcs_adds by (rule PPs_closed_adds)

lemma PPs_closed_lcs:
  assumes "s \<in> .[X]" and "t \<in> .[X]"
  shows "lcs s t \<in> .[X]"
proof -
  from assms have "s + t \<in> .[X]" by (rule PPs_closed_plus)
  hence "(s + t) - gcs s t \<in> .[X]" by (rule PPs_closed_minus)
  thus ?thesis by (simp add: gcs_plus_lcs[of s t, symmetric])
qed

lemma PPs_closed_except': "t \<in> .[X] \<Longrightarrow> except t Y \<in> .[X - Y]"
  by (auto simp: keys_except PPs_def)

lemma PPs_closed_except: "t \<in> .[X] \<Longrightarrow> except t Y \<in> .[X]"
  by (auto simp: keys_except PPs_def)

lemma PPs_UnI:
  assumes "tx \<in> .[X]" and "ty \<in> .[Y]" and "t = tx + ty"
  shows "t \<in> .[X \<union> Y]"
proof -
  from assms(1) have "tx \<in> .[X \<union> Y]" by rule (simp add: PPs_mono)
  moreover from assms(2) have "ty \<in> .[X \<union> Y]" by rule (simp add: PPs_mono)
  ultimately show ?thesis unfolding assms(3) by (rule PPs_closed_plus)
qed

lemma PPs_UnE:
  assumes "t \<in> .[X \<union> Y]"
  obtains tx ty where "tx \<in> .[X]" and "ty \<in> .[Y]" and "t = tx + ty"
proof -
  from assms have "keys t \<subseteq> X \<union> Y" by (rule PPsD)
  define tx where "tx = except t (- X)"
  have "keys tx \<subseteq> X" by (simp add: tx_def keys_except)
  hence "tx \<in> .[X]" by (simp add: PPs_def)
  have "tx adds t" by (simp add: tx_def adds_poly_mappingI le_fun_def lookup_except)
  from adds_minus[OF this] have "t = tx + (t - tx)" by (simp only: ac_simps)
  have "t - tx \<in> .[Y]"
  proof (rule PPsI, rule)
    fix x
    assume "x \<in> keys (t - tx)"
    also have "... \<subseteq> keys t \<union> keys tx" by (rule keys_minus)
    also from \<open>keys t \<subseteq> X \<union> Y\<close> \<open>keys tx \<subseteq> X\<close> have "... \<subseteq> X \<union> Y" by blast
    finally show "x \<in> Y"
    proof
      assume "x \<in> X"
      hence "x \<notin> keys (t - tx)" by (simp add: tx_def lookup_except lookup_minus)
      thus ?thesis using \<open>x \<in> keys (t - tx)\<close> ..
    qed
  qed
  with \<open>tx \<in> .[X]\<close> show ?thesis using \<open>t = tx + (t - tx)\<close> ..
qed

lemma PPs_Un: ".[X \<union> Y] = (\<Union>t\<in>.[X]. (+) t ` .[Y])"  (is "?A = ?B")
proof (rule set_eqI)
  fix t
  show "t \<in> ?A \<longleftrightarrow> t \<in> ?B"
  proof
    assume "t \<in> ?A"
    then obtain tx ty where "tx \<in> .[X]" and "ty \<in> .[Y]" and "t = tx + ty" by (rule PPs_UnE)
    from this(2) have "t \<in> (+) tx ` .[Y]" unfolding \<open>t = tx + ty\<close> by (rule imageI)
    with \<open>tx \<in> .[X]\<close> show "t \<in> ?B" ..
  next
    assume "t \<in> ?B"
    then obtain tx where "tx \<in> .[X]" and "t \<in> (+) tx ` .[Y]" ..
    from this(2) obtain ty where "ty \<in> .[Y]" and "t = tx + ty" ..
    with \<open>tx \<in> .[X]\<close> show "t \<in> ?A" by (rule PPs_UnI)
  qed
qed

corollary PPs_insert: ".[insert x X] = (\<Union>e. (+) (Poly_Mapping.single x e) ` .[X])"
proof -
  have ".[insert x X] = .[{x} \<union> X]" by simp
  also have "... = (\<Union>t\<in>.[{x}]. (+) t ` .[X])" by (fact PPs_Un)
  also have "... = (\<Union>e. (+) (Poly_Mapping.single x e) ` .[X])" by (simp add: PPs_singleton)
  finally show ?thesis .
qed

corollary PPs_insertI:
  assumes "tx \<in> .[X]" and "t = Poly_Mapping.single x e + tx"
  shows "t \<in> .[insert x X]"
proof -
  from assms(1) have "t \<in> (+) (Poly_Mapping.single x e) ` .[X]" unfolding assms(2) by (rule imageI)
  with UNIV_I show ?thesis unfolding PPs_insert by (rule UN_I)
qed

corollary PPs_insertE:
  assumes "t \<in> .[insert x X]"
  obtains e tx where "tx \<in> .[X]" and "t = Poly_Mapping.single x e + tx"
proof -
  from assms obtain e where "t \<in> (+) (Poly_Mapping.single x e) ` .[X]" unfolding PPs_insert ..
  then obtain tx where "tx \<in> .[X]" and "t = Poly_Mapping.single x e + tx" ..
  thus ?thesis ..
qed

lemma PPs_Int: ".[X \<inter> Y] = .[X] \<inter> .[Y]"
  by (auto simp: PPs_def)

lemma PPs_INT: ".[\<Inter> X] = \<Inter> (PPs ` X)"
  by (auto simp: PPs_def)

subsubsection \<open>@{const Polys}\<close>

lemma Polys_alt: "P[X] = {p. indets p \<subseteq> X}"
  by (auto simp: Polys_def PPs_def indets_def)

lemma PolysI: "keys p \<subseteq> .[X] \<Longrightarrow> p \<in> P[X]"
  by (simp add: Polys_def)

lemma PolysI_alt: "indets p \<subseteq> X \<Longrightarrow> p \<in> P[X]"
  by (simp add: Polys_alt)

lemma PolysD:
  assumes "p \<in> P[X]"
  shows "keys p \<subseteq> .[X]" and "indets p \<subseteq> X"
  using assms by (simp add: Polys_def, simp add: Polys_alt)

lemma Polys_empty: "P[{}] = ((range (Poly_Mapping.single 0))::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) set)"
proof (rule set_eqI)
  fix p :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero"
  show "p \<in> P[{}] \<longleftrightarrow> p \<in> range (Poly_Mapping.single 0)"
  proof
    assume "p \<in> P[{}]"
    hence "keys p \<subseteq> .[{}]" by (rule PolysD)
    also have "... = {0}" by simp
    finally have "keys p \<subseteq> {0}" .
    hence "Poly_Mapping.single 0 (lookup p 0) = p" by (rule keys_subset_singleton_imp_monomial)
    from this[symmetric] UNIV_I show "p \<in> range (Poly_Mapping.single 0)" ..
  next
    assume "p \<in> range (Poly_Mapping.single 0)"
    then obtain c where "p = monomial c 0" ..
    thus "p \<in> P[{}]" by (simp add: Polys_def)
  qed
qed

lemma Polys_UNIV [simp]: "P[UNIV] = UNIV"
  by (simp add: Polys_def)

lemma zero_in_Polys: "0 \<in> P[X]"
  by (simp add: Polys_def)

lemma one_in_Polys: "1 \<in> P[X]"
  by (simp add: Polys_def zero_in_PPs)

lemma Polys_mono: "X \<subseteq> Y \<Longrightarrow> P[X] \<subseteq> P[Y]"
  by (auto simp: Polys_alt)

lemma Polys_closed_monomial: "t \<in> .[X] \<Longrightarrow> monomial c t \<in> P[X]"
  using indets_monomial_subset[where c=c and t=t] by (auto simp: Polys_alt PPs_def)

lemma Polys_closed_plus: "p \<in> P[X] \<Longrightarrow> q \<in> P[X] \<Longrightarrow> p + q \<in> P[X]"
  using indets_plus_subset[of p q] by (auto simp: Polys_alt PPs_def)

lemma Polys_closed_uminus: "p \<in> P[X] \<Longrightarrow> -p \<in> P[X]"
  by (simp add: Polys_def keys_uminus)

lemma Polys_closed_minus: "p \<in> P[X] \<Longrightarrow> q \<in> P[X] \<Longrightarrow> p - q \<in> P[X]"
  using indets_minus_subset[of p q] by (auto simp: Polys_alt PPs_def)

lemma Polys_closed_monom_mult: "t \<in> .[X] \<Longrightarrow> p \<in> P[X] \<Longrightarrow> punit.monom_mult c t p \<in> P[X]"
  using indets_monom_mult_subset[of c t p] by (auto simp: Polys_alt PPs_def)

corollary Polys_closed_map_scale: "p \<in> P[X] \<Longrightarrow> (c::_::semiring_0) \<cdot> p \<in> P[X]"
  unfolding punit.map_scale_eq_monom_mult using zero_in_PPs by (rule Polys_closed_monom_mult)

lemma Polys_closed_times: "p \<in> P[X] \<Longrightarrow> q \<in> P[X] \<Longrightarrow> p * q \<in> P[X]"
  using indets_times_subset[of p q] by (auto simp: Polys_alt PPs_def)

lemma Polys_closed_sum: "(\<And>a. a \<in> A \<Longrightarrow> f a \<in> P[X]) \<Longrightarrow> sum f A \<in> P[X]"
  by (induct A rule: infinite_finite_induct) (auto intro: zero_in_Polys Polys_closed_plus)

lemma Polys_closed_prod: "(\<And>a. a \<in> A \<Longrightarrow> f a \<in> P[X]) \<Longrightarrow> prod f A \<in> P[X]"
  by (induct A rule: infinite_finite_induct) (auto intro: one_in_Polys Polys_closed_times)

lemma Polys_closed_sum_list: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> P[X]) \<Longrightarrow> sum_list xs \<in> P[X]"
  by (induct xs) (auto intro: zero_in_Polys Polys_closed_plus)

lemma Polys_closed_except: "p \<in> P[X] \<Longrightarrow> except p T \<in> P[X]"
  by (auto intro!: PolysI simp: keys_except dest!: PolysD(1))

lemma times_in_PolysD:
  assumes "p * q \<in> P[X]" and "p \<in> P[X]" and "p \<noteq> (0::('x::linorder \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::semiring_no_zero_divisors)"
  shows "q \<in> P[X]"
proof -
  define qX where "qX = except q (- .[X])"
  define qY where "qY = except q .[X]"
  have q: "q = qX + qY" by (simp only: qX_def qY_def add.commute flip: except_decomp)
  have "qX \<in> P[X]" by (rule PolysI) (simp add: qX_def keys_except)
  with assms(2) have "p * qX \<in> P[X]" by (rule Polys_closed_times)
  show ?thesis
  proof (cases "qY = 0")
    case True
    with \<open>qX \<in> P[X]\<close> show ?thesis by (simp add: q)
  next
    case False
    with assms(3) have "p * qY \<noteq> 0" by simp
    hence "keys (p * qY) \<noteq> {}" by simp
    then obtain t where "t \<in> keys (p * qY)" by blast
    then obtain t1 t2 where "t2 \<in> keys qY" and t: "t = t1 + t2" by (rule in_keys_timesE)
    have "t \<notin> .[X]" unfolding t
    proof
      assume "t1 + t2 \<in> .[X]"
      hence "t1 + t2 - t1 \<in> .[X]" by (rule PPs_closed_minus)
      hence "t2 \<in> .[X]" by simp
      with \<open>t2 \<in> keys qY\<close> show False by (simp add: qY_def keys_except)
    qed
    have "t \<notin> keys (p * qX)"
    proof
      assume "t \<in> keys (p * qX)"
      also from \<open>p * qX \<in> P[X]\<close> have "\<dots> \<subseteq> .[X]" by (rule PolysD)
      finally have "t \<in> .[X]" .
      with \<open>t \<notin> .[X]\<close> show False ..
    qed
    with \<open>t \<in> keys (p * qY)\<close> have "t \<in> keys (p * qX + p * qY)" by (rule in_keys_plusI2)
    also have "\<dots> = keys (p * q)" by (simp only: q algebra_simps)
    finally have "p * q \<notin> P[X]" using \<open>t \<notin> .[X]\<close> by (auto simp: Polys_def)
    thus ?thesis using assms(1) ..
  qed
qed

lemma poly_mapping_plus_induct_Polys [consumes 1, case_names 0 plus]:
  assumes "p \<in> P[X]" and "P 0"
    and "\<And>p c t. t \<in> .[X] \<Longrightarrow> p \<in> P[X] \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> t \<notin> keys p \<Longrightarrow> P p \<Longrightarrow> P (monomial c t + p)"
  shows "P p"
  using assms(1)
proof (induct p rule: poly_mapping_plus_induct)
  case 1
  show ?case by (fact assms(2))
next
  case step: (2 p c t)
  from step.hyps(1) have 1: "keys (monomial c t) = {t}" by simp
  also from step.hyps(2) have "\<dots> \<inter> keys p = {}" by simp
  finally have "keys (monomial c t + p) = keys (monomial c t) \<union> keys p" by (rule keys_add[symmetric])
  hence "keys (monomial c t + p) = insert t (keys p)" by (simp only: 1 flip: insert_is_Un)
  moreover from step.prems(1) have "keys (monomial c t + p) \<subseteq> .[X]" by (rule PolysD)
  ultimately have "t \<in> .[X]" and "keys p \<subseteq> .[X]" by blast+
  from this(2) have "p \<in> P[X]" by (rule PolysI)
  hence "P p" by (rule step.hyps)
  with \<open>t \<in> .[X]\<close> \<open>p \<in> P[X]\<close> step.hyps(1, 2) show ?case by (rule assms(3))
qed

lemma Polys_Int: "P[X \<inter> Y] = P[X] \<inter> P[Y]"
  by (auto simp: Polys_def PPs_Int)

lemma Polys_INT: "P[\<Inter> X] = \<Inter> (Polys ` X)"
  by (auto simp: Polys_def PPs_INT)

subsection \<open>Degree-Sections of Power-Products\<close>

definition deg_sect :: "'x set \<Rightarrow> nat \<Rightarrow> ('x::countable \<Rightarrow>\<^sub>0 nat) set"
  where "deg_sect X d = .[X] \<inter> {t. deg_pm t = d}"

definition deg_le_sect :: "'x set \<Rightarrow> nat \<Rightarrow> ('x::countable \<Rightarrow>\<^sub>0 nat) set"
  where "deg_le_sect X d = (\<Union>d0\<le>d. deg_sect X d0)"

lemma deg_sectI: "t \<in> .[X] \<Longrightarrow> deg_pm t = d \<Longrightarrow> t \<in> deg_sect X d"
  by (simp add: deg_sect_def)

lemma deg_sectD:
  assumes "t \<in> deg_sect X d"
  shows "t \<in> .[X]" and "deg_pm t = d"
  using assms by (simp_all add: deg_sect_def)

lemma deg_le_sect_alt: "deg_le_sect X d = .[X] \<inter> {t. deg_pm t \<le> d}"
  by (auto simp: deg_le_sect_def deg_sect_def)

lemma deg_le_sectI: "t \<in> .[X] \<Longrightarrow> deg_pm t \<le> d \<Longrightarrow> t \<in> deg_le_sect X d"
  by (simp add: deg_le_sect_alt)

lemma deg_le_sectD:
  assumes "t \<in> deg_le_sect X d"
  shows "t \<in> .[X]" and "deg_pm t \<le> d"
  using assms by (simp_all add: deg_le_sect_alt)

lemma deg_sect_zero [simp]: "deg_sect X 0 = {0}"
  by (auto simp: deg_sect_def zero_in_PPs)

lemma deg_sect_empty: "deg_sect {} d = (if d = 0 then {0} else {})"
  by (auto simp: deg_sect_def)

lemma deg_sect_singleton [simp]: "deg_sect {x} d = {Poly_Mapping.single x d}"
  by (auto simp: deg_sect_def deg_pm_single PPs_singleton)

lemma deg_le_sect_zero [simp]: "deg_le_sect X 0 = {0}"
  by (auto simp: deg_le_sect_def)

lemma deg_le_sect_empty [simp]: "deg_le_sect {} d = {0}"
  by (auto simp: deg_le_sect_alt varnum_eq_zero_iff)

lemma deg_le_sect_singleton: "deg_le_sect {x} d = Poly_Mapping.single x ` {..d}"
  by (auto simp: deg_le_sect_alt deg_pm_single PPs_singleton)

lemma deg_sect_mono: "X \<subseteq> Y \<Longrightarrow> deg_sect X d \<subseteq> deg_sect Y d"
  by (auto simp: deg_sect_def dest: PPs_mono)

lemma deg_le_sect_mono_1: "X \<subseteq> Y \<Longrightarrow> deg_le_sect X d \<subseteq> deg_le_sect Y d"
  by (auto simp: deg_le_sect_alt dest: PPs_mono)

lemma deg_le_sect_mono_2: "d1 \<le> d2 \<Longrightarrow> deg_le_sect X d1 \<subseteq> deg_le_sect X d2"
  by (auto simp: deg_le_sect_alt)

lemma zero_in_deg_le_sect: "0 \<in> deg_le_sect n d"
  by (simp add: deg_le_sect_alt zero_in_PPs)

lemma deg_sect_disjoint: "d1 \<noteq> d2 \<Longrightarrow> deg_sect X d1 \<inter> deg_sect Y d2 = {}"
  by (auto simp: deg_sect_def)

lemma deg_le_sect_deg_sect_disjoint: "d1 < d2 \<Longrightarrow> deg_le_sect Y d1 \<inter> deg_sect X d2 = {}"
  by (auto simp: deg_sect_def deg_le_sect_alt)

lemma deg_sect_Suc:
  "deg_sect X (Suc d) = (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` deg_sect X d)" (is "?A = ?B")
proof (rule set_eqI)
  fix t
  show "t \<in> ?A \<longleftrightarrow> t \<in> ?B"
  proof
    assume "t \<in> ?A"
    hence "t \<in> .[X]" and "deg_pm t = Suc d" by (rule deg_sectD)+
    from this(2) have "keys t \<noteq> {}" by auto
    then obtain x where "x \<in> keys t" by blast
    hence "1 \<le> lookup t x" by (simp add: in_keys_iff)
    from \<open>t \<in> .[X]\<close> have "keys t \<subseteq> X" by (rule PPsD)
    with \<open>x \<in> keys t\<close> have "x \<in> X" ..
    let ?s = "Poly_Mapping.single x (1::nat)"
    from \<open>1 \<le> lookup t x\<close> have "?s adds t"
      by (auto simp: lookup_single when_def intro!: adds_poly_mappingI le_funI)
    hence t: "?s + (t - ?s) = t" by (metis add.commute adds_minus)
    have "t - ?s \<in> deg_sect X d"
    proof (rule deg_sectI)
      from \<open>t \<in> .[X]\<close> show "t - ?s \<in> .[X]" by (rule PPs_closed_minus)
    next
      from deg_pm_plus[of ?s "t - ?s"] have "deg_pm t = Suc (deg_pm (t - ?s))"
        by (simp only: t deg_pm_single)
      thus "deg_pm (t - ?s) = d" by (simp add: \<open>deg_pm t = Suc d\<close>)
    qed
    hence "?s + (t - ?s) \<in> (+) ?s ` deg_sect X d" by (rule imageI)
    hence "t \<in> (+) ?s ` deg_sect X d" by (simp only: t)
    with \<open>x \<in> X\<close> show "t \<in> ?B" ..
  next
    assume "t \<in> ?B"
    then obtain x where "x \<in> X" and "t \<in> (+) (Poly_Mapping.single x 1) ` deg_sect X d" ..
    from this(2) obtain s where s: "s \<in> deg_sect X d"
      and t: "t = Poly_Mapping.single x 1 + s" (is "t = ?s + s") ..
    show "t \<in> ?A"
    proof (rule deg_sectI)
      from \<open>x \<in> X\<close> have "?s \<in> .[X]" by (rule PPs_closed_single)
      moreover from s have "s \<in> .[X]" by (rule deg_sectD)
      ultimately show "t \<in> .[X]" unfolding t by (rule PPs_closed_plus)
    next
      from s have "deg_pm s = d" by (rule deg_sectD)
      thus "deg_pm t = Suc d" by (simp add: t deg_pm_single deg_pm_plus)
    qed
  qed
qed

lemma deg_sect_insert:
  "deg_sect (insert x X) d = (\<Union>d0\<le>d. (+) (Poly_Mapping.single x (d - d0)) ` deg_sect X d0)"
    (is "?A = ?B")
proof (rule set_eqI)
  fix t
  show "t \<in> ?A \<longleftrightarrow> t \<in> ?B"
  proof
    assume "t \<in> ?A"
    hence "t \<in> .[insert x X]" and "deg_pm t = d" by (rule deg_sectD)+
    from this(1) obtain e tx where "tx \<in> .[X]" and t: "t = Poly_Mapping.single x e + tx"
      by (rule PPs_insertE)
    have "e + deg_pm tx = deg_pm t" by (simp add: t deg_pm_plus deg_pm_single)
    hence "e + deg_pm tx = d" by (simp only: \<open>deg_pm t = d\<close>)
    hence "deg_pm tx \<in> {..d}" and e: "e = d - deg_pm tx" by simp_all
    from \<open>tx \<in> .[X]\<close> refl have "tx \<in> deg_sect X (deg_pm tx)" by (rule deg_sectI)
    hence "t \<in> (+) (Poly_Mapping.single x (d - deg_pm tx)) ` deg_sect X (deg_pm tx)"
      unfolding t e by (rule imageI)
    with \<open>deg_pm tx \<in> {..d}\<close> show "t \<in> ?B" ..
  next
    assume "t \<in> ?B"
    then obtain d0 where "d0 \<in> {..d}" and "t \<in> (+) (Poly_Mapping.single x (d - d0)) ` deg_sect X d0" ..
    from this(2) obtain s where s: "s \<in> deg_sect X d0"
      and t: "t = Poly_Mapping.single x (d - d0) + s" (is "t = ?s + s") ..
    show "t \<in> ?A"
    proof (rule deg_sectI)
      have "?s \<in> .[insert x X]" by (rule PPs_closed_single, simp)
      from s have "s \<in> .[X]" by (rule deg_sectD)
      also have "... \<subseteq> .[insert x X]" by (rule PPs_mono, blast)
      finally have "s \<in> .[insert x X]" .
      with \<open>?s \<in> .[insert x X]\<close> show "t \<in> .[insert x X]" unfolding t by (rule PPs_closed_plus)
    next
      from s have "deg_pm s = d0" by (rule deg_sectD)
      moreover from \<open>d0 \<in> {..d}\<close> have "d0 \<le> d" by simp
      ultimately show "deg_pm t = d" by (simp add: t deg_pm_single deg_pm_plus)
    qed
  qed
qed

lemma deg_le_sect_Suc: "deg_le_sect X (Suc d) = deg_le_sect X d \<union> deg_sect X (Suc d)"
  by (simp add: deg_le_sect_def atMost_Suc Un_commute)

lemma deg_le_sect_Suc_2:
  "deg_le_sect X (Suc d) = insert 0 (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` deg_le_sect X d)"
    (is "?A = ?B")
proof -
  have eq1: "{Suc 0..Suc d} = Suc ` {..d}" by (simp add: image_Suc_atMost)
  have "insert 0 {1..Suc d} = {..Suc d}" by fastforce
  hence "?A = (\<Union>d0\<in>insert 0 {1..Suc d}. deg_sect X d0)" by (simp add: deg_le_sect_def)
  also have "... = insert 0 (\<Union>d0\<le>d. deg_sect X (Suc d0))" by (simp add: eq1)
  also have "... = insert 0 (\<Union>d0\<le>d. (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` deg_sect X d0))"
    by (simp only: deg_sect_Suc)
  also have "... = insert 0 (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` (\<Union>d0\<le>d. deg_sect X d0))"
    by fastforce
  also have "... = ?B" by (simp only: deg_le_sect_def)
  finally show ?thesis .
qed

lemma finite_deg_sect:
  assumes "finite X"
  shows "finite ((deg_sect X d)::('x::countable \<Rightarrow>\<^sub>0 nat) set)"
proof (induct d)
  case 0
  show ?case by simp
next
  case (Suc d)
  with assms show ?case by (simp add: deg_sect_Suc)
qed

corollary finite_deg_le_sect: "finite X \<Longrightarrow> finite ((deg_le_sect X d)::('x::countable \<Rightarrow>\<^sub>0 nat) set)"
  by (simp add: deg_le_sect_def finite_deg_sect)

lemma keys_subset_deg_le_sectI:
  assumes "p \<in> P[X]" and "poly_deg p \<le> d"
  shows "keys p \<subseteq> deg_le_sect X d"
proof
  fix t
  assume "t \<in> keys p"
  also from assms(1) have "... \<subseteq> .[X]" by (rule PolysD)
  finally have "t \<in> .[X]" .
  from \<open>t \<in> keys p\<close> have "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
  from this assms(2) have "deg_pm t \<le> d" by (rule le_trans)
  with \<open>t \<in> .[X]\<close> show "t \<in> deg_le_sect X d" by (rule deg_le_sectI)
qed

lemma binomial_symmetric_plus: "(n + k) choose n = (n + k) choose k"
  by (metis add_diff_cancel_left' binomial_symmetric le_add1)

lemma card_deg_sect:
  assumes "finite X" and "X \<noteq> {}"
  shows "card (deg_sect X d) = (d + (card X - 1)) choose (card X - 1)"
  using assms
proof (induct X arbitrary: d)
  case empty
  thus ?case by simp
next
  case (insert x X)
  from insert(1, 2) have eq1: "card (insert x X) = Suc (card X)" by simp
  show ?case
  proof (cases "X = {}")
    case True
    thus ?thesis by simp
  next
    case False
    with insert.hyps(1) have "0 < card X" by (simp add: card_gt_0_iff)
    let ?f = "\<lambda>d0. Poly_Mapping.single x (d - d0)"
    from False have eq2: "card (deg_sect X d0) = d0 + (card X - 1) choose (card X - 1)" for d0
      by (rule insert.hyps)
    have "finite {..d}" by simp
    moreover from insert.hyps(1) have "\<forall>d0\<in>{..d}. finite ((+) (?f d0) ` deg_sect X d0)"
      by (simp add: finite_deg_sect)
    moreover have "\<forall>d0\<in>{..d}. \<forall>d1\<in>{..d}. d0 \<noteq> d1 \<longrightarrow>
                          ((+) (?f d0) ` deg_sect X d0) \<inter> ((+) (?f d1) ` deg_sect X d1) = {}"
    proof (intro ballI impI, rule ccontr)
      fix d1 d2 :: nat
      assume "d1 \<noteq> d2"
      assume "((+) (?f d1) ` deg_sect X d1) \<inter> ((+) (?f d2) ` deg_sect X d2) \<noteq> {}"
      then obtain t where "t \<in> ((+) (?f d1) ` deg_sect X d1) \<inter> ((+) (?f d2) ` deg_sect X d2)"
        by blast
      hence t1: "t \<in> (+) (?f d1) ` deg_sect X d1" and t2: "t \<in> (+) (?f d2) ` deg_sect X d2" by simp_all
      from t1 obtain s1 where "s1 \<in> deg_sect X d1" and s1: "t = ?f d1 + s1" ..
      from this(1) have "s1 \<in> .[X]" by (rule deg_sectD)
      hence "keys s1 \<subseteq> X" by (rule PPsD)
      with insert.hyps(2) have eq3: "lookup s1 x = 0" by auto
      from t2 obtain s2 where "s2 \<in> deg_sect X d2" and s2: "t = ?f d2 + s2" ..
      from this(1) have "s2 \<in> .[X]" by (rule deg_sectD)
      hence "keys s2 \<subseteq> X" by (rule PPsD)
      with insert.hyps(2) have eq4: "lookup s2 x = 0" by auto
      from s2 have "lookup (?f d1 + s1) x = lookup (?f d2 + s2) x" by (simp only: s1)
      hence "d - d1 = d - d2" by (simp add: lookup_add eq3 eq4)
      moreover assume "d1 \<in> {..d}" and "d2 \<in> {..d}"
      ultimately have "d1 = d2" by simp
      with \<open>d1 \<noteq> d2\<close> show False ..
    qed
    ultimately have "card (deg_sect (insert x X) d) =
                       (\<Sum>d0\<le>d. card ((+) (monomial (d - d0) x) ` deg_sect X d0))"
      unfolding deg_sect_insert by (rule card_UN_disjoint)
    also from refl have "... = (\<Sum>d0\<le>d. card (deg_sect X d0))"
    proof (rule sum.cong)
      fix d0
      have "inj_on ((+) (monomial (d - d0) x)) (deg_sect X d0)" by (rule, rule add_left_imp_eq)
      thus "card ((+) (monomial (d - d0) x) ` deg_sect X d0) = card (deg_sect X d0)"
        by (rule card_image)
    qed
    also have "... = (\<Sum>d0\<le>d. (card X - 1) + d0 choose (card X - 1))" by (simp only: eq2 add.commute)
    also have "... = (\<Sum>d0\<le>d. (card X - 1) + d0 choose d0)" by (simp only: binomial_symmetric_plus)
    also have "... = Suc ((card X - 1) + d) choose d" by (rule sum_choose_lower)
    also from \<open>0 < card X\<close> have "... = d + (card (insert x X) - 1) choose d"
      by (simp add: eq1 add.commute)
    also have "... = d + (card (insert x X) - 1) choose (card (insert x X) - 1)"
      by (fact binomial_symmetric_plus)
    finally show ?thesis .
  qed
qed

corollary card_deg_sect_Suc:
  assumes "finite X"
  shows "card (deg_sect X (Suc d)) = (d + card X) choose (Suc d)"
proof (cases "X = {}")
  case True
  thus ?thesis by (simp add: deg_sect_empty)
next
  case False
  with assms have "0 < card X" by (simp add: card_gt_0_iff)
  from assms False have "card (deg_sect X (Suc d)) = (Suc d + (card X - 1)) choose (card X - 1)"
    by (rule card_deg_sect)
  also have "... = (Suc d + (card X - 1)) choose (Suc d)" by (rule sym, rule binomial_symmetric_plus)
  also from \<open>0 < card X\<close> have "... = (d + card X) choose (Suc d)" by simp
  finally show ?thesis .
qed

corollary card_deg_le_sect:
  assumes "finite X"
  shows "card (deg_le_sect X d) = (d + card X) choose card X"
proof (induct d)
  case 0
  show ?case by simp
next
  case (Suc d)
  from assms have "finite (deg_le_sect X d)" by (rule finite_deg_le_sect)
  moreover from assms have "finite (deg_sect X (Suc d))" by (rule finite_deg_sect)
  moreover from lessI have "deg_le_sect X d \<inter> deg_sect X (Suc d) = {}"
    by (rule deg_le_sect_deg_sect_disjoint)
  ultimately have "card (deg_le_sect X (Suc d)) = card (deg_le_sect X d) + card (deg_sect X (Suc d))"
    unfolding deg_le_sect_Suc by (rule card_Un_disjoint)
  also from assms have "... = (Suc d + card X) choose Suc d"
    by (simp add: Suc.hyps card_deg_sect_Suc binomial_symmetric_plus[of d])
  also have "... = (Suc d + card X) choose card X" by (rule binomial_symmetric_plus)
  finally show ?case .
qed

subsection \<open>Substitution Homomorphisms\<close>

text \<open>The substitution homomorphisms defined here are more general than @{const insertion} etc., since
  they replace indeterminates by @{emph \<open>polynomials\<close>} rather than coefficients, and therefore
  construct new polynomials.\<close>

definition subst_pp :: "('x \<Rightarrow> (('y \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a)) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> (('y \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
  where "subst_pp f t = (\<Prod>x\<in>keys t. (f x) ^ (lookup t x))"

definition poly_subst :: "('x \<Rightarrow> (('y \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a)) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('y \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
  where "poly_subst f p = (\<Sum>t\<in>keys p. punit.monom_mult (lookup p t) 0 (subst_pp f t))"

lemma subst_pp_alt: "subst_pp f t = (\<Prod>x. (f x) ^ (lookup t x))"
proof -
  from finite_keys have "subst_pp f t = (\<Prod>x. if x \<in> keys t then (f x) ^ (lookup t x) else 1)"
    unfolding subst_pp_def by (rule Prod_any.conditionalize)
  also have "... = (\<Prod>x. (f x) ^ (lookup t x))" by (rule Prod_any.cong, simp)
  finally show ?thesis .
qed

lemma subst_pp_zero [simp]: "subst_pp f 0 = 1"
  by (simp add: subst_pp_def)

lemma subst_pp_trivial_not_zero:
  assumes "t \<noteq> 0"
  shows "subst_pp (\<lambda>_. 0) t = (0::(_ \<Rightarrow>\<^sub>0 'b::comm_semiring_1))"
  unfolding subst_pp_def using finite_keys
proof (rule prod_zero)
  from assms have "keys t \<noteq> {}" by simp
  then obtain x where "x \<in> keys t" by blast
  thus "\<exists>x\<in>keys t. 0 ^ lookup t x = (0::(_ \<Rightarrow>\<^sub>0 'b))"
  proof
    from \<open>x \<in> keys t\<close> have "0 < lookup t x" by (simp add: in_keys_iff)
    thus "0 ^ lookup t x = (0::(_ \<Rightarrow>\<^sub>0 'b))" by (rule Power.semiring_1_class.zero_power)
  qed
qed

lemma subst_pp_single: "subst_pp f (Poly_Mapping.single x e) = (f x) ^ e"
  by (simp add: subst_pp_def)

corollary subst_pp_trivial: "subst_pp (\<lambda>_. 0) t = (if t = 0 then 1 else 0)"
  by (simp split: if_split add: subst_pp_trivial_not_zero)

lemma power_lookup_not_one_subset_keys: "{x. f x ^ (lookup t x) \<noteq> 1} \<subseteq> keys t"
proof (rule, simp)
  fix x
  assume "f x ^ (lookup t x) \<noteq> 1"
  thus "x \<in> keys t" unfolding in_keys_iff by (metis power_0)
qed

corollary finite_power_lookup_not_one: "finite {x. f x ^ (lookup t x) \<noteq> 1}"
  by (rule finite_subset, fact power_lookup_not_one_subset_keys, fact finite_keys)

lemma subst_pp_plus: "subst_pp f (s + t) = subst_pp f s * subst_pp f t"
  by (simp add: subst_pp_alt lookup_add power_add, rule Prod_any.distrib, (fact finite_power_lookup_not_one)+)

lemma subst_pp_id:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> f x = monomial 1 (Poly_Mapping.single x 1)"
  shows "subst_pp f t = monomial 1 t"
proof -
  have "subst_pp f t = (\<Prod>x\<in>keys t. monomial 1 (Poly_Mapping.single x (lookup t x)))"
  proof (simp only: subst_pp_def, rule prod.cong, fact refl)
    fix x
    assume "x \<in> keys t"
    thus "f x ^ lookup t x = monomial 1 (Poly_Mapping.single x (lookup t x))"
      by (simp add: assms monomial_single_power)
  qed
  also have "... = monomial 1 t"
    by (simp add: punit.monomial_prod_sum[symmetric] poly_mapping_sum_monomials)
  finally show ?thesis .
qed

lemma in_indets_subst_ppE:
  assumes "x \<in> indets (subst_pp f t)"
  obtains y where "y \<in> keys t" and "x \<in> indets (f y)"
proof -
  note assms
  also have "indets (subst_pp f t) \<subseteq> (\<Union>y\<in>keys t. indets ((f y) ^ (lookup t y)))" unfolding subst_pp_def
    by (rule indets_prod_subset)
  finally obtain y where "y \<in> keys t" and "x \<in> indets ((f y) ^ (lookup t y))" ..
  note this(2)
  also have "indets ((f y) ^ (lookup t y)) \<subseteq> indets (f y)" by (rule indets_power_subset)
  finally have "x \<in> indets (f y)" .
  with \<open>y \<in> keys t\<close> show ?thesis ..
qed

lemma subst_pp_by_monomials:
  assumes "\<And>y. y \<in> keys t \<Longrightarrow> f y = monomial (c y) (s y)"
  shows "subst_pp f t = monomial (\<Prod>y\<in>keys t. (c y) ^ lookup t y) (\<Sum>y\<in>keys t. lookup t y \<cdot> s y)"
  by (simp add: subst_pp_def assms monomial_power_map_scale punit.monomial_prod_sum)

lemma poly_deg_subst_pp_eq_zeroI:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> poly_deg (f x) = 0"
  shows "poly_deg (subst_pp f t) = 0"
proof -
  have "poly_deg (subst_pp f t) \<le> (\<Sum>x\<in>keys t. poly_deg ((f x) ^ (lookup t x)))"
    unfolding subst_pp_def by (fact poly_deg_prod_le)
  also have "... = 0"
  proof (rule sum.neutral, rule)
    fix x
    assume "x \<in> keys t"
    hence "poly_deg (f x) = 0" by (rule assms)
    have "f x ^ lookup t x = (\<Prod>i=0..<lookup t x. f x)" by simp
    also have "poly_deg ... \<le> (\<Sum>i=0..<lookup t x. poly_deg (f x))" by (rule poly_deg_prod_le)
    also have "... = 0" by (simp add: \<open>poly_deg (f x) = 0\<close>)
    finally show "poly_deg (f x ^ lookup t x) = 0" by simp
  qed
  finally show ?thesis by simp
qed

lemma poly_deg_subst_pp_le:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> poly_deg (f x) \<le> 1"
  shows "poly_deg (subst_pp f t) \<le> deg_pm t"
proof -
  have "poly_deg (subst_pp f t) \<le> (\<Sum>x\<in>keys t. poly_deg ((f x) ^ (lookup t x)))"
    unfolding subst_pp_def by (fact poly_deg_prod_le)
  also have "... \<le> (\<Sum>x\<in>keys t. lookup t x)"
  proof (rule sum_mono)
    fix x
    assume "x \<in> keys t"
    hence "poly_deg (f x) \<le> 1" by (rule assms)
    have "f x ^ lookup t x = (\<Prod>i=0..<lookup t x. f x)" by simp
    also have "poly_deg ... \<le> (\<Sum>i=0..<lookup t x. poly_deg (f x))" by (rule poly_deg_prod_le)
    also from \<open>poly_deg (f x) \<le> 1\<close> have "... \<le> (\<Sum>i=0..<lookup t x. 1)" by (rule sum_mono)
    finally show "poly_deg (f x ^ lookup t x) \<le> lookup t x" by simp
  qed
  also have "... = deg_pm t" by (rule deg_pm_superset[symmetric], fact subset_refl, fact finite_keys)
  finally show ?thesis by simp
qed

lemma poly_subst_alt: "poly_subst f p = (\<Sum>t. punit.monom_mult (lookup p t) 0 (subst_pp f t))"
proof -
  from finite_keys have "poly_subst f p = (\<Sum>t. if t \<in> keys p then punit.monom_mult (lookup p t) 0 (subst_pp f t) else 0)"
    unfolding poly_subst_def by (rule Sum_any.conditionalize)
  also have "... = (\<Sum>t. punit.monom_mult (lookup p t) 0 (subst_pp f t))" by (rule Sum_any.cong, simp)
  finally show ?thesis .
qed

lemma poly_subst_trivial [simp]: "poly_subst (\<lambda>_. 0) p = monomial (lookup p 0) 0"
  by (simp add: poly_subst_def subst_pp_trivial if_distrib cong: if_cong)
      (metis mult.right_neutral times_monomial_left)

lemma poly_subst_zero [simp]: "poly_subst f 0 = 0"
  by (simp add: poly_subst_def)

lemma monom_mult_lookup_not_zero_subset_keys:
  "{t. punit.monom_mult (lookup p t) 0 (subst_pp f t) \<noteq> 0} \<subseteq> keys p"
proof (rule, simp)
  fix t
  assume "punit.monom_mult (lookup p t) 0 (subst_pp f t) \<noteq> 0"
  thus "t \<in> keys p" unfolding in_keys_iff by (metis punit.monom_mult_zero_left)
qed

corollary finite_monom_mult_lookup_not_zero:
  "finite {t. punit.monom_mult (lookup p t) 0 (subst_pp f t) \<noteq> 0}"
  by (rule finite_subset, fact monom_mult_lookup_not_zero_subset_keys, fact finite_keys)

lemma poly_subst_plus: "poly_subst f (p + q) = poly_subst f p + poly_subst f q"
  by (simp add: poly_subst_alt lookup_add punit.monom_mult_dist_left, rule Sum_any.distrib,
      (fact finite_monom_mult_lookup_not_zero)+)

lemma poly_subst_uminus: "poly_subst f (-p) = - poly_subst f (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_ring_1)"
  by (simp add: poly_subst_def keys_uminus punit.monom_mult_uminus_left sum_negf)

lemma poly_subst_minus:
  "poly_subst f (p - q) = poly_subst f p - poly_subst f (q::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_ring_1)"
proof -
  have "poly_subst f (p + (-q)) = poly_subst f p + poly_subst f (-q)" by (fact poly_subst_plus)
  thus ?thesis by (simp add: poly_subst_uminus)
qed

lemma poly_subst_monomial: "poly_subst f (monomial c t) = punit.monom_mult c 0 (subst_pp f t)"
  by (simp add: poly_subst_def lookup_single)

corollary poly_subst_one [simp]: "poly_subst f 1 = 1"
  by (simp add: single_one[symmetric] poly_subst_monomial punit.monom_mult_monomial del: single_one)

lemma poly_subst_times: "poly_subst f (p * q) = poly_subst f p * poly_subst f q"
proof -
  have bij: "bij (\<lambda>(l, n, m). (m, l, n))"
    by (auto intro!: bijI injI simp add: image_def)
  let ?P = "keys p"
  let ?Q = "keys q"
  let ?PQ = "{s + t | s t. lookup p s \<noteq> 0 \<and> lookup q t \<noteq> 0}"
  have fin_PQ: "finite ?PQ"
    by (rule finite_not_eq_zero_sumI, simp_all)
  have fin_1: "finite {l. lookup p l * (\<Sum>qa. lookup q qa when t = l + qa) \<noteq> 0}" for t
  proof (rule finite_subset)
    show "{l. lookup p l * (\<Sum>qa. lookup q qa when t = l + qa) \<noteq> 0} \<subseteq> keys p"
      by (rule, auto simp add: in_keys_iff simp del: lookup_not_eq_zero_eq_in_keys)
  qed (fact finite_keys)
  have fin_2: "finite {v. (lookup q v when t = u + v) \<noteq> 0}" for t u
  proof (rule finite_subset)
    show "{v. (lookup q v when t = u + v) \<noteq> 0} \<subseteq> keys q"
      by (rule, auto simp add: in_keys_iff simp del: lookup_not_eq_zero_eq_in_keys)
  qed (fact finite_keys)
  have fin_3: "finite {v. (lookup p u * lookup q v when t = u + v) \<noteq> 0}" for t u
  proof (rule finite_subset)
    show "{v. (lookup p u * lookup q v when t = u + v) \<noteq> 0} \<subseteq> keys q"
      by (rule, auto simp add: in_keys_iff simp del: lookup_not_eq_zero_eq_in_keys)
  qed (fact finite_keys)
  have "(\<Sum>t. punit.monom_mult (lookup (p * q) t) 0 (subst_pp f t)) =
        (\<Sum>t. \<Sum>u. punit.monom_mult (lookup p u * (\<Sum>v. lookup q v when t = u + v)) 0 (subst_pp f t))"
    by (simp add: times_poly_mapping.rep_eq prod_fun_def punit.monom_mult_Sum_any_left[OF fin_1])
  also have "\<dots> = (\<Sum>t. \<Sum>u. \<Sum>v. (punit.monom_mult (lookup p u * lookup q v) 0 (subst_pp f t)) when t = u + v)"
    by (simp add: Sum_any_right_distrib[OF fin_2] punit.monom_mult_Sum_any_left[OF fin_3] mult_when punit.when_monom_mult)
  also have "\<dots> = (\<Sum>t. (\<Sum>(u, v). (punit.monom_mult (lookup p u * lookup q v) 0 (subst_pp f t)) when t = u + v))"
    apply (subst (2) Sum_any.cartesian_product [of "?P \<times> ?Q"])
    apply (auto simp add: in_keys_iff simp del: lookup_not_eq_zero_eq_in_keys)
    done
  also have "\<dots> = (\<Sum>(t, u, v). punit.monom_mult (lookup p u * lookup q v) 0 (subst_pp f t) when t = u + v)"
    apply (subst Sum_any.cartesian_product [of "?PQ \<times> (?P \<times> ?Q)"])
    apply (auto simp add: fin_PQ in_keys_iff simp del: lookup_not_eq_zero_eq_in_keys)
    apply (metis monomial_0I mult_not_zero times_monomial_left)
    done
  also have "\<dots> = (\<Sum>(u, v, t). punit.monom_mult (lookup p u * lookup q v) 0 (subst_pp f t) when t = u + v)"
    using bij by (rule Sum_any.reindex_cong [of "\<lambda>(u, v, t). (t, u, v)"]) (simp add: fun_eq_iff)
  also have "\<dots> = (\<Sum>(u, v). \<Sum>t. punit.monom_mult (lookup p u * lookup q v) 0 (subst_pp f t) when t = u + v)"
    apply (subst Sum_any.cartesian_product2 [of "(?P \<times> ?Q) \<times> ?PQ"])
    apply (auto simp add: fin_PQ in_keys_iff simp del: lookup_not_eq_zero_eq_in_keys)
    apply (metis monomial_0I mult_not_zero times_monomial_left)
    done
  also have "\<dots> = (\<Sum>(u, v). punit.monom_mult (lookup p u * lookup q v) 0 (subst_pp f u * subst_pp f v))"
    by (simp add: subst_pp_plus)
  also have "\<dots> = (\<Sum>u. \<Sum>v. punit.monom_mult (lookup p u * lookup q v) 0 (subst_pp f u * subst_pp f v))"
    apply (subst Sum_any.cartesian_product [of "?P \<times> ?Q"])
    apply (auto simp add: in_keys_iff simp del: lookup_not_eq_zero_eq_in_keys)
    done
  also have "\<dots> = (\<Sum>u. \<Sum>v. (punit.monom_mult (lookup p u) 0 (subst_pp f u)) * (punit.monom_mult (lookup q v) 0 (subst_pp f v)))"
    by (simp add: times_monomial_left[symmetric] ac_simps mult_single)
  also have "\<dots> = (\<Sum>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) *
                  (\<Sum>t. punit.monom_mult (lookup q t) 0 (subst_pp f t))"
    by (rule Sum_any_product [symmetric], (fact finite_monom_mult_lookup_not_zero)+)
  finally show ?thesis by (simp add: poly_subst_alt)
qed

corollary poly_subst_monom_mult:
  "poly_subst f (punit.monom_mult c t p) = punit.monom_mult c 0 (subst_pp f t * poly_subst f p)"
  by (simp only: times_monomial_left[symmetric] poly_subst_times poly_subst_monomial mult.assoc)

corollary poly_subst_monom_mult':
  "poly_subst f (punit.monom_mult c t p) = (punit.monom_mult c 0 (subst_pp f t)) * poly_subst f p"
  by (simp only: times_monomial_left[symmetric] poly_subst_times poly_subst_monomial)

lemma poly_subst_sum: "poly_subst f (sum p A) = (\<Sum>a\<in>A. poly_subst f (p a))"
  by (rule fun_sum_commute, simp_all add: poly_subst_plus)

lemma poly_subst_prod: "poly_subst f (prod p A) = (\<Prod>a\<in>A. poly_subst f (p a))"
  by (rule fun_prod_commute, simp_all add: poly_subst_times)

lemma poly_subst_power: "poly_subst f (p ^ n) = (poly_subst f p) ^ n"
  by (induct n, simp_all add: poly_subst_times)

lemma poly_subst_subst_pp: "poly_subst f (subst_pp g t) = subst_pp (\<lambda>x. poly_subst f (g x)) t"
  by (simp only: subst_pp_def poly_subst_prod poly_subst_power)

lemma poly_subst_poly_subst: "poly_subst f (poly_subst g p) = poly_subst (\<lambda>x. poly_subst f (g x)) p"
proof -
  have "poly_subst f (poly_subst g p) =
          poly_subst f (\<Sum>t\<in>keys p. punit.monom_mult (lookup p t) 0 (subst_pp g t))"
    by (simp only: poly_subst_def)
  also have "\<dots> = (\<Sum>t\<in>keys p. punit.monom_mult (lookup p t) 0 (subst_pp (\<lambda>x. poly_subst f (g x)) t))"
    by (simp add: poly_subst_sum poly_subst_monom_mult poly_subst_subst_pp)
  also have "\<dots> = poly_subst (\<lambda>x. poly_subst f (g x)) p" by (simp only: poly_subst_def)
  finally show ?thesis .
qed

lemma poly_subst_id:
  assumes "\<And>x. x \<in> indets p \<Longrightarrow> f x = monomial 1 (Poly_Mapping.single x 1)"
  shows "poly_subst f p = p"
proof -
  have "poly_subst f p = (\<Sum>t\<in>keys p. monomial (lookup p t) t)"
  proof (simp only: poly_subst_def, rule sum.cong, fact refl)
    fix t
    assume "t \<in> keys p"
    have eq: "subst_pp f t = monomial 1 t"
      by (rule subst_pp_id, rule assms, erule in_indetsI, fact \<open>t \<in> keys p\<close>)
    show "punit.monom_mult (lookup p t) 0 (subst_pp f t) = monomial (lookup p t) t"
      by (simp add: eq punit.monom_mult_monomial)
  qed
  also have "... = p" by (simp only: poly_mapping_sum_monomials)
  finally show ?thesis .
qed

lemma in_indets_poly_substE:
  assumes "x \<in> indets (poly_subst f p)"
  obtains y where "y \<in> indets p" and "x \<in> indets (f y)"
proof -
  note assms
  also have "indets (poly_subst f p) \<subseteq> (\<Union>t\<in>keys p. indets (punit.monom_mult (lookup p t) 0 (subst_pp f t)))"
    unfolding poly_subst_def by (rule indets_sum_subset)
  finally obtain t where "t \<in> keys p" and "x \<in> indets (punit.monom_mult (lookup p t) 0 (subst_pp f t))" ..
  note this(2)
  also have "indets (punit.monom_mult (lookup p t) 0 (subst_pp f t)) \<subseteq> keys (0::('a \<Rightarrow>\<^sub>0 nat)) \<union> indets (subst_pp f t)"
    by (rule indets_monom_mult_subset)
  also have "... = indets (subst_pp f t)" by simp
  finally obtain y where "y \<in> keys t" and "x \<in> indets (f y)" by (rule in_indets_subst_ppE)
  from this(1) \<open>t \<in> keys p\<close> have "y \<in> indets p" by (rule in_indetsI)
  from this \<open>x \<in> indets (f y)\<close> show ?thesis ..
qed

lemma poly_deg_poly_subst_eq_zeroI:
  assumes "\<And>x. x \<in> indets p \<Longrightarrow> poly_deg (f x) = 0"
  shows "poly_deg (poly_subst (f::_ \<Rightarrow> (('y \<Rightarrow>\<^sub>0 _) \<Rightarrow>\<^sub>0 _)) (p::('x \<Rightarrow>\<^sub>0 _) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)) = 0"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  have "poly_deg (poly_subst f p) \<le> Max (poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
    unfolding poly_subst_def by (fact poly_deg_sum_le)
  also have "... \<le> 0"
  proof (rule Max.boundedI)
    show "finite (poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
      by (simp add: finite_image_iff)
  next
    from False show "poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p \<noteq> {}" by simp
  next
    fix d
    assume "d \<in> poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p"
    then obtain t where "t \<in> keys p" and d: "d = poly_deg (punit.monom_mult (lookup p t) 0 (subst_pp f t))"
      by fastforce
    have "d \<le> deg_pm (0::'y \<Rightarrow>\<^sub>0 nat) + poly_deg (subst_pp f t)"
      unfolding d by (fact poly_deg_monom_mult_le)
    also have "... = poly_deg (subst_pp f t)" by simp
    also have "... = 0" by (rule poly_deg_subst_pp_eq_zeroI, rule assms, erule in_indetsI, fact)
    finally show "d \<le> 0" .
  qed
  finally show ?thesis by simp
qed

lemma poly_deg_poly_subst_le:
  assumes "\<And>x. x \<in> indets p \<Longrightarrow> poly_deg (f x) \<le> 1"
  shows "poly_deg (poly_subst (f::_ \<Rightarrow> (('y \<Rightarrow>\<^sub>0 _) \<Rightarrow>\<^sub>0 _)) (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)) \<le> poly_deg p"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  have "poly_deg (poly_subst f p) \<le> Max (poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
    unfolding poly_subst_def by (fact poly_deg_sum_le)
  also have "... \<le> poly_deg p"
  proof (rule Max.boundedI)
    show "finite (poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
      by (simp add: finite_image_iff)
  next
    from False show "poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p \<noteq> {}" by simp
  next
    fix d
    assume "d \<in> poly_deg ` (\<lambda>t. punit.monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p"
    then obtain t where "t \<in> keys p" and d: "d = poly_deg (punit.monom_mult (lookup p t) 0 (subst_pp f t))"
      by fastforce
    have "d \<le> deg_pm (0::'y \<Rightarrow>\<^sub>0 nat) + poly_deg (subst_pp f t)"
      unfolding d by (fact poly_deg_monom_mult_le)
    also have "... = poly_deg (subst_pp f t)" by simp
    also have "... \<le> deg_pm t" by (rule poly_deg_subst_pp_le, rule assms, erule in_indetsI, fact)
    also from \<open>t \<in> keys p\<close> have "... \<le> poly_deg p" by (rule poly_deg_max_keys)
    finally show "d \<le> poly_deg p" .
  qed
  finally show ?thesis by simp
qed

lemma subst_pp_cong: "s = t \<Longrightarrow> (\<And>x. x \<in> keys t \<Longrightarrow> f x = g x) \<Longrightarrow> subst_pp f s = subst_pp g t"
  by (simp add: subst_pp_def)

lemma poly_subst_cong:
  assumes "p = q" and "\<And>x. x \<in> indets q \<Longrightarrow> f x = g x"
  shows "poly_subst f p = poly_subst g q"
proof (simp add: poly_subst_def assms(1), rule sum.cong)
  fix t
  assume "t \<in> keys q"
  {
    fix x
    assume "x \<in> keys t"
    with \<open>t \<in> keys q\<close> have "x \<in> indets q" by (auto simp: indets_def)
    hence "f x = g x" by (rule assms(2))
  }
  thus "punit.monom_mult (lookup q t) 0 (subst_pp f t) = punit.monom_mult (lookup q t) 0 (subst_pp g t)"
    by (simp cong: subst_pp_cong)
qed (fact refl)

lemma Polys_homomorphismE:
  obtains h where "\<And>p q. h (p + q) = h p + h q" and "\<And>p q. h (p * q) = h p * h q"
    and "\<And>p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1. h (h p) = h p" and "range h = P[X]"
proof -
  let ?f = "\<lambda>x. if x \<in> X then monomial (1::'a) (Poly_Mapping.single x 1) else 1"

  have 1: "poly_subst ?f p = p" if "p \<in> P[X]" for p
  proof (rule poly_subst_id)
    fix x
    assume "x \<in> indets p"
    also from that have "\<dots> \<subseteq> X" by (rule PolysD)
    finally show "?f x = monomial 1 (Poly_Mapping.single x 1)" by simp
  qed

  have 2: "poly_subst ?f p \<in> P[X]" for p
  proof (intro PolysI_alt subsetI)
    fix x
    assume "x \<in> indets (poly_subst ?f p)"
    then obtain y where "x \<in> indets (?f y)" by (rule in_indets_poly_substE)
    thus "x \<in> X" by (simp add: indets_monomial split: if_split_asm)
  qed

  from poly_subst_plus poly_subst_times show ?thesis
  proof
    fix p
    from 2 show "poly_subst ?f (poly_subst ?f p) = poly_subst ?f p" by (rule 1)
  next
    show "range (poly_subst ?f) = P[X]"
    proof (intro set_eqI iffI)
      fix p :: "_ \<Rightarrow>\<^sub>0 'a"
      assume "p \<in> P[X]"
      hence "p = poly_subst ?f p" by (simp only: 1)
      thus "p \<in> range (poly_subst ?f)" by (rule image_eqI) simp
    qed (auto intro: 2)
  qed
qed

lemma in_idealE_Polys_finite:
  assumes "finite B" and "B \<subseteq> P[X]" and "p \<in> P[X]" and "(p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) \<in> ideal B"
  obtains q where "\<And>b. q b \<in> P[X]" and "p = (\<Sum>b\<in>B. q b * b)"
proof -
  obtain h where "\<And>p q. h (p + q) = h p + h q" and "\<And>p q. h (p * q) = h p * h q"
    and "\<And>p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a. h (h p) = h p" and rng[symmetric]: "range h = P[X]"
    by (rule Polys_homomorphismE) blast
  from this(1-3) assms obtain q where "\<And>b. q b \<in> P[X]" and "p = (\<Sum>b\<in>B. q b * b)"
    unfolding rng by (rule in_idealE_homomorphism_finite) blast
  thus ?thesis ..
qed

corollary in_idealE_Polys:
  assumes "B \<subseteq> P[X]" and "p \<in> P[X]" and "p \<in> ideal B"
  obtains A q where "finite A" and "A \<subseteq> B" and "\<And>b. q b \<in> P[X]" and "p = (\<Sum>b\<in>A. q b * b)"
proof -
  from assms(3) obtain A where "finite A" and "A \<subseteq> B" and "p \<in> ideal A"
    by (rule ideal.span_finite_subset)
  from this(2) assms(1) have "A \<subseteq> P[X]" by (rule subset_trans)
  with \<open>finite A\<close> obtain q where "\<And>b. q b \<in> P[X]" and "p = (\<Sum>b\<in>A. q b * b)"
    using assms(2) \<open>p \<in> ideal A\<close> by (rule in_idealE_Polys_finite) blast
  with \<open>finite A\<close> \<open>A \<subseteq> B\<close> show ?thesis ..
qed

lemma ideal_induct_Polys [consumes 3, case_names 0 plus]:
  assumes "F \<subseteq> P[X]" and "p \<in> P[X]" and "p \<in> ideal F"
  assumes "P 0" and "\<And>c q h. c \<in> P[X] \<Longrightarrow> q \<in> F \<Longrightarrow> P h \<Longrightarrow> h \<in> P[X] \<Longrightarrow> P (c * q + h)"
  shows "P (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1)"
proof -
  obtain h where "\<And>p q. h (p + q) = h p + h q" and "\<And>p q. h (p * q) = h p * h q"
    and "\<And>p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a. h (h p) = h p" and rng[symmetric]: "range h = P[X]"
    by (rule Polys_homomorphismE) blast
  from this(1-3) assms show ?thesis
    unfolding rng by (rule ideal_induct_homomorphism) blast
qed

lemma image_poly_subst_ideal_subset: "poly_subst g ` ideal F \<subseteq> ideal (poly_subst g ` F)"
proof (intro subsetI, elim imageE)
  fix h f
  assume h: "h = poly_subst g f"
  assume "f \<in> ideal F"
  thus "h \<in> ideal (poly_subst g ` F)" unfolding h
  proof (induct f rule: ideal.span_induct_alt)
    case base
    show ?case by (simp add: ideal.span_zero)
  next
    case (step c f h)
    from step.hyps(1) have "poly_subst g f \<in> ideal (poly_subst g ` F)"
      by (intro ideal.span_base imageI)
    hence "poly_subst g c * poly_subst g f \<in> ideal (poly_subst g ` F)" by (rule ideal.span_scale)
    hence "poly_subst g c * poly_subst g f + poly_subst g h \<in> ideal (poly_subst g ` F)"
      using step.hyps(2) by (rule ideal.span_add)
    thus ?case by (simp only: poly_subst_plus poly_subst_times)
  qed
qed

subsection \<open>Evaluating Polynomials\<close>

lemma lookup_times_zero:
  "lookup (p * q) 0 = lookup p 0 * lookup q (0::'a::{comm_powerprod,ninv_comm_monoid_add})"
proof -
  have eq: "(\<Sum>v\<in>keys q. lookup q v when t + v = 0) = (lookup q 0 when t = 0)" for t
  proof -
    have "(\<Sum>v\<in>keys q. lookup q v when t + v = 0) = (\<Sum>v\<in>keys q \<inter> {0}. lookup q v when t + v = 0)"
    proof (intro sum.mono_neutral_right ballI)
      fix v
      assume "v \<in> keys q - keys q \<inter> {0}"
      hence "v \<noteq> 0" by blast
      hence "t + v \<noteq> 0" using plus_eq_zero_2 by blast
      thus "(lookup q v when t + v = 0) = 0" by simp
    qed simp_all
    also have "\<dots> = (lookup q 0 when t = 0)" by (cases "0 \<in> keys q") simp_all
    finally show ?thesis .
  qed
  have "(\<Sum>t\<in>keys p. lookup p t * lookup q 0 when t = 0) =
          (\<Sum>t\<in>keys p \<inter> {0}. lookup p t * lookup q 0 when t = 0)"
  proof (intro sum.mono_neutral_right ballI)
    fix t
    assume "t \<in> keys p - keys p \<inter> {0}"
    hence "t \<noteq> 0" by blast
    thus "(lookup p t * lookup q 0 when t = 0) = 0" by simp
  qed simp_all
  also have "\<dots> = lookup p 0 * lookup q 0" by (cases "0 \<in> keys p") simp_all
  finally show ?thesis by (simp add: lookup_times eq when_distrib)
qed

corollary lookup_prod_zero:
  "lookup (prod f I) 0 = (\<Prod>i\<in>I. lookup (f i) (0::_::{comm_powerprod,ninv_comm_monoid_add}))"
  by (induct I rule: infinite_finite_induct) (simp_all add: lookup_times_zero)

corollary lookup_power_zero:
  "lookup (p ^ k) 0 = lookup p (0::_::{comm_powerprod,ninv_comm_monoid_add}) ^ k"
  by (induct k) (simp_all add: lookup_times_zero)

definition eval_pm :: "('x \<Rightarrow> 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> 'a::comm_semiring_1"
  where "eval_pm a p = lookup (poly_subst (\<lambda>y. monomial (a y) (0::'x \<Rightarrow>\<^sub>0 nat)) p) 0"

lemma eval_pm_alt: "eval_pm a p = (\<Sum>t\<in>keys p. lookup p t * (\<Prod>x\<in>keys t. a x ^ lookup t x))"
  by (simp add: eval_pm_def poly_subst_def lookup_sum lookup_times_zero subst_pp_def
          lookup_prod_zero lookup_power_zero flip: times_monomial_left)

lemma eval_pm_monomial: "eval_pm a (monomial c t) = c * (\<Prod>x\<in>keys t. a x ^ lookup t x)"
  by (simp add: eval_pm_def poly_subst_monomial subst_pp_def punit.lookup_monom_mult
      lookup_prod_zero lookup_power_zero)

lemma eval_pm_zero [simp]: "eval_pm a 0 = 0"
  by (simp only: eval_pm_def poly_subst_zero lookup_zero)

lemma eval_pm_zero_left [simp]: "eval_pm 0 p = lookup p 0"
  by (simp add: eval_pm_def)

lemma eval_pm_plus: "eval_pm a (p + q) = eval_pm a p + eval_pm a q"
  by (simp only: eval_pm_def poly_subst_plus lookup_add)

lemma eval_pm_uminus [simp]: "eval_pm a (- p) = - eval_pm (a::_::comm_ring_1) p"
  by (simp only: eval_pm_def poly_subst_uminus lookup_uminus)

lemma eval_pm_minus: "eval_pm a (p - q) = eval_pm a p - eval_pm (a::_::comm_ring_1) q"
  by (simp only: eval_pm_def poly_subst_minus lookup_minus)

lemma eval_pm_one [simp]: "eval_pm a 1 = 1"
  by (simp add: eval_pm_def lookup_one)

lemma eval_pm_times: "eval_pm a (p * q) = eval_pm a p * eval_pm a q"
  by (simp only: eval_pm_def poly_subst_times lookup_times_zero)

lemma eval_pm_power: "eval_pm a (p ^ m) = eval_pm a p ^ m"
  by (induct m) (simp_all add: eval_pm_times)

lemma eval_pm_sum: "eval_pm a (sum f I) = (\<Sum>i\<in>I. eval_pm a (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: eval_pm_plus)

lemma eval_pm_prod: "eval_pm a (prod f I) = (\<Prod>i\<in>I. eval_pm a (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: eval_pm_times)

lemma eval_pm_cong: "p = q \<Longrightarrow> (\<And>x. x \<in> indets q \<Longrightarrow> a x = b x) \<Longrightarrow> eval_pm a p = eval_pm b q"
  by (simp add: eval_pm_def cong: poly_subst_cong)

lemma indets_eval_pm_subset:
  "indets (eval_pm a p) \<subseteq> \<Union> (indets ` a ` indets p) \<union> \<Union> (indets ` lookup p ` keys p)"
proof (induct p rule: poly_mapping_plus_induct)
  case 1
  show ?case by simp
next
  case (2 p c t)
  have "keys (monomial c t + p) = keys (monomial c t) \<union> keys p"
    by (rule keys_plus_eqI) (simp add: 2(2))
  with 2(1) have eq1: "keys (monomial c t + p) = insert t (keys p)" by simp
  hence eq2: "indets (monomial c t + p) = keys t \<union> indets p" by (simp add: indets_def)
  from 2(2) have eq3: "lookup (monomial c t + p) t = c" by (simp add: lookup_add)
  have eq4: "lookup (monomial c t + p) s = lookup p s" if "s \<in> keys p" for s
    using that 2(2) by (auto simp: lookup_add lookup_single when_def)
  have "indets (eval_pm a (monomial c t + p)) =
          indets (c * (\<Prod>x\<in>keys t. a x ^ lookup t x) + eval_pm a p)"
    by (simp only: eval_pm_plus eval_pm_monomial)
  also have "\<dots> \<subseteq> indets (c * (\<Prod>x\<in>keys t. a x ^ lookup t x)) \<union> indets (eval_pm a p)"
    by (fact indets_plus_subset)
  also have "\<dots> \<subseteq> indets c \<union> (\<Union> (indets ` a ` keys t)) \<union>
                    (\<Union> (indets ` a ` indets p) \<union> \<Union> (indets ` lookup p ` keys p))"
  proof (intro Un_mono 2(3))
    have "indets (c * (\<Prod>x\<in>keys t. a x ^ lookup t x)) \<subseteq> indets c \<union> indets (\<Prod>x\<in>keys t. a x ^ lookup t x)"
      by (fact indets_times_subset)
    also have "indets (\<Prod>x\<in>keys t. a x ^ lookup t x) \<subseteq> (\<Union>x\<in>keys t. indets (a x ^ lookup t x))"
      by (fact indets_prod_subset)
    also have "\<dots> \<subseteq> (\<Union>x\<in>keys t. indets (a x))" by (intro UN_mono subset_refl indets_power_subset)
    also have "\<dots> = \<Union> (indets ` a ` keys t)" by simp
    finally show "indets (c * (\<Prod>x\<in>keys t. a x ^ lookup t x)) \<subseteq> indets c \<union> \<Union> (indets ` a ` keys t)"
      by blast
  qed
  also have "\<dots> = \<Union> (indets ` a ` indets (monomial c t + p)) \<union>
                    \<Union> (indets ` lookup (monomial c t + p) ` keys (monomial c t + p))"
    by (simp add: eq1 eq2 eq3 eq4 Un_commute Un_assoc Un_left_commute)
  finally show ?case .
qed

lemma image_eval_pm_ideal: "eval_pm a ` ideal F = ideal (eval_pm a ` F)"
proof (intro image_ideal_eq_surj eval_pm_plus eval_pm_times surjI)
  fix x
  show "eval_pm a (monomial x 0) = x" by (simp add: eval_pm_monomial)
qed

subsection \<open>Homogeneity\<close>

definition homogeneous :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<Rightarrow> bool"
  where "homogeneous p \<longleftrightarrow> (\<forall>s\<in>keys p. \<forall>t\<in>keys p. deg_pm s = deg_pm t)"

definition hom_component :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero)"
  where "hom_component p n = except p {t. deg_pm t \<noteq> n}"

definition hom_components :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set"
  where "hom_components p = hom_component p ` deg_pm ` keys p"

definition homogeneous_set :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set \<Rightarrow> bool"
  where "homogeneous_set A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>n. hom_component a n \<in> A)"

lemma homogeneousI: "(\<And>s t. s \<in> keys p \<Longrightarrow> t \<in> keys p \<Longrightarrow> deg_pm s = deg_pm t) \<Longrightarrow> homogeneous p"
  unfolding homogeneous_def by blast

lemma homogeneousD: "homogeneous p \<Longrightarrow> s \<in> keys p \<Longrightarrow> t \<in> keys p \<Longrightarrow> deg_pm s = deg_pm t"
  unfolding homogeneous_def by blast

lemma homogeneousD_poly_deg:
  assumes "homogeneous p" and "t \<in> keys p"
  shows "deg_pm t = poly_deg p"
proof (rule antisym)
  from assms(2) show "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
next
  show "poly_deg p \<le> deg_pm t"
  proof (rule poly_deg_leI)
    fix s
    assume "s \<in> keys p"
    with assms(1) have "deg_pm s = deg_pm t" using assms(2) by (rule homogeneousD)
    thus "deg_pm s \<le> deg_pm t" by simp
  qed
qed

lemma homogeneous_monomial [simp]: "homogeneous (monomial c t)"
  by (auto split: if_split_asm intro: homogeneousI)

corollary homogeneous_zero [simp]: "homogeneous 0" and homogeneous_one [simp]: "homogeneous 1"
  by (simp_all only: homogeneous_monomial flip: single_zero[of 0] single_one)

lemma homogeneous_uminus_iff [simp]: "homogeneous (- p) \<longleftrightarrow> homogeneous p"
  by (auto intro!: homogeneousI dest: homogeneousD simp: keys_uminus)

lemma homogeneous_monom_mult: "homogeneous p \<Longrightarrow> homogeneous (punit.monom_mult c t p)"
  by (auto intro!: homogeneousI elim!: punit.keys_monom_multE simp: deg_pm_plus dest: homogeneousD)

lemma homogeneous_monom_mult_rev:
  assumes "c \<noteq> (0::'a::semiring_no_zero_divisors)" and "homogeneous (punit.monom_mult c t p)"
  shows "homogeneous p"
proof (rule homogeneousI)
  fix s s'
  assume "s \<in> keys p"
  hence 1: "t + s \<in> keys (punit.monom_mult c t p)"
    using assms(1) by (rule punit.keys_monom_multI[simplified])
  assume "s' \<in> keys p"
  hence "t + s' \<in> keys (punit.monom_mult c t p)"
    using assms(1) by (rule punit.keys_monom_multI[simplified])
  with assms(2) 1 have "deg_pm (t + s) = deg_pm (t + s')" by (rule homogeneousD)
  thus "deg_pm s = deg_pm s'" by (simp add: deg_pm_plus)
qed

lemma homogeneous_times:
  assumes "homogeneous p" and "homogeneous q"
  shows "homogeneous (p * q)"
proof (rule homogeneousI)
  fix s t
  assume "s \<in> keys (p * q)"
  then obtain sp sq where sp: "sp \<in> keys p" and sq: "sq \<in> keys q" and s: "s = sp + sq"
    by (rule in_keys_timesE)
  assume "t \<in> keys (p * q)"
  then obtain tp tq where tp: "tp \<in> keys p" and tq: "tq \<in> keys q" and t: "t = tp + tq"
    by (rule in_keys_timesE)
  from assms(1) sp tp have "deg_pm sp = deg_pm tp" by (rule homogeneousD)
  moreover from assms(2) sq tq have "deg_pm sq = deg_pm tq" by (rule homogeneousD)
  ultimately show "deg_pm s = deg_pm t" by (simp only: s t deg_pm_plus)
qed

lemma lookup_hom_component: "lookup (hom_component p n) = (\<lambda>t. lookup p t when deg_pm t = n)"
  by (rule ext) (simp add: hom_component_def lookup_except)

lemma keys_hom_component: "keys (hom_component p n) = {t. t \<in> keys p \<and> deg_pm t = n}"
  by (auto simp: hom_component_def keys_except)

lemma keys_hom_componentD:
  assumes "t \<in> keys (hom_component p n)"
  shows "t \<in> keys p" and "deg_pm t = n"
  using assms by (simp_all add: keys_hom_component)

lemma homogeneous_hom_component: "homogeneous (hom_component p n)"
  by (auto dest: keys_hom_componentD intro: homogeneousI)

lemma hom_component_zero [simp]: "hom_component 0 = 0"
  by (rule ext) (simp add: hom_component_def)

lemma hom_component_zero_iff: "hom_component p n = 0 \<longleftrightarrow> (\<forall>t\<in>keys p. deg_pm t \<noteq> n)"
  by (metis (mono_tags, lifting) empty_iff keys_eq_empty_iff keys_hom_component mem_Collect_eq subsetI subset_antisym)

lemma hom_component_uminus [simp]: "hom_component (- p) = - hom_component p"
  by (intro ext poly_mapping_eqI) (simp add: hom_component_def lookup_except)

lemma hom_component_plus: "hom_component (p + q) n = hom_component p n + hom_component q n"
  by (rule poly_mapping_eqI) (simp add: hom_component_def lookup_except lookup_add)

lemma hom_component_minus: "hom_component (p - q) n = hom_component p n - hom_component q n"
  by (rule poly_mapping_eqI) (simp add: hom_component_def lookup_except lookup_minus)

lemma hom_component_monom_mult:
  "punit.monom_mult c t (hom_component p n) = hom_component (punit.monom_mult c t p) (deg_pm t + n)"
  by (auto simp: hom_component_def lookup_except punit.lookup_monom_mult deg_pm_minus deg_pm_mono intro!: poly_mapping_eqI)

lemma hom_component_inject:
  assumes "t \<in> keys p" and "hom_component p (deg_pm t) = hom_component p n"
  shows "deg_pm t = n"
proof -
  from assms(1) have "t \<in> keys (hom_component p (deg_pm t))" by (simp add: keys_hom_component)
  hence "0 \<noteq> lookup (hom_component p (deg_pm t)) t" by simp
  also have "lookup (hom_component p (deg_pm t)) t = lookup (hom_component p n) t"
    by (simp only: assms(2))
  also have "\<dots> = (lookup p t when deg_pm t = n)" by (simp only: lookup_hom_component)
  finally show ?thesis by simp
qed

lemma hom_component_of_homogeneous:
  assumes "homogeneous p"
  shows "hom_component p n = (p when n = poly_deg p)"
proof (cases "n = poly_deg p")
  case True
  have "hom_component p n = p"
  proof (rule poly_mapping_eqI)
    fix t
    show "lookup (hom_component p n) t = lookup p t"
    proof (cases "t \<in> keys p")
      case True
      with assms have "deg_pm t = n" unfolding \<open>n = poly_deg p\<close> by (rule homogeneousD_poly_deg)
      thus ?thesis by (simp add: lookup_hom_component)
    next
      case False
      moreover from this have "t \<notin> keys (hom_component p n)" by (simp add: keys_hom_component)
      ultimately show ?thesis by simp
    qed
  qed
  with True show ?thesis by simp
next
  case False
  have "hom_component p n = 0" unfolding hom_component_zero_iff
  proof (intro ballI notI)
    fix t
    assume "t \<in> keys p"
    with assms have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
    moreover assume "deg_pm t = n"
    ultimately show False using False by simp
  qed
  with False show ?thesis by simp
qed

lemma hom_components_zero [simp]: "hom_components 0 = {}"
  by (simp add: hom_components_def)

lemma hom_components_zero_iff [simp]: "hom_components p = {} \<longleftrightarrow> p = 0"
  by (simp add: hom_components_def)

lemma hom_components_uminus: "hom_components (- p) = uminus ` hom_components p"
  by (simp add: hom_components_def keys_uminus image_image)

lemma hom_components_monom_mult:
  "hom_components (punit.monom_mult c t p) = (if c = 0 then {} else punit.monom_mult c t ` hom_components p)"
  for c::"'a::semiring_no_zero_divisors"
  by (simp add: hom_components_def punit.keys_monom_mult image_image deg_pm_plus hom_component_monom_mult)

lemma hom_componentsI: "q = hom_component p (deg_pm t) \<Longrightarrow> t \<in> keys p \<Longrightarrow> q \<in> hom_components p"
  unfolding hom_components_def by blast

lemma hom_componentsE:
  assumes "q \<in> hom_components p"
  obtains t where "t \<in> keys p" and "q = hom_component p (deg_pm t)"
  using assms unfolding hom_components_def by blast

lemma hom_components_of_homogeneous:
  assumes "homogeneous p"
  shows "hom_components p = (if p = 0 then {} else {p})"
proof (split if_split, intro conjI impI)
  assume "p \<noteq> 0"
  have "deg_pm ` keys p = {poly_deg p}"
  proof (rule set_eqI)
    fix n
    have "n \<in> deg_pm ` keys p \<longleftrightarrow> n = poly_deg p"
    proof
      assume "n \<in> deg_pm ` keys p"
      then obtain t where "t \<in> keys p" and "n = deg_pm t" ..
      from assms this(1) have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
      thus "n = poly_deg p" by (simp only: \<open>n = deg_pm t\<close>)
    next
      assume "n = poly_deg p"
      from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" by simp
      then obtain t where "t \<in> keys p" by blast
      with assms have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
      hence "n = deg_pm t" by (simp only: \<open>n = poly_deg p\<close>)
      with \<open>t \<in> keys p\<close> show "n \<in> deg_pm ` keys p" by (rule rev_image_eqI)
    qed
    thus "n \<in> deg_pm ` keys p \<longleftrightarrow> n \<in> {poly_deg p}" by simp
  qed
  with assms show "hom_components p = {p}"
    by (simp add: hom_components_def hom_component_of_homogeneous)
qed simp

lemma finite_hom_components: "finite (hom_components p)"
  unfolding hom_components_def using finite_keys by (intro finite_imageI)

lemma hom_components_homogeneous: "q \<in> hom_components p \<Longrightarrow> homogeneous q"
  by (elim hom_componentsE) (simp only: homogeneous_hom_component)

lemma hom_components_nonzero: "q \<in> hom_components p \<Longrightarrow> q \<noteq> 0"
  by (auto elim!: hom_componentsE simp: hom_component_zero_iff)

lemma deg_pm_hom_components:
  assumes "q1 \<in> hom_components p" and "q2 \<in> hom_components p" and "t1 \<in> keys q1" and "t2 \<in> keys q2"
  shows "deg_pm t1 = deg_pm t2 \<longleftrightarrow> q1 = q2"
proof -
  from assms(1) obtain s1 where "s1 \<in> keys p" and q1: "q1 = hom_component p (deg_pm s1)"
    by (rule hom_componentsE)
  from assms(3) have t1: "deg_pm t1 = deg_pm s1" unfolding q1 by (rule keys_hom_componentD)
  from assms(2) obtain s2 where "s2 \<in> keys p" and q2: "q2 = hom_component p (deg_pm s2)"
    by (rule hom_componentsE)
  from assms(4) have t2: "deg_pm t2 = deg_pm s2" unfolding q2 by (rule keys_hom_componentD)
  from \<open>s1 \<in> keys p\<close> show ?thesis by (auto simp: q1 q2 t1 t2 dest: hom_component_inject)
qed

lemma poly_deg_hom_components:
  assumes "q1 \<in> hom_components p" and "q2 \<in> hom_components p"
  shows "poly_deg q1 = poly_deg q2 \<longleftrightarrow> q1 = q2"
proof -
  from assms(1) have "homogeneous q1" and "q1 \<noteq> 0"
    by (rule hom_components_homogeneous, rule hom_components_nonzero)
  from this(2) have "keys q1 \<noteq> {}" by simp
  then obtain t1 where "t1 \<in> keys q1" by blast
  with \<open>homogeneous q1\<close> have t1: "deg_pm t1 = poly_deg q1" by (rule homogeneousD_poly_deg)
  from assms(2) have "homogeneous q2" and "q2 \<noteq> 0"
    by (rule hom_components_homogeneous, rule hom_components_nonzero)
  from this(2) have "keys q2 \<noteq> {}" by simp
  then obtain t2 where "t2 \<in> keys q2" by blast
  with \<open>homogeneous q2\<close> have t2: "deg_pm t2 = poly_deg q2" by (rule homogeneousD_poly_deg)
  from assms \<open>t1 \<in> keys q1\<close> \<open>t2 \<in> keys q2\<close> have "deg_pm t1 = deg_pm t2 \<longleftrightarrow> q1 = q2"
    by (rule deg_pm_hom_components)
  thus ?thesis by (simp only: t1 t2)
qed

lemma hom_components_keys_disjoint:
  assumes "q1 \<in> hom_components p" and "q2 \<in> hom_components p" and "q1 \<noteq> q2"
  shows "keys q1 \<inter> keys q2 = {}"
proof (rule ccontr)
  assume "keys q1 \<inter> keys q2 \<noteq> {}"
  then obtain t where "t \<in> keys q1" and "t \<in> keys q2" by blast
  with assms(1, 2) have "deg_pm t = deg_pm t \<longleftrightarrow> q1 = q2" by (rule deg_pm_hom_components)
  with assms(3) show False by simp
qed

lemma Keys_hom_components: "Keys (hom_components p) = keys p"
  by (auto simp: Keys_def hom_components_def keys_hom_component)

lemma lookup_hom_components: "q \<in> hom_components p \<Longrightarrow> t \<in> keys q \<Longrightarrow> lookup q t = lookup p t"
  by (auto elim!: hom_componentsE simp: keys_hom_component lookup_hom_component)

lemma poly_deg_hom_components_le:
  assumes "q \<in> hom_components p"
  shows "poly_deg q \<le> poly_deg p"
proof (rule poly_deg_leI)
  fix t
  assume "t \<in> keys q"
  also from assms have "\<dots> \<subseteq> Keys (hom_components p)" by (rule keys_subset_Keys)
  also have "\<dots> = keys p" by (fact Keys_hom_components)
  finally show "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
qed

lemma sum_hom_components: "\<Sum>(hom_components p) = p"
proof (rule poly_mapping_eqI)
  fix t
  show "lookup (\<Sum>(hom_components p)) t = lookup p t" unfolding lookup_sum
  proof (cases "t \<in> keys p")
    case True
    also have "keys p = Keys (hom_components p)" by (simp only: Keys_hom_components)
    finally obtain q where q: "q \<in> hom_components p" and t: "t \<in> keys q" by (rule in_KeysE)
    from this(1) have "(\<Sum>q0\<in>hom_components p. lookup q0 t) =
                        (\<Sum>q0\<in>insert q (hom_components p). lookup q0 t)"
      by (simp only: insert_absorb)
    also from finite_hom_components have "\<dots> = lookup q t + (\<Sum>q0\<in>hom_components p - {q}. lookup q0 t)"
      by (rule sum.insert_remove)
    also from q t have "\<dots> = lookup p t + (\<Sum>q0\<in>hom_components p - {q}. lookup q0 t)"
      by (simp only: lookup_hom_components)
    also have "(\<Sum>q0\<in>hom_components p - {q}. lookup q0 t) = 0"
    proof (intro sum.neutral ballI)
      fix q0
      assume "q0 \<in> hom_components p - {q}"
      hence "q0 \<in> hom_components p" and "q \<noteq> q0" by blast+
      with q have "keys q \<inter> keys q0 = {}" by (rule hom_components_keys_disjoint)
      with t have "t \<notin> keys q0" by blast
      thus "lookup q0 t = 0" by simp
    qed
    finally show "(\<Sum>q\<in>hom_components p. lookup q t) = lookup p t" by simp
  next
    case False
    hence "t \<notin> Keys (hom_components p)" by (simp add: Keys_hom_components)
    hence "\<forall>q\<in>hom_components p. lookup q t = 0" by (simp add: Keys_def)
    hence "(\<Sum>q\<in>hom_components p. lookup q t) = 0" by (rule sum.neutral)
    also from False have "\<dots> = lookup p t" by simp
    finally show "(\<Sum>q\<in>hom_components p. lookup q t) = lookup p t" .
  qed
qed

lemma homogeneous_setI: "(\<And>a n. a \<in> A \<Longrightarrow> hom_component a n \<in> A) \<Longrightarrow> homogeneous_set A"
  by (simp add: homogeneous_set_def)

lemma homogeneous_setD: "homogeneous_set A \<Longrightarrow> a \<in> A \<Longrightarrow> hom_component a n \<in> A"
  by (simp add: homogeneous_set_def)

lemma homogeneous_set_Polys: "homogeneous_set (P[X]::(_ \<Rightarrow>\<^sub>0 'a::zero) set)"
proof (intro homogeneous_setI PolysI subsetI)
  fix p::"_ \<Rightarrow>\<^sub>0 'a" and n t
  assume "p \<in> P[X]"
  assume "t \<in> keys (hom_component p n)"
  hence "t \<in> keys p" by (rule keys_hom_componentD)
  also from \<open>p \<in> P[X]\<close> have "\<dots> \<subseteq> .[X]" by (rule PolysD)
  finally show "t \<in> .[X]" .
qed

lemma homogeneous_set_IntI: "homogeneous_set A \<Longrightarrow> homogeneous_set B \<Longrightarrow> homogeneous_set (A \<inter> B)"
  by (simp add: homogeneous_set_def)

lemma homogeneous_setD_hom_components:
  assumes "homogeneous_set A" and "a \<in> A" and "b \<in> hom_components a"
  shows "b \<in> A"
proof -
  from assms(3) obtain t::"'a \<Rightarrow>\<^sub>0 nat" where "b = hom_component a (deg_pm t)"
    by (rule hom_componentsE)
  also from assms(1, 2) have "\<dots> \<in> A" by (rule homogeneous_setD)
  finally show ?thesis .
qed

lemma zero_in_homogeneous_set:
  assumes "homogeneous_set A" and "A \<noteq> {}"
  shows "0 \<in> A"
proof -
  from assms(2) obtain a where "a \<in> A" by blast
  have "lookup a t = 0" if "deg_pm t = Suc (poly_deg a)" for t
  proof (rule ccontr)
    assume "lookup a t \<noteq> 0"
    hence "t \<in> keys a" by simp
    hence "deg_pm t \<le> poly_deg a" by (rule poly_deg_max_keys)
    thus False by (simp add: that)
  qed
  hence "0 = hom_component a (Suc (poly_deg a))"
    by (intro poly_mapping_eqI) (simp add: lookup_hom_component when_def)
  also from assms(1) \<open>a \<in> A\<close> have "\<dots> \<in> A" by (rule homogeneous_setD)
  finally show ?thesis .
qed

lemma homogeneous_ideal:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F"
  shows "hom_component p n \<in> ideal F"
proof -
  from assms(2) have "p \<in> punit.pmdl F" by simp
  thus ?thesis
  proof (induct p rule: punit.pmdl_induct)
    case module_0
    show ?case by (simp add: ideal.span_zero)
  next
    case (module_plus a f c t)
    let ?f = "punit.monom_mult c t f"
    from module_plus.hyps(3) have "f \<in> punit.pmdl F" by (simp add: ideal.span_base)
    hence *: "?f \<in> punit.pmdl F" by (rule punit.pmdl_closed_monom_mult)
    from module_plus.hyps(3) have "homogeneous f" by (rule assms(1))
    hence "homogeneous ?f" by (rule homogeneous_monom_mult)
    hence "hom_component ?f n = (?f when n = poly_deg ?f)" by (rule hom_component_of_homogeneous)
    also from * have "\<dots> \<in> ideal F" by (simp add: when_def ideal.span_zero)
    finally have "hom_component ?f n \<in> ideal F" .
    with module_plus.hyps(2) show ?case unfolding hom_component_plus by (rule ideal.span_add)
  qed
qed

corollary homogeneous_set_homogeneous_ideal:
  "(\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> homogeneous_set (ideal F)"
  by (auto intro: homogeneous_setI homogeneous_ideal)

corollary homogeneous_ideal':
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F" and "q \<in> hom_components p"
  shows "q \<in> ideal F"
  using _ assms(2, 3)
proof (rule homogeneous_setD_hom_components)
  from assms(1) show "homogeneous_set (ideal F)" by (rule homogeneous_set_homogeneous_ideal)
qed

lemma homogeneous_idealE_homogeneous:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F" and "homogeneous p"
  obtains F' q where "finite F'" and "F' \<subseteq> F" and "p = (\<Sum>f\<in>F'. q f * f)" and "\<And>f. homogeneous (q f)"
    and "\<And>f. f \<in> F' \<Longrightarrow> poly_deg (q f * f) = poly_deg p" and "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0"
proof -
  from assms(2) obtain F'' q' where "finite F''" and "F'' \<subseteq> F" and p: "p = (\<Sum>f\<in>F''. q' f * f)"
    by (rule ideal.spanE)
  let ?A = "\<lambda>f. {h \<in> hom_components (q' f). poly_deg h + poly_deg f = poly_deg p}"
  let ?B = "\<lambda>f. {h \<in> hom_components (q' f). poly_deg h + poly_deg f \<noteq> poly_deg p}"
  define F' where "F' = {f \<in> F''. (\<Sum>(?A f)) * f \<noteq> 0}"
  define q where "q = (\<lambda>f. (\<Sum>(?A f)) when f \<in> F')"
  have "F' \<subseteq> F''" by (simp add: F'_def)
  hence "F' \<subseteq> F" using \<open>F'' \<subseteq> F\<close> by (rule subset_trans)
  have 1: "deg_pm t + poly_deg f = poly_deg p" if "f \<in> F'" and "t \<in> keys (q f)" for f t
  proof -
    from that have "t \<in> keys (\<Sum>(?A f))" by (simp add: q_def)
    also have "\<dots> \<subseteq> (\<Union>h\<in>?A f. keys h)" by (fact keys_sum_subset)
    finally obtain h where "h \<in> ?A f" and "t \<in> keys h" ..
    from this(1) have "h \<in> hom_components (q' f)" and eq: "poly_deg h + poly_deg f = poly_deg p"
      by simp_all
    from this(1) have "homogeneous h" by (rule hom_components_homogeneous)
    hence "deg_pm t = poly_deg h" using \<open>t \<in> keys h\<close> by (rule homogeneousD_poly_deg)
    thus ?thesis by (simp only: eq)
  qed
  have 2: "deg_pm t = poly_deg p" if "f \<in> F'" and "t \<in> keys (q f * f)" for f t
  proof -
    from that(1) \<open>F' \<subseteq> F\<close> have "f \<in> F" ..
    hence "homogeneous f" by (rule assms(1))
    from that(2) obtain s1 s2 where "s1 \<in> keys (q f)" and "s2 \<in> keys f" and t: "t = s1 + s2"
      by (rule in_keys_timesE)
    from that(1) this(1) have "deg_pm s1 + poly_deg f = poly_deg p" by (rule 1)
    moreover from \<open>homogeneous f\<close> \<open>s2 \<in> keys f\<close> have "deg_pm s2 = poly_deg f"
      by (rule homogeneousD_poly_deg)
    ultimately show ?thesis by (simp add: t deg_pm_plus)
  qed
  from \<open>F' \<subseteq> F''\<close> \<open>finite F''\<close> have "finite F'" by (rule finite_subset)
  thus ?thesis using \<open>F' \<subseteq> F\<close>
  proof
    note p
    also from refl have "(\<Sum>f\<in>F''. q' f * f) = (\<Sum>f\<in>F''. (\<Sum>(?A f) * f) + (\<Sum>(?B f) * f))"
    proof (rule sum.cong)
      fix f
      assume "f \<in> F''"
      from sum_hom_components have "q' f = (\<Sum>(hom_components (q' f)))" by (rule sym)
      also have "\<dots> = (\<Sum>(?A f \<union> ?B f))" by (rule arg_cong[where f="sum (\<lambda>x. x)"]) blast
      also have "\<dots> = \<Sum>(?A f) + \<Sum>(?B f)"
      proof (rule sum.union_disjoint)
        have "?A f \<subseteq> hom_components (q' f)" by blast
        thus "finite (?A f)" using finite_hom_components by (rule finite_subset)
      next
        have "?B f \<subseteq> hom_components (q' f)" by blast
        thus "finite (?B f)" using finite_hom_components by (rule finite_subset)
      qed blast
      finally show "q' f * f = (\<Sum>(?A f) * f) + (\<Sum>(?B f) * f)"
        by (metis (no_types, lifting) distrib_right)
    qed
    also have "\<dots> = (\<Sum>f\<in>F''. \<Sum>(?A f) * f) + (\<Sum>f\<in>F''. \<Sum>(?B f) * f)" by (rule sum.distrib)
    also from \<open>finite F''\<close> \<open>F' \<subseteq> F''\<close> have "(\<Sum>f\<in>F''. \<Sum>(?A f) * f) = (\<Sum>f\<in>F'. q f * f)"
    proof (intro sum.mono_neutral_cong_right ballI)
      fix f
      assume "f \<in> F'' - F'"
      thus "\<Sum>(?A f) * f = 0" by (simp add: F'_def)
    next
      fix f
      assume "f \<in> F'"
      thus "\<Sum>(?A f) * f = q f * f" by (simp add: q_def)
    qed
    finally have p[symmetric]: "p = (\<Sum>f\<in>F'. q f * f) + (\<Sum>f\<in>F''. \<Sum>(?B f) * f)" .
    moreover have "keys (\<Sum>f\<in>F''. \<Sum>(?B f) * f) = {}"
    proof (rule, rule)
      fix t
      assume t_in: "t \<in> keys (\<Sum>f\<in>F''. \<Sum>(?B f) * f)"
      also have "\<dots> \<subseteq> (\<Union>f\<in>F''. keys (\<Sum>(?B f) * f))" by (fact keys_sum_subset)
      finally obtain f where "f \<in> F''" and "t \<in> keys (\<Sum>(?B f) * f)" ..
      from this(2) obtain s1 s2 where "s1 \<in> keys (\<Sum>(?B f))" and "s2 \<in> keys f" and t: "t = s1 + s2"
        by (rule in_keys_timesE)
      from \<open>f \<in> F''\<close> \<open>F'' \<subseteq> F\<close> have "f \<in> F" ..
      hence "homogeneous f" by (rule assms(1))
      note \<open>s1 \<in> keys (\<Sum>(?B f))\<close>
      also have "keys (\<Sum>(?B f)) \<subseteq> (\<Union>h\<in>?B f. keys h)" by (fact keys_sum_subset)
      finally obtain h where "h \<in> ?B f" and "s1 \<in> keys h" ..
      from this(1) have "h \<in> hom_components (q' f)" and neq: "poly_deg h + poly_deg f \<noteq> poly_deg p"
        by simp_all
      from this(1) have "homogeneous h" by (rule hom_components_homogeneous)
      hence "deg_pm s1 = poly_deg h" using \<open>s1 \<in> keys h\<close> by (rule homogeneousD_poly_deg)
      moreover from \<open>homogeneous f\<close> \<open>s2 \<in> keys f\<close> have "deg_pm s2 = poly_deg f"
        by (rule homogeneousD_poly_deg)
      ultimately have "deg_pm t \<noteq> poly_deg p" using neq by (simp add: t deg_pm_plus)
      have "t \<notin> keys (\<Sum>f\<in>F'. q f * f)"
      proof
        assume "t \<in> keys (\<Sum>f\<in>F'. q f * f)"
        also have "\<dots> \<subseteq> (\<Union>f\<in>F'. keys (q f * f))" by (fact keys_sum_subset)
        finally obtain f where "f \<in> F'" and "t \<in> keys (q f * f)" ..
        hence "deg_pm t = poly_deg p" by (rule 2)
        with \<open>deg_pm t \<noteq> poly_deg p\<close> show False ..
      qed
      with t_in have "t \<in> keys ((\<Sum>f\<in>F'. q f * f) + (\<Sum>f\<in>F''. \<Sum>(?B f) * f))"
        by (rule in_keys_plusI2)
      hence "t \<in> keys p" by (simp only: p)
      with assms(3) have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
      with \<open>deg_pm t \<noteq> poly_deg p\<close> show "t \<in> {}" ..
    qed (fact empty_subsetI)
    ultimately show "p = (\<Sum>f\<in>F'. q f * f)" by simp
  next
    fix f
    show "homogeneous (q f)"
    proof (cases "f \<in> F'")
      case True
      show ?thesis
      proof (rule homogeneousI)
        fix s t
        assume "s \<in> keys (q f)"
        with True have *: "deg_pm s + poly_deg f = poly_deg p" by (rule 1)
        assume "t \<in> keys (q f)"
        with True have "deg_pm t + poly_deg f = poly_deg p" by (rule 1)
        with * show "deg_pm s = deg_pm t" by simp
      qed
    next
      case False
      thus ?thesis by (simp add: q_def)
    qed

    assume "f \<in> F'"
    show "poly_deg (q f * f) = poly_deg p"
    proof (intro antisym)
      show "poly_deg (q f * f) \<le> poly_deg p"
      proof (rule poly_deg_leI)
        fix t
        assume "t \<in> keys (q f * f)"
        with \<open>f \<in> F'\<close> have "deg_pm t = poly_deg p" by (rule 2)
        thus "deg_pm t \<le> poly_deg p" by simp
      qed
    next
      from \<open>f \<in> F'\<close> have "q f * f \<noteq> 0" by (simp add: q_def F'_def)
      hence "keys (q f * f) \<noteq> {}" by simp
      then obtain t where "t \<in> keys (q f * f)" by blast
      with \<open>f \<in> F'\<close> have "deg_pm t = poly_deg p" by (rule 2)
      moreover from \<open>t \<in> keys (q f * f)\<close> have "deg_pm t \<le> poly_deg (q f * f)" by (rule poly_deg_max_keys)
      ultimately show "poly_deg p \<le> poly_deg (q f * f)" by simp
    qed
  qed (simp add: q_def)
qed

corollary homogeneous_idealE:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F"
  obtains F' q where "finite F'" and "F' \<subseteq> F" and "p = (\<Sum>f\<in>F'. q f * f)"
    and "\<And>f. poly_deg (q f * f) \<le> poly_deg p" and "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0"
proof (cases "p = 0")
  case True
  show ?thesis
  proof
    show "p = (\<Sum>f\<in>{}. (\<lambda>_. 0) f * f)" by (simp add: True)
  qed simp_all
next
  case False
  define P where "P = (\<lambda>h qf. finite (fst qf) \<and> fst qf \<subseteq> F \<and> h = (\<Sum>f\<in>fst qf. snd qf f * f) \<and>
                  (\<forall>f\<in>fst qf. poly_deg (snd qf f * f) = poly_deg h) \<and> (\<forall>f. f \<notin> fst qf \<longrightarrow> snd qf f = 0))"
  define q0 where "q0 = (\<lambda>h. SOME qf. P h qf)"
  have 1: "P h (q0 h)" if "h \<in> hom_components p" for h
  proof -
    note assms(1)
    moreover from assms that have "h \<in> ideal F" by (rule homogeneous_ideal')
    moreover from that have "homogeneous h" by (rule hom_components_homogeneous)
    ultimately obtain F' q where "finite F'" and "F' \<subseteq> F" and "h = (\<Sum>f\<in>F'. q f * f)"
      and "\<And>f. f \<in> F' \<Longrightarrow> poly_deg (q f * f) = poly_deg h" and "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0"
      by (rule homogeneous_idealE_homogeneous) blast+
    hence "P h (F', q)" by (simp add: P_def)
    thus ?thesis unfolding q0_def by (rule someI)
  qed
  define F' where "F' = (\<Union>h\<in>hom_components p. fst (q0 h))"
  define q where "q = (\<lambda>f. \<Sum>h\<in>hom_components p. snd (q0 h) f)"
  show ?thesis
  proof
    have "finite F' \<and> F' \<subseteq> F" unfolding F'_def UN_subset_iff finite_UN[OF finite_hom_components]
    proof (intro conjI ballI)
      fix h
      assume "h \<in> hom_components p"
      hence "P h (q0 h)" by (rule 1)
      thus "finite (fst (q0 h))" and "fst (q0 h) \<subseteq> F" by (simp_all only: P_def)
    qed
    thus "finite F'" and "F' \<subseteq> F" by simp_all

    from sum_hom_components have "p = (\<Sum>(hom_components p))" by (rule sym)
    also from refl have "\<dots> = (\<Sum>h\<in>hom_components p. \<Sum>f\<in>F'. snd (q0 h) f * f)"
    proof (rule sum.cong)
      fix h
      assume "h \<in> hom_components p"
      hence "P h (q0 h)" by (rule 1)
      hence "h = (\<Sum>f\<in>fst (q0 h). snd (q0 h) f * f)" and 2: "\<And>f. f \<notin> fst (q0 h) \<Longrightarrow> snd (q0 h) f = 0"
        by (simp_all add: P_def)
      note this(1)
      also from \<open>finite F'\<close> have "(\<Sum>f\<in>fst (q0 h). (snd (q0 h)) f * f) = (\<Sum>f\<in>F'. snd (q0 h) f * f)"
      proof (intro sum.mono_neutral_left ballI)
        show "fst (q0 h) \<subseteq> F'" unfolding F'_def using \<open>h \<in> hom_components p\<close> by blast
      next
        fix f
        assume "f \<in> F' - fst (q0 h)"
        hence "f \<notin> fst (q0 h)" by simp
        hence "snd (q0 h) f = 0" by (rule 2)
        thus "snd (q0 h) f * f = 0" by simp
      qed
      finally show "h = (\<Sum>f\<in>F'. snd (q0 h) f * f)" .
    qed
    also have "\<dots> = (\<Sum>f\<in>F'. \<Sum>h\<in>hom_components p. snd (q0 h) f * f)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>f\<in>F'. q f * f)" by (simp only: q_def sum_distrib_right)
    finally show "p = (\<Sum>f\<in>F'. q f * f)" .

    fix f
    have "poly_deg (q f * f) = poly_deg (\<Sum>h\<in>hom_components p. snd (q0 h) f * f)"
      by (simp only: q_def sum_distrib_right)
    also have "\<dots> \<le> Max (poly_deg ` (\<lambda>h. snd (q0 h) f * f) ` hom_components p)"
      by (rule poly_deg_sum_le)
    also have "\<dots> = Max ((\<lambda>h. poly_deg (snd (q0 h) f * f)) ` hom_components p)"
      (is "_ = Max (?f ` _)") by (simp only: image_image)
    also have "\<dots> \<le> poly_deg p"
    proof (rule Max.boundedI)
      from finite_hom_components show "finite (?f ` hom_components p)" by (rule finite_imageI)
    next
      from False show "?f ` hom_components p \<noteq> {}" by simp
    next
      fix d
      assume "d \<in> ?f ` hom_components p"
      then obtain h where "h \<in> hom_components p" and d: "d = ?f h" ..
      from this(1) have "P h (q0 h)" by (rule 1)
      hence 2: "\<And>f. f \<in> fst (q0 h) \<Longrightarrow> poly_deg (snd (q0 h) f * f) = poly_deg h"
        and 3: "\<And>f. f \<notin> fst (q0 h) \<Longrightarrow> snd (q0 h) f = 0" by (simp_all add: P_def)
      show "d \<le> poly_deg p"
      proof (cases "f \<in> fst (q0 h)")
        case True
        hence "poly_deg (snd (q0 h) f * f) = poly_deg h" by (rule 2)
        hence "d = poly_deg h" by (simp only: d)
        also from \<open>h \<in> hom_components p\<close> have "\<dots> \<le> poly_deg p" by (rule poly_deg_hom_components_le)
        finally show ?thesis .
      next
        case False
        hence "snd (q0 h) f = 0" by (rule 3)
        thus ?thesis by (simp add: d)
      qed
    qed
    finally show "poly_deg (q f * f) \<le> poly_deg p" .

    assume "f \<notin> F'"
    show "q f = 0" unfolding q_def
    proof (intro sum.neutral ballI)
      fix h
      assume "h \<in> hom_components p"
      hence "P h (q0 h)" by (rule 1)
      hence 2: "\<And>f. f \<notin> fst (q0 h) \<Longrightarrow> snd (q0 h) f = 0" by (simp add: P_def)
      show "snd (q0 h) f = 0"
      proof (intro 2 notI)
        assume "f \<in> fst (q0 h)"
        hence "f \<in> F'" unfolding F'_def using \<open>h \<in> hom_components p\<close> by blast
        with \<open>f \<notin> F'\<close> show False ..
      qed
    qed
  qed
qed

corollary homogeneous_idealE_finite:
  assumes "finite F" and "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F"
  obtains q where "p = (\<Sum>f\<in>F. q f * f)" and "\<And>f. poly_deg (q f * f) \<le> poly_deg p"
    and "\<And>f. f \<notin> F \<Longrightarrow> q f = 0"
proof -
  from assms(2, 3) obtain F' q where "F' \<subseteq> F" and p: "p = (\<Sum>f\<in>F'. q f * f)"
    and "\<And>f. poly_deg (q f * f) \<le> poly_deg p" and 1: "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0"
    by (rule homogeneous_idealE) blast+
  show ?thesis
  proof
    from assms(1) \<open>F' \<subseteq> F\<close> have "(\<Sum>f\<in>F'. q f * f) = (\<Sum>f\<in>F. q f * f)"
    proof (intro sum.mono_neutral_left ballI)
      fix f
      assume "f \<in> F - F'"
      hence "f \<notin> F'" by simp
      hence "q f = 0" by (rule 1)
      thus "q f * f = 0" by simp
    qed
    thus "p = (\<Sum>f\<in>F. q f * f)" by (simp only: p)
  next
    fix f
    show "poly_deg (q f * f) \<le> poly_deg p" by fact

    assume "f \<notin> F"
    with \<open>F' \<subseteq> F\<close> have "f \<notin> F'" by blast
    thus "q f = 0" by (rule 1)
  qed
qed

subsubsection \<open>Homogenization and Dehomogenization\<close>

definition homogenize :: "'x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::semiring_1)"
  where "homogenize x p = (\<Sum>t\<in>keys p. monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t))"

definition dehomo_subst :: "'x \<Rightarrow> 'x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero_neq_one)"
  where "dehomo_subst x = (\<lambda>y. if y = x then 1 else monomial 1 (Poly_Mapping.single y 1))"

definition dehomogenize :: "'x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
  where "dehomogenize x = poly_subst (dehomo_subst x)"

lemma homogenize_zero [simp]: "homogenize x 0 = 0"
  by (simp add: homogenize_def)

lemma homogenize_uminus [simp]: "homogenize x (- p) = - homogenize x (p::_ \<Rightarrow>\<^sub>0 'a::ring_1)"
  by (simp add: homogenize_def keys_uminus sum.reindex inj_on_def single_uminus sum_negf)

lemma homogenize_monom_mult [simp]:
  "homogenize x (punit.monom_mult c t p) = punit.monom_mult c t (homogenize x p)"
  for c::"'a::{semiring_1,semiring_no_zero_divisors_cancel}"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "c = 0")
    case True
    thus ?thesis by simp
  next
    case False
    show ?thesis
      by (simp add: homogenize_def punit.keys_monom_mult \<open>p \<noteq> 0\<close> False sum.reindex
          punit.lookup_monom_mult punit.monom_mult_sum_right poly_deg_monom_mult
          punit.monom_mult_monomial ac_simps deg_pm_plus)
  qed
qed

lemma homogenize_alt:
  "homogenize x p = (\<Sum>q\<in>hom_components p. punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q)"
proof -
  have "homogenize x p = (\<Sum>t\<in>Keys (hom_components p). monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t))"
    by (simp only: homogenize_def Keys_hom_components)
  also have "\<dots> = (\<Sum>t\<in>(\<Union> (keys ` hom_components p)). monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t))"
    by (simp only: Keys_def)
  also have "\<dots> = (\<Sum>q\<in>hom_components p. (\<Sum>t\<in>keys q. monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t)))"
    by (auto intro!: sum.UNION_disjoint finite_hom_components finite_keys dest: hom_components_keys_disjoint)
  also have "\<dots> = (\<Sum>q\<in>hom_components p. punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q)"
    using refl
  proof (rule sum.cong)
    fix q
    assume q: "q \<in> hom_components p"
    hence "homogeneous q" by (rule hom_components_homogeneous)
    have "(\<Sum>t\<in>keys q. monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t)) =
          (\<Sum>t\<in>keys q. punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) (monomial (lookup q t) t))"
      using refl
    proof (rule sum.cong)
      fix t
      assume "t \<in> keys q"
      with \<open>homogeneous q\<close> have "deg_pm t = poly_deg q" by (rule homogeneousD_poly_deg)
      moreover from q \<open>t \<in> keys q\<close> have "lookup q t = lookup p t" by (rule lookup_hom_components)
      ultimately show "monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t) =
            punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) (monomial (lookup q t) t)"
        by (simp add: punit.monom_mult_monomial)
    qed
    also have "\<dots> = punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q"
      by (simp only: poly_mapping_sum_monomials flip: punit.monom_mult_sum_right)
    finally show "(\<Sum>t\<in>keys q. monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t)) =
                  punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q" .
  qed
  finally show ?thesis .
qed

lemma keys_homogenizeE:
  assumes "t \<in> keys (homogenize x p)"
  obtains t' where "t' \<in> keys p" and "t = Poly_Mapping.single x (poly_deg p - deg_pm t') + t'"
proof -
  note assms
  also have "keys (homogenize x p) \<subseteq>
            (\<Union>t\<in>keys p. keys (monomial (lookup p t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t)))"
    unfolding homogenize_def by (rule keys_sum_subset)
  finally obtain t' where "t' \<in> keys p"
    and "t \<in> keys (monomial (lookup p t') (Poly_Mapping.single x (poly_deg p - deg_pm t') + t'))" ..
  from this(2) have "t = Poly_Mapping.single x (poly_deg p - deg_pm t') + t'"
    by (simp split: if_split_asm)
  with \<open>t' \<in> keys p\<close> show ?thesis ..
qed

lemma keys_homogenizeE_alt:
  assumes "t \<in> keys (homogenize x p)"
  obtains q t' where "q \<in> hom_components p" and "t' \<in> keys q"
    and "t = Poly_Mapping.single x (poly_deg p - poly_deg q) + t'"
proof -
  note assms
  also have "keys (homogenize x p) \<subseteq>
            (\<Union>q\<in>hom_components p. keys (punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q))"
    unfolding homogenize_alt by (rule keys_sum_subset)
  finally obtain q where q: "q \<in> hom_components p"
    and "t \<in> keys (punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q)" ..
  note this(2)
  also have "\<dots> \<subseteq> (+) (Poly_Mapping.single x (poly_deg p - poly_deg q)) ` keys q"
    by (rule punit.keys_monom_mult_subset[simplified])
  finally obtain t' where "t' \<in> keys q" and "t = Poly_Mapping.single x (poly_deg p - poly_deg q) + t'" ..
  with q show ?thesis ..
qed

lemma deg_pm_homogenize:
  assumes "t \<in> keys (homogenize x p)"
  shows "deg_pm t = poly_deg p"
proof -
  from assms obtain q t' where q: "q \<in> hom_components p" and "t' \<in> keys q"
    and t: "t = Poly_Mapping.single x (poly_deg p - poly_deg q) + t'" by (rule keys_homogenizeE_alt)
  from q have "homogeneous q" by (rule hom_components_homogeneous)
  hence "deg_pm t' = poly_deg q" using \<open>t' \<in> keys q\<close> by (rule homogeneousD_poly_deg)
  moreover from q have "poly_deg q \<le> poly_deg p" by (rule poly_deg_hom_components_le)
  ultimately show ?thesis by (simp add: t deg_pm_plus deg_pm_single)
qed

corollary homogeneous_homogenize: "homogeneous (homogenize x p)"
proof (rule homogeneousI)
  fix s t
  assume "s \<in> keys (homogenize x p)"
  hence *: "deg_pm s = poly_deg p" by (rule deg_pm_homogenize)
  assume "t \<in> keys (homogenize x p)"
  hence "deg_pm t = poly_deg p" by (rule deg_pm_homogenize)
  with * show "deg_pm s = deg_pm t" by simp
qed

corollary poly_deg_homogenize_le: "poly_deg (homogenize x p) \<le> poly_deg p"
proof (rule poly_deg_leI)
  fix t
  assume "t \<in> keys (homogenize x p)"
  hence "deg_pm t = poly_deg p" by (rule deg_pm_homogenize)
  thus "deg_pm t \<le> poly_deg p" by simp
qed

lemma homogenize_id_iff [simp]: "homogenize x p = p \<longleftrightarrow> homogeneous p"
proof
  assume "homogenize x p = p"
  moreover have "homogeneous (homogenize x p)" by (fact homogeneous_homogenize)
  ultimately show "homogeneous p" by simp
next
  assume "homogeneous p"
  hence "hom_components p = (if p = 0 then {} else {p})" by (rule hom_components_of_homogeneous)
  thus "homogenize x p = p" by (simp add: homogenize_alt split: if_split_asm)
qed

lemma homogenize_homogenize [simp]: "homogenize x (homogenize x p) = homogenize x p"
  by (simp add: homogeneous_homogenize)

lemma homogenize_monomial: "homogenize x (monomial c t) = monomial c t"
  by (simp only: homogenize_id_iff homogeneous_monomial)

lemma indets_homogenize_subset: "indets (homogenize x p) \<subseteq> insert x (indets p)"
proof
  fix y
  assume "y \<in> indets (homogenize x p)"
  then obtain t where "t \<in> keys (homogenize x p)" and "y \<in> keys t" by (rule in_indetsE)
  from this(1) obtain t' where "t' \<in> keys p"
    and t: "t = Poly_Mapping.single x (poly_deg p - deg_pm t') + t'" by (rule keys_homogenizeE)
  note \<open>y \<in> keys t\<close>
  also have "keys t \<subseteq> keys (Poly_Mapping.single x (poly_deg p - deg_pm t')) \<union> keys t'"
    unfolding t by (rule keys_add_subset)
  finally show "y \<in> insert x (indets p)"
  proof
    assume "y \<in> keys (Poly_Mapping.single x (poly_deg p - deg_pm t'))"
    thus ?thesis by (simp split: if_split_asm)
  next
    assume "y \<in> keys t'"
    hence "y \<in> indets p" using \<open>t' \<in> keys p\<close> by (rule in_indetsI)
    thus ?thesis by simp
  qed
qed

lemma homogenize_in_Polys: "p \<in> P[X] \<Longrightarrow> homogenize x p \<in> P[insert x X]"
  using indets_homogenize_subset[of x p] by (auto simp: Polys_alt)

lemma lookup_homogenize:
  assumes "x \<notin> indets p" and "x \<notin> keys t"
  shows "lookup (homogenize x p) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t) = lookup p t"
proof -
  let ?p = "homogenize x p"
  let ?t = "Poly_Mapping.single x (poly_deg p - deg_pm t) + t"
  have eq: "(\<Sum>s\<in>keys p - {t}. lookup (monomial (lookup p s) (Poly_Mapping.single x (poly_deg p - deg_pm s) + s)) ?t) = 0"
  proof (intro sum.neutral ballI)
    fix s
    assume "s \<in> keys p - {t}"
    hence "s \<in> keys p" and "s \<noteq> t" by simp_all
    from this(1) have "keys s \<subseteq> indets p" by (simp add: in_indetsI subsetI)
    with assms(1) have "x \<notin> keys s" by blast
    have "?t \<noteq> Poly_Mapping.single x (poly_deg p - deg_pm s) + s"
    proof
      assume a: "?t = Poly_Mapping.single x (poly_deg p - deg_pm s) + s"
      hence "lookup ?t x = lookup (Poly_Mapping.single x (poly_deg p - deg_pm s) + s) x"
        by simp
      moreover from assms(2) have "lookup t x = 0" by simp
      moreover from \<open>x \<notin> keys s\<close> have "lookup s x = 0" by simp
      ultimately have "poly_deg p - deg_pm t = poly_deg p - deg_pm s" by (simp add: lookup_add)
      with a have "s = t" by simp
      with \<open>s \<noteq> t\<close> show False ..
    qed
    thus "lookup (monomial (lookup p s) (Poly_Mapping.single x (poly_deg p - deg_pm s) + s)) ?t = 0"
      by (simp add: lookup_single)
  qed
  show ?thesis
  proof (cases "t \<in> keys p")
    case True
    have "lookup ?p ?t = (\<Sum>s\<in>keys p. lookup (monomial (lookup p s) (Poly_Mapping.single x (poly_deg p - deg_pm s) + s)) ?t)"
      by (simp add: homogenize_def lookup_sum)
    also have "\<dots> = lookup (monomial (lookup p t) ?t) ?t +
                    (\<Sum>s\<in>keys p - {t}. lookup (monomial (lookup p s) (Poly_Mapping.single x (poly_deg p - deg_pm s) + s)) ?t)"
      using finite_keys True by (rule sum.remove)
    also have "\<dots> = lookup p t" by (simp add: eq)
    finally show ?thesis .
  next
    case False
    hence 1: "keys p - {t} = keys p" by simp
    have "lookup ?p ?t = (\<Sum>s\<in>keys p - {t}. lookup (monomial (lookup p s) (Poly_Mapping.single x (poly_deg p - deg_pm s) + s)) ?t)"
      by (simp add: homogenize_def lookup_sum 1)
    also have "\<dots> = 0" by (simp only: eq)
    also from False have "\<dots> = lookup p t" by simp
    finally show ?thesis .
  qed
qed

lemma keys_homogenizeI:
  assumes "x \<notin> indets p" and "t \<in> keys p"
  shows "Poly_Mapping.single x (poly_deg p - deg_pm t) + t \<in> keys (homogenize x p)" (is "?t \<in> keys ?p")
proof -
  from assms(2) have "keys t \<subseteq> indets p" by (simp add: in_indetsI subsetI)
  with assms(1) have "x \<notin> keys t" by blast
  with assms(1) have "lookup ?p ?t = lookup p t" by (rule lookup_homogenize)
  also from assms(2) have "\<dots> \<noteq> 0" by simp
  finally show ?thesis by simp
qed

lemma keys_homogenize:
  "x \<notin> indets p \<Longrightarrow> keys (homogenize x p) = (\<lambda>t. Poly_Mapping.single x (poly_deg p - deg_pm t) + t) ` keys p"
  by (auto intro: keys_homogenizeI elim: keys_homogenizeE)

lemma card_keys_homogenize:
  assumes "x \<notin> indets p"
  shows "card (keys (homogenize x p)) = card (keys p)"
  unfolding keys_homogenize[OF assms]
proof (intro card_image inj_onI)
  fix s t
  assume "s \<in> keys p" and "t \<in> keys p"
  with assms have "x \<notin> keys s" and "x \<notin> keys t" by (auto dest: in_indetsI simp only:)
  let ?s = "Poly_Mapping.single x (poly_deg p - deg_pm s)"
  let ?t = "Poly_Mapping.single x (poly_deg p - deg_pm t)"
  assume "?s + s = ?t + t"
  hence "lookup (?s + s) x = lookup (?t + t) x" by simp
  with \<open>x \<notin> keys s\<close> \<open>x \<notin> keys t\<close> have "?s = ?t" by (simp add: lookup_add)
  with \<open>?s + s = ?t + t\<close> show "s = t" by simp
qed

lemma poly_deg_homogenize:
  assumes "x \<notin> indets p"
  shows "poly_deg (homogenize x p) = poly_deg p"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  then obtain t where "t \<in> keys p" and 1: "poly_deg p = deg_pm t" by (rule poly_degE)
  from assms this(1) have "Poly_Mapping.single x (poly_deg p - deg_pm t) + t \<in> keys (homogenize x p)"
    by (rule keys_homogenizeI)
  hence "t \<in> keys (homogenize x p)" by (simp add: 1)
  hence "poly_deg p \<le> poly_deg (homogenize x p)" unfolding 1 by (rule poly_deg_max_keys)
  with poly_deg_homogenize_le show ?thesis by (rule antisym)
qed

lemma maxdeg_homogenize:
  assumes "x \<notin> UNION F indets"
  shows "maxdeg (homogenize x ` F) = maxdeg F"
  unfolding maxdeg_def image_image
proof (rule arg_cong[where f=Max], rule set_eqI)
  fix d
  show "d \<in> (\<lambda>f. poly_deg (homogenize x f)) ` F \<longleftrightarrow> d \<in> poly_deg ` F"
  proof
    assume "d \<in> (\<lambda>f. poly_deg (homogenize x f)) ` F"
    then obtain f where "f \<in> F" and d: "d = poly_deg (homogenize x f)" ..
    from assms this(1) have "x \<notin> indets f" by blast
    hence "d = poly_deg f" by (simp add: d poly_deg_homogenize)
    with \<open>f \<in> F\<close> show "d \<in> poly_deg ` F" by (rule rev_image_eqI)
  next
    assume "d \<in> poly_deg ` F"
    then obtain f where "f \<in> F" and d: "d = poly_deg f" ..
    from assms this(1) have "x \<notin> indets f" by blast
    hence "d = poly_deg (homogenize x f)" by (simp add: d poly_deg_homogenize)
    with \<open>f \<in> F\<close> show "d \<in> (\<lambda>f. poly_deg (homogenize x f)) ` F" by (rule rev_image_eqI)
  qed
qed

lemma homogeneous_ideal_homogenize:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F"
  shows "homogenize x p \<in> ideal F"
proof -
  have "homogenize x p = (\<Sum>q\<in>hom_components p. punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q)"
    by (fact homogenize_alt)
  also have "\<dots> \<in> ideal F"
  proof (rule ideal.span_sum)
    fix q
    assume "q \<in> hom_components p"
    with assms have "q \<in> ideal F" by (rule homogeneous_ideal')
    thus "punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q \<in> ideal F"
      by (rule punit.pmdl_closed_monom_mult[simplified])
  qed
  finally show ?thesis .
qed

lemma subst_pp_dehomo_subst [simp]:
  "subst_pp (dehomo_subst x) t = monomial (1::'b::comm_semiring_1) (except t {x})"
proof -
  have "subst_pp (dehomo_subst x) t = ((\<Prod>y\<in>keys t. dehomo_subst x y ^ lookup t y)::_ \<Rightarrow>\<^sub>0 'b)"
    by (fact subst_pp_def)
  also have "\<dots> = (\<Prod>y\<in>keys t - {y0. dehomo_subst x y0 ^ lookup t y0 = (1::_ \<Rightarrow>\<^sub>0 'b)}. dehomo_subst x y ^ lookup t y)"
    by (rule sym, rule prod.setdiff_irrelevant, fact finite_keys)
  also have "\<dots> = (\<Prod>y\<in>keys t - {x}. monomial 1 (Poly_Mapping.single y 1) ^ lookup t y)"
  proof (rule prod.cong)
    have "dehomo_subst x x ^ lookup t x = 1" by (simp add: dehomo_subst_def)
    moreover {
      fix y
      assume "y \<noteq> x"
      hence "dehomo_subst x y ^ lookup t y = monomial 1 (Poly_Mapping.single y (lookup t y))"
        by (simp add: dehomo_subst_def monomial_single_power)
      moreover assume "dehomo_subst x y ^ lookup t y = 1"
      ultimately have "Poly_Mapping.single y (lookup t y) = 0"
        by (smt single_one monomial_inj zero_neq_one)
      hence "lookup t y = 0" by (rule monomial_0D)
      moreover assume "y \<in> keys t"
      ultimately have False by (simp add: in_keys_iff)
    }
    ultimately show "keys t - {y0. dehomo_subst x y0 ^ lookup t y0 = 1} = keys t - {x}" by auto
  qed (simp add: dehomo_subst_def)
  also have "\<dots> = (\<Prod>y\<in>keys t - {x}. monomial 1 (Poly_Mapping.single y (lookup t y)))"
    by (simp add: monomial_single_power)
  also have "\<dots> = monomial 1 (\<Sum>y\<in>keys t - {x}. Poly_Mapping.single y (lookup t y))"
    by (simp flip: punit.monomial_prod_sum)
  also have "(\<Sum>y\<in>keys t - {x}. Poly_Mapping.single y (lookup t y)) = except t {x}"
  proof (rule poly_mapping_eqI, simp add: lookup_sum lookup_except lookup_single, rule)
    fix y
    assume "y \<noteq> x"
    show "(\<Sum>z\<in>keys t - {x}. lookup t z when z = y) = lookup t y"
    proof (cases "y \<in> keys t")
      case True
      have "finite (keys t - {x})" by simp
      moreover from True \<open>y \<noteq> x\<close> have "y \<in> keys t - {x}" by simp
      ultimately have "(\<Sum>z\<in>keys t - {x}. lookup t z when z = y) =
                        (lookup t y when y = y) + (\<Sum>z\<in>keys t - {x} - {y}. lookup t z when z = y)"
        by (rule sum.remove)
      also have "(\<Sum>z\<in>keys t - {x} - {y}. lookup t z when z = y) = 0" by auto
      finally show ?thesis by simp
    next
      case False
      hence "(\<Sum>z\<in>keys t - {x}. lookup t z when z = y) = 0" by (auto simp: when_def)
      also from False have "\<dots> = lookup t y" by simp
      finally show ?thesis .
    qed
  qed
  finally show ?thesis .
qed

lemma
  shows dehomogenize_zero [simp]: "dehomogenize x 0 = 0"
    and dehomogenize_one [simp]: "dehomogenize x 1 = 1"
    and dehomogenize_monomial: "dehomogenize x (monomial c t) = monomial c (except t {x})"
    and dehomogenize_plus: "dehomogenize x (p + q) = dehomogenize x p + dehomogenize x q"
    and dehomogenize_uminus: "dehomogenize x (- r) = - dehomogenize x (r::_ \<Rightarrow>\<^sub>0 _::comm_ring_1)"
    and dehomogenize_minus: "dehomogenize x (r - r') = dehomogenize x r - dehomogenize x r'"
    and dehomogenize_times: "dehomogenize x (p * q) = dehomogenize x p * dehomogenize x q"
    and dehomogenize_power: "dehomogenize x (p ^ n) = dehomogenize x p ^ n"
    and dehomogenize_sum: "dehomogenize x (sum f A) = (\<Sum>a\<in>A. dehomogenize x (f a))"
    and dehomogenize_prod: "dehomogenize x (prod f A) = (\<Prod>a\<in>A. dehomogenize x (f a))"
  by (simp_all add: dehomogenize_def poly_subst_monomial poly_subst_plus poly_subst_uminus
      poly_subst_minus poly_subst_times poly_subst_power poly_subst_sum poly_subst_prod punit.monom_mult_monomial)

corollary dehomogenize_monom_mult:
  "dehomogenize x (punit.monom_mult c t p) = punit.monom_mult c (except t {x}) (dehomogenize x p)"
  by (simp only: times_monomial_left[symmetric] dehomogenize_times dehomogenize_monomial)

lemma poly_deg_dehomogenize_le: "poly_deg (dehomogenize x p) \<le> poly_deg p"
  unfolding dehomogenize_def dehomo_subst_def
  by (rule poly_deg_poly_subst_le) (simp add: poly_deg_monomial deg_pm_single)

lemma indets_dehomogenize: "indets (dehomogenize x p) \<subseteq> indets p - {x}"
  for p::"('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1"
proof
  fix y::'x
  assume "y \<in> indets (dehomogenize x p)"
  then obtain y' where "y' \<in> indets p" and "y \<in> indets ((dehomo_subst x y')::_ \<Rightarrow>\<^sub>0 'a)"
    unfolding dehomogenize_def by (rule in_indets_poly_substE)
  from this(2) have "y = y'" and "y' \<noteq> x"
    by (simp_all add: dehomo_subst_def indets_monomial split: if_split_asm)
  with \<open>y' \<in> indets p\<close> show "y \<in> indets p - {x}" by simp
qed

lemma dehomogenize_id_iff [simp]: "dehomogenize x p = p \<longleftrightarrow> x \<notin> indets p"
proof
  assume eq: "dehomogenize x p = p"
  from indets_dehomogenize[of x p] show "x \<notin> indets p" by (auto simp: eq)
next
  assume a: "x \<notin> indets p"
  show "dehomogenize x p = p" unfolding dehomogenize_def
  proof (rule poly_subst_id)
    fix y
    assume "y \<in> indets p"
    with a have "y \<noteq> x" by blast
    thus "dehomo_subst x y = monomial 1 (Poly_Mapping.single y 1)" by (simp add: dehomo_subst_def)
  qed
qed

lemma dehomogenize_dehomogenize [simp]: "dehomogenize x (dehomogenize x p) = dehomogenize x p"
proof -
  from indets_dehomogenize[of x p] have "x \<notin> indets (dehomogenize x p)" by blast
  thus ?thesis by simp
qed

lemma dehomogenize_homogenize [simp]: "dehomogenize x (homogenize x p) = dehomogenize x p"
proof -
  have "dehomogenize x (homogenize x p) = sum (dehomogenize x) (hom_components p)"
    by (simp add: homogenize_alt dehomogenize_sum dehomogenize_monom_mult except_single)
  also have "\<dots> = dehomogenize x p" by (simp only: sum_hom_components flip: dehomogenize_sum)
  finally show ?thesis .
qed

corollary dehomogenize_homogenize_id: "x \<notin> indets p \<Longrightarrow> dehomogenize x (homogenize x p) = p"
  by simp

lemma dehomogenize_alt: "dehomogenize x p = (\<Sum>t\<in>keys p. monomial (lookup p t) (except t {x}))"
proof -
  have "dehomogenize x p = dehomogenize x (\<Sum>t\<in>keys p. monomial (lookup p t) t)"
    by (simp only: poly_mapping_sum_monomials)
  also have "\<dots> = (\<Sum>t\<in>keys p. monomial (lookup p t) (except t {x}))"
    by (simp only: dehomogenize_sum dehomogenize_monomial)
  finally show ?thesis .
qed

lemma keys_dehomogenizeE:
  assumes "t \<in> keys (dehomogenize x p)"
  obtains s where "s \<in> keys p" and "t = except s {x}"
proof -
  note assms
  also have "keys (dehomogenize x p) \<subseteq> (\<Union>s\<in>keys p. keys (monomial (lookup p s) (except s {x})))"
    unfolding dehomogenize_alt by (rule keys_sum_subset)
  finally obtain s where "s \<in> keys p" and "t \<in> keys (monomial (lookup p s) (except s {x}))" ..
  from this(2) have "t = except s {x}" by (simp split: if_split_asm)
  with \<open>s \<in> keys p\<close> show ?thesis ..
qed

lemma except_inj_on_keys_homogeneous:
  assumes "homogeneous p"
  shows "inj_on (\<lambda>t. except t {x}) (keys p)"
proof
  fix s t
  assume "s \<in> keys p" and "t \<in> keys p"
  from assms this(1) have "deg_pm s = poly_deg p" by (rule homogeneousD_poly_deg)
  moreover from assms \<open>t \<in> keys p\<close> have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
  ultimately have "deg_pm (Poly_Mapping.single x (lookup s x) + except s {x}) =
                   deg_pm (Poly_Mapping.single x (lookup t x) + except t {x})"
    by (simp only: flip: plus_except)
  moreover assume 1: "except s {x} = except t {x}"
  ultimately have 2: "lookup s x = lookup t x"
    by (simp only: deg_pm_plus deg_pm_single)
  show "s = t"
  proof (rule poly_mapping_eqI)
    fix y
    show "lookup s y = lookup t y"
    proof (cases "y = x")
      case True
      with 2 show ?thesis by simp
    next
      case False
      hence "lookup s y = lookup (except s {x}) y" and "lookup t y = lookup (except t {x}) y"
        by (simp_all add: lookup_except)
      with 1 show ?thesis by simp
    qed
  qed
qed

lemma lookup_dehomogenize:
  assumes "homogeneous p" and "t \<in> keys p"
  shows "lookup (dehomogenize x p) (except t {x}) = lookup p t"
proof -
  let ?t = "except t {x}"
  have eq: "(\<Sum>s\<in>keys p - {t}. lookup (monomial (lookup p s) (except s {x})) ?t) = 0"
  proof (intro sum.neutral ballI)
    fix s
    assume "s \<in> keys p - {t}"
    hence "s \<in> keys p" and "s \<noteq> t" by simp_all
    have "?t \<noteq> except s {x}"
    proof
      from assms(1) have "inj_on (\<lambda>t. except t {x}) (keys p)" by (rule except_inj_on_keys_homogeneous)
      moreover assume "?t = except s {x}"
      ultimately have "t = s" using assms(2) \<open>s \<in> keys p\<close> by (rule inj_onD)
      with \<open>s \<noteq> t\<close> show False by simp
    qed
    thus "lookup (monomial (lookup p s) (except s {x})) ?t = 0" by (simp add: lookup_single)
  qed
  have "lookup (dehomogenize x p) ?t = (\<Sum>s\<in>keys p. lookup (monomial (lookup p s) (except s {x})) ?t)"
    by (simp only: dehomogenize_alt lookup_sum)
  also have "\<dots> = lookup (monomial (lookup p t) ?t) ?t +
                  (\<Sum>s\<in>keys p - {t}. lookup (monomial (lookup p s) (except s {x})) ?t)"
    using finite_keys assms(2) by (rule sum.remove)
  also have "\<dots> = lookup p t" by (simp add: eq)
  finally show ?thesis .
qed

lemma keys_dehomogenizeI:
  assumes "homogeneous p" and "t \<in> keys p"
  shows "except t {x} \<in> keys (dehomogenize x p)"
proof -
  from assms have "lookup (dehomogenize x p) (except t {x}) = lookup p t" by (rule lookup_dehomogenize)
  also from assms(2) have "\<dots> \<noteq> 0" by simp
  finally show ?thesis by simp
qed

lemma homogeneous_homogenize_dehomogenize:
  assumes "homogeneous p"
  obtains d where "d = poly_deg p - poly_deg (homogenize x (dehomogenize x p))"
    and "punit.monom_mult 1 (Poly_Mapping.single x d) (homogenize x (dehomogenize x p)) = p"
proof (cases "p = 0")
  case True
  hence "0 = poly_deg p - poly_deg (homogenize x (dehomogenize x p))"
    and "punit.monom_mult 1 (Poly_Mapping.single x 0) (homogenize x (dehomogenize x p)) = p"
    by simp_all
  thus ?thesis ..
next
  case False
  let ?q = "dehomogenize x p"
  let ?p = "homogenize x ?q"
  define d where "d = poly_deg p - poly_deg ?p"
  show ?thesis
  proof
    have "punit.monom_mult 1 (Poly_Mapping.single x d) ?p =
          (\<Sum>t\<in>keys ?q. monomial (lookup ?q t) (Poly_Mapping.single x (d + (poly_deg ?q - deg_pm t)) + t))"
      by (simp add: homogenize_def punit.monom_mult_sum_right punit.monom_mult_monomial flip: add.assoc single_add)
    also have "\<dots> = (\<Sum>t\<in>keys ?q. monomial (lookup ?q t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t))"
      using refl
    proof (rule sum.cong)
      fix t
      assume "t \<in> keys ?q"
      have "poly_deg ?p = poly_deg ?q"
      proof (rule poly_deg_homogenize)
        from indets_dehomogenize show "x \<notin> indets ?q" by fastforce
      qed
      hence d: "d = poly_deg p - poly_deg ?q" by (simp only: d_def)
      thm poly_deg_dehomogenize_le
      from \<open>t \<in> keys ?q\<close> have "d + (poly_deg ?q - deg_pm t) = (d + poly_deg ?q) - deg_pm t"
        by (intro add_diff_assoc poly_deg_max_keys)
      also have "d + poly_deg ?q = poly_deg p" by (simp add: d poly_deg_dehomogenize_le)
      finally show "monomial (lookup ?q t) (Poly_Mapping.single x (d + (poly_deg ?q - deg_pm t)) + t) =
                    monomial (lookup ?q t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t)"
        by (simp only:)
    qed
    also have "\<dots> = (\<Sum>t\<in>(\<lambda>s. except s {x}) ` keys p.
                    monomial (lookup ?q t) (Poly_Mapping.single x (poly_deg p - deg_pm t) + t))"
    proof (rule sum.mono_neutral_left)
      show "keys (dehomogenize x p) \<subseteq> (\<lambda>s. except s {x}) ` keys p"
      proof
        fix t
        assume "t \<in> keys (dehomogenize x p)"
        then obtain s where "s \<in> keys p" and "t = except s {x}" by (rule keys_dehomogenizeE)
        thus "t \<in> (\<lambda>s. except s {x}) ` keys p" by (rule rev_image_eqI)
      qed
    qed simp_all
    also from assms have "\<dots> = (\<Sum>t\<in>keys p. monomial (lookup ?q (except t {x}))
                (Poly_Mapping.single x (poly_deg p - deg_pm (except t {x})) + except t {x}))"
      by (intro sum.reindex[unfolded comp_def] except_inj_on_keys_homogeneous)
    also from refl have "\<dots> = (\<Sum>t\<in>keys p. monomial (lookup p t) t)"
    proof (rule sum.cong)
      fix t
      assume "t \<in> keys p"
      with assms have "lookup ?q (except t {x}) = lookup p t" by (rule lookup_dehomogenize)
      moreover have "Poly_Mapping.single x (poly_deg p - deg_pm (except t {x})) + except t {x} = t"
        (is "?l = _")
      proof (rule poly_mapping_eqI)
        fix y
        show "lookup ?l y = lookup t y"
        proof (cases "y = x")
          case True
          from assms \<open>t \<in> keys p\<close> have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
          also have "deg_pm t = deg_pm (Poly_Mapping.single x (lookup t x) + except t {x})"
            by (simp flip: plus_except)
          also have "\<dots> = lookup t x + deg_pm (except t {x})" by (simp only: deg_pm_plus deg_pm_single)
          finally have "poly_deg p - deg_pm (except t {x}) = lookup t x" by simp
          thus ?thesis by (simp add: True lookup_add lookup_except lookup_single)
        next
          case False
          thus ?thesis by (simp add: lookup_add lookup_except lookup_single)
        qed
      qed
      ultimately show "monomial (lookup ?q (except t {x}))
              (Poly_Mapping.single x (poly_deg p - deg_pm (except t {x})) + except t {x}) =
            monomial (lookup p t) t" by (simp only:)
    qed
    also have "\<dots> = p" by (fact poly_mapping_sum_monomials)
    finally show "punit.monom_mult 1 (Poly_Mapping.single x d) ?p = p" .
  qed (simp only: d_def)
qed

lemma dehomogenize_zeroD:
  assumes "dehomogenize x p = 0" and "homogeneous p"
  shows "p = 0"
proof -
  from assms(2) obtain d
    where "punit.monom_mult 1 (Poly_Mapping.single x d) (homogenize x (dehomogenize x p)) = p"
    by (rule homogeneous_homogenize_dehomogenize)
  thus ?thesis by (simp add: assms(1))
qed

lemma dehomogenize_ideal_subset: "dehomogenize x ` ideal F \<subseteq> ideal (dehomogenize x ` F)"
proof
  fix q
  assume "q \<in> dehomogenize x ` ideal F"
  then obtain p where "p \<in> ideal F" and q: "q = dehomogenize x p" ..
  from this(1) show "q \<in> ideal (dehomogenize x ` F)" unfolding q
  proof (induct p rule: ideal.span_induct')
    case base
    show ?case by (simp add: ideal.span_zero)
  next
    case (step a q p)
    have "dehomogenize x (a + q * p) = dehomogenize x a + dehomogenize x q * dehomogenize x p"
      by (simp only: dehomogenize_plus dehomogenize_times)
    also from step.hyps(2, 3) have "\<dots> \<in> ideal (dehomogenize x ` F)"
      by (intro ideal.span_add ideal.span_scale ideal.span_base[of "dehomogenize x p"] imageI)
    finally show ?case .
  qed
qed

lemma ideal_dehomogenize:
  assumes "ideal G = ideal (homogenize x ` F)" and "F \<subseteq> P[UNIV - {x}]"
  shows "ideal (dehomogenize x ` G) = ideal F"
proof -
  have eq: "dehomogenize x (homogenize x f) = f" if "f \<in> F" for f
  proof (rule dehomogenize_homogenize_id)
    from that assms(2) have "f \<in> P[UNIV - {x}]" ..
    thus "x \<notin> indets f" by (auto simp: Polys_alt)
  qed
  show ?thesis
  proof (intro Set.equalityI ideal.span_subset_spanI)
    show "dehomogenize x ` G \<subseteq> ideal F"
    proof
      fix q
      assume "q \<in> dehomogenize x ` G"
      then obtain g where "g \<in> G" and q: "q = dehomogenize x g" ..
      from this(1) have "g \<in> ideal G" by (rule ideal.span_base)
      also have "\<dots> = ideal (homogenize x ` F)" by fact
      finally have "q \<in> dehomogenize x ` ideal (homogenize x ` F)" using q by (rule rev_image_eqI)
      also have "\<dots> \<subseteq> ideal (dehomogenize x ` homogenize x ` F)" by (rule dehomogenize_ideal_subset)
      also have "dehomogenize x ` homogenize x ` F = F"
        by (auto simp: eq image_image simp del: dehomogenize_homogenize intro!: image_eqI)
      finally show "q \<in> ideal F" .
    qed
  next
    show "F \<subseteq> ideal (dehomogenize x ` G)"
    proof
      fix f
      assume "f \<in> F"
      hence "homogenize x f \<in> homogenize x ` F" by (rule imageI)
      also have "\<dots> \<subseteq> ideal (homogenize x ` F)" by (rule ideal.span_superset)
      also from assms(1) have "\<dots> = ideal G" by (rule sym)
      finally have "dehomogenize x (homogenize x f) \<in> dehomogenize x ` ideal G" by (rule imageI)
      with \<open>f \<in> F\<close> have "f \<in> dehomogenize x ` ideal G" by (simp only: eq)
      also have "\<dots> \<subseteq> ideal (dehomogenize x ` G)" by (rule dehomogenize_ideal_subset)
      finally show "f \<in> ideal (dehomogenize x ` G)" .
    qed
  qed
qed

subsection \<open>Embedding Polynomial Rings in Larger Polynomial Rings (With One Additional Indeterminate)\<close>

text \<open>We define a homomorphism for embedding a polynomial ring in a larger polynomial ring, and its
  inverse. This is mainly needed for homogenizing wrt. a fresh indeterminate.\<close>

definition extend_indets_subst :: "'x \<Rightarrow> ('x option \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1"
  where "extend_indets_subst x = monomial 1 (Poly_Mapping.single (Some x) 1)"

definition extend_indets :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> ('x option \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1"
  where "extend_indets = poly_subst extend_indets_subst"

definition restrict_indets_subst :: "'x option \<Rightarrow> 'x \<Rightarrow>\<^sub>0 nat"
  where "restrict_indets_subst x = (case x of Some y \<Rightarrow> Poly_Mapping.single y 1 | _ \<Rightarrow> 0)"

definition restrict_indets :: "(('x option \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1"
  where "restrict_indets = poly_subst (\<lambda>x. monomial 1 (restrict_indets_subst x))"

definition restrict_indets_pp :: "('x option \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat)"
  where "restrict_indets_pp t = (\<Sum>x\<in>keys t. lookup t x \<cdot> restrict_indets_subst x)"

lemma lookup_extend_indets_subst_aux:
  "lookup (\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y)) = (\<lambda>x. case x of Some y \<Rightarrow> lookup t y | _ \<Rightarrow> 0)"
proof -
  have "(\<Sum>x\<in>keys t. lookup t x when x = y) = lookup t y" for y
  proof (cases "y \<in> keys t")
    case True
    hence "(\<Sum>x\<in>keys t. lookup t x when x = y) = (\<Sum>x\<in>insert y (keys t). lookup t x when x = y)"
      by (simp only: insert_absorb)
    also have "\<dots> = lookup t y + (\<Sum>x\<in>keys t - {y}. lookup t x when x = y)"
      by (simp add: sum.insert_remove)
    also have "(\<Sum>x\<in>keys t - {y}. lookup t x when x = y) = 0"
      by (auto simp: when_def intro: sum.neutral)
    finally show ?thesis by simp
  next
    case False
    hence "(\<Sum>x\<in>keys t. lookup t x when x = y) = 0" by (auto simp: when_def intro: sum.neutral)
    with False show ?thesis by simp
  qed
  thus ?thesis by (auto simp: lookup_sum lookup_single split: option.split)
qed

lemma keys_extend_indets_subst_aux:
  "keys (\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y)) = Some ` keys t"
  by (auto simp: lookup_extend_indets_subst_aux simp flip: lookup_not_eq_zero_eq_in_keys split: option.splits)

lemma subst_pp_extend_indets_subst:
  "subst_pp extend_indets_subst t = monomial 1 (\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y))"
proof -
  have "subst_pp extend_indets_subst t =
      monomial (\<Prod>y\<in>keys t. 1 ^ lookup t y) (\<Sum>y\<in>keys t. lookup t y \<cdot> Poly_Mapping.single (Some y) 1)"
    by (rule subst_pp_by_monomials) (simp only: extend_indets_subst_def)
  also have "\<dots> = monomial 1 (\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y))"
    by simp
  finally show ?thesis .
qed

lemma keys_extend_indets:
  "keys (extend_indets p) = (\<lambda>t. \<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y)) ` keys p"
proof -
  have "keys (extend_indets p) = (\<Union>t\<in>keys p. keys (punit.monom_mult (lookup p t) 0 (subst_pp extend_indets_subst t)))"
    unfolding extend_indets_def poly_subst_def using finite_keys
  proof (rule keys_sum)
    fix s t :: "'a \<Rightarrow>\<^sub>0 nat"
    assume "s \<noteq> t"
    then obtain x where "lookup s x \<noteq> lookup t x" by (meson poly_mapping_eqI)
    have "(\<Sum>y\<in>keys t. monomial (lookup t y) (Some y)) \<noteq> (\<Sum>y\<in>keys s. monomial (lookup s y) (Some y))"
      (is "?l \<noteq> ?r")
    proof
      assume "?l = ?r"
      hence "lookup ?l (Some x) = lookup ?r (Some x)" by (simp only:)
      hence "lookup s x = lookup t x" by (simp add: lookup_extend_indets_subst_aux)
      with \<open>lookup s x \<noteq> lookup t x\<close> show False ..
    qed
    thus "keys (punit.monom_mult (lookup p s) 0 (subst_pp extend_indets_subst s)) \<inter>
          keys (punit.monom_mult (lookup p t) 0 (subst_pp extend_indets_subst t)) =
          {}"
      by (simp add: subst_pp_extend_indets_subst punit.monom_mult_monomial)
  qed
  also have "\<dots> = (\<lambda>t. \<Sum>y\<in>keys t. monomial (lookup t y) (Some y)) ` keys p"
    by (auto simp: subst_pp_extend_indets_subst punit.monom_mult_monomial split: if_split_asm)
  finally show ?thesis .
qed

lemma indets_extend_indets: "indets (extend_indets p) = Some ` indets (p::_ \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
proof (rule set_eqI)
  fix x
  show "x \<in> indets (extend_indets p) \<longleftrightarrow> x \<in> Some ` indets p"
  proof
    assume "x \<in> indets (extend_indets p)"
    then obtain y where "y \<in> indets p" and "x \<in> indets (monomial (1::'a) (Poly_Mapping.single (Some y) 1))"
      unfolding extend_indets_def extend_indets_subst_def by (rule in_indets_poly_substE)
    from this(2) indets_monomial_single_subset have "x \<in> {Some y}" ..
    hence "x = Some y" by simp
    with \<open>y \<in> indets p\<close> show "x \<in> Some ` indets p" by (rule rev_image_eqI)
  next
    assume "x \<in> Some ` indets p"
    then obtain y where "y \<in> indets p" and x: "x = Some y" ..
    from this(1) obtain t where "t \<in> keys p" and "y \<in> keys t" by (rule in_indetsE)
    from this(2) have "Some y \<in> keys (\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y))"
      unfolding keys_extend_indets_subst_aux by (rule imageI)
    moreover have "(\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y)) \<in> keys (extend_indets p)"
      unfolding keys_extend_indets using \<open>t \<in> keys p\<close> by (rule imageI)
    ultimately show "x \<in> indets (extend_indets p)" unfolding x by (rule in_indetsI)
  qed
qed

lemma poly_deg_extend_indets [simp]: "poly_deg (extend_indets p) = poly_deg p"
proof -
  have eq: "deg_pm ((\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y))) = deg_pm t"
    for t::"'a \<Rightarrow>\<^sub>0 nat"
  proof -
    have "deg_pm ((\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y))) = (\<Sum>y\<in>keys t. lookup t y)"
      by (simp add: deg_pm_sum deg_pm_single)
    also from subset_refl finite_keys have "\<dots> = deg_pm t" by (rule deg_pm_superset[symmetric])
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule antisym)
    show "poly_deg (extend_indets p) \<le> poly_deg p"
    proof (rule poly_deg_leI)
      fix t
      assume "t \<in> keys (extend_indets p)"
      then obtain s where "s \<in> keys p" and "t = (\<Sum>y\<in>keys s. Poly_Mapping.single (Some y) (lookup s y))"
        unfolding keys_extend_indets ..
      from this(2) have "deg_pm t = deg_pm s" by (simp only: eq)
      also from \<open>s \<in> keys p\<close> have "\<dots> \<le> poly_deg p" by (rule poly_deg_max_keys)
      finally show "deg_pm t \<le> poly_deg p" .
    qed
  next
    show "poly_deg p \<le> poly_deg (extend_indets p)"
    proof (rule poly_deg_leI)
      fix t
      assume "t \<in> keys p"
      hence *: "(\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y)) \<in> keys (extend_indets p)"
        unfolding keys_extend_indets by (rule imageI)
      have "deg_pm t = deg_pm (\<Sum>y\<in>keys t. Poly_Mapping.single (Some y) (lookup t y))"
        by (simp only: eq)
      also from * have "\<dots> \<le> poly_deg (extend_indets p)" by (rule poly_deg_max_keys)
      finally show "deg_pm t \<le> poly_deg (extend_indets p)" .
    qed
  qed
qed

lemma
  shows extend_indets_zero [simp]: "extend_indets 0 = 0"
    and extend_indets_one [simp]: "extend_indets 1 = 1"
    and extend_indets_monomial: "extend_indets (monomial c t) = punit.monom_mult c 0 (subst_pp extend_indets_subst t)"
    and extend_indets_plus: "extend_indets (p + q) = extend_indets p + extend_indets q"
    and extend_indets_uminus: "extend_indets (- r) = - extend_indets (r::_ \<Rightarrow>\<^sub>0 _::comm_ring_1)"
    and extend_indets_minus: "extend_indets (r - r') = extend_indets r - extend_indets r'"
    and extend_indets_times: "extend_indets (p * q) = extend_indets p * extend_indets q"
    and extend_indets_power: "extend_indets (p ^ n) = extend_indets p ^ n"
    and extend_indets_sum: "extend_indets (sum f A) = (\<Sum>a\<in>A. extend_indets (f a))"
    and extend_indets_prod: "extend_indets (prod f A) = (\<Prod>a\<in>A. extend_indets (f a))"
  by (simp_all add: extend_indets_def poly_subst_monomial poly_subst_plus poly_subst_uminus
      poly_subst_minus poly_subst_times poly_subst_power poly_subst_sum poly_subst_prod)

lemma extend_indets_zero_iff [simp]: "extend_indets p = 0 \<longleftrightarrow> p = 0"
  by (simp add: keys_extend_indets flip: keys_eq_empty_iff)

lemma lookup_restrict_indets_pp: "lookup (restrict_indets_pp t) = (\<lambda>x. lookup t (Some x))"
proof -
  let ?f = "\<lambda>z x. lookup t x * lookup (case x of None \<Rightarrow> 0 | Some y \<Rightarrow> Poly_Mapping.single y 1) z"
  have "sum (?f z) (keys t) = lookup t (Some z)" for z
  proof (cases "Some z \<in> keys t")
    case True
    hence "sum (?f z) (keys t) = sum (?f z) (insert (Some z) (keys t))"
      by (simp only: insert_absorb)
    also have "\<dots> = lookup t (Some z) + sum (?f z) (keys t - {Some z})"
      by (simp add: sum.insert_remove)
    also have "sum (?f z) (keys t - {Some z}) = 0"
      by (auto simp: when_def lookup_single intro: sum.neutral split: option.splits)
    finally show ?thesis by simp
  next
    case False
    hence "sum (?f z) (keys t) = 0"
      by (auto simp: when_def lookup_single intro: sum.neutral split: option.splits)
    with False show ?thesis by simp
  qed
  thus ?thesis by (auto simp: restrict_indets_pp_def restrict_indets_subst_def lookup_sum)
qed

lemma keys_restrict_indets_pp: "keys (restrict_indets_pp t) = the ` (keys t - {None})"
proof (rule set_eqI)
  fix x
  show "x \<in> keys (restrict_indets_pp t) \<longleftrightarrow> x \<in> the ` (keys t - {None})"
  proof
    assume "x \<in> keys (restrict_indets_pp t)"
    hence "Some x \<in> keys t" by (simp add: lookup_restrict_indets_pp flip: lookup_not_eq_zero_eq_in_keys)
    hence "Some x \<in> keys t - {None}" by blast
    moreover have "x = the (Some x)" by simp
    ultimately show "x \<in> the ` (keys t - {None})" by (rule rev_image_eqI)
  next
    assume "x \<in> the ` (keys t - {None})"
    then obtain y where "y \<in> keys t - {None}" and "x = the y" ..
    hence "Some x \<in> keys t" by auto
    thus "x \<in> keys (restrict_indets_pp t)"
      by (simp add: lookup_restrict_indets_pp flip: lookup_not_eq_zero_eq_in_keys)
  qed
qed

lemma subst_pp_restrict_indets_subst:
  "subst_pp (\<lambda>x. monomial 1 (restrict_indets_subst x)) t = monomial 1 (restrict_indets_pp t)"
  by (simp add: subst_pp_def monomial_power_map_scale restrict_indets_pp_def flip: punit.monomial_prod_sum)

lemma restrict_indets_pp_zero [simp]: "restrict_indets_pp 0 = 0"
  by (simp add: restrict_indets_pp_def)

lemma restrict_indets_pp_plus: "restrict_indets_pp (s + t) = restrict_indets_pp s + restrict_indets_pp t"
  by (rule poly_mapping_eqI) (simp add: lookup_add lookup_restrict_indets_pp)

lemma restrict_indets_pp_except_None [simp]:
  "restrict_indets_pp (except t {None}) = restrict_indets_pp t"
  by (rule poly_mapping_eqI) (simp add: lookup_add lookup_restrict_indets_pp lookup_except)

lemma deg_pm_restrict_indets_pp: "deg_pm (restrict_indets_pp t) + lookup t None = deg_pm t"
proof -
  have "deg_pm t = sum (lookup t) (insert None (keys t))" by (rule deg_pm_superset) auto
  also from finite_keys have "\<dots> = lookup t None + sum (lookup t) (keys t - {None})"
    by (rule sum.insert_remove)
  also have "sum (lookup t) (keys t - {None}) = (\<Sum>x\<in>keys t. lookup t x * deg_pm (restrict_indets_subst x))"
    by (intro sum.mono_neutral_cong_left) (auto simp: restrict_indets_subst_def deg_pm_single)
  also have "\<dots> = deg_pm (restrict_indets_pp t)"
    by (simp only: restrict_indets_pp_def deg_pm_sum deg_pm_map_scale)
  finally show ?thesis by simp
qed

lemma keys_restrict_indets_subset: "keys (restrict_indets p) \<subseteq> restrict_indets_pp ` keys p"
proof
  fix t
  assume "t \<in> keys (restrict_indets p)"
  also have "\<dots> = keys (\<Sum>t\<in>keys p. monomial (lookup p t) (restrict_indets_pp t))"
    by (simp add: restrict_indets_def poly_subst_def subst_pp_restrict_indets_subst punit.monom_mult_monomial)
  also have "\<dots> \<subseteq> (\<Union>t\<in>keys p. keys (monomial (lookup p t) (restrict_indets_pp t)))"
    by (rule keys_sum_subset)
  also have "\<dots> = restrict_indets_pp ` keys p" by (auto split: if_split_asm)
  finally show "t \<in> restrict_indets_pp ` keys p" .
qed

lemma keys_restrict_indets:
  assumes "None \<notin> indets p"
  shows "keys (restrict_indets p) = restrict_indets_pp ` keys p"
proof -
  have "keys (restrict_indets p) = keys (\<Sum>t\<in>keys p. monomial (lookup p t) (restrict_indets_pp t))"
    by (simp add: restrict_indets_def poly_subst_def subst_pp_restrict_indets_subst punit.monom_mult_monomial)
  also from finite_keys have "\<dots> = (\<Union>t\<in>keys p. keys (monomial (lookup p t) (restrict_indets_pp t)))"
  proof (rule keys_sum)
    fix s t
    assume "s \<in> keys p"
    hence "keys s \<subseteq> indets p" by (rule keys_subset_indets)
    with assms have "None \<notin> keys s" by blast
    assume "t \<in> keys p"
    hence "keys t \<subseteq> indets p" by (rule keys_subset_indets)
    with assms have "None \<notin> keys t" by blast
    assume "s \<noteq> t"
    then obtain x where neq: "lookup s x \<noteq> lookup t x" by (meson poly_mapping_eqI)
    have "x \<noteq> None"
    proof
      assume "x = None"
      with \<open>None \<notin> keys s\<close> and \<open>None \<notin> keys t\<close> have "x \<notin> keys s" and "x \<notin> keys t" by blast+
      with neq show False by simp
    qed
    then obtain y where x: "x = Some y" by blast
    have "restrict_indets_pp t \<noteq> restrict_indets_pp s"
    proof
      assume "restrict_indets_pp t = restrict_indets_pp s"
      hence "lookup (restrict_indets_pp t) y = lookup (restrict_indets_pp s) y" by (simp only:)
      hence "lookup s x = lookup t x" by (simp add: x lookup_restrict_indets_pp)
      with neq show False ..
    qed
    thus "keys (monomial (lookup p s) (restrict_indets_pp s)) \<inter>
          keys (monomial (lookup p t) (restrict_indets_pp t)) = {}"
      by (simp add: subst_pp_extend_indets_subst)
  qed
  also have "\<dots> = restrict_indets_pp ` keys p" by (auto split: if_split_asm)
  finally show ?thesis .
qed

lemma indets_restrict_indets_subset: "indets (restrict_indets p) \<subseteq> the ` (indets p - {None})"
proof
  fix x
  assume "x \<in> indets (restrict_indets p)"
  then obtain t where "t \<in> keys (restrict_indets p)" and "x \<in> keys t" by (rule in_indetsE)
  from this(1) keys_restrict_indets_subset have "t \<in> restrict_indets_pp ` keys p" ..
  then obtain s where "s \<in> keys p" and "t = restrict_indets_pp s" ..
  from \<open>x \<in> keys t\<close> this(2) have "x \<in> the ` (keys s - {None})" by (simp only: keys_restrict_indets_pp)
  also from \<open>s \<in> keys p\<close> have "\<dots> \<subseteq> the ` (indets p - {None})"
    by (intro image_mono Diff_mono keys_subset_indets subset_refl)
  finally show "x \<in> the ` (indets p - {None})" .
qed

lemma poly_deg_restrict_indets_le: "poly_deg (restrict_indets p) \<le> poly_deg p"
proof (rule poly_deg_leI)
  fix t
  assume "t \<in> keys (restrict_indets p)"
  hence "t \<in> restrict_indets_pp ` keys p" using keys_restrict_indets_subset ..
  then obtain s where "s \<in> keys p" and "t = restrict_indets_pp s" ..
  from this(2) have "deg_pm t + lookup s None = deg_pm s"
    by (simp only: deg_pm_restrict_indets_pp)
  also from \<open>s \<in> keys p\<close> have "\<dots> \<le> poly_deg p" by (rule poly_deg_max_keys)
  finally show "deg_pm t \<le> poly_deg p" by simp
qed

lemma
  shows restrict_indets_zero [simp]: "restrict_indets 0 = 0"
    and restrict_indets_one [simp]: "restrict_indets 1 = 1"
    and restrict_indets_monomial: "restrict_indets (monomial c t) = monomial c (restrict_indets_pp t)"
    and restrict_indets_plus: "restrict_indets (p + q) = restrict_indets p + restrict_indets q"
    and restrict_indets_uminus: "restrict_indets (- r) = - restrict_indets (r::_ \<Rightarrow>\<^sub>0 _::comm_ring_1)"
    and restrict_indets_minus: "restrict_indets (r - r') = restrict_indets r - restrict_indets r'"
    and restrict_indets_times: "restrict_indets (p * q) = restrict_indets p * restrict_indets q"
    and restrict_indets_power: "restrict_indets (p ^ n) = restrict_indets p ^ n"
    and restrict_indets_sum: "restrict_indets (sum f A) = (\<Sum>a\<in>A. restrict_indets (f a))"
    and restrict_indets_prod: "restrict_indets (prod f A) = (\<Prod>a\<in>A. restrict_indets (f a))"
  by (simp_all add: restrict_indets_def poly_subst_monomial poly_subst_plus poly_subst_uminus
      poly_subst_minus poly_subst_times poly_subst_power poly_subst_sum poly_subst_prod
      subst_pp_restrict_indets_subst punit.monom_mult_monomial)

lemma restrict_extend_indets [simp]: "restrict_indets (extend_indets p) = p"
  unfolding extend_indets_def restrict_indets_def poly_subst_poly_subst
  by (rule poly_subst_id)
    (simp add: extend_indets_subst_def restrict_indets_subst_def poly_subst_monomial subst_pp_single)

lemma extend_restrict_indets:
  assumes "None \<notin> indets p"
  shows "extend_indets (restrict_indets p) = p"
  unfolding extend_indets_def restrict_indets_def poly_subst_poly_subst
proof (rule poly_subst_id)
  fix x
  assume "x \<in> indets p"
  with assms have "x \<noteq> None" by meson
  then obtain y where x: "x = Some y" by blast
  thus "poly_subst extend_indets_subst (monomial 1 (restrict_indets_subst x)) =
         monomial 1 (Poly_Mapping.single x 1)"
    by (simp add: extend_indets_subst_def restrict_indets_subst_def poly_subst_monomial subst_pp_single)
qed

lemma restrict_indets_dehomogenize [simp]: "restrict_indets (dehomogenize None p) = restrict_indets p"
proof -
  have eq: "poly_subst (\<lambda>x. (monomial 1 (restrict_indets_subst x))) (dehomo_subst None y) =
            monomial 1 (restrict_indets_subst y)" for y::"'x option"
    by (auto simp: restrict_indets_subst_def dehomo_subst_def poly_subst_monomial subst_pp_single)
  show ?thesis by (simp only: dehomogenize_def restrict_indets_def poly_subst_poly_subst eq) 
qed

corollary restrict_indets_comp_dehomogenize: "restrict_indets \<circ> dehomogenize None = restrict_indets"
  by (rule ext) (simp only: o_def restrict_indets_dehomogenize)

corollary extend_restrict_indets_eq_dehomogenize:
  "extend_indets (restrict_indets p) = dehomogenize None p"
proof -
  have "extend_indets (restrict_indets p) = extend_indets (restrict_indets (dehomogenize None p))"
    by simp
  also have "\<dots> = dehomogenize None p"
  proof (intro extend_restrict_indets notI)
    assume "None \<in> indets (dehomogenize None p)"
    hence "None \<in> indets p - {None}" using indets_dehomogenize ..
    thus False by simp
  qed
  finally show ?thesis .
qed

corollary extend_indets_comp_restrict_indets: "extend_indets \<circ> restrict_indets = dehomogenize None"
  by (rule ext) (simp only: o_def extend_restrict_indets_eq_dehomogenize)

lemma restrict_homogenize_extend_indets [simp]:
  "restrict_indets (homogenize None (extend_indets p)) = p"
proof -
  have "restrict_indets (homogenize None (extend_indets p)) =
          restrict_indets (dehomogenize None (homogenize None (extend_indets p)))"
    by (simp only: restrict_indets_dehomogenize)
  also have "\<dots> = restrict_indets (dehomogenize None (extend_indets p))"
    by (simp only: dehomogenize_homogenize)
  also have "\<dots> = p" by simp
  finally show ?thesis .
qed

lemma extend_indets_ideal_subset: "extend_indets ` ideal F \<subseteq> ideal (extend_indets ` F)"
proof
  fix q
  assume "q \<in> extend_indets ` ideal F"
  then obtain p where "p \<in> ideal F" and q: "q = extend_indets p" ..
  from this(1) show "q \<in> ideal (extend_indets ` F)" unfolding q
  proof (induct p rule: ideal.span_induct')
    case base
    show ?case by (simp add: ideal.span_zero)
  next
    case (step a q p)
    have "extend_indets (a + q * p) = extend_indets a + extend_indets q * extend_indets p"
      by (simp only: extend_indets_plus extend_indets_times)
    also from step.hyps(2, 3) have "\<dots> \<in> ideal (extend_indets ` F)"
      by (intro ideal.span_add ideal.span_scale ideal.span_base[of "extend_indets p"] imageI)
    finally show ?case .
  qed
qed

lemma restrict_indets_ideal_subset: "restrict_indets ` ideal F \<subseteq> ideal (restrict_indets ` F)"
proof
  fix q
  assume "q \<in> restrict_indets ` ideal F"
  then obtain p where "p \<in> ideal F" and q: "q = restrict_indets p" ..
  from this(1) show "q \<in> ideal (restrict_indets ` F)" unfolding q
  proof (induct p rule: ideal.span_induct')
    case base
    show ?case by (simp add: ideal.span_zero)
  next
    case (step a q p)
    have "restrict_indets (a + q * p) = restrict_indets a + restrict_indets q * restrict_indets p"
      by (simp only: restrict_indets_plus restrict_indets_times)
    also from step.hyps(2, 3) have "\<dots> \<in> ideal (restrict_indets ` F)"
      by (intro ideal.span_add ideal.span_scale ideal.span_base[of "restrict_indets p"] imageI)
    finally show ?case .
  qed
qed

lemma ideal_restrict_indets:
  assumes "ideal G = ideal (homogenize None ` extend_indets ` F)" (is "_ = ideal ?F")
  shows "ideal (restrict_indets ` G) = ideal F"
proof (intro Set.equalityI ideal.span_subset_spanI)
  show "restrict_indets ` G \<subseteq> ideal F"
  proof
    fix q
    assume "q \<in> restrict_indets ` G"
    then obtain g where "g \<in> G" and q: "q = restrict_indets g" ..
    from this(1) have "g \<in> ideal G" by (rule ideal.span_base)
    also have "\<dots> = ideal ?F" by fact
    finally have "q \<in> restrict_indets ` ideal ?F" using q by (rule rev_image_eqI)
    also have "\<dots> \<subseteq> ideal (restrict_indets ` ?F)" by (rule restrict_indets_ideal_subset)
    also have "restrict_indets ` ?F = F"
      by (auto simp: image_image simp del: dehomogenize_homogenize)
    finally show "q \<in> ideal F" .
  qed
next
  show "F \<subseteq> ideal (restrict_indets ` G)"
  proof
    fix f
    assume "f \<in> F"
    hence "homogenize None (extend_indets f) \<in> ?F" by (intro imageI)
    also have "\<dots> \<subseteq> ideal ?F" by (rule ideal.span_superset)
    also from assms(1) have "\<dots> = ideal G" by (rule sym)
    finally have "restrict_indets (homogenize None (extend_indets f)) \<in> restrict_indets ` ideal G"
      by (rule imageI)
    with \<open>f \<in> F\<close> have "f \<in> restrict_indets ` ideal G" by simp
    also have "\<dots> \<subseteq> ideal (restrict_indets ` G)" by (rule restrict_indets_ideal_subset)
    finally show "f \<in> ideal (restrict_indets ` G)" .
  qed
qed

subsection \<open>Canonical Isomorphisms between \<open>P[X,Y]\<close> and \<open>P[X][Y]\<close>: \<open>focus\<close> and \<open>flatten\<close>\<close>

definition focus :: "'x set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_monoid_add)"
  where "focus X p = (\<Sum>t\<in>keys p. monomial (monomial (lookup p t) (except t X)) (except t (- X)))"

definition flatten :: "('a \<Rightarrow>\<^sub>0 'a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a::comm_powerprod \<Rightarrow>\<^sub>0 'b::semiring_1)"
  where "flatten p = (\<Sum>t\<in>keys p. punit.monom_mult 1 t (lookup p t))"

lemma focus_superset:
  assumes "finite A" and "keys p \<subseteq> A"
  shows "focus X p = (\<Sum>t\<in>A. monomial (monomial (lookup p t) (except t X)) (except t (- X)))"
  unfolding focus_def using assms by (rule sum.mono_neutral_left) simp

lemma keys_focus: "keys (focus X p) = (\<lambda>t. except t (- X)) ` keys p"
proof
  have "keys (focus X p) \<subseteq> (\<Union>t\<in>keys p. keys (monomial (monomial (lookup p t) (except t X)) (except t (- X))))"
    unfolding focus_def by (rule keys_sum_subset)
  also have "\<dots> \<subseteq> (\<Union>t\<in>keys p. {except t (- X)})" by (intro UN_mono subset_refl) simp
  also have "\<dots> = (\<lambda>t. except t (- X)) ` keys p" by (rule UNION_singleton_eq_range)
  finally show "keys (focus X p) \<subseteq> (\<lambda>t. except t (- X)) ` keys p" .
next
  {
    fix s
    assume "s \<in> keys p"
    have "lookup (focus X p) (except s (- X)) =
              (\<Sum>t\<in>keys p. monomial (lookup p t) (except t X) when except t (- X) = except s (- X))"
      (is "_ = ?p")
      by (simp only: focus_def lookup_sum lookup_single)
    also have "\<dots> \<noteq> 0"
    proof
      have "lookup ?p (except s X) =
              (\<Sum>t\<in>keys p. lookup p t when except t X = except s X \<and> except t (- X) = except s (- X))"
        by (simp add: lookup_sum lookup_single when_def if_distrib if_distribR)
            (metis (no_types, hide_lams) lookup_single_eq lookup_single_not_eq lookup_zero)
      also have "\<dots> = (\<Sum>t\<in>{s}. lookup p t)"
      proof (intro sum.mono_neutral_cong_right ballI)
        fix t
        assume "t \<in> keys p - {s}"
        hence "t \<noteq> s" by simp
        hence "except t X + except t (- X) \<noteq> except s X + except s (- X)"
          by (simp flip: except_decomp)
        thus "(lookup p t when except t X = except s X \<and> except t (- X) = except s (- X)) = 0"
          by (auto simp: when_def)
      next
        from \<open>s \<in> keys p\<close> show "{s} \<subseteq> keys p" by simp
      qed simp_all
      also from \<open>s \<in> keys p\<close> have "\<dots> \<noteq> 0" by simp
      finally have "except s X \<in> keys ?p" by simp
      moreover assume "?p = 0"
      ultimately show False by simp
    qed
    finally have "except s (- X) \<in> keys (focus X p)" by simp
  }
  thus "(\<lambda>t. except t (- X)) ` keys p \<subseteq> keys (focus X p)" by blast
qed

lemma keys_coeffs_focus_subset:
  assumes "c \<in> range (lookup (focus X p))"
  shows "keys c \<subseteq> (\<lambda>t. except t X) ` keys p"
proof -
  from assms obtain s where "c = lookup (focus X p) s" ..
  hence "keys c = keys (lookup (focus X p) s)" by (simp only:)
  also have "\<dots> \<subseteq> (\<Union>t\<in>keys p. keys (lookup (monomial (monomial (lookup p t) (except t X)) (except t (- X))) s))"
    unfolding focus_def lookup_sum by (rule keys_sum_subset)
  also from subset_refl have "\<dots> \<subseteq> (\<Union>t\<in>keys p. {except t X})"
    by (rule UN_mono) (simp add: lookup_single when_def)
  also have "\<dots> = (\<lambda>t. except t X) ` keys p" by (rule UNION_singleton_eq_range)
  finally show ?thesis .
qed

lemma focus_in_Polys':
  assumes "p \<in> P[Y]"
  shows "focus X p \<in> P[Y \<inter> X]"
proof (intro PolysI subsetI)
  fix t
  assume "t \<in> keys (focus X p)"
  then obtain s where "s \<in> keys p" and t: "t = except s (- X)" unfolding keys_focus ..
  note this(1)
  also from assms have "keys p \<subseteq> .[Y]" by (rule PolysD)
  finally have "keys s \<subseteq> Y" by (rule PPsD)
  hence "keys t \<subseteq> Y \<inter> X" by (simp add: t keys_except le_infI1)
  thus "t \<in> .[Y \<inter> X]" by (rule PPsI)
qed

corollary focus_in_Polys: "focus X p \<in> P[X]"
proof -
  have "p \<in> P[UNIV]" by simp
  hence "focus X p \<in> P[UNIV \<inter> X]" by (rule focus_in_Polys')
  thus ?thesis by simp
qed

lemma focus_coeffs_subset_Polys':
  assumes "p \<in> P[Y]"
  shows "range (lookup (focus X p)) \<subseteq> P[Y - X]"
proof (intro subsetI PolysI)
  fix c t
  assume "c \<in> range (lookup (focus X p))"
  hence "keys c \<subseteq> (\<lambda>t. except t X) ` keys p" by (rule keys_coeffs_focus_subset)
  moreover assume "t \<in> keys c"
  ultimately have "t \<in> (\<lambda>t. except t X) ` keys p" ..
  then obtain s where "s \<in> keys p" and t: "t = except s X" ..
  note this(1)
  also from assms have "keys p \<subseteq> .[Y]" by (rule PolysD)
  finally have "keys s \<subseteq> Y" by (rule PPsD)
  hence "keys t \<subseteq> Y - X" by (simp add: t keys_except Diff_mono)
  thus "t \<in> .[Y - X]" by (rule PPsI)
qed

corollary focus_coeffs_subset_Polys: "range (lookup (focus X p)) \<subseteq> P[- X]"
proof -
  have "p \<in> P[UNIV]" by simp
  hence "range (lookup (focus X p)) \<subseteq> P[UNIV - X]" by (rule focus_coeffs_subset_Polys')
  thus ?thesis by (simp only: Compl_eq_Diff_UNIV)
qed

lemma focus_zero [simp]: "focus X 0 = 0"
  by (simp add: focus_def)

lemma focus_eq_zero_iff [iff]: "focus X p = 0 \<longleftrightarrow> p = 0"
  by (simp add: keys_focus flip: keys_eq_empty_iff)

lemma focus_one [simp]: "focus X 1 = 1"
  by (simp add: focus_def)

lemma focus_monomial: "focus X (monomial c t) = monomial (monomial c (except t X)) (except t (- X))"
  by (simp add: focus_def)

lemma focus_uminus [simp]: "focus X (- p) = - focus X p"
  by (simp add: focus_def keys_uminus single_uminus sum_negf)

lemma focus_plus: "focus X (p + q) = focus X p + focus X q"
proof -
  have "finite (keys p \<union> keys q)" by simp
  moreover have "keys (p + q) \<subseteq> keys p \<union> keys q" by (rule keys_add_subset)
  ultimately show ?thesis
    by (simp add: focus_superset[where A="keys p \<union> keys q"] lookup_add single_add sum.distrib)
qed

lemma focus_minus: "focus X (p - q) = focus X p - focus X (q::_ \<Rightarrow>\<^sub>0 _::ab_group_add)"
  by (simp only: diff_conv_add_uminus focus_plus focus_uminus)

lemma focus_times: "focus X (p * q) = focus X p * focus X q"
proof -
  have eq: "focus X (monomial c s * q) = focus X (monomial c s) * focus X q" for c s
  proof -
    have "focus X (monomial c s * q) = focus X (punit.monom_mult c s q)"
      by (simp only: times_monomial_left)
    also have "\<dots> = (\<Sum>t\<in>(+) s ` keys q. monomial (monomial (lookup (punit.monom_mult c s q) t)
                                            (except t X)) (except t (- X)))"
      by (rule focus_superset) (simp_all add: punit.keys_monom_mult_subset[simplified])
    also have "\<dots> = (\<Sum>t\<in>keys q. ((\<lambda>t. monomial (monomial (lookup (punit.monom_mult c s q) t)
                                  (except t X)) (except t (- X))) \<circ> ((+) s)) t)"
      by (rule sum.reindex) simp
    also have "\<dots> = monomial (monomial c (except s X)) (except s (- X)) *
                      (\<Sum>t\<in>keys q. monomial (monomial (lookup q t) (except t X)) (except t (- X)))"
      by (simp add: o_def punit.lookup_monom_mult except_plus times_monomial_monomial sum_distrib_left)
    also have "\<dots> = focus X (monomial c s) * focus X q"
      by (simp only: focus_monomial focus_def[where p=q])
    finally show ?thesis .
  qed
  show ?thesis by (induct p rule: poly_mapping_plus_induct) (simp_all add: ring_distribs focus_plus eq)
qed

lemma focus_sum: "focus X (sum f I) = (\<Sum>i\<in>I. focus X (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: focus_plus)

lemma focus_prod: "focus X (prod f I) = (\<Prod>i\<in>I. focus X (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: focus_times)

lemma focus_power [simp]: "focus X (f ^ m) = focus X f ^ m"
  by (induct m) (simp_all add: focus_times)

lemma focus_Polys:
  assumes "p \<in> P[X]"
  shows "focus X p = (\<Sum>t\<in>keys p. monomial (monomial (lookup p t) 0) t)"
  unfolding focus_def
proof (rule sum.cong)
  fix t
  assume "t \<in> keys p"
  also from assms have "\<dots> \<subseteq> .[X]" by (rule PolysD)
  finally have "keys t \<subseteq> X" by (rule PPsD)
  hence "except t X = 0" and "except t (- X) = t" by (rule except_eq_zeroI, auto simp: except_id_iff)
  thus "monomial (monomial (lookup p t) (except t X)) (except t (- X)) =
        monomial (monomial (lookup p t) 0) t" by simp
qed (fact refl)

lemma focus_Polys_Compl:
  assumes "p \<in> P[- X]"
  shows "focus X p = monomial p 0"
proof -
  have "focus X p = (\<Sum>t\<in>keys p. monomial (monomial (lookup p t) t) 0)" unfolding focus_def
  proof (rule sum.cong)
    fix t
    assume "t \<in> keys p"
    also from assms have "\<dots> \<subseteq> .[- X]" by (rule PolysD)
    finally have "keys t \<subseteq> - X" by (rule PPsD)
    hence "except t (- X) = 0" and "except t X = t" by (rule except_eq_zeroI, auto simp: except_id_iff)
    thus "monomial (monomial (lookup p t) (except t X)) (except t (- X)) =
          monomial (monomial (lookup p t) t) 0" by simp
  qed (fact refl)
  also have "\<dots> = monomial (\<Sum>t\<in>keys p. monomial (lookup p t) t) 0" by (simp only: monomial_sum)
  also have "\<dots> = monomial p 0" by (simp only: poly_mapping_sum_monomials)
  finally show ?thesis .
qed

corollary focus_empty [simp]: "focus {} p = monomial p 0"
  by (rule focus_Polys_Compl) simp

lemma focus_Int:
  assumes "p \<in> P[Y]"
  shows "focus (X \<inter> Y) p = focus X p"
  unfolding focus_def using refl
proof (rule sum.cong)
  fix t
  assume "t \<in> keys p"
  also from assms have "\<dots> \<subseteq> .[Y]" by (rule PolysD)
  finally have "keys t \<subseteq> Y" by (rule PPsD)
  hence "keys t \<subseteq> X \<union> Y" by blast
  hence "except t (X \<inter> Y) = except t X + except t Y" by (rule except_Int)
  also from \<open>keys t \<subseteq> Y\<close> have "except t Y = 0" by (rule except_eq_zeroI)
  finally have eq: "except t (X \<inter> Y) = except t X" by simp
  have "except t (- (X \<inter> Y)) = except (except t (- Y)) (- X)" by (simp add: except_except Un_commute)
  also from \<open>keys t \<subseteq> Y\<close> have "except t (- Y) = t" by (auto simp: except_id_iff)
  finally show "monomial (monomial (lookup p t) (except t (X \<inter> Y))) (except t (- (X \<inter> Y))) =
                monomial (monomial (lookup p t) (except t X)) (except t (- X))" by (simp only: eq)
qed

lemma flatten_superset:
  assumes "finite A" and "keys p \<subseteq> A"
  shows "flatten p = (\<Sum>t\<in>A. punit.monom_mult 1 t (lookup p t))"
  unfolding flatten_def using assms by (rule sum.mono_neutral_left) simp

lemma keys_flatten_subset: "keys (flatten p) \<subseteq> (\<Union>t\<in>keys p. (+) t ` keys (lookup p t))"
proof -
  have "keys (flatten p) \<subseteq> (\<Union>t\<in>keys p. keys (punit.monom_mult 1 t (lookup p t)))"
    unfolding flatten_def by (rule keys_sum_subset)
  also from subset_refl have "\<dots> \<subseteq> (\<Union>t\<in>keys p. (+) t ` keys (lookup p t))"
    by (rule UN_mono) (rule punit.keys_monom_mult_subset[simplified])
  finally show ?thesis .
qed

lemma flatten_in_Polys:
  assumes "p \<in> P[X]" and "lookup p ` keys p \<subseteq> P[Y]"
  shows "flatten p \<in> P[X \<union> Y]"
proof (intro PolysI subsetI)
  fix t
  assume "t \<in> keys (flatten p)"
  also have "\<dots> \<subseteq> (\<Union>t\<in>keys p. (+) t ` keys (lookup p t))" by (rule keys_flatten_subset)
  finally obtain s where "s \<in> keys p" and "t \<in> (+) s ` keys (lookup p s)" ..
  from this(2) obtain s' where "s' \<in> keys (lookup p s)" and t: "t = s + s'" ..
  from assms(1) have "keys p \<subseteq> .[X]" by (rule PolysD)
  with \<open>s \<in> keys p\<close> have "s \<in> .[X]" ..
  also have "\<dots> \<subseteq> .[X \<union> Y]" by (rule PPs_mono) simp
  finally have 1: "s \<in> .[X \<union> Y]" .
  from \<open>s \<in> keys p\<close> have "lookup p s \<in> lookup p ` keys p" by (rule imageI)
  also have "\<dots> \<subseteq> P[Y]" by fact
  finally have "keys (lookup p s) \<subseteq> .[Y]" by (rule PolysD)
  with \<open>s' \<in> _\<close> have "s' \<in> .[Y]" ..
  also have "\<dots> \<subseteq> .[X \<union> Y]" by (rule PPs_mono) simp
  finally have "s' \<in> .[X \<union> Y]" .
  with 1 show "t \<in> .[X \<union> Y]" unfolding t by (rule PPs_closed_plus)
qed

lemma flatten_zero [simp]: "flatten 0 = 0"
  by (simp add: flatten_def)

lemma flatten_one [simp]: "flatten 1 = 1"
  by (simp add: flatten_def)

lemma flatten_monomial: "flatten (monomial c t) = punit.monom_mult 1 t c"
  by (simp add: flatten_def)

lemma flatten_uminus [simp]: "flatten (- p) = - flatten (p::_ \<Rightarrow>\<^sub>0 _ \<Rightarrow>\<^sub>0 _::ring)"
  by (simp add: flatten_def keys_uminus punit.monom_mult_uminus_right sum_negf)

lemma flatten_plus: "flatten (p + q) = flatten p + flatten q"
proof -
  have "finite (keys p \<union> keys q)" by simp
  moreover have "keys (p + q) \<subseteq> keys p \<union> keys q" by (rule keys_add_subset)
  ultimately show ?thesis
    by (simp add: flatten_superset[where A="keys p \<union> keys q"] punit.monom_mult_dist_right lookup_add
                  sum.distrib)
qed

lemma flatten_minus: "flatten (p - q) = flatten p - flatten (q::_ \<Rightarrow>\<^sub>0 _ \<Rightarrow>\<^sub>0 _::ring)"
  by (simp only: diff_conv_add_uminus flatten_plus flatten_uminus)

lemma flatten_times: "flatten (p * q) = flatten p * flatten (q::_ \<Rightarrow>\<^sub>0 _ \<Rightarrow>\<^sub>0 'b::comm_semiring_1)"
proof -
  have eq: "flatten (monomial c s * q) = flatten (monomial c s) * flatten q" for c s
  proof -
    have eq: "monomial 1 (t + s) = monomial 1 s * monomial (1::'b) t" for t
      by (simp add: times_monomial_monomial add.commute)
    have "flatten (monomial c s * q) = flatten (punit.monom_mult c s q)"
      by (simp only: times_monomial_left)
    also have "\<dots> = (\<Sum>t\<in>(+) s ` keys q. punit.monom_mult 1 t (lookup (punit.monom_mult c s q) t))"
      by (rule flatten_superset) (simp_all add: punit.keys_monom_mult_subset[simplified])
    also have "\<dots> = (\<Sum>t\<in>keys q. ((\<lambda>t. punit.monom_mult 1 t (lookup (punit.monom_mult c s q) t)) \<circ> (+) s) t)"
      by (rule sum.reindex) simp
    thm times_monomial_left
    also have "\<dots> = punit.monom_mult 1 s c *
                      (\<Sum>t\<in>keys q. punit.monom_mult 1 t (lookup q t))"
      by (simp add: o_def punit.lookup_monom_mult sum_distrib_left)
          (simp add: algebra_simps eq flip: times_monomial_left)
    also have "\<dots> = flatten (monomial c s) * flatten q"
      by (simp only: flatten_monomial flatten_def[where p=q])
    finally show ?thesis .
  qed
  show ?thesis by (induct p rule: poly_mapping_plus_induct) (simp_all add: ring_distribs flatten_plus eq)
qed

lemma flatten_monom_mult:
  "flatten (punit.monom_mult c t p) = punit.monom_mult 1 t (c * flatten (p::_ \<Rightarrow>\<^sub>0 _ \<Rightarrow>\<^sub>0 'b::comm_semiring_1))"
  by (simp only: flatten_times flatten_monomial mult.assoc flip: times_monomial_left)

lemma flatten_sum: "flatten (sum f I) = (\<Sum>i\<in>I. flatten (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: flatten_plus)

lemma flatten_prod: "flatten (prod f I) = (\<Prod>i\<in>I. flatten (f i :: _ \<Rightarrow>\<^sub>0 _::comm_semiring_1))"
  by (induct I rule: infinite_finite_induct) (simp_all add: flatten_times)

lemma flatten_power [simp]: "flatten (f ^ m) = flatten (f:: _ \<Rightarrow>\<^sub>0 _::comm_semiring_1) ^ m"
  by (induct m) (simp_all add: flatten_times)

lemma inj_focus: "inj ((focus X) :: (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::ab_group_add) \<Rightarrow> _)"
proof (rule injI)
  fix p q :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"
  assume "focus X p = focus X q"
  hence "focus X (p - q) = 0" by (simp add: focus_minus)
  thus "p = q" by simp
qed

lemma flatten_focus [simp]: "flatten (focus X p) = p"
  by (induct p rule: poly_mapping_plus_induct)
      (simp_all add: focus_plus flatten_plus focus_monomial flatten_monomial
                      punit.monom_mult_monomial add.commute flip: except_decomp)

lemma focus_flatten:
  assumes "p \<in> P[X]" and "lookup p ` keys p \<subseteq> P[- X]"
  shows "focus X (flatten p) = p"
  using assms
proof (induct p rule: poly_mapping_plus_induct_Polys)
  case 0
  show ?case by simp
next
  case (plus p c t)
  from plus.hyps(3) have 1: "keys (monomial c t) = {t}" by simp
  also from plus.hyps(4) have "\<dots> \<inter> keys p = {}" by simp
  finally have "keys (monomial c t + p) = keys (monomial c t) \<union> keys p" by (rule keys_add[symmetric])
  hence 2: "keys (monomial c t + p) = insert t (keys p)" by (simp only: 1 flip: insert_is_Un)
  from \<open>t \<in> .[X]\<close> have "keys t \<subseteq> X" by (rule PPsD)
  hence eq1: "except t X = 0" and eq2: "except t (- X) = t"
    by (rule except_eq_zeroI, auto simp: except_id_iff)
  from plus.hyps(3, 4) plus.prems have "c \<in> P[- X]" and "lookup p ` keys p \<subseteq> P[- X]"
    by (simp_all add: 2 lookup_add lookup_single)
        (smt add.commute add.right_neutral image_cong plus.hyps(4) when_simps(2))
  from this(2) have "focus X (flatten p) = p" by (rule plus.hyps)
  thus ?case
    by (simp add: flatten_plus focus_plus flatten_monomial focus_times focus_monomial eq1 eq2
                  focus_Polys_Compl[OF \<open>c \<in> _\<close>] times_monomial_monomial flip: times_monomial_left)
qed

lemma indets_eval_pm_focus_subset: "indets (eval_pm a (focus X p)) \<subseteq> \<Union> (indets ` a ` X) \<union> (indets p - X)"
proof -
  let ?p = "focus X p"
  have "indets (eval_pm a ?p) \<subseteq> \<Union> (indets ` a ` indets ?p) \<union> \<Union> (indets ` lookup ?p ` keys ?p)"
    by (fact indets_eval_pm_subset)
  also have "\<dots> \<subseteq> \<Union> (indets ` a ` X) \<union> (indets p - X)"
  proof (rule Un_mono)
    from focus_in_Polys have "indets (focus X p) \<subseteq> X" by (rule PolysD)
    thus "\<Union> (indets ` a ` indets (focus X p)) \<subseteq> \<Union> (indets ` a ` X)" by blast
  next
    show "\<Union> (indets ` lookup ?p ` keys ?p) \<subseteq> indets p - X"
    proof (intro subsetI, elim UN_E)
      fix x c
      from subset_refl have "p \<in> P[indets p]" by (rule PolysI_alt)
      hence "range (lookup (focus X p)) \<subseteq> P[indets p - X]"
        by (rule focus_coeffs_subset_Polys')
      with image_mono have "lookup (focus X p) ` keys ?p \<subseteq> P[indets p - X]"
        by (rule subset_trans) simp
      moreover assume "c \<in> lookup (focus X p) ` keys (focus X p)"
      ultimately have "c \<in> P[indets p - X]" ..
      hence "indets c \<subseteq> indets p - X" by (rule PolysD)
      moreover assume "x \<in> indets c"
      ultimately show "x \<in> indets p - X" ..
    qed
  qed
  finally show ?thesis .
qed

subsection \<open>\<open>varnum_wrt\<close>\<close>

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
  have "{t::'x \<Rightarrow>\<^sub>0 'b. varnum_wrt X t \<le> m} \<subseteq> {t. keys t \<subseteq> ?V}"
  proof (rule, simp, intro subsetI, simp)
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
    thus "almost_full_on (adds) {t::'x \<Rightarrow>\<^sub>0 'b. keys t \<subseteq> ?V}" by (rule Dickson_poly_mapping)
  qed
qed

lemma varnum_wrt_le_iff: "varnum_wrt X t \<le> n \<longleftrightarrow> keys t \<subseteq> X \<union> {x. elem_index x < n}"
  by (auto simp: varnum_wrt_def Suc_le_eq)

lemma hom_grading_varnum_wrt:
  "hom_grading ((varnum_wrt X)::('x::countable \<Rightarrow>\<^sub>0 'b::add_wellorder) \<Rightarrow> nat)"
proof -
  define f where "f = (\<lambda>n t. (except t (- (X \<union> {x. elem_index x < n})))::'x \<Rightarrow>\<^sub>0 'b)"
  show ?thesis unfolding hom_grading_def hom_grading_fun_def
  proof (intro exI allI conjI impI)
    fix n s t
    show "f n (s + t) = f n s + f n t" by (simp only: f_def except_plus)
  next
    fix n t
    show "varnum_wrt X (f n t) \<le> n" by (auto simp: varnum_wrt_le_iff keys_except f_def)
  next
    fix n t
    show "varnum_wrt X  t \<le> n \<Longrightarrow> f n t = t" by (auto simp: f_def except_id_iff varnum_wrt_le_iff)
  qed
qed

lemma dgrad_set_varnum_wrt: "dgrad_set (varnum_wrt X) 0 = .[X]"
  by (simp add: dgrad_set_def PPs_def varnum_wrt_eq_zero_iff)

subsection \<open>Locale @{term pm_powerprod}\<close>

context ordered_powerprod
begin

abbreviation "lcf \<equiv> punit.lc"
abbreviation "tcf \<equiv> punit.tc"
abbreviation "lpp \<equiv> punit.lt"
abbreviation "tpp \<equiv> punit.tt"

end (* ordered_powerprod *)

locale pm_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"('x::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

sublocale gd_powerprod ..

lemma PPs_closed_lpp:
  assumes "p \<in> P[X]"
  shows "lpp p \<in> .[X]"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: zero_in_PPs)
next
  case False
  hence "lpp p \<in> keys p" by (rule punit.lt_in_keys)
  also from assms have "\<dots> \<subseteq> .[X]" by (rule PolysD)
  finally show ?thesis .
qed

lemma PPs_closed_tpp:
  assumes "p \<in> P[X]"
  shows "tpp p \<in> .[X]"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: zero_in_PPs)
next
  case False
  hence "tpp p \<in> keys p" by (rule punit.tt_in_keys)
  also from assms have "\<dots> \<subseteq> .[X]" by (rule PolysD)
  finally show ?thesis .
qed

corollary PPs_closed_image_lpp: "F \<subseteq> P[X] \<Longrightarrow> lpp ` F \<subseteq> .[X]"
  by (auto intro: PPs_closed_lpp)

corollary PPs_closed_image_tpp: "F \<subseteq> P[X] \<Longrightarrow> tpp ` F \<subseteq> .[X]"
  by (auto intro: PPs_closed_tpp)

lemma hom_component_lpp:
  assumes "p \<noteq> 0"
  shows "hom_component p (deg_pm (lpp p)) \<noteq> 0" (is "?p \<noteq> 0")
    and "lpp (hom_component p (deg_pm (lpp p))) = lpp p"
proof -
  from assms have "lpp p \<in> keys p" by (rule punit.lt_in_keys)
  hence *: "lpp p \<in> keys ?p" by (simp add: keys_hom_component)
  thus "?p \<noteq> 0" by auto

  from * show "lpp ?p = lpp p"
  proof (rule punit.lt_eqI_keys)
    fix t
    assume "t \<in> keys ?p"
    hence "t \<in> keys p" by (simp add: keys_hom_component)
    thus "t \<preceq> lpp p" by (rule punit.lt_max_keys)
  qed
qed

definition is_hom_ord :: "'x \<Rightarrow> bool"
  where "is_hom_ord x \<longleftrightarrow> (\<forall>s t. deg_pm s = deg_pm t \<longrightarrow> (s \<preceq> t \<longleftrightarrow> except s {x} \<preceq> except t {x}))"

lemma is_hom_ordD: "is_hom_ord x \<Longrightarrow> deg_pm s = deg_pm t \<Longrightarrow> s \<preceq> t \<longleftrightarrow> except s {x} \<preceq> except t {x}"
  by (simp add: is_hom_ord_def)

lemma dgrad_p_set_varnum_wrt: "punit.dgrad_p_set (varnum_wrt X) 0 = P[X]"
  by (simp add: punit.dgrad_p_set_def dgrad_set_varnum_wrt Polys_def)

end

text \<open>We must create a copy of @{locale pm_powerprod} to avoid infinite chains of interpretations.\<close>

instantiation option :: (linorder) linorder
begin

fun less_eq_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_eq_option None _ = True" |
  "less_eq_option (Some x) None = False" |
  "less_eq_option (Some x) (Some y) = (x \<le> y)"

definition less_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  where "less_option x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance proof
  fix x :: "'a option"
  show "x \<le> x" using less_eq_option.elims(3) by fastforce
qed (auto simp: less_option_def elim!: less_eq_option.elims)

end

locale extended_ord_pm_powerprod = pm_powerprod
begin

definition extended_ord :: "('a option \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('a option \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool"
  where "extended_ord s t \<longleftrightarrow> (restrict_indets_pp s \<prec> restrict_indets_pp t \<or>
                          (restrict_indets_pp s = restrict_indets_pp t \<and> lookup s None \<le> lookup t None))"

definition extended_ord_strict :: "('a option \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('a option \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool"
  where "extended_ord_strict s t \<longleftrightarrow> (restrict_indets_pp s \<prec> restrict_indets_pp t \<or>
                          (restrict_indets_pp s = restrict_indets_pp t \<and> lookup s None < lookup t None))"

sublocale extended_ord: pm_powerprod extended_ord extended_ord_strict
proof -
  have 1: "s = t" if "lookup s None = lookup t None" and "restrict_indets_pp s = restrict_indets_pp t"
    for s t :: "'a option \<Rightarrow>\<^sub>0 nat"
  proof (rule poly_mapping_eqI)
    fix y
    show "lookup s y = lookup t y"
    proof (cases y)
      case None
      with that(1) show ?thesis by simp
    next
      case y: (Some z)
      have "lookup s y = lookup (restrict_indets_pp s) z" by (simp only: lookup_restrict_indets_pp y)
      also have "\<dots> = lookup (restrict_indets_pp t) z" by (simp only: that(2))
      also have "\<dots> = lookup t y" by (simp only: lookup_restrict_indets_pp y)
      finally show ?thesis .
    qed
  qed
  have 2: "0 \<prec> t" if "t \<noteq> 0" for t::"'a \<Rightarrow>\<^sub>0 nat"
    using that zero_min by (rule ordered_powerprod_lin.dual_order.not_eq_order_implies_strict)
  show "pm_powerprod extended_ord extended_ord_strict"
    by standard (auto simp: extended_ord_def extended_ord_strict_def restrict_indets_pp_plus lookup_add 1
                  dest: plus_monotone_strict 2)
qed

lemma extended_ord_is_hom_ord: "extended_ord.is_hom_ord None"
  by (auto simp add: extended_ord_def lookup_restrict_indets_pp lookup_except extended_ord.is_hom_ord_def
            simp flip: deg_pm_restrict_indets_pp)

end

end (* theory *)
