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

(*
subsection \<open>Integral Domains\<close>

class orderable_powerprod = comm_powerprod +
  assumes "\<exists>ord ord_strict::'a \<Rightarrow> 'a \<Rightarrow> bool. class.linorder ord ord_strict \<and>
                  (\<forall>s. ord 0 s) \<and> (\<forall>s t u. ord s t \<longrightarrow> ord (s + u) (t + u))"

instance "fun" :: (wellorder, add_linorder_min) orderable_powerprod
proof (standard, intro exI conjI allI impI)
  show "class.linorder (lex_fun::('a \<Rightarrow> 'b) \<Rightarrow> _) lex_fun_strict"
    apply standard
    subgoal by (simp add: lex_fun_strict_def)
    subgoal by (fact lex_fun_refl)
    subgoal by (fact lex_fun_trans)
    subgoal by (fact lex_fun_antisym)
    subgoal by (fact lex_fun_lin)
    done
next
  fix s::"'a \<Rightarrow> 'b"
  show "lex_fun 0 s" by (fact lex_fun_zero_min)
next
  fix s t u :: "'a \<Rightarrow> 'b"
  assume "lex_fun s t"
  thus "lex_fun (s + u) (t + u)" by (rule lex_fun_plus_monotone)
qed

instance poly_mapping :: (wellorder, add_linorder_min) orderable_powerprod
proof (standard, intro exI conjI allI impI)
  show "class.linorder (lex_pm::('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> _) lex_pm_strict"
    apply standard
    subgoal by (simp add: lex_pm_strict_def)
    subgoal by (fact lex_pm_refl)
    subgoal by (fact lex_pm_trans)
    subgoal by (fact lex_pm_antisym)
    subgoal by (fact lex_pm_lin)
    done
next
  fix s::"'a \<Rightarrow>\<^sub>0 'b"
  show "lex_pm 0 s" by (fact lex_pm_zero_min)
next
  fix s t u :: "'a \<Rightarrow>\<^sub>0 'b"
  assume "lex_pm s t"
  thus "lex_pm (s + u) (t + u)" by (rule lex_pm_plus_monotone)
qed

instance poly_mapping :: (orderable_powerprod, ring_no_zero_divisors) ring_no_zero_divisors
  sorry

instance poly_mapping :: (orderable_powerprod, ring_1_no_zero_divisors) ring_1_no_zero_divisors
  ..

instance poly_mapping :: (orderable_powerprod, idom) idom
  ..
*)

subsection \<open>Order relation on polynomial mappings\<close>

definition le_pm :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::{ord,zero}) \<Rightarrow> bool" (infixl "\<unlhd>" 50)
  where "le_pm s t \<longleftrightarrow> (lookup s \<le> lookup t)"

lemma le_pmI:
  assumes "\<And>x. lookup s x \<le> lookup t x"
  shows "s \<unlhd> t"
  unfolding le_pm_def le_fun_def using assms ..

lemma le_pmD:
  assumes "s \<unlhd> t"
  shows "lookup s x \<le> lookup t x"
  using assms unfolding le_pm_def le_fun_def ..

lemma adds_pmI:
  assumes "s \<unlhd> t"
  shows "s adds (t::'a \<Rightarrow>\<^sub>0 'b::add_linorder)"
  using assms by (simp add: le_pm_def, intro adds_poly_mappingI)

lemma adds_pm: "s adds t \<longleftrightarrow> s \<unlhd> t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  by (simp add: adds_poly_mapping le_pm_def)

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

lemma deg_pm_mono: "s adds t \<Longrightarrow> deg_pm s \<le> deg_pm (t::_ \<Rightarrow>\<^sub>0 _::add_linorder_min)"
  unfolding adds_poly_mapping by (transfer) (auto intro!: deg_fun_leq simp: supp_fun_def)

lemma deg_pm_minus:
  assumes "s adds (t::_ \<Rightarrow>\<^sub>0 _::comm_monoid_add)"
  shows "deg_pm (t - s) = deg_pm t - deg_pm s"
proof -
  from assms have "(t - s) + s = t" by (rule adds_minus)
  hence "deg_pm t = deg_pm ((t - s) + s)" by simp
  also have "\<dots> = deg_pm (t - s) + deg_pm s" by (simp only: deg_pm_plus)
  finally show ?thesis by simp
qed

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

lemma poly_deg_max_keys:
  assumes "t \<in> keys p"
  shows "deg_pm t \<le> poly_deg p"
  unfolding poly_deg_def using finite_keys assms by auto

lemma poly_deg_leI:
  assumes "\<And>t. t \<in> keys p \<Longrightarrow> deg_pm t \<le> (d::'a::add_linorder_min)"
  shows "poly_deg p \<le> d"
  unfolding poly_deg_def using finite_keys assms by auto

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

lemma zero_in_Polys: "0 \<in> P[X]"
  by (simp add: Polys_def)

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

lemma Polys_closed_times: "p \<in> P[X] \<Longrightarrow> q \<in> P[X] \<Longrightarrow> p * q \<in> P[X]"
  using indets_times_subset[of p q] by (auto simp: Polys_alt PPs_def)

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

lemma zero_in_deg_set: "0 \<in> deg_le_sect n d"
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

definition subst_pp :: "('x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a)) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
  where "subst_pp f t = (\<Prod>x\<in>keys t. (f x) ^ (lookup t x))"

definition poly_subst :: "('x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a)) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
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
  shows "subst_pp (\<lambda>_. 0) t = (0::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1))"
  unfolding subst_pp_def using finite_keys
proof (rule prod_zero)
  from assms have "keys t \<noteq> {}" by simp
  then obtain x where "x \<in> keys t" by blast
  thus "\<exists>x\<in>keys t. 0 ^ lookup t x = (0::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b))"
  proof
    from \<open>x \<in> keys t\<close> have "0 < lookup t x" by (simp add: in_keys_iff)
    thus "0 ^ lookup t x = (0::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b))" by (rule Power.semiring_1_class.zero_power)
  qed
qed

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
    by (simp add: punit.monomial_prod_sum[symmetric] punit.poly_mapping_sum_monomials)
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

lemma poly_deg_subst_pp_eq_zeroI:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> poly_deg (f x) = 0"
  shows "poly_deg (subst_pp f (t::'x \<Rightarrow>\<^sub>0 nat)) = 0"
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
  shows "poly_deg (subst_pp f (t::'x \<Rightarrow>\<^sub>0 nat)) \<le> deg_pm t"
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
  also have "... = p" by (simp only: punit.poly_mapping_sum_monomials)
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
  shows "poly_deg (poly_subst f (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)) = 0"
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
    have "d \<le> deg_pm (0::'x \<Rightarrow>\<^sub>0 nat) + poly_deg (subst_pp f t)"
      unfolding d by (fact poly_deg_monom_mult_le)
    also have "... = poly_deg (subst_pp f t)" by simp
    also have "... = 0" by (rule poly_deg_subst_pp_eq_zeroI, rule assms, erule in_indetsI, fact)
    finally show "d \<le> 0" .
  qed
  finally show ?thesis by simp
qed

lemma poly_deg_poly_subst_le:
  assumes "\<And>x. x \<in> indets p \<Longrightarrow> poly_deg (f x) \<le> 1"
  shows "poly_deg (poly_subst f (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)) \<le> poly_deg p"
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
    have "d \<le> deg_pm (0::'x \<Rightarrow>\<^sub>0 nat) + poly_deg (subst_pp f t)"
      unfolding d by (fact poly_deg_monom_mult_le)
    also have "... = poly_deg (subst_pp f t)" by simp
    also have "... \<le> deg_pm t" by (rule poly_deg_subst_pp_le, rule assms, erule in_indetsI, fact)
    also from \<open>t \<in> keys p\<close> have "... \<le> poly_deg p" by (rule poly_deg_max_keys)
    finally show "d \<le> poly_deg p" .
  qed
  finally show ?thesis by simp
qed

subsection \<open>Homogeneity\<close>

definition homogeneous :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) \<Rightarrow> bool"
  where "homogeneous p \<longleftrightarrow> (\<forall>s\<in>keys p. \<forall>t\<in>keys p. deg_pm s = deg_pm t)"

definition hom_component :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero)"
  where "hom_component p n = except p {t. deg_pm t \<noteq> n}"

definition hom_components :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set"
  where "hom_components p = hom_component p ` deg_pm ` keys p"

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

lemma homogeneous_ideal:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F"
  shows "hom_component p n \<in> ideal F"
proof -
  from assms(2) have "p \<in> punit.pmdl F" by simp
  thus ?thesis
  proof (induct p rule: punit.pmdl_induct)
    case module_0
    show ?case by (simp add: ideal.module_0)
  next
    case (module_plus a f c t)
    let ?f = "punit.monom_mult c t f"
    from module_plus.hyps(3) have "f \<in> punit.pmdl F" by (simp add: ideal.generator_in_module)
    hence *: "?f \<in> punit.pmdl F" by (rule punit.pmdl_closed_monom_mult)
    from module_plus.hyps(3) have "homogeneous f" by (rule assms(1))
    hence "homogeneous ?f" by (rule homogeneous_monom_mult)
    hence "hom_component ?f n = (?f when n = poly_deg ?f)" by (rule hom_component_of_homogeneous)
    also from * have "\<dots> \<in> ideal F" by (simp add: when_def ideal.module_0)
    finally have "hom_component ?f n \<in> ideal F" .
    with module_plus.hyps(2) show ?case unfolding hom_component_plus by (rule ideal.module_closed_plus)
  qed
qed

corollary homogeneous_ideal':
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F" and "q \<in> hom_components p"
  shows "q \<in> ideal F"
proof -
  from assms(3) obtain s::"'a \<Rightarrow>\<^sub>0 nat" where "q = hom_component p (deg_pm s)"
    by (rule hom_componentsE)
  also from assms(1, 2) have "\<dots> \<in> ideal F" by (rule homogeneous_ideal)
  finally show ?thesis .
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
      by (simp only: punit.poly_mapping_sum_monomials flip: punit.monom_mult_sum_right)
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
    unfolding homogenize_def by (rule punit.keys_sum_subset)
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
    unfolding homogenize_alt by (rule punit.keys_sum_subset)
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

lemma homogeneous_ideal_homogenize:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "p \<in> ideal F"
  shows "homogenize x p \<in> ideal F"
proof -
  have "homogenize x p = (\<Sum>q\<in>hom_components p. punit.monom_mult 1 (Poly_Mapping.single x (poly_deg p - poly_deg q)) q)"
    by (fact homogenize_alt)
  also have "\<dots> \<in> ideal F"
  proof (rule ideal.module_closed_sum)
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

lemma dehomogenize_zero [simp]: "dehomogenize x 0 = 0"
  by (simp add: dehomogenize_def)

lemma dehomogenize_plus: "dehomogenize x (p + q) = dehomogenize x p + dehomogenize x q"
  by (simp only: dehomogenize_def poly_subst_plus)

lemma dehomogenize_uminus: "dehomogenize x (- p) = - dehomogenize x (p::_ \<Rightarrow>\<^sub>0 'a::comm_ring_1)"
  by (simp only: dehomogenize_def poly_subst_uminus)

lemma dehomogenize_minus:
  "dehomogenize x (p - q) = dehomogenize x p - dehomogenize x (q::_ \<Rightarrow>\<^sub>0 'a::comm_ring_1)"
  by (simp only: dehomogenize_def poly_subst_minus)

lemma dehomogenize_monomial: "dehomogenize x (monomial c t) = monomial c (except t {x})"
  by (simp add: dehomogenize_def poly_subst_monomial punit.monom_mult_monomial)

corollary dehomogenize_one [simp]: "dehomogenize x 1 = 1"
  by (simp add: dehomogenize_monomial flip: single_one)

lemma dehomogenize_times: "dehomogenize x (p * q) = dehomogenize x p * dehomogenize x q"
  by (simp only: dehomogenize_def poly_subst_times)

corollary dehomogenize_monom_mult:
  "dehomogenize x (punit.monom_mult c t p) = punit.monom_mult c (except t {x}) (dehomogenize x p)"
  by (simp only: times_monomial_left[symmetric] dehomogenize_times dehomogenize_monomial)

lemma dehomogenize_power: "dehomogenize x (p ^ n) = (dehomogenize x p) ^ n"
  by (induct n, simp_all add: dehomogenize_times)

lemma dehomogenize_sum: "dehomogenize x (sum p A) = (\<Sum>a\<in>A. dehomogenize x (p a))"
  by (simp only: dehomogenize_def poly_subst_sum)

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
    by (simp only: punit.poly_mapping_sum_monomials)
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
    unfolding dehomogenize_alt by (rule punit.keys_sum_subset)
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
    also have "\<dots> = p" by (fact punit.poly_mapping_sum_monomials)
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
  proof (induct p rule: ideal.module_induct)
    case module_0
    show ?case by (simp add: ideal.module_0)
  next
    case (module_plus a q p)
    have "dehomogenize x (a + q * p) = dehomogenize x a + dehomogenize x q * dehomogenize x p"
      by (simp only: dehomogenize_plus dehomogenize_times)
    also from module_plus.hyps(2, 3) have "\<dots> \<in> ideal (dehomogenize x ` F)"
      by (intro ideal.module_plus imageI)
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
  proof (intro Set.equalityI ideal.module_subset_moduleI)
    show "dehomogenize x ` G \<subseteq> ideal F"
    proof
      fix q
      assume "q \<in> dehomogenize x ` G"
      then obtain g where "g \<in> G" and q: "q = dehomogenize x g" ..
      from this(1) have "g \<in> ideal G" by (rule ideal.generator_in_module)
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
      also have "\<dots> \<subseteq> ideal (homogenize x ` F)" by (rule ideal.generator_subset_module)
      also from assms(1) have "\<dots> = ideal G" by (rule sym)
      finally have "dehomogenize x (homogenize x f) \<in> dehomogenize x ` ideal G" by (rule imageI)
      with \<open>f \<in> F\<close> have "f \<in> dehomogenize x ` ideal G" by (simp only: eq)
      also have "\<dots> \<subseteq> ideal (dehomogenize x ` G)" by (rule dehomogenize_ideal_subset)
      finally show "f \<in> ideal (dehomogenize x ` G)" .
    qed
  qed
qed

subsection \<open>\<open>varnum_wrt\<close>\<close>

(* TODO: Move. *)
lemma subset_imageE_inj:
  assumes "B \<subseteq> f ` A"
  obtains C where "C \<subseteq> A" and "B = f ` C" and "inj_on f C"
proof -
  define g where "g = (\<lambda>x. SOME a. a \<in> A \<and> f a = x)"
  have "g b \<in> A \<and> f (g b) = b" if "b \<in> B" for b
  proof -
    from that assms have "b \<in> f ` A" ..
    then obtain a where "a \<in> A" and "b = f a" ..
    hence "a \<in> A \<and> f a = b" by simp
    thus ?thesis unfolding g_def by (rule someI)
  qed
  hence 1: "\<And>b. b \<in> B \<Longrightarrow> g b \<in> A" and 2: "\<And>b. b \<in> B \<Longrightarrow> f (g b) = b" by simp_all
  let ?C = "g ` B"
  show ?thesis
  proof
    show "?C \<subseteq> A" by (auto intro: 1)
  next
    show "B = f ` ?C"
    proof (rule set_eqI)
      fix b
      show "b \<in> B \<longleftrightarrow> b \<in> f ` ?C"
      proof
        assume "b \<in> B"
        moreover from this have "f (g b) = b" by (rule 2)
        ultimately show "b \<in> f ` ?C" by force
      next
        assume "b \<in> f ` ?C"
        then obtain b' where "b' \<in> B" and "b = f (g b')" unfolding image_image ..
        moreover from this(1) have "f (g b') = b'" by (rule 2)
        ultimately show "b \<in> B" by simp
      qed
    qed
  next
    show "inj_on f ?C"
    proof
      fix x y
      assume "x \<in> ?C"
      then obtain bx where "bx \<in> B" and x: "x = g bx" ..
      moreover from this(1) have "f (g bx) = bx" by (rule 2)
      ultimately have *: "f x = bx" by simp
      assume "y \<in> ?C"
      then obtain "by" where "by \<in> B" and y: "y = g by" ..
      moreover from this(1) have "f (g by) = by" by (rule 2)
      ultimately have "f y = by" by simp
      moreover assume "f x = f y"
      ultimately have "bx = by" using * by simp
      thus "x = y" by (simp only: x y)
    qed
  qed
qed

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

subsection \<open>Locale @{term pm_powerprod}\<close>

locale pm_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"('x::countable \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

sublocale gd_powerprod ..

definition is_hom_ord :: "'x \<Rightarrow> bool"
  where "is_hom_ord x \<longleftrightarrow> (\<forall>s t. deg_pm s = deg_pm t \<longrightarrow> (s \<preceq> t \<longleftrightarrow> except s {x} \<preceq> except t {x}))"

definition hom_ord_of :: "'x \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool"
  where "hom_ord_of x s t \<longleftrightarrow> (except s {x} \<prec> except t {x} \<or> (except s {x} = except t {x} \<and> lookup s x \<le> lookup t x))"

definition hom_ord_strict_of :: "'x \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool"
  where "hom_ord_strict_of x s t \<longleftrightarrow> (except s {x} \<prec> except t {x} \<or> (except s {x} = except t {x} \<and> lookup s x < lookup t x))"

lemma is_hom_ordD: "is_hom_ord x \<Longrightarrow> deg_pm s = deg_pm t \<Longrightarrow> s \<preceq> t \<longleftrightarrow> except s {x} \<preceq> except t {x}"
  by (simp add: is_hom_ord_def)

lemma dgrad_set_varnum_wrt: "dgrad_set (varnum_wrt X) 0 = .[X]"
  by (simp add: dgrad_set_def PPs_def varnum_wrt_eq_zero_iff)

lemma dgrad_p_set_varnum_wrt: "punit.dgrad_p_set (varnum_wrt X) 0 = P[X]"
  by (simp add: punit.dgrad_p_set_def dgrad_set_varnum_wrt Polys_def)

lemmas in_idealE_Polys =
  punit.in_moduleE_dgrad_p_set[simplified, OF hom_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]

end

text \<open>We must create a copy of @{locale pm_powerprod} to avoid infinite chains of interpretations.\<close>

locale hom_ord_pm_powerprod = pm_powerprod
begin

sublocale hom_ord: pm_powerprod "hom_ord_of x" "hom_ord_strict_of x" for x
proof -
  have 1: "s = t" if "lookup s x = lookup t x" and "except s {x} = except t {x}" for s t :: "'a \<Rightarrow>\<^sub>0 nat"
  proof (rule poly_mapping_eqI)
    fix y
    show "lookup s y = lookup t y"
    proof (cases "y = x")
      case True
      with that(1) show ?thesis by simp
    next
      case False
      have "lookup s y = lookup (except s {x}) y" by (simp add: lookup_except False)
      also have "\<dots> = lookup (except t {x}) y" by (simp only: that(2))
      also have "\<dots> = lookup t y" by (simp add: lookup_except False)
      finally show ?thesis .
    qed
  qed
  have 2: "0 \<prec> t" if "t \<noteq> 0" for t::"'a \<Rightarrow>\<^sub>0 nat"
    using that zero_min by (rule ordered_powerprod_lin.dual_order.not_eq_order_implies_strict)
  show "pm_powerprod (hom_ord_of x) (hom_ord_strict_of x)"
    by standard (auto simp: hom_ord_of_def hom_ord_strict_of_def except_plus lookup_add 1
                  dest: plus_monotone_strict 2)
qed

lemma hom_ord_is_hom_ord: "hom_ord.is_hom_ord x x"
  unfolding hom_ord.is_hom_ord_def
proof (intro allI impI)
  fix s t :: "'a \<Rightarrow>\<^sub>0 nat"
  assume *: "deg_pm s = deg_pm t"
  have 1: "lookup s x \<le> lookup t x" if "except s {x} = except t {x}"
  proof -
    have "deg_pm (Poly_Mapping.single x (lookup s x) + except s {x}) =
          deg_pm (Poly_Mapping.single x (lookup t x) + except t {x})"
      by (simp only: * flip: plus_except)
    thus ?thesis by (simp add: deg_pm_plus that deg_pm_single)
  qed
  show "hom_ord_of x s t \<longleftrightarrow> hom_ord_of x (except s {x}) (except t {x})"
    by (auto simp add: hom_ord_of_def except_except lookup_except dest: 1)
qed

end

end (* theory *)
