section \<open>Multivariate Polynomials with Power-Products Represented by Polynomial Mappings\<close>

theory MPoly_PM
  imports Polynomials.MPoly_Type_Class
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
  from assms(2) have "keys p \<noteq> {}" by simp
  then obtain s where "s \<in> keys p" and "poly_deg p = deg_pm s" unfolding poly_deg_def
    by (metis (mono_tags, lifting) finite_keys Max_in finite_imageI image_iff image_is_empty)
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
  define tx where "tx = truncate_poly_mapping X t"
  from sub_keys_truncate have "keys tx \<subseteq> X" unfolding tx_def sub_keys_def .
  hence "tx \<in> .[X]" by (simp add: PPs_def)
  have "tx adds t"
    by (simp add: tx_def adds_poly_mappingI le_fun_def lookup_truncate_fun truncate_fun_def)
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
      hence "x \<notin> keys (t - tx)"
        by (simp add: tx_def lookup_truncate_fun truncate_fun_def lookup_minus)
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

subsection \<open>Locale @{term pm_powerprod}\<close>

locale pm_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"('x::countable \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

sublocale gd_powerprod ..

end

end (* theory *)
