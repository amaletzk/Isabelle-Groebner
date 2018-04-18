section \<open>Multivariate Polynomials with Power-Products Represented by Polynomial Mappings\<close>

theory MPoly_PM
  imports Polynomials.MPoly_Type_Class
begin

text \<open>Many notions introduced in this theory for type @{typ "('n \<Rightarrow>\<^sub>0 'a) \<Rightarrow>\<^sub>0 'b"} closely resemble
  those introduced in @{theory MPoly_Type} for type @{typ "'a mpoly"}.\<close>

lemma monomial_single_power:
  "(monomial c (Poly_Mapping.single x k)) ^ n = monomial (c ^ n) (Poly_Mapping.single x (k * n))"
proof -
  have eq: "(\<Sum>i = 0..<n. Poly_Mapping.single x k) = Poly_Mapping.single x (k * n)"
    by (induct n, simp_all add: add.commute single_add)
  show ?thesis by (simp add: monomial_power eq)
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

definition poly_deg :: "(('n \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a" where
  "poly_deg p = (if keys p = {} then 0 else Max (deg_pm ` keys p))"

definition maxdeg :: "(('n \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> 'a" where
  "maxdeg A = Max (poly_deg ` A)"
  
definition mindeg :: "(('n \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> 'a" where
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
  "poly_deg (monom_mult c (t::_ \<Rightarrow>\<^sub>0 'a::add_linorder_min) p) \<le> deg_pm t + poly_deg p"
proof -
  have "poly_deg (monom_mult c t p) \<le> poly_deg (monomial c t) + poly_deg p"
    by (simp only: times_monomial_left[symmetric] poly_deg_times_le)
  also have "... \<le> deg_pm t + poly_deg p" by (simp add: poly_deg_monomial)
  finally show ?thesis .
qed

lemma poly_deg_monom_mult:
  assumes "c \<noteq> 0" and "p \<noteq> (0::(_ \<Rightarrow>\<^sub>0 'a::add_linorder_min) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "poly_deg (monom_mult c t p) = deg_pm t + poly_deg p"
proof (rule order.antisym, fact poly_deg_monom_mult_le)
  from assms(2) have "keys p \<noteq> {}" by simp
  then obtain s where "s \<in> keys p" and "poly_deg p = deg_pm s" unfolding poly_deg_def
    by (metis (mono_tags, lifting) finite_keys Max_in finite_imageI image_iff image_is_empty)
  have "deg_pm t + poly_deg p = deg_pm (t + s)" by (simp add: \<open>poly_deg p = deg_pm s\<close> deg_pm_plus)
  also have "... \<le> poly_deg (monom_mult c t p)"
  proof (rule poly_deg_max_keys)
    from \<open>s \<in> keys p\<close> show "t + s \<in> keys (monom_mult c t p)"
      unfolding keys_monom_mult[OF assms(1)] by fastforce
  qed
  finally show "deg_pm t + poly_deg p \<le> poly_deg (monom_mult c t p)" .
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

definition indets :: "(('n \<Rightarrow>\<^sub>0 'a::zero) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'n set"
  where "indets p = UNION (keys p) keys"

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

lemma indets_times_subset: "indets (p * q) \<subseteq> indets p \<union> indets q"
proof
  fix x
  assume "x \<in> indets (p * q)"
  then obtain t where "t \<in> keys (p * q)" and "x \<in> keys t" unfolding indets_def by blast
  from this(1) obtain u v where "u \<in> keys p" "v \<in> keys q" and "t = u + v" by (rule in_keys_timesE)
  hence "x \<in> keys u \<union> keys v" by (metis \<open>x \<in> keys t\<close> keys_add_subset subsetCE)
  thus "x \<in> indets p \<union> indets q" unfolding indets_def using \<open>u \<in> keys p\<close> \<open>v \<in> keys q\<close> by blast
qed

corollary indets_monom_mult_subset: "indets (monom_mult c t p) \<subseteq> keys t \<union> indets p"
proof -
  have "indets (monom_mult c t p) \<subseteq> indets (monomial c t) \<union> indets p"
    by (simp only: times_monomial_left[symmetric] indets_times_subset)
  also have "... \<subseteq> keys t \<union> indets p" using indets_monomial_subset[of t c] by blast
  finally show ?thesis .
qed

lemma indets_monom_mult:
  assumes "c \<noteq> 0" and "p \<noteq> (0::('n \<Rightarrow>\<^sub>0 'a::{comm_powerprod,ninv_comm_monoid_add}) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
  shows "indets (monom_mult c t p) = keys t \<union> indets p"
proof (rule, fact indets_monom_mult_subset, rule)
  fix x
  assume "x \<in> keys t \<union> indets p"
  thus "x \<in> indets (monom_mult c t p)"
  proof
    assume "x \<in> keys t"
    from assms(2) have "keys p \<noteq> {}" by simp
    then obtain s where "s \<in> keys p" by blast
    hence "t + s \<in> (+) t ` keys p" by fastforce
    also from assms(1) have "... = keys (monom_mult c t p)" by (simp add: keys_monom_mult)
    finally have "t + s \<in> keys (monom_mult c t p)" .
    show ?thesis
    proof (rule in_indetsI)
      from \<open>x \<in> keys t\<close> show "x \<in> keys (t + s)" by (simp add: keys_plus_ninv_comm_monoid_add)
    qed fact
  next
    assume "x \<in> indets p"
    then obtain s where "s \<in> keys p" and "x \<in> keys s" by (rule in_indetsE)
    from this(1) have "t + s \<in> (+) t ` keys p" by fastforce
    also from assms(1) have "... = keys (monom_mult c t p)" by (simp add: keys_monom_mult)
    finally have "t + s \<in> keys (monom_mult c t p)" .
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

lemma indets_prod_subset: "indets (prod f A) \<subseteq> (\<Union>a\<in>A. indets (f a))"
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

lemma indets_power_subset: "indets (p ^ n) \<subseteq> indets (p::('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)"
proof -
  have "p ^ n = (\<Prod>i=0..<n. p)" by (simp add: prod_constant)
  also have "indets ... \<subseteq> (\<Union>i\<in>{0..<n}. indets p)" by (fact indets_prod_subset)
  also have "... \<subseteq> indets p" by simp
  finally show ?thesis .
qed

lemma indets_empty_iff_poly_deg_zero: "indets p = {} \<longleftrightarrow> poly_deg p = (0::'a::add_linorder_min)"
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

subsection \<open>Substitution Homomorphisms\<close>

text \<open>The substitution homomorphisms defined here are more general than @{const insertion} etc., since
  they replace indeterminates by @{emph \<open>polynomials\<close>} rather than coefficients, and therefore
  construct new polynomials.\<close>

definition subst_pp :: "('n \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a)) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
  where "subst_pp f t = (\<Prod>x\<in>keys t. (f x) ^ (lookup t x))"

definition poly_subst :: "('n \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a)) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
  where "poly_subst f p = (\<Sum>t\<in>keys p. monom_mult (lookup p t) 0 (subst_pp f t))"

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
  shows "subst_pp (\<lambda>_. 0) t = (0::(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1))"
  unfolding subst_pp_def using finite_keys
proof (rule prod_zero)
  from assms have "keys t \<noteq> {}" by simp
  then obtain x where "x \<in> keys t" by blast
  thus "\<exists>x\<in>keys t. 0 ^ lookup t x = (0::(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b))"
  proof
    from \<open>x \<in> keys t\<close> have "0 < lookup t x" by (simp add: in_keys_iff)
    thus "0 ^ lookup t x = (0::(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b))" by (rule Power.semiring_1_class.zero_power)
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
  also have "... = monomial 1 t" by (simp add: monomial_prod_sum[symmetric] poly_mapping_sum_monomials)
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
  shows "poly_deg (subst_pp f (t::'n \<Rightarrow>\<^sub>0 nat)) = 0"
proof -
  have "poly_deg (subst_pp f t) \<le> (\<Sum>x\<in>keys t. poly_deg ((f x) ^ (lookup t x)))"
    unfolding subst_pp_def by (fact poly_deg_prod_le)
  also have "... = 0"
  proof (rule sum.neutral, rule)
    fix x
    assume "x \<in> keys t"
    hence "poly_deg (f x) = 0" by (rule assms)
    have "f x ^ lookup t x = (\<Prod>i=0..<lookup t x. f x)" by (simp add: prod_constant)
    also have "poly_deg ... \<le> (\<Sum>i=0..<lookup t x. poly_deg (f x))" by (rule poly_deg_prod_le)
    also have "... = 0" by (simp add: \<open>poly_deg (f x) = 0\<close>)
    finally show "poly_deg (f x ^ lookup t x) = 0" by simp
  qed
  finally show ?thesis by simp
qed

lemma poly_deg_subst_pp_le:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> poly_deg (f x) \<le> 1"
  shows "poly_deg (subst_pp f (t::'n \<Rightarrow>\<^sub>0 nat)) \<le> deg_pm t"
proof -
  have "poly_deg (subst_pp f t) \<le> (\<Sum>x\<in>keys t. poly_deg ((f x) ^ (lookup t x)))"
    unfolding subst_pp_def by (fact poly_deg_prod_le)
  also have "... \<le> (\<Sum>x\<in>keys t. lookup t x)"
  proof (rule sum_mono)
    fix x
    assume "x \<in> keys t"
    hence "poly_deg (f x) \<le> 1" by (rule assms)
    have "f x ^ lookup t x = (\<Prod>i=0..<lookup t x. f x)" by (simp add: prod_constant)
    also have "poly_deg ... \<le> (\<Sum>i=0..<lookup t x. poly_deg (f x))" by (rule poly_deg_prod_le)
    also from \<open>poly_deg (f x) \<le> 1\<close> have "... \<le> (\<Sum>i=0..<lookup t x. 1)" by (rule sum_mono)
    finally show "poly_deg (f x ^ lookup t x) \<le> lookup t x" by simp
  qed
  also have "... = deg_pm t" by (rule deg_pm_superset[symmetric], fact subset_refl, fact finite_keys)
  finally show ?thesis by simp
qed

lemma poly_subst_alt: "poly_subst f p = (\<Sum>t. monom_mult (lookup p t) 0 (subst_pp f t))"
proof -
  from finite_keys have "poly_subst f p = (\<Sum>t. if t \<in> keys p then monom_mult (lookup p t) 0 (subst_pp f t) else 0)"
    unfolding poly_subst_def by (rule Sum_any.conditionalize)
  also have "... = (\<Sum>t. monom_mult (lookup p t) 0 (subst_pp f t))"
    by (rule Sum_any.cong, simp add: monom_mult_left0)
  finally show ?thesis .
qed

lemma poly_subst_trivial [simp]: "poly_subst (\<lambda>_. 0) p = monomial (lookup p 0) 0"
  apply (simp add: poly_subst_def subst_pp_trivial if_distrib)
  apply (simp add: monom_mult_right0 cong: if_cong)
  apply (metis mult.right_neutral times_monomial_left)
  done

lemma poly_subst_zero [simp]: "poly_subst f 0 = 0"
  by (simp add: poly_subst_def)

lemma monom_mult_lookup_not_zero_subset_keys: "{t. monom_mult (lookup p t) 0 (subst_pp f t) \<noteq> 0} \<subseteq> keys p"
proof (rule, simp)
  fix t
  assume "monom_mult (lookup p t) 0 (subst_pp f t) \<noteq> 0"
  thus "t \<in> keys p" unfolding in_keys_iff by (metis monom_mult_left0)
qed

corollary finite_monom_mult_lookup_not_zero: "finite {t. monom_mult (lookup p t) 0 (subst_pp f t) \<noteq> 0}"
  by (rule finite_subset, fact monom_mult_lookup_not_zero_subset_keys, fact finite_keys)

lemma poly_subst_plus: "poly_subst f (p + q) = poly_subst f p + poly_subst f q"
  by (simp add: poly_subst_alt lookup_add monom_mult_dist_left, rule Sum_any.distrib,
      (fact finite_monom_mult_lookup_not_zero)+)

lemma poly_subst_uminus: "poly_subst f (-p) = - poly_subst f (p::('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_ring_1)"
  by (simp add: poly_subst_def keys_uminus monom_mult_uminus_left sum_negf)

lemma poly_subst_minus: "poly_subst f (p - q) = poly_subst f p - poly_subst f (q::('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_ring_1)"
proof -
  have "poly_subst f (p + (-q)) = poly_subst f p + poly_subst f (-q)" by (fact poly_subst_plus)
  thus ?thesis by (simp add: poly_subst_uminus)
qed

lemma poly_subst_monomial: "poly_subst f (monomial c t) = monom_mult c 0 (subst_pp f t)"
  by (simp add: poly_subst_def lookup_single monom_mult_left0)

corollary poly_subst_one [simp]: "poly_subst f 1 = 1"
  by (simp add: single_one[symmetric] poly_subst_monomial monom_mult_monomial del: single_one)

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
  have "(\<Sum>t. monom_mult (lookup (p * q) t) 0 (subst_pp f t)) =
        (\<Sum>t. \<Sum>u. monom_mult (lookup p u * (\<Sum>v. lookup q v when t = u + v)) 0 (subst_pp f t))"
    by (simp add: times_poly_mapping.rep_eq prod_fun_def monom_mult_Sum_any_left[OF fin_1])
  also have "\<dots> = (\<Sum>t. \<Sum>u. \<Sum>v. (monom_mult (lookup p u * lookup q v) 0 (subst_pp f t)) when t = u + v)"
    by (simp add: Sum_any_right_distrib[OF fin_2] monom_mult_Sum_any_left[OF fin_3] mult_when when_monom_mult)
  also have "\<dots> = (\<Sum>t. (\<Sum>(u, v). (monom_mult (lookup p u * lookup q v) 0 (subst_pp f t)) when t = u + v))"
    apply (subst (2) Sum_any.cartesian_product [of "?P \<times> ?Q"])
    apply (auto simp add: in_keys_iff monom_mult_left0 simp del: lookup_not_eq_zero_eq_in_keys)
    done
  also have "\<dots> = (\<Sum>(t, u, v). monom_mult (lookup p u * lookup q v) 0 (subst_pp f t) when t = u + v)"
    apply (subst Sum_any.cartesian_product [of "?PQ \<times> (?P \<times> ?Q)"])
    apply (auto simp add: fin_PQ in_keys_iff monom_mult_left0 simp del: lookup_not_eq_zero_eq_in_keys)
    apply (metis monomial_0I mult_not_zero times_monomial_left)
    done
  also have "\<dots> = (\<Sum>(u, v, t). monom_mult (lookup p u * lookup q v) 0 (subst_pp f t) when t = u + v)"
    using bij by (rule Sum_any.reindex_cong [of "\<lambda>(u, v, t). (t, u, v)"]) (simp add: fun_eq_iff)
  also have "\<dots> = (\<Sum>(u, v). \<Sum>t. monom_mult (lookup p u * lookup q v) 0 (subst_pp f t) when t = u + v)"
    apply (subst Sum_any.cartesian_product2 [of "(?P \<times> ?Q) \<times> ?PQ"])
    apply (auto simp add: fin_PQ in_keys_iff monom_mult_left0 simp del: lookup_not_eq_zero_eq_in_keys)
    apply (metis monomial_0I mult_not_zero times_monomial_left)
    done
  also have "\<dots> = (\<Sum>(u, v). monom_mult (lookup p u * lookup q v) 0 (subst_pp f u * subst_pp f v))"
    by (simp add: subst_pp_plus)
  also have "\<dots> = (\<Sum>u. \<Sum>v. monom_mult (lookup p u * lookup q v) 0 (subst_pp f u * subst_pp f v))"
    apply (subst Sum_any.cartesian_product [of "?P \<times> ?Q"])
    apply (auto simp add: in_keys_iff monom_mult_left0 simp del: lookup_not_eq_zero_eq_in_keys)
    done
  also have "\<dots> = (\<Sum>u. \<Sum>v. (monom_mult (lookup p u) 0 (subst_pp f u)) * (monom_mult (lookup q v) 0 (subst_pp f v)))"
    by (simp add: times_monomial_left[symmetric] ac_simps mult_single)
  also have "\<dots> = (\<Sum>t. monom_mult (lookup p t) 0 (subst_pp f t)) *
                  (\<Sum>t. monom_mult (lookup q t) 0 (subst_pp f t))"
    by (rule Sum_any_product [symmetric], (fact finite_monom_mult_lookup_not_zero)+)
  finally show ?thesis by (simp add: poly_subst_alt)
qed

corollary poly_subst_monom_mult: "poly_subst f (monom_mult c t p) = monom_mult c 0 (subst_pp f t * poly_subst f p)"
  by (simp only: times_monomial_left[symmetric] poly_subst_times poly_subst_monomial mult.assoc)

corollary poly_subst_monom_mult': "poly_subst f (monom_mult c t p) = (monom_mult c 0 (subst_pp f t)) * poly_subst f p"
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
    show "monom_mult (lookup p t) 0 (subst_pp f t) = monomial (lookup p t) t"
      by (simp add: eq monom_mult_monomial)
  qed
  also have "... = p" by (simp only: poly_mapping_sum_monomials)
  finally show ?thesis .
qed

lemma in_indets_poly_substE:
  assumes "x \<in> indets (poly_subst f p)"
  obtains y where "y \<in> indets p" and "x \<in> indets (f y)"
proof -
  note assms
  also have "indets (poly_subst f p) \<subseteq> (\<Union>t\<in>keys p. indets (monom_mult (lookup p t) 0 (subst_pp f t)))"
    unfolding poly_subst_def by (rule indets_sum_subset)
  finally obtain t where "t \<in> keys p" and "x \<in> indets (monom_mult (lookup p t) 0 (subst_pp f t))" ..
  note this(2)
  also have "indets (monom_mult (lookup p t) 0 (subst_pp f t)) \<subseteq> keys (0::('a \<Rightarrow>\<^sub>0 nat)) \<union> indets (subst_pp f t)"
    by (rule indets_monom_mult_subset)
  also have "... = indets (subst_pp f t)" by simp
  finally obtain y where "y \<in> keys t" and "x \<in> indets (f y)" by (rule in_indets_subst_ppE)
  from this(1) \<open>t \<in> keys p\<close> have "y \<in> indets p" by (rule in_indetsI)
  from this \<open>x \<in> indets (f y)\<close> show ?thesis ..
qed

lemma poly_deg_poly_subst_eq_zeroI:
  assumes "\<And>x. x \<in> indets p \<Longrightarrow> poly_deg (f x) = 0"
  shows "poly_deg (poly_subst f (p::('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)) = 0"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  have "poly_deg (poly_subst f p) \<le> Max (poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
    unfolding poly_subst_def by (fact poly_deg_sum_le)
  also have "... \<le> 0"
  proof (rule Max.boundedI)
    show "finite (poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
      by (simp add: finite_image_iff)
  next
    from False show "poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p \<noteq> {}" by simp
  next
    fix d
    assume "d \<in> poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p"
    then obtain t where "t \<in> keys p" and d: "d = poly_deg (monom_mult (lookup p t) 0 (subst_pp f t))"
      by fastforce
    have "d \<le> deg_pm (0::'n \<Rightarrow>\<^sub>0 nat) + poly_deg (subst_pp f t)"
      unfolding d by (fact poly_deg_monom_mult_le)
    also have "... = poly_deg (subst_pp f t)" by simp
    also have "... = 0" by (rule poly_deg_subst_pp_eq_zeroI, rule assms, erule in_indetsI, fact)
    finally show "d \<le> 0" .
  qed
  finally show ?thesis by simp
qed

lemma poly_deg_poly_subst_le:
  assumes "\<And>x. x \<in> indets p \<Longrightarrow> poly_deg (f x) \<le> 1"
  shows "poly_deg (poly_subst f (p::('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_semiring_1)) \<le> poly_deg p"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  have "poly_deg (poly_subst f p) \<le> Max (poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
    unfolding poly_subst_def by (fact poly_deg_sum_le)
  also have "... \<le> poly_deg p"
  proof (rule Max.boundedI)
    show "finite (poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p)"
      by (simp add: finite_image_iff)
  next
    from False show "poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p \<noteq> {}" by simp
  next
    fix d
    assume "d \<in> poly_deg ` (\<lambda>t. monom_mult (lookup p t) 0 (subst_pp f t)) ` keys p"
    then obtain t where "t \<in> keys p" and d: "d = poly_deg (monom_mult (lookup p t) 0 (subst_pp f t))"
      by fastforce
    have "d \<le> deg_pm (0::'n \<Rightarrow>\<^sub>0 nat) + poly_deg (subst_pp f t)"
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
  for ord::"('n::countable \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

sublocale gd_powerprod ..

end

end (* theory *)
