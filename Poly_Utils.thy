(* Author: Alexander Maletzky *)

theory Poly_Utils
  imports Polynomials.MPoly_Type_Class_Ordered Groebner_Bases.More_MPoly_Type_Class General_Utils
begin

text \<open>Some further general properties of (ordered) multivariate polynomials. This theory is an
  extension of @{theory Polynomials.MPoly_Type_Class}.\<close>
  
section \<open>Further Properties of Multivariate Polynomials\<close>

lemma keys_sum_list_subset: "keys (sum_list ps) \<subseteq> Keys (set ps)"
proof (induct ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  have "keys (sum_list (p # ps)) = keys (p + sum_list ps)" by simp
  also have "\<dots> \<subseteq> keys p \<union> keys (sum_list ps)" by (fact keys_add_subset)
  also from Cons have "\<dots> \<subseteq> keys p \<union> Keys (set ps)" by blast
  also have "\<dots> = Keys (set (p # ps))" by (simp add: Keys_insert)
  finally show ?case .
qed

subsection \<open>Multiplication\<close>

lemma (in term_powerprod) lookup_mult_scalar_explicit:
  "lookup (p \<odot> q) u = (\<Sum>t\<in>keys p. lookup p t * (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v))"
proof -
  let ?f = "\<lambda>t s. lookup (proj_poly (component_of_term u) q) s when pp_of_term u = t + s"
  note lookup_mult_scalar
  also have "lookup (p * proj_poly (component_of_term u) q) (pp_of_term u) =
              (\<Sum>t. lookup p t * (Sum_any (?f t)))"
    by (fact lookup_mult)
  also from finite_keys have "\<dots> = (\<Sum>t\<in>keys p. lookup p t * (Sum_any (?f t)))"
    by (rule Sum_any.expand_superset) (auto dest: mult_not_zero)
  also from refl have "\<dots> = (\<Sum>t\<in>keys p. lookup p t * (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v))"
  proof (rule sum.cong)
    fix t
    assume "t \<in> keys p"
    from finite_keys have "Sum_any (?f t) = (\<Sum>s\<in>keys (proj_poly (component_of_term u) q). ?f t s)"
      by (rule Sum_any.expand_superset) auto
    also have "\<dots> = (\<Sum>v\<in>{x \<in> keys q. component_of_term x = component_of_term u}. ?f t (pp_of_term v))"
      unfolding keys_proj_poly
    proof (intro sum.reindex[simplified o_def] inj_onI)
      fix v1 v2
      assume "v1 \<in> {x \<in> keys q. component_of_term x = component_of_term u}"
        and "v2 \<in> {x \<in> keys q. component_of_term x = component_of_term u}"
      hence "component_of_term v1 = component_of_term v2" by simp
      moreover assume "pp_of_term v1 = pp_of_term v2"
      ultimately show "v1 = v2" by (metis term_of_pair_pair)
    qed
    also from finite_keys have "\<dots> = (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v)"
    proof (intro sum.mono_neutral_cong_left ballI)
      fix v
      assume "v \<in> keys q - {x \<in> keys q. component_of_term x = component_of_term u}"
      hence "u \<noteq> t \<oplus> v" by (auto simp: component_of_term_splus)
      thus "(lookup q v when u = t \<oplus> v) = 0" by simp
    next
      fix v
      assume "v \<in> {x \<in> keys q. component_of_term x = component_of_term u}"
      hence eq[symmetric]: "component_of_term v = component_of_term u" by simp
      have "u = t \<oplus> v \<longleftrightarrow> pp_of_term u = t + pp_of_term v"
      proof
        assume "pp_of_term u = t + pp_of_term v"
        hence "pp_of_term u = pp_of_term (t \<oplus> v)" by (simp only: pp_of_term_splus)
        moreover have "component_of_term u = component_of_term (t \<oplus> v)"
          by (simp only: eq component_of_term_splus)
        ultimately show "u = t \<oplus> v" by (metis term_of_pair_pair)
      qed (simp add: pp_of_term_splus)
      thus "?f t (pp_of_term v) = (lookup q v when u = t \<oplus> v)"
        by (simp add: lookup_proj_poly eq term_of_pair_pair)
    qed auto
    finally show "lookup p t * (Sum_any (?f t)) = lookup p t * (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v)"
      by (simp only:)
  qed
  finally show ?thesis .
qed

lemmas lookup_times = punit.lookup_mult_scalar_explicit[simplified]

subsection \<open>Sub-Polynomials\<close>

definition subpoly :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  where "subpoly p q \<longleftrightarrow> (\<forall>v\<in>(keys p). lookup p v = lookup q v)"

lemma subpolyI: "(\<And>v. v \<in> keys p \<Longrightarrow> lookup p v = lookup q v) \<Longrightarrow> p \<sqsubseteq> q"
  by (simp add: subpoly_def)

lemma subpolyE:
  assumes "p \<sqsubseteq> q" and "v \<in> keys p"
  shows "lookup p v = lookup q v"
  using assms by (auto simp: subpoly_def)

lemma subpoly_keys:
  assumes "p \<sqsubseteq> q"
  shows "keys p \<subseteq> keys q"
proof
  fix v
  assume "v \<in> keys p"
  hence "lookup p v \<noteq> 0" unfolding in_keys_iff .
  from assms \<open>v \<in> keys p\<close> have "lookup p v = lookup q v" by (rule subpolyE)
  with \<open>lookup p v \<noteq> 0\<close> show "v \<in> keys q" unfolding in_keys_iff by simp
qed

lemma subpoly_diff_keys_disjoint:
  assumes "p \<sqsubseteq> q"
  shows "keys p \<inter> keys (q - p) = {}"
  unfolding disjoint_iff_not_equal
proof (intro ballI)
  fix s t
  assume "s \<in> keys p" and "t \<in> keys (q - p)"
  show "s \<noteq> t"
  proof
    assume "s = t"
    from assms \<open>s \<in> keys p\<close> have "lookup p t = lookup q t" unfolding \<open>s = t\<close> by (rule subpolyE)
    from \<open>t \<in> keys (q - p)\<close> have "lookup (q - p) t \<noteq> 0" unfolding in_keys_iff .
    moreover have "lookup (q - p) t = 0" unfolding lookup_minus \<open>lookup p t = lookup q t\<close> by simp
    ultimately show False by simp
  qed
qed

lemma zero_subpoly: "0 \<sqsubseteq> q"
  by (rule subpolyI, simp)

lemma monomial_subpoly: "(monomial (lookup p t) t) \<sqsubseteq> p" (is "?q \<sqsubseteq> _")
proof (rule subpolyI)
  fix s
  assume "s \<in> keys ?q"
  have "lookup p t \<noteq> 0"
  proof
    assume "lookup p t = 0"
    hence "?q = 0" by (rule monomial_0I)
    hence "keys ?q = {}" by simp
    with \<open>s \<in> keys ?q\<close> show False by simp
  qed
  from keys_single \<open>s \<in> keys ?q\<close> have "s = t" using \<open>lookup p t \<noteq> 0\<close> by auto
  show "lookup ?q s = lookup p s" by (simp add: \<open>s = t\<close> lookup_single)
qed

lemma subpoly_refl: "p \<sqsubseteq> p"
  by (rule subpolyI, rule)

lemma subpoly_antisym:
  assumes "p \<sqsubseteq> q" and "q \<sqsubseteq> p"
  shows "p = q"
proof (rule poly_mapping_keys_eqI, rule, rule subpoly_keys, fact, rule subpoly_keys, fact)
  fix t
  assume "t \<in> keys p"
  with \<open>p \<sqsubseteq> q\<close> show "lookup p t = lookup q t" by (rule subpolyE)
qed

lemma subpoly_trans:
  assumes "p \<sqsubseteq> q" and "q \<sqsubseteq> r"
  shows "p \<sqsubseteq> r"
proof (rule subpolyI)
  fix t
  assume "t \<in> keys p"
  have "t \<in> keys q" by (rule, rule subpoly_keys, fact+)
  from \<open>p \<sqsubseteq> q\<close> \<open>t \<in> keys p\<close> have "lookup p t = lookup q t" by (rule subpolyE)
  also from \<open>q \<sqsubseteq> r\<close> \<open>t \<in> keys q\<close> have "... = lookup r t" by (rule subpolyE)
  finally show "lookup p t = lookup r t" .
qed

lemma plus_subpolyI:
  assumes "p \<sqsubseteq> r" and "q \<sqsubseteq> r" and "keys p \<inter> keys q = {}"
  shows "p + q \<sqsubseteq> r"
proof (rule subpolyI)
  fix t
  assume "t \<in> keys (p + q)"
  also from assms(3) have "\<dots> = keys p \<union> keys q" by (rule keys_plus_eqI)
  finally show "lookup (p + q) t = lookup r t"
  proof
    assume "t \<in> keys p"
    with assms(1) have eq1: "lookup p t = lookup r t" by (rule subpolyE)
    from \<open>t \<in> keys p\<close> assms(3) have "t \<notin> keys q" by auto
    hence "lookup q t = 0" unfolding in_keys_iff by simp
    thus ?thesis by (simp add: lookup_add eq1)
  next
    assume "t \<in> keys q"
    with assms(2) have eq1: "lookup q t = lookup r t" by (rule subpolyE)
    from \<open>t \<in> keys q\<close> assms(3) have "t \<notin> keys p" by auto
    hence "lookup p t = 0" unfolding in_keys_iff by simp
    thus ?thesis by (simp add: lookup_add eq1)
  qed
qed

lemma except_subpoly: "except p S \<sqsubseteq> p"
proof (rule subpolyI)
  fix s
  assume "s \<in> keys (except p S)"
  hence "s \<notin> S" unfolding keys_except ..
  thus "lookup (except p S) s = lookup p s" by (rule lookup_except_eq_idI)
qed

subsection \<open>Bounded Support\<close>
  
definition has_bounded_keys :: "nat \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool" where
  "has_bounded_keys n p \<longleftrightarrow> card (keys p) \<le> n"

definition has_bounded_keys_set :: "nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool" where
  "has_bounded_keys_set n A \<longleftrightarrow> (\<forall>a\<in>A. has_bounded_keys n a)"

lemma not_has_bounded_keys: "\<not> has_bounded_keys n p \<longleftrightarrow> n < card (keys p)"
  by (auto simp add: has_bounded_keys_def)
  
lemma has_bounded_keys_set_union:
  shows "has_bounded_keys_set n (A \<union> B) \<longleftrightarrow> (has_bounded_keys_set n A \<and> has_bounded_keys_set n B)"
  unfolding has_bounded_keys_set_def by auto

lemma has_bounded_keys_set_singleton:
  shows "has_bounded_keys_set n {p} \<longleftrightarrow> has_bounded_keys n p"
  unfolding has_bounded_keys_set_def by simp
    
lemma has_bounded_keys_set_subset:
  assumes "has_bounded_keys_set n A" and "B \<subseteq> A"
  shows "has_bounded_keys_set n B"
  using assms unfolding has_bounded_keys_set_def by auto

lemma has_bounded_keys_setI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> has_bounded_keys n a"
  shows "has_bounded_keys_set n A"
  unfolding has_bounded_keys_set_def using assms by simp

lemma has_bounded_keys_setD:
  assumes "has_bounded_keys_set n A" and "a \<in> A"
  shows "has_bounded_keys n a"
  using assms unfolding has_bounded_keys_set_def by simp
    
subsection \<open>Binomials\<close>
  
definition is_binomial :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "is_binomial p \<longleftrightarrow> (card (keys p) = 1 \<or> card (keys p) = 2)"

definition is_proper_binomial :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "is_proper_binomial p \<longleftrightarrow> card (keys p) = 2"
    
definition binomial :: "'b::comm_monoid_add \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "binomial c s d t = monomial c s + monomial d t"
    
definition is_monomial_set :: "('a \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool"
  where "is_monomial_set A \<longleftrightarrow> (\<forall>p\<in>A. is_monomial p)"

definition is_binomial_set :: "('a \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool"
  where "is_binomial_set A \<longleftrightarrow> (\<forall>p\<in>A. is_binomial p)"

definition is_pbd :: "'b::zero \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_pbd c s d t \<longleftrightarrow> (c \<noteq> 0 \<and> d \<noteq> 0 \<and> s \<noteq> t)"

text \<open>@{const is_pbd} stands for "is proper binomial data".\<close>

lemma is_monomial_setI:
  assumes "\<And>p. p \<in> A \<Longrightarrow> is_monomial p"
  shows "is_monomial_set A"
  using assms unfolding is_monomial_set_def by simp

lemma is_monomial_setD:
  assumes "is_monomial_set A" and "p \<in> A"
  shows "is_monomial p"
  using assms unfolding is_monomial_set_def by simp
    
lemma is_binomial_setI:
  assumes "\<And>p. p \<in> A \<Longrightarrow> is_binomial p"
  shows "is_binomial_set A"
  using assms unfolding is_binomial_set_def by simp

lemma is_binomial_setD:
  assumes "is_binomial_set A" and "p \<in> A"
  shows "is_binomial p"
  using assms unfolding is_binomial_set_def by simp

lemma has_bounded_keys_1_I1:
  assumes "is_monomial p"
  shows "has_bounded_keys 1 p"
  using assms unfolding is_monomial_def has_bounded_keys_def by simp

lemma has_bounded_keys_1_I2:
  shows "has_bounded_keys 1 0"
  unfolding has_bounded_keys_def by simp
    
lemma has_bounded_keys_1_D:
  assumes "has_bounded_keys 1 p"
  shows "p = 0 \<or> is_monomial p"
  using assms unfolding is_monomial_def has_bounded_keys_def
proof -
  assume "card (keys p) \<le> 1"
  hence "card (keys p) = 0 \<or> card (keys p) = 1" by linarith
  thus "p = 0 \<or> card (keys p) = 1"
  proof
    assume "card (keys p) = 0"
    hence "keys p = {}" using finite_keys[of p] by simp
    thus ?thesis unfolding keys_eq_empty_iff ..
  next
    assume "card (keys p) = 1"
    thus ?thesis ..
  qed
qed
  
lemma has_bounded_keys_2_I1:
  assumes "is_binomial p"
  shows "has_bounded_keys 2 p"
  using assms unfolding is_binomial_def has_bounded_keys_def by auto

lemma has_bounded_keys_2_I2:
  shows "has_bounded_keys 2 0"
  unfolding has_bounded_keys_def keys_zero by simp
    
lemma has_bounded_keys_2_D:
  assumes "has_bounded_keys 2 p"
  shows "p = 0 \<or> is_binomial p"
  using assms unfolding is_binomial_def has_bounded_keys_def
proof -
  assume "card (keys p) \<le> 2"
  hence "card (keys p) = 0 \<or> card (keys p) = 1 \<or> card (keys p) = 2" by linarith
  thus "p = 0 \<or> card (keys p) = 1 \<or> card (keys p) = 2"
  proof
    assume "card (keys p) = 0"
    hence "keys p = {}" using finite_keys[of p] by simp
    thus ?thesis by simp
  next
    assume "card (keys p) = 1 \<or> card (keys p) = 2"
    thus ?thesis ..
  qed
qed
    
lemma has_bounded_keys_set_1_I1:
  assumes "is_monomial_set A"
  shows "has_bounded_keys_set 1 A"
  unfolding has_bounded_keys_set_def
proof (intro ballI has_bounded_keys_1_I1)
  fix p
  assume "p \<in> A"
  from assms have "\<forall>p\<in>A. is_monomial p" unfolding is_monomial_set_def .
  from this[rule_format, OF \<open>p \<in> A\<close>] show "is_monomial p" .
qed
    
lemma has_bounded_keys_set_1_D:
  assumes "has_bounded_keys_set 1 A" and "0 \<notin> A"
  shows "is_monomial_set A"
  unfolding is_monomial_set_def
proof
  fix p
  assume "p \<in> A"
  from assms(1) have "\<forall>p\<in>A. has_bounded_keys 1 p" unfolding has_bounded_keys_set_def .
  from this[rule_format, OF \<open>p \<in> A\<close>] have "has_bounded_keys 1 p" .
  hence "p = 0 \<or> is_monomial p" by (rule has_bounded_keys_1_D)
  thus "is_monomial p"
  proof
    assume "p = 0"
    with \<open>p \<in> A\<close> have "0 \<in> A" by simp
    with assms(2) show ?thesis ..
  qed
qed
  
lemma has_bounded_keys_set_2_I1:
  assumes "is_binomial_set A"
  shows "has_bounded_keys_set 2 A"
  unfolding has_bounded_keys_set_def
proof (intro ballI has_bounded_keys_2_I1)
  fix p
  assume "p \<in> A"
  from assms have "\<forall>p\<in>A. is_binomial p" unfolding is_binomial_set_def .
  from this[rule_format, OF \<open>p \<in> A\<close>] show "is_binomial p" .
qed
    
lemma has_bounded_keys_set_2_D:
  assumes "has_bounded_keys_set 2 A" and "0 \<notin> A"
  shows "is_binomial_set A"
  unfolding is_binomial_set_def
proof
  fix p
  assume "p \<in> A"
  from assms(1) have "\<forall>p\<in>A. has_bounded_keys 2 p" unfolding has_bounded_keys_set_def .
  from this[rule_format, OF \<open>p \<in> A\<close>] have "has_bounded_keys 2 p" .
  hence "p = 0 \<or> is_binomial p" by (rule has_bounded_keys_2_D)
  thus "is_binomial p"
  proof
    assume "p = 0"
    with \<open>p \<in> A\<close> have "0 \<in> A" by simp
    with assms(2) show ?thesis ..
  qed
qed
    
lemma is_proper_binomial_uminus: "is_proper_binomial (- p) \<longleftrightarrow> is_proper_binomial p"
  unfolding is_proper_binomial_def keys_uminus ..
    
lemma is_binomial_uminus: "is_binomial (- p) \<longleftrightarrow> is_binomial p"
  unfolding is_binomial_def keys_uminus ..

lemma monomial_imp_binomial: "is_monomial p \<Longrightarrow> is_binomial p"
  by (simp add: is_monomial_def is_binomial_def)

lemma proper_binomial_imp_binomial: "is_proper_binomial p \<Longrightarrow> is_binomial p"
  by (simp add: is_proper_binomial_def is_binomial_def)

lemma proper_binomial_no_monomial: "is_proper_binomial p \<Longrightarrow> \<not> is_monomial p"
  by (simp add: is_proper_binomial_def is_monomial_def)
  
lemma is_binomial_alt: "is_binomial p \<longleftrightarrow> (is_monomial p \<or> is_proper_binomial p)"
  unfolding is_monomial_def is_binomial_def is_proper_binomial_def ..

lemma proper_binomial_not_0: "is_proper_binomial p \<Longrightarrow> p \<noteq> 0"
  by (auto simp: is_proper_binomial_def)

corollary binomial_not_0: "is_binomial p \<Longrightarrow> p \<noteq> 0"
  unfolding is_binomial_alt using monomial_not_0 proper_binomial_not_0 by auto
    
lemma is_pbdD:
  assumes "is_pbd c s d t"
  shows "c \<noteq> 0" and "d \<noteq> 0" and "s \<noteq> t"
  using assms by (simp_all add: is_pbd_def)
    
lemma is_pbdI: "c \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> s \<noteq> t \<Longrightarrow> is_pbd c s d t"
  by (simp add: is_pbd_def)

lemma binomial_comm: "binomial c s d t = binomial d t c s"
  unfolding binomial_def by (simp add: ac_simps)

lemma keys_binomial_subset: "keys (binomial c s d t) \<subseteq> {s, t}"
proof
  fix u
  assume "u \<in> keys (binomial c s d t)"
  hence "lookup (binomial c s d t) u \<noteq> 0" by simp
  hence "u = s \<or> u = t" unfolding binomial_def lookup_add lookup_single Poly_Mapping.when_def
    by (metis (full_types) add.comm_neutral)
  thus "u \<in> {s, t}" by simp
qed
    
lemma card_keys_binomial: "card (keys (binomial c s d t)) \<le> 2"
proof -
  have "finite {s, t}" by simp
  from this keys_binomial_subset have "card (keys (binomial c s d t)) \<le> card {s, t}" by (rule card_mono)
  also have "... \<le> 2" by (simp add: card_insert_le_m1)
  finally show ?thesis .
qed

lemma keys_binomial_pbd:
  assumes "is_pbd c s d t"
  shows "keys (binomial c s d t) = {s, t}"
proof -
  from assms have "c \<noteq> 0" and "d \<noteq> 0" and "s \<noteq> t" by (rule is_pbdD)+
  have "keys (monomial c s + monomial d t) = (keys (monomial c s)) \<union> (keys (monomial d t))"
  proof (rule, rule keys_add_subset, rule)
    fix x
    assume "x \<in> keys (monomial c s) \<union> keys (monomial d t)"
    hence "x \<in> {s} \<union> {t}" unfolding keys_of_monomial[OF \<open>c \<noteq> 0\<close>] keys_of_monomial[OF \<open>d \<noteq> 0\<close>] .
    hence c: "x = s \<or> x = t" by auto
    from \<open>s \<noteq> t\<close> \<open>c \<noteq> 0\<close> have "lookup (monomial c s + monomial d t) s \<noteq> 0"
      unfolding lookup_add lookup_single by simp
    hence s: "s \<in> keys (monomial c s + monomial d t)" by simp
    from \<open>s \<noteq> t\<close> \<open>d \<noteq> 0\<close> have "lookup (monomial c s + monomial d t) t \<noteq> 0"
      unfolding lookup_add lookup_single by simp
    hence t: "t \<in> keys (monomial c s + monomial d t)" by simp
    from c show "x \<in> keys (monomial c s + monomial d t)" using s t by auto
  qed
  thus ?thesis unfolding binomial_def keys_of_monomial[OF \<open>c \<noteq> 0\<close>] keys_of_monomial[OF \<open>d \<noteq> 0\<close>] by auto
qed

lemma lookup_binomial':
  "s \<noteq> t \<Longrightarrow> lookup (binomial c s d t) u = (if u = s then c else if u = t then d else 0)"
  by (simp add: binomial_def lookup_add lookup_single)

lemma lookup_binomial:
  assumes "is_pbd c s d t"
  shows "lookup (binomial c s d t) u = (if u = s then c else (if u = t then d else 0))"
  using is_pbdD(3)[OF assms] by (simp add: lookup_binomial')
    
lemma binomial_uminus: "- binomial c s d t = binomial (-c) s (-d) t"
  by (simp add: binomial_def monomial_uminus)

lemma binomial_is_proper_binomial:
  assumes "is_pbd c s d t"
  shows "is_proper_binomial (binomial c s d t)"
  unfolding is_proper_binomial_def keys_binomial_pbd[OF assms] using is_pbdD(3)[OF assms] by simp

lemma is_proper_binomial_binomial:
  assumes "is_proper_binomial p"
  obtains c d s t where "is_pbd c s d t" and "p = binomial c s d t"
proof -
  from assms have "card (keys p) = 2" unfolding is_proper_binomial_def .
  then obtain s t where "s \<noteq> t" and sp: "keys p = {s, t}" by (rule card_2_E)
  let ?c = "lookup p s"
  let ?d = "lookup p t"
  from sp have "?c \<noteq> 0" by fastforce
  from sp have "?d \<noteq> 0" by fastforce
  have "is_pbd ?c s ?d t" by (rule is_pbdI, fact+)
  show ?thesis
  proof
    show "p = binomial ?c s ?d t"
    proof (intro poly_mapping_keys_eqI)
      have a: "keys (binomial ?c s ?d t) = {s, t}" by (rule keys_binomial_pbd, fact)
      show "keys p = keys (binomial ?c s ?d t)" unfolding a sp by auto
    next
      fix u
      assume "u \<in> keys p"
      hence "u \<in> {s, t}" unfolding sp .
      hence "u = s \<or> u = t" by simp
      hence "(u = s \<and> u \<noteq> t) \<or> (u = t \<and> u \<noteq> s)" using \<open>s \<noteq> t\<close> by auto
      thus "lookup p u = lookup (binomial ?c s ?d t) u" unfolding lookup_binomial[OF \<open>is_pbd ?c s ?d t\<close>] by auto
    qed
  qed fact+
qed

lemma is_binomial_eq_binomial:
  assumes "is_binomial p" and "s \<in> keys p" and "t \<in> keys p" and "s \<noteq> t"
  shows "p = binomial (lookup p s) s (lookup p t) t" (is "_ = ?r")
proof (rule poly_mapping_eqI)
  fix u
  show "lookup p u = lookup ?r u"
  proof (simp add: lookup_binomial'[OF assms(4)], intro impI)
    assume "u \<noteq> t" and "u \<noteq> s"
    with assms(4) have eq: "card {s, t, u} = 3" by auto
    with assms(1) have "\<not> card {s, t, u} \<le> card (keys p)" by (auto simp: is_binomial_def)
    with finite_keys card_mono have "\<not> {s, t, u} \<subseteq> keys p" by blast
    with assms(2, 3) show "lookup p u = 0" by simp
  qed
qed

corollary is_proper_binomial_eq_binomial:
  assumes "is_proper_binomial p" and "s \<in> keys p" and "t \<in> keys p" and "s \<noteq> t"
  shows "p = binomial (lookup p s) s (lookup p t) t"
proof -
  from assms(1) have "is_binomial p" by (rule proper_binomial_imp_binomial)
  thus ?thesis using assms(2-4) by (rule is_binomial_eq_binomial)
qed

lemma is_proper_binomial_keysE_1:
  assumes "is_proper_binomial p" and "s \<in> keys p"
  obtains t where "s \<noteq> t" and "keys p = {s, t}"
proof -
  from assms(1) have "card (keys p) = 2" by (simp only: is_proper_binomial_def)
  then obtain t where "s \<noteq> t" and "keys p = {s, t}" using assms(2) by (rule card_2_E_1)
  thus ?thesis ..
qed

lemma is_proper_binomial_keysE:
  assumes "is_proper_binomial p"
  obtains s t where "s \<noteq> t" and "keys p = {s, t}"
proof -
  from assms(1) have "card (keys p) = 2" by (simp only: is_proper_binomial_def)
  then obtain s t where "s \<noteq> t" and "keys p = {s, t}" by (rule card_2_E)
  thus ?thesis ..
qed

context term_powerprod
begin

lemma is_pbd_mult:
  assumes "is_pbd (c::'b::semiring_no_zero_divisors) u d v" and "a \<noteq> 0"
  shows "is_pbd (a * c) (t \<oplus> u) (a * d) (t \<oplus> v)"
  using assms unfolding is_pbd_def by (auto simp add: term_simps)
    
lemma monom_mult_binomial:
  "monom_mult a t (binomial c u d v) = binomial (a * c) (t \<oplus> u) (a * d) (t \<oplus> v)"
  unfolding binomial_def monom_mult_dist_right monom_mult_monomial ..

lemma is_proper_binomial_monom_mult:
  assumes "is_proper_binomial p" and "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "is_proper_binomial (monom_mult c u p)"
proof -
  from assms(2) have "card (keys (monom_mult c u p)) = card ((\<oplus>) u ` keys p)"
    by (simp add: keys_monom_mult)
  also have "\<dots> = card (keys p)" by (rule card_image) (meson inj_onI splus_left_canc)
  also from assms(1) have "\<dots> = 2" by (simp only: is_proper_binomial_def)
  finally show ?thesis by (simp only: is_proper_binomial_def)
qed

subsection \<open>Submodules\<close>

lemma pmdl_closed_sum_list: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> pmdl B) \<Longrightarrow> sum_list xs \<in> pmdl B"
  by (induct xs) (auto intro: pmdl.span_zero pmdl.span_add)

end (* term_powerprod *)
  
section \<open>Further Properties of Ordered Polynomials\<close>
  
context ordered_term
begin

subsection \<open>Modules and Linear Hulls\<close>

text \<open>The following lemma also holds in context @{locale term_powerprod}, but then one needs the
  additional assumption that function @{const monom_mult} is injective in its second argument (the
  power-product), provided the other two arguments (coefficient, polynomial) are non-zero.\<close>

lemma in_pmdl_in_phull:
  fixes B::"('t \<Rightarrow>\<^sub>0 'b::{comm_ring_1,ring_1_no_zero_divisors}) set"
    and A::"('t \<Rightarrow>\<^sub>0 'b) set"
    and q::"('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  assumes "\<And>b t. b \<in> B \<Longrightarrow> t \<in> keys (q b) \<Longrightarrow> monom_mult 1 t b \<in> A"
  shows "(\<Sum>b\<in>B. q b \<odot> b) \<in> phull A" (is "?p \<in> _")
proof (cases "finite B")
  case True
  define f where "f = (\<lambda>a. \<lambda>b. lookup (q b) (THE t. a = monom_mult 1 t b) when (\<exists>t. a = monom_mult 1 t b))"
  let ?B = "B - {0}"
  let ?c = "\<lambda>a. (\<Sum>b\<in>?B. f a b)"
  let ?A = "{a \<in> A. \<exists>b\<in>?B. f a b \<noteq> 0}"
  let ?A' = "\<Union>b\<in>?B. {monom_mult 1 t b | t. t \<in> keys (q b)}"

  have "finite ?A"
  proof (rule finite_subset)
    show "?A \<subseteq> ?A'"
    proof (rule, simp, elim conjE bexE)
      fix a b
      assume "a \<in> A" and "b \<in> ?B"
      assume "f a b \<noteq> 0"
      then obtain t where a: "a = monom_mult 1 t b" and *: "lookup (q b) (THE t. a = monom_mult 1 t b) \<noteq> 0"
        unfolding f_def by auto
      have "(THE t. a = monom_mult 1 t b) = t" unfolding a
      proof (rule, rule)
        fix t'
        assume "monom_mult 1 t b = monom_mult 1 t' b"
        hence "t = t'"
        proof (rule monom_mult_inj_2, simp)
          from \<open>b \<in> ?B\<close> show "b \<noteq> 0" by simp
        qed
        thus "t' = t" by simp
      qed
      with * have "lookup (q b) t \<noteq> 0" by simp
      hence "t \<in> keys (q b)" by simp
      show "\<exists>b2\<in>B - {0}. \<exists>t. a = monom_mult 1 t b2 \<and> t \<in> keys (q b2)" by (rule, rule, rule, fact+)
    qed
  next
    show "finite ?A'" by (rule, simp add: True, simp)
  qed

  have "?p = (\<Sum>b\<in>?B. q b \<odot> b)"
  proof (cases "0 \<in> B")
    case True
    show ?thesis by (simp add: sum.remove[OF \<open>finite B\<close> True])
  next
    case False
    hence "?B = B" by simp
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>a\<in>?A. monom_mult (?c a) 0 a)"
  proof (simp only: monom_mult_sum_left sum.swap[of _ _ ?A], rule sum.cong, rule)
    fix b
    assume "b \<in> ?B"
    hence "b \<in> B" and "b \<noteq> 0" by auto
    have "q b \<odot> b = (\<Sum>t\<in>keys (q b). monom_mult (lookup (q b) t) t b)"
      by (fact mult_scalar_sum_monomials)
    also have "... = sum ((\<lambda>a. monom_mult (f a b) 0 a) \<circ> (\<lambda>t. monom_mult 1 t b)) (keys (q b))"
    proof (rule sum.cong, rule, simp add: monom_mult_assoc)
      fix t
      assume "t \<in> keys (q b)"
      have "\<exists>ta. monom_mult 1 t b = monom_mult 1 ta b" by auto
      moreover have "(THE ta. monom_mult 1 t b = monom_mult 1 ta b) = t"
        by (rule, rule, elim monom_mult_inj_2[symmetric], simp, fact \<open>b \<noteq> 0\<close>)
      ultimately show "monom_mult (lookup (q b) t) t b = monom_mult (f (monom_mult 1 t b) b) t b"
        by (simp add: f_def)
    qed
    also have "... = (\<Sum>a\<in>((\<lambda>t. monom_mult 1 t b) ` keys (q b)). monom_mult (f a b) 0 a)"
    proof (rule sum.reindex[symmetric], rule)
      fix s t
      assume "monom_mult 1 s b = monom_mult 1 t b"
      thus "s = t" by (rule monom_mult_inj_2, simp, intro \<open>b \<noteq> 0\<close>)
    qed
    also have "... = (\<Sum>a\<in>?A. monom_mult (f a b) 0 a)"
    proof (rule sum.mono_neutral_cong, fact, rule, fact finite_keys)
      fix a
      assume "a \<in> ?A - (\<lambda>t. monom_mult 1 t b) ` keys (q b)"
      hence "a \<notin> (\<lambda>t. monom_mult 1 t b) ` keys (q b)" ..
      hence 1: "\<And>t. t \<in> keys (q b) \<Longrightarrow> a \<noteq> monom_mult 1 t b" by auto
      show "monom_mult (f a b) 0 a = 0" unfolding f_def when_def
      proof (split if_split, intro conjI impI, elim exE)
        fix t
        assume a: "a = monom_mult 1 t b"
        with 1 have "t \<notin> keys (q b)" by blast
        have "(THE t. a = monom_mult 1 t b) = t" unfolding a
          by (rule, rule, elim monom_mult_inj_2[symmetric], simp, rule \<open>b \<noteq> 0\<close>)
        with \<open>t \<notin> keys (q b)\<close> show "monom_mult (lookup (q b) (THE t. a = monom_mult 1 t b)) 0 a = 0"
          by simp
      qed (simp only: monom_mult_zero_left)
    next
      fix a
      assume "a \<in> (\<lambda>t. monom_mult 1 t b) ` keys (q b) - ?A"
      hence "a \<notin> ?A" ..
      hence "a \<notin> A \<or> (\<forall>b\<in>?B. f a b = 0)" by simp
      hence "f a b = 0"
      proof
        assume "a \<notin> A"
        show ?thesis unfolding f_def when_def
        proof (split if_split, intro conjI impI, elim exE)
          fix t
          assume a: "a = monom_mult 1 t b"
          have eq: "(THE t. a = monom_mult 1 t b) = t" unfolding a
            by (rule, rule, elim monom_mult_inj_2[symmetric], simp, rule \<open>b \<noteq> 0\<close>)
          show "(lookup (q b) (THE t. a = monom_mult 1 t b)) = 0" unfolding eq
          proof (cases "t \<in> keys (q b)")
            case True
            with \<open>b \<in> B\<close> have "monom_mult 1 t b \<in> A" by (rule assms)
            hence "a \<in> A" by (simp only: a)
            with \<open>a \<notin> A\<close> show "lookup (q b) t = 0" ..
          next
            case False
            thus "lookup (q b) t = 0" by simp
          qed
        qed rule
      next
        assume "\<forall>b\<in>?B. f a b = 0"
        from this \<open>b \<in> ?B\<close> show ?thesis ..
      qed
      thus "monom_mult (f a b) 0 a = 0" by simp
    qed (rule)
    finally show "q b \<odot> b = (\<Sum>a\<in>?A. monom_mult (f a b) 0 a)" .
  qed
  finally have *: "?p = (\<Sum>a\<in>?A. monom_mult (?c a) 0 a)" .

  have "?p \<in> phull ?A" unfolding * by (rule phull.sum_in_spanI)
  also have "... \<subseteq> phull A" by (rule phull.span_mono, auto)
  finally show ?thesis .
next                             
  case False
  thus ?thesis by (simp add: phull.span_zero)
qed
  
subsection \<open>Trailing Terms and -Coefficients\<close>

lemma lt_gr_tt_iff: "(tt p \<prec>\<^sub>t lt p) \<longleftrightarrow> (\<not> has_bounded_keys 1 p)"
  unfolding not_has_bounded_keys
proof
  assume "tt p \<prec>\<^sub>t lt p"
  hence "tt p \<noteq> lt p" by simp
  show "1 < card (keys p)"
  proof (rule ccontr)
    assume "\<not> 1 < card (keys p)"
    hence "card (keys p) = 0 \<or> card (keys p) = 1" by linarith
    hence "lt p = tt p"
    proof
      assume "card (keys p) = 0"
      hence "keys p = {}" using finite_keys[of p] by simp
      hence "p = 0" using keys_eq_empty_iff[of p] by simp
      show ?thesis unfolding \<open>p = 0\<close> lt_def tt_def by simp
    next
      assume "card (keys p) = 1"
      hence "is_monomial p" unfolding is_monomial_def .
      thus "lt p = tt p" by (rule lt_eq_tt_monomial)
    qed
    with \<open>tt p \<noteq> lt p\<close> show False by simp
  qed
next
  assume "1 < card (keys p)"
  hence "2 \<le> card (keys p)" by simp
  then obtain A where "card A = 2" and sp: "A \<subseteq> keys p" by (rule card_geq_ex_subset)
  from \<open>card A = 2\<close> obtain s t where "s \<noteq> t" and A: "A = {s, t}" by (rule card_2_E)
  from sp have "s \<in> keys p" and "t \<in> keys p" unfolding A by simp_all
  from \<open>s \<noteq> t\<close> have "s \<prec>\<^sub>t t \<or> t \<prec>\<^sub>t s" by auto
  thus "tt p \<prec>\<^sub>t lt p"
  proof
    assume "s \<prec>\<^sub>t t"
    also from \<open>t \<in> keys p\<close> have "... \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
    finally have "s \<prec>\<^sub>t lt p" .
    with \<open>s \<in> keys p\<close> show ?thesis by (rule tt_less)
  next
    assume "t \<prec>\<^sub>t s"
    also from \<open>s \<in> keys p\<close> have "... \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
    finally have "t \<prec>\<^sub>t lt p" .
    with \<open>t \<in> keys p\<close> show ?thesis by (rule tt_less)
  qed
qed

lemma lt_eq_tt_iff: "lt p = tt p \<longleftrightarrow> has_bounded_keys 1 p" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<longleftrightarrow> (tt p \<preceq>\<^sub>t lt p \<and> \<not> tt p \<prec>\<^sub>t lt p)" by auto
  also from lt_ge_tt[of p] have "... \<longleftrightarrow> \<not> tt p \<prec>\<^sub>t lt p" by simp
  finally show ?thesis by (simp add: lt_gr_tt_iff)
qed
  
subsection \<open>@{const lower}, @{const higher}, @{const tail}\<close>

lemma tail_0D:
  assumes "tail p = 0"
  shows "has_bounded_keys 1 p"
proof -
  from assms have "keys (tail p) = {}" by simp
  hence "keys p \<subseteq> {lt p}" by (simp add: keys_tail)
  thus ?thesis unfolding has_bounded_keys_def
    by (metis One_nat_def card.insert card_empty finite.emptyI insert_absorb order_class.le_less subset_singleton_iff zero_le_one)
qed

lemma tail_eq_0_iff_has_bounded_keys_1: "(tail p = 0) \<longleftrightarrow> has_bounded_keys 1 p" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  hence "(\<forall>s. s \<prec>\<^sub>t lt p \<longrightarrow> lookup p s = 0)" by (simp add: tail_def lower_eq_zero_iff)
  hence "\<And>s. s \<in> keys p \<Longrightarrow> lt p \<preceq>\<^sub>t s" unfolding in_keys_iff using ord_term_lin.leI by auto
  hence a: "\<And>s. s \<in> keys p \<Longrightarrow> s = lt p" using lt_max_keys by force
  show ?R unfolding has_bounded_keys_def
  proof (rule ccontr)
    assume "\<not> card (keys p) \<le> 1"
    hence "card (keys p) \<ge> 2" by simp
    then obtain A where "card A = 2" and "A \<subseteq> keys p" by (rule card_geq_ex_subset) 
    from \<open>card A = 2\<close> obtain s t where "s \<noteq> t" and A_eq: "A = {s, t}" by (rule card_2_E)
    from \<open>A \<subseteq> keys p\<close> have "s \<in> keys p" by (rule in_mono[rule_format], simp add: A_eq)
    hence "s = lt p" by (rule a)
    from \<open>A \<subseteq> keys p\<close> have "t \<in> keys p" by (rule in_mono[rule_format], simp add: A_eq)
    hence "t = lt p" by (rule a)
    with \<open>s \<noteq> t\<close> \<open>s = lt p\<close> show False by simp
  qed
next
  assume ?R
  hence "p = 0 \<or> is_monomial p" by (rule has_bounded_keys_1_D)
  thus ?L
  proof
    assume "p = 0"
    thus ?L by simp
  next
    assume "is_monomial p"
    then obtain c t where "p = monomial c t" by (rule is_monomial_monomial)
    thus ?L by (simp add: tail_monomial)
  qed
qed

subsection \<open>Monomials and Binomials\<close>

lemma lt_eq_min_term_monomial:
  assumes "lt p = min_term"
  shows "monomial (lc p) min_term = p"
proof (rule poly_mapping_eqI)
  fix v
  from min_term_min[of v] have "v = min_term \<or> min_term \<prec>\<^sub>t v" by auto
  thus "lookup (monomial (lc p) min_term) v = lookup p v"
  proof
    assume "v = min_term"
    thus ?thesis by (simp add: lookup_single lc_def assms)
  next
    assume "min_term \<prec>\<^sub>t v"
    moreover have "v \<notin> keys p"
    proof
      assume "v \<in> keys p"
      hence "v \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
      with \<open>min_term \<prec>\<^sub>t v\<close> show False by (simp add: assms)
    qed
    ultimately show ?thesis by (simp add: lookup_single)
  qed
qed

lemma lt_gr_tt_binomial:
  assumes "is_proper_binomial p"
  shows "tt p \<prec>\<^sub>t lt p"
  using assms by (simp only: lt_gr_tt_iff is_proper_binomial_def not_has_bounded_keys)

lemma keys_proper_binomial:
  assumes "is_proper_binomial p"
  shows "keys p = {lt p, tt p}"
proof -
  from assms have "p \<noteq> 0" and "tt p \<prec>\<^sub>t lt p"
    by (simp only: is_proper_binomial_def, rule proper_binomial_not_0, rule lt_gr_tt_binomial)
  from this(2) have "lt p \<noteq> tt p" by simp
  from assms obtain s t where keys_p: "keys p = {s, t}" and "s \<noteq> t" by (rule is_proper_binomial_keysE)
  with lt_in_keys[OF \<open>p \<noteq> 0\<close>] tt_in_keys[OF \<open>p \<noteq> 0\<close>] \<open>lt p \<noteq> tt p\<close> show ?thesis by auto
qed

corollary keys_binomial:
  assumes "is_binomial p"
  shows "keys p = {lt p, tt p}"
proof -
  from assms have "is_monomial p \<or> is_proper_binomial p" by (simp only: is_binomial_alt)
  thus ?thesis
  proof
    assume "is_monomial p"
    hence "lt p = tt p" and "keys p = {lt p}" by (rule lt_eq_tt_monomial, rule keys_monomial)
    thus ?thesis by simp
  next
    assume "is_proper_binomial p"
    thus ?thesis by (rule keys_proper_binomial)
  qed
qed

lemma binomial_eq_itself:
  assumes "is_proper_binomial p"
  shows "binomial (lc p) (lt p) (tc p) (tt p) = p"
proof -
  from assms have "p \<noteq> 0" by (rule proper_binomial_not_0)
  hence "lc p \<noteq> 0" and "tc p \<noteq> 0" by (rule lc_not_0, rule tc_not_0)
  from assms have "tt p \<prec>\<^sub>t lt p" by (rule lt_gr_tt_binomial)
  hence "tt p \<noteq> lt p" by simp
  with \<open>lc p \<noteq> 0\<close> \<open>tc p \<noteq> 0\<close> have pbd: "is_pbd (lc p) (lt p) (tc p) (tt p)" by (simp add: is_pbd_def)
  hence keys1: "keys (binomial (lc p) (lt p) (tc p) (tt p)) = {lt p, tt p}" by (rule keys_binomial_pbd)
  show ?thesis
    by (rule poly_mapping_keys_eqI, simp only: keys_proper_binomial[OF assms] keys1, simp add: keys1 lookup_binomial,
        elim disjE, simp add: lookup_binomial[OF pbd] lc_def[symmetric],
        simp add: lookup_binomial[OF pbd] \<open>tt p \<noteq> lt p\<close> tc_def[symmetric])
qed

definition is_obd :: "'b::zero \<Rightarrow> 't \<Rightarrow> 'b \<Rightarrow> 't \<Rightarrow> bool"
  where "is_obd c s d t \<longleftrightarrow> (c \<noteq> 0 \<and> d \<noteq> 0 \<and> t \<prec>\<^sub>t s)"

text \<open>@{const is_obd} stands for "is ordered binomial data".\<close>
    
lemma obd_imp_pbd:
  assumes "is_obd c s d t"
  shows "is_pbd c s d t"
  using assms unfolding is_obd_def is_pbd_def by auto
    
lemma pbd_imp_obd:
  assumes "is_pbd c s d t"
  shows "is_obd c s d t \<or> is_obd d t c s"
proof -
  from assms have "s \<noteq> t" by (rule is_pbdD)
  hence "s \<prec>\<^sub>t t \<or> t \<prec>\<^sub>t s" by auto
  thus ?thesis
  proof
    assume "s \<prec>\<^sub>t t"
    with \<open>is_pbd c s d t\<close> have "is_obd d t c s" unfolding is_pbd_def is_obd_def by simp
    thus ?thesis ..
  next
    assume "t \<prec>\<^sub>t s"
    with \<open>is_pbd c s d t\<close> have "is_obd c s d t" unfolding is_pbd_def is_obd_def by simp
    thus ?thesis ..
  qed
qed

lemma is_obd_mult:
  assumes "is_obd (c::'b::semiring_no_zero_divisors) u d v" and "a \<noteq> 0"
  shows "is_obd (a * c) (t \<oplus> u) (a * d) (t \<oplus> v)"
  using assms splus_mono_strict[of v u t] unfolding is_obd_def by auto

lemma is_proper_binomial_binomial_od:
  fixes p
  assumes "is_proper_binomial p"
  obtains c d s t where "is_obd c s d t" and "p = binomial c s d t"
proof -
  from is_proper_binomial_binomial[OF assms] obtain c s d t
    where "is_pbd c s d t" and p_def: "p = binomial c s d t" .
  from \<open>is_pbd c s d t\<close> have "is_obd c s d t \<or> is_obd d t c s" by (rule pbd_imp_obd)
  thus ?thesis
  proof
    assume "is_obd d t c s"
    show ?thesis
    proof
      from p_def show "p = binomial d t c s" by (simp add: binomial_comm)
    qed fact
  next
    assume "is_obd c s d t"
    show ?thesis
    proof
      from p_def show "p = binomial c s d t" .
    qed fact
  qed
qed
  
lemma lt_binomial:
  assumes "is_obd c s d t"
  shows "lt (binomial c s d t) = s"
proof -
  have pbd: "is_pbd c s d t" by (rule obd_imp_pbd, fact)
  hence "c \<noteq> 0" by (rule is_pbdD)
  show ?thesis
  proof (intro lt_eqI)
    from \<open>c \<noteq> 0\<close> show "lookup (binomial c s d t) s \<noteq> 0" unfolding lookup_binomial[OF pbd] by simp
  next
    fix u
    assume "lookup (binomial c s d t) u \<noteq> 0"
    hence "u \<in> keys (binomial c s d t)" by simp
    hence "u \<in> {s, t}" unfolding keys_binomial_pbd[OF pbd] .
    hence "u = s \<or> u = t" by simp
    thus "u \<preceq>\<^sub>t s"
    proof
      assume "u = s"
      thus "u \<preceq>\<^sub>t s" by simp
    next
      assume "u = t"
      from \<open>is_obd c s d t\<close> have "u \<prec>\<^sub>t s" unfolding \<open>u = t\<close> is_obd_def by simp
      thus "u \<preceq>\<^sub>t s" by simp
    qed
  qed
qed

lemma lc_binomial:
  assumes "is_obd c s d t"
  shows "lc (binomial c s d t) = c"
  unfolding lc_def lt_binomial[OF assms] lookup_binomial[OF assms[THEN obd_imp_pbd]] by simp

lemma tt_binomial:
  assumes "is_obd c s d t"
  shows "tt (binomial c s d t) = t"
proof -
  from assms have pbd: "is_pbd c s d t" by (rule obd_imp_pbd)
  hence "c \<noteq> 0" by (rule is_pbdD)
  show ?thesis
  proof (intro tt_eqI)
    from \<open>c \<noteq> 0\<close> show "t \<in> keys (binomial c s d t)" unfolding keys_binomial_pbd[OF pbd] by simp
  next
    fix u
    assume "u \<in> keys (binomial c s d t)"
    hence "u \<in> {s, t}" unfolding keys_binomial_pbd[OF pbd] .
    hence "u = s \<or> u = t" by simp
    thus "t \<preceq>\<^sub>t u"
    proof
      assume "u = s"
      from \<open>is_obd c s d t\<close> have "t \<prec>\<^sub>t u" unfolding \<open>u = s\<close> is_obd_def by simp
      thus ?thesis by simp
    next
      assume "u = t"
      thus ?thesis by simp
    qed
  qed
qed

lemma tc_binomial:
  assumes "is_obd c s d t"
  shows "tc (binomial c s d t) = d"
proof -
  from assms have "is_pbd c s d t" by (rule obd_imp_pbd)
  hence "s \<noteq> t" unfolding is_pbd_def by simp
  thus ?thesis unfolding tc_def tt_binomial[OF assms] lookup_binomial[OF assms[THEN obd_imp_pbd]] by simp
qed

lemma keys_2_lt:
  assumes "keys p = {s, t}" and "t \<preceq>\<^sub>t s"
  shows "lt p = s"
  by (rule lt_eqI_keys, simp_all add: assms(1), auto simp add: assms(2))

lemma keys_2_tt:
  assumes "keys p = {s, t}" and "t \<preceq>\<^sub>t s"
  shows "tt p = t"
  by (rule tt_eqI, simp_all add: assms(1), auto simp add: assms(2))

lemma keys_2_plus:
  assumes "keys p = {s, t}" and "keys q = {t, u}" and "u \<prec>\<^sub>t t" and "t \<prec>\<^sub>t s" and "lookup p t + lookup q t = 0"
  shows "keys (p + q) = {s, u}"
proof -
  have "lookup (p + q) t = 0" by (simp only: lookup_add assms(5))
  hence "t \<notin> keys (p + q)" by simp
  show ?thesis
  proof
    have "keys (p + q) \<subseteq> keys p \<union> keys q" by (rule keys_add_subset)
    also have "... = {s, t} \<union> {t, u}" by (simp only: assms(1) assms(2))
    finally have "keys (p + q) \<subseteq> {s, t, u}" by auto
    with \<open>t \<notin> keys (p + q)\<close> show "keys (p + q) \<subseteq> {s, u}" by auto
  next
    from \<open>u \<prec>\<^sub>t t\<close> \<open>t \<prec>\<^sub>t s\<close> have "u \<prec>\<^sub>t s" by simp
    have "s \<in> keys (p + q)"
    proof (rule in_keys_plusI1, simp add: assms(1), simp add: assms(2), rule conjI)
      from \<open>t \<prec>\<^sub>t s\<close> show "s \<noteq> t" by simp
    next
      from \<open>u \<prec>\<^sub>t s\<close> show "s \<noteq> u" by simp
    qed
    moreover have "u \<in> keys (p + q)"
    proof (rule in_keys_plusI2, simp add: assms(2), simp add: assms(1), rule conjI)
      from \<open>u \<prec>\<^sub>t s\<close> show "u \<noteq> s" by simp
    next
      from \<open>u \<prec>\<^sub>t t\<close> show "u \<noteq> t" by simp
    qed
    ultimately show "{s, u} \<subseteq> keys (p + q)" by simp
  qed
qed

subsection \<open>Monicity\<close>

lemma monic_has_bounded_keys:
  assumes "has_bounded_keys n p"
  shows "has_bounded_keys n (monic p)"
  using assms by (simp only: has_bounded_keys_def keys_monic)
    
lemma image_monic_has_bounded_keys:
  assumes "has_bounded_keys_set n A"
  shows "has_bounded_keys_set n (monic ` A)"
proof (rule has_bounded_keys_setI)
  fix a
  assume "a \<in> monic ` A"
  then obtain a' where a_def: "a = monic a'" and "a' \<in> A" ..
  from assms \<open>a' \<in> A\<close> have "has_bounded_keys n a'" by (rule has_bounded_keys_setD)
  thus "has_bounded_keys n a" unfolding a_def by (rule monic_has_bounded_keys)
qed

end (* ordered_term *)

end (* theory *)
