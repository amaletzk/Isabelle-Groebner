(* Author: Alexander Maletzky *)

theory Poly_Utils
  imports "Polynomials/MPoly_Type_Class_Ordered" General_Utils
begin

text \<open>Some further general properties of (ordered) multivariate polynomials. This theory is an
  extension of @{theory MPoly_Type_Class}.\<close>
  
section \<open>Further Properties of Multivariate Polynomials\<close>

context term_powerprod
begin

subsection \<open>Sub-Polynomials\<close>

definition subpoly :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  where "subpoly p q \<longleftrightarrow> (\<forall>v\<in>(keys p). lookup p v = lookup q v)"

lemma subpolyI:
  assumes "\<And>v. v \<in> keys p \<Longrightarrow> lookup p v = lookup q v"
  shows "p \<sqsubseteq> (q::'t \<Rightarrow>\<^sub>0 _)"
  unfolding subpoly_def using assms by auto

lemma subpolyE:
  assumes "p \<sqsubseteq> (q::'t \<Rightarrow>\<^sub>0 _)" and "v \<in> keys p"
  shows "lookup p v = lookup q v"
  using assms unfolding subpoly_def by auto

lemma subpoly_keys:
  assumes "p \<sqsubseteq> (q::'t \<Rightarrow>\<^sub>0 _)"
  shows "keys p \<subseteq> keys q"
proof
  fix v
  assume "v \<in> keys p"
  hence "lookup p v \<noteq> 0" unfolding in_keys_iff .
  from assms \<open>v \<in> keys p\<close> have "lookup p v = lookup q v" by (rule subpolyE)
  with \<open>lookup p v \<noteq> 0\<close> show "v \<in> keys q" unfolding in_keys_iff by simp
qed

lemma subpoly_diff_keys_disjoint:
  assumes "p \<sqsubseteq> (q::'t \<Rightarrow>\<^sub>0 _)"
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

lemma zero_subpoly: "0 \<sqsubseteq> (q::'t \<Rightarrow>\<^sub>0 _)"
  by (rule subpolyI, simp)

lemma monomial_subpoly: "(monomial (lookup p t) t) \<sqsubseteq> (p::'t \<Rightarrow>\<^sub>0 _)" (is "?q \<sqsubseteq> (_::'t \<Rightarrow>\<^sub>0 _)")
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

lemma subpoly_refl: "p \<sqsubseteq> (p::'t \<Rightarrow>\<^sub>0 _)"
  by (rule subpolyI, rule)

lemma subpoly_antisym:
  assumes "p \<sqsubseteq> (q::'t \<Rightarrow>\<^sub>0 _)" and "q \<sqsubseteq> (p::'t \<Rightarrow>\<^sub>0 _)"
  shows "p = q"
proof (rule poly_mapping_keys_eqI, rule, rule subpoly_keys, fact, rule subpoly_keys, fact)
  fix t
  assume "t \<in> keys p"
  with \<open>p \<sqsubseteq> q\<close> show "lookup p t = lookup q t" by (rule subpolyE)
qed

lemma subpoly_trans:
  assumes "p \<sqsubseteq> (q::'t \<Rightarrow>\<^sub>0 _)" and "q \<sqsubseteq> (r::'t \<Rightarrow>\<^sub>0 _)"
  shows "p \<sqsubseteq> (r::'t \<Rightarrow>\<^sub>0 _)"
proof (rule subpolyI)
  fix t
  assume "t \<in> keys p"
  have "t \<in> keys q" by (rule, rule subpoly_keys, fact+)
  from \<open>p \<sqsubseteq> q\<close> \<open>t \<in> keys p\<close> have "lookup p t = lookup q t" by (rule subpolyE)
  also from \<open>q \<sqsubseteq> r\<close> \<open>t \<in> keys q\<close> have "... = lookup r t" by (rule subpolyE)
  finally show "lookup p t = lookup r t" .
qed

lemma plus_subpolyI:
  assumes "p \<sqsubseteq> (r::'t \<Rightarrow>\<^sub>0 _)" and "q \<sqsubseteq> (r::'t \<Rightarrow>\<^sub>0 _)" and "keys p \<inter> keys q = {}"
  shows "p + q \<sqsubseteq> (r::'t \<Rightarrow>\<^sub>0 _)"
proof (rule subpolyI)
  fix t
  assume "t \<in> keys (p + q)"
  also from assms(3) have "... = keys p \<union> keys q" by (rule keys_plus_eqI)
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

lemma except_subpoly: "except p S \<sqsubseteq> (p::'t \<Rightarrow>\<^sub>0 _)"
proof (rule subpolyI)
  fix s
  assume "s \<in> keys (except p S)"
  hence "s \<notin> S" unfolding keys_except ..
  thus "lookup (except p S) s = lookup p s" by (rule lookup_except_eq_idI)
qed

subsection \<open>Modules and Linear Hulls\<close>

lemma monomial_1_in_pmdlI:
  assumes "(f::_ \<Rightarrow>\<^sub>0 'b::field) \<in> pmdl F" and "keys f = {t}"
  shows "monomial 1 t \<in> pmdl F"
proof -
  define c where "c \<equiv> lookup f t"
  from assms(2) have f_eq: "f = monomial c t" unfolding c_def
    by (metis (mono_tags, lifting) Diff_insert_absorb cancel_comm_monoid_add_class.add_cancel_right_right
        plus_except insert_absorb insert_not_empty keys_eq_empty_iff keys_except)
  from assms(2) have "c \<noteq> 0" by (simp add: c_def)
  hence "monomial 1 t = monom_mult (1 / c) 0 f" by (simp add: f_eq monom_mult_monomial term_simps)
  also from assms(1) have "... \<in> pmdl F" by (rule pmdl_closed_monom_mult)
  finally show ?thesis .
qed

lemma in_pmdl_listE:
  assumes "p \<in> pmdl (set bs)"
  obtains qs where "length qs = length bs" and "p = (\<Sum>(q, b)\<leftarrow>zip qs bs. q \<odot> b)"
proof -
  have "finite (set bs)" ..
  from this assms obtain q where p: "p = (\<Sum>b\<in>set bs. (q b) \<odot> b)" by (rule pmdl.in_module_finiteE)
  let ?qs = "map_dup q (\<lambda>_. 0) bs"
  show ?thesis
  proof
    show "length ?qs = length bs" by simp
  next
    let ?zs = "zip (map q (remdups bs)) (remdups bs)"
    have *: "distinct ?zs" by (rule distinct_zipI2, rule distinct_remdups)
    have inj: "inj_on (\<lambda>b. (q b, b)) (set bs)" by (rule, simp)
    have "p = (\<Sum>(q, b)\<leftarrow>?zs. q \<odot> b)"
      by (simp add: sum_list_distinct_conv_sum_set[OF *] set_zip_map1 p comm_monoid_add_class.sum.reindex[OF inj])
    also have "... = (\<Sum>(q, b)\<leftarrow>(filter (\<lambda>(q, b). q \<noteq> 0) ?zs). q \<odot> b)"
      by (rule monoid_add_class.sum_list_map_filter[symmetric], auto)
    also have "... = (\<Sum>(q, b)\<leftarrow>(filter (\<lambda>(q, b). q \<noteq> 0) (zip ?qs bs)). q \<odot> b)"
      by (simp only: filter_zip_map_dup_const)
    also have "... = (\<Sum>(q, b)\<leftarrow>zip ?qs bs. q \<odot> b)"
      by (rule monoid_add_class.sum_list_map_filter, auto)
    finally show "p = (\<Sum>(q, b)\<leftarrow>zip ?qs bs. q \<odot> b)" .
  qed
qed

lemma in_pmdl_listI: "(\<Sum>(q, b)\<leftarrow>zip qs bs. q \<odot> b) \<in> pmdl (set bs)"
proof (induct qs arbitrary: bs)
  case Nil
  show ?case by (simp add: pmdl.module_0)
next
  case step: (Cons q qs)
  show ?case
  proof (simp add: zip_Cons1 pmdl.module_0 split: list.split, intro allI impI)
    fix a as
    have "(\<Sum>(x, y)\<leftarrow>zip qs as. x \<odot> y) \<in> pmdl (insert a (set as))" (is "?x \<in> ?A")
      by (rule, fact step, rule pmdl.module_mono, auto)
    show "q \<odot> a + ?x \<in> ?A" by (rule pmdl.module_closed_plus, rule pmdl.smult_in_module, simp, fact)
  qed
qed

lemma in_phull_listE:
  assumes "p \<in> phull (set bs)"
  obtains cs where "length cs = length bs" and "p = (\<Sum>(c, b)\<leftarrow>zip cs bs. monom_mult c 0 b)"
proof -
  have "finite (set bs)" ..
  from this assms obtain c where p: "p = (\<Sum>b\<in>set bs. monom_mult (c b) 0 b)"
    by (rule phull.in_module_finiteE)
  let ?cs = "map_dup c (\<lambda>_. 0) bs"
  show ?thesis
  proof
    show "length ?cs = length bs" by simp
  next
    let ?zs = "zip (map c (remdups bs)) (remdups bs)"
    have *: "distinct ?zs" by (rule distinct_zipI2, rule distinct_remdups)
    have inj: "inj_on (\<lambda>x. (c x, x)) (set bs)" by (rule, simp)
    have "p = (\<Sum>(q, b)\<leftarrow>?zs. monom_mult q 0 b)"
      by (simp add: sum_list_distinct_conv_sum_set[OF *] set_zip_map1 p comm_monoid_add_class.sum.reindex[OF inj])
    also have "... = (\<Sum>(q, b)\<leftarrow>(filter (\<lambda>(c, b). c \<noteq> 0) ?zs). monom_mult q 0 b)"
      by (rule monoid_add_class.sum_list_map_filter[symmetric], auto)
    also have "... = (\<Sum>(q, b)\<leftarrow>(filter (\<lambda>(c, b). c \<noteq> 0) (zip ?cs bs)). monom_mult q 0 b)"
      by (simp only: filter_zip_map_dup_const)
    also have "... = (\<Sum>(q, b)\<leftarrow>zip ?cs bs. monom_mult q 0 b)"
      by (rule monoid_add_class.sum_list_map_filter, auto)
    finally show "p = (\<Sum>(q, b)\<leftarrow>zip ?cs bs. monom_mult q 0 b)" .
  qed
qed

lemma in_phull_listI: "(\<Sum>(c, b)\<leftarrow>zip cs bs. monom_mult c 0 b) \<in> phull (set bs)"
proof (induct cs arbitrary: bs)
  case Nil
  show ?case by (simp add: phull.module_0)
next
  case step: (Cons c cs)
  show ?case
  proof (simp add: zip_Cons1 phull.module_0 split: list.split, intro allI impI)
    fix a and as::"('t \<Rightarrow>\<^sub>0 'b) list"
    have "(\<Sum>(x, y)\<leftarrow>zip cs as. monom_mult x 0 y) \<in> phull (insert a (set as))" (is "?x \<in> ?A")
      by (rule, fact step, rule phull.module_mono, auto)
    show "monom_mult c 0 a + ?x \<in> ?A" by (rule phull.module_closed_plus, rule phull.smult_in_module, simp, fact)
  qed
qed

subsection \<open>Bounded Support\<close>
  
definition has_bounded_keys :: "nat \<Rightarrow> ('t, 'b::zero) poly_mapping \<Rightarrow> bool" where
  "has_bounded_keys n p \<longleftrightarrow> card (keys p) \<le> n"

definition has_bounded_keys_set :: "nat \<Rightarrow> ('t, 'b::zero) poly_mapping set \<Rightarrow> bool" where
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
  
definition is_binomial :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "is_binomial p \<longleftrightarrow> (card (keys p) = 1 \<or> card (keys p) = 2)"

definition is_proper_binomial :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "is_proper_binomial p \<longleftrightarrow> card (keys p) = 2"
    
definition binomial :: "'b::comm_monoid_add \<Rightarrow> 't \<Rightarrow> 'b \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where "binomial c s d t = monomial c s + monomial d t"
    
definition is_monomial_set :: "('t \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool"
  where "is_monomial_set A \<longleftrightarrow> (\<forall>p\<in>A. is_monomial p)"

definition is_binomial_set :: "('t \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool"
  where "is_binomial_set A \<longleftrightarrow> (\<forall>p\<in>A. is_binomial p)"

definition is_pbd :: "'b::zero \<Rightarrow> 't \<Rightarrow> 'b \<Rightarrow> 't \<Rightarrow> bool"
  where "is_pbd c s d t \<longleftrightarrow> (c \<noteq> 0 \<and> d \<noteq> 0 \<and> s \<noteq> t)"

text \<open>@{const is_pbd} stands for "is proper binomial data".\<close>

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
    
lemma is_proper_binomial_uminus: "is_proper_binomial (-p) \<longleftrightarrow> is_proper_binomial p"
  unfolding is_proper_binomial_def keys_uminus ..
    
lemma is_binomial_uminus: "is_binomial (-p) \<longleftrightarrow> is_binomial p"
  unfolding is_binomial_def keys_uminus ..

lemma monomial_imp_binomial:
  assumes "is_monomial p"
  shows "is_binomial p"
  using assms unfolding is_monomial_def is_binomial_def by simp

lemma proper_binomial_imp_binomial:
  assumes "is_proper_binomial p"
  shows "is_binomial p"
  using assms unfolding is_proper_binomial_def is_binomial_def by simp

lemma proper_binomial_no_monomial:
  assumes "is_proper_binomial p"
  shows "\<not> is_monomial p"
  using assms unfolding is_proper_binomial_def is_monomial_def by simp
  
lemma is_binomial_alt:
  shows "is_binomial p \<longleftrightarrow> (is_monomial p \<or> is_proper_binomial p)"
  unfolding is_monomial_def is_binomial_def is_proper_binomial_def ..

lemma proper_binomial_not_0:
  assumes "is_proper_binomial p"
  shows "p \<noteq> 0"
  using assms unfolding is_proper_binomial_def by auto

corollary binomial_not_0:
  assumes "is_binomial p"
  shows "p \<noteq> 0"
  using assms unfolding is_binomial_alt using monomial_not_0 proper_binomial_not_0 by auto
    
lemma is_pbdE1:
  assumes "is_pbd c s d t"
  shows "c \<noteq> 0"
  using assms unfolding is_pbd_def by simp

lemma is_pbdE2:
  assumes "is_pbd c s d t"
  shows "d \<noteq> 0"
  using assms unfolding is_pbd_def by simp
    
lemma is_pbdE3:
  assumes "is_pbd c s d t"
  shows "s \<noteq> t"
  using assms unfolding is_pbd_def by simp
    
lemma is_pbdI:
  assumes "c \<noteq> 0" and "d \<noteq> 0" and "s \<noteq> t"
  shows "is_pbd c s d t"
  using assms unfolding is_pbd_def by simp

lemma binomial_comm:
  shows "binomial c s d t = binomial d t c s"
  unfolding binomial_def by (simp add: ac_simps)

lemma keys_binomial:
  shows "keys (binomial c s d t) \<subseteq> {s, t}"
proof
  fix u
  assume "u \<in> keys (binomial c s d t)"
  hence "lookup (binomial c s d t) u \<noteq> 0" by simp
  hence "u = s \<or> u = t" unfolding binomial_def lookup_add lookup_single Poly_Mapping.when_def
    by (metis (full_types) add.comm_neutral)
  thus "u \<in> {s, t}" by simp
qed
    
lemma card_keys_binomial:
  shows "card (keys (binomial c s d t)) \<le> 2"
proof -
  have "finite {s, t}" by simp
  from this keys_binomial have "card (keys (binomial c s d t)) \<le> card {s, t}" by (rule card_mono)
  also have "... \<le> 2" by (simp add: card_insert_le_m1)
  finally show ?thesis .
qed

lemma keys_binomial_pbd:
  fixes c d s t
  assumes "is_pbd c s d t"
  shows "keys (binomial c s d t) = {s, t}"
proof -
  from assms have "c \<noteq> 0" by (rule is_pbdE1)
  from assms have "d \<noteq> 0" by (rule is_pbdE2)
  from assms have "s \<noteq> t" by (rule is_pbdE3)
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
  
lemma lookup_binomial:
  fixes c d s t
  assumes "is_pbd c s d t"
  shows "lookup (binomial c s d t) u = (if u = s then c else (if u = t then d else 0))"
  unfolding binomial_def lookup_add lookup_single using is_pbdE3[OF assms] by simp
    
lemma binomial_uminus:
  shows "- binomial c s d t = binomial (-c) s (-d) t"
  unfolding binomial_def by (simp add: monomial_uminus)

lemma binomial_is_proper_binomial:
  fixes c d s t
  assumes "is_pbd c s d t"
  shows "is_proper_binomial (binomial c s d t)"
  unfolding is_proper_binomial_def keys_binomial_pbd[OF assms] using is_pbdE3[OF assms] by simp

lemma is_proper_binomial_binomial:
  fixes p
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
    
lemma is_pbd_mult:
  assumes "is_pbd (c::'b::field) u d v" and "a \<noteq> 0"
  shows "is_pbd (a * c) (t \<oplus> u) (a * d) (t \<oplus> v)"
  using assms unfolding is_pbd_def by (auto simp add: term_simps)
    
lemma monom_mult_binomial:
  "monom_mult a t (binomial c u d v) = binomial (a * c) (t \<oplus> u) (a * d) (t \<oplus> v)"
  unfolding binomial_def monom_mult_dist_right monom_mult_monomial ..

end (* term_powerprod *)
  
section \<open>Further Properties of Ordered Polynomials\<close>
  
context ordered_term
begin

subsection \<open>Modules and Linear Hulls\<close>

text \<open>The following lemma also holds in context @{locale term_powerprod}, but then one needs the
  additional assumption that function @{const monom_mult} is injective in its second argument (the
  power-product), provided the other two arguments (coefficient, polynomial) are non-zero.\<close>

lemma in_pmdl_in_phull:
  fixes B::"('t \<Rightarrow>\<^sub>0 'b::ring_1_no_zero_divisors) set"
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

  have "?p \<in> phull ?A" unfolding * by (rule phull.sum_in_moduleI)
  also have "... \<subseteq> phull A" by (rule phull.module_mono, auto)
  finally show ?thesis .
next                             
  case False
  thus ?thesis by (simp add: phull.module_0)
qed

subsection \<open>Sets of Leading Terms and -Coefficients\<close>
  
definition lt_set :: "('t, 'b::zero) poly_mapping set \<Rightarrow> 't set" where
  "lt_set F = lt ` (F - {0})"

definition lc_set :: "('t, 'b::zero) poly_mapping set \<Rightarrow> 'b set" where
  "lc_set F = lc ` (F - {0})"
  
lemma lt_setI:
  assumes "f \<in> F" and "f \<noteq> 0"
  shows "lt f \<in> lt_set F"
  unfolding lt_set_def using assms by simp

lemma lt_setE:
  assumes "t \<in> lt_set F"
  obtains f where "f \<in> F" and "f \<noteq> 0" and "lt f = t"
  using assms unfolding lt_set_def by auto
    
lemma lt_set_iff:
  shows "t \<in> lt_set F \<longleftrightarrow> (\<exists>f\<in>F. f \<noteq> 0 \<and> lt f = t)"
  unfolding lt_set_def by auto

lemma lc_setI:
  assumes "f \<in> F" and "f \<noteq> 0"
  shows "lc f \<in> lc_set F"
  unfolding lc_set_def using assms by simp

lemma lc_setE:
  assumes "c \<in> lc_set F"
  obtains f where "f \<in> F" and "f \<noteq> 0" and "lc f = c"
  using assms unfolding lc_set_def by auto
    
lemma lc_set_iff:
  shows "c \<in> lc_set F \<longleftrightarrow> (\<exists>f\<in>F. f \<noteq> 0 \<and> lc f = c)"
  unfolding lc_set_def by auto

lemma lc_set_nonzero:
  shows "0 \<notin> lc_set F"
proof
  assume "0 \<in> lc_set F"
  then obtain f where "f \<in> F" and "f \<noteq> 0" and "lc f = 0" by (rule lc_setE)
  from \<open>f \<noteq> 0\<close> have "lc f \<noteq> 0" by (rule lc_not_0)
  from this \<open>lc f = 0\<close> show False ..
qed

lemma lt_sum_distinct_eq_Max:
  assumes "finite I" and "sum p I \<noteq> 0"
    and "\<And>i1 i2. i1 \<in> I \<Longrightarrow> i2 \<in> I \<Longrightarrow> p i1 \<noteq> 0 \<Longrightarrow> p i2 \<noteq> 0 \<Longrightarrow> lt (p i1) = lt (p i2) \<Longrightarrow> i1 = i2"
  shows "lt (sum p I) = ord_term_lin.Max (lt_set (p ` I))"
proof -
  have "\<not> p ` I \<subseteq> {0}"
  proof
    assume "p ` I \<subseteq> {0}"
    hence "sum p I = 0" by (rule sum_poly_mapping_eq_zeroI)
    with assms(2) show False ..
  qed
  from assms(1) this assms(3) show ?thesis
  proof (induct I)
    case empty
    from empty(1) show ?case by simp
  next
    case (insert x I)
    show ?case
    proof (cases "p ` I \<subseteq> {0}")
      case True
      hence "p ` I - {0} = {}" by simp
      have "p x \<noteq> 0"
      proof
        assume "p x = 0"
        with True have " p ` insert x I \<subseteq> {0}" by simp
        with insert(4) show False ..
      qed
      hence "insert (p x) (p ` I) - {0} = insert (p x) (p ` I - {0})" by auto
      hence "lt_set (p ` insert x I) = {lt (p x)}" by (simp add: lt_set_def \<open>p ` I - {0} = {}\<close>)
      hence eq1: "ord_term_lin.Max (lt_set (p ` insert x I)) = lt (p x)" by simp
      have eq2: "sum p I = 0"
      proof (rule ccontr)
        assume "sum p I \<noteq> 0"
        then obtain y where "y \<in> I" and "p y \<noteq> 0" by (rule sum.not_neutral_contains_not_neutral)
        with True show False by auto
      qed
      show ?thesis by (simp only: eq1 sum.insert[OF insert(1) insert(2)], simp add: eq2)
    next
      case False
      hence IH: "lt (sum p I) = ord_term_lin.Max (lt_set (p ` I))"
      proof (rule insert(3))
        fix i1 i2
        assume "i1 \<in> I" and "i2 \<in> I"
        hence "i1 \<in> insert x I" and "i2 \<in> insert x I" by simp_all
        moreover assume "p i1 \<noteq> 0" and "p i2 \<noteq> 0" and "lt (p i1) = lt (p i2)"
        ultimately show "i1 = i2" by (rule insert(5))
      qed
      show ?thesis
      proof (cases "p x = 0")
        case True
        hence eq: "lt_set (p ` insert x I) = lt_set (p ` I)" by (simp add: lt_set_def)
        show ?thesis by (simp only: eq, simp add: sum.insert[OF insert(1) insert(2)] True, fact IH)
      next
        case False
        hence eq1: "lt_set (p ` insert x I) = insert (lt (p x)) (lt_set (p ` I))"
          by (auto simp add: lt_set_def)
        from insert(1) have "finite (lt_set (p ` I))" by (simp add: lt_set_def)
        moreover from \<open>\<not> p ` I \<subseteq> {0}\<close> have "lt_set (p ` I) \<noteq> {}" by (simp add: lt_set_def)
        ultimately have eq2: "ord_term_lin.Max (insert (lt (p x)) (lt_set (p ` I))) =
                          ord_term_lin.max (lt (p x)) (ord_term_lin.Max (lt_set (p ` I)))"
          by (rule ord_term_lin.Max_insert)
        show ?thesis
        proof (simp only: eq1, simp add: sum.insert[OF insert(1) insert(2)] eq2 IH[symmetric],
            rule lt_plus_distinct_eq_max, rule)
          assume *: "lt (p x) = lt (sum p I)"
          have "lt (p x) \<in> lt_set (p ` I)" by (simp only: * IH, rule ord_term_lin.Max_in, fact+)
          then obtain f where "f \<in> p ` I" and "f \<noteq> 0" and ltf: "lt f = lt (p x)" by (rule lt_setE)
          from this(1) obtain y where "y \<in> I" and "f = p y" ..
          from this(2) \<open>f \<noteq> 0\<close> ltf have "p y \<noteq> 0" and lt_eq: "lt (p y) = lt (p x)" by simp_all
          from _ _ this(1) \<open>p x \<noteq> 0\<close> this(2) have "y = x"
          proof (rule insert(5))
            from \<open>y \<in> I\<close> show "y \<in> insert x I" by simp
          next
            show "x \<in> insert x I" by simp
          qed
          with \<open>y \<in> I\<close> have "x \<in> I" by simp
          with \<open>x \<notin> I\<close> show False ..
        qed
      qed
    qed
  qed
qed

lemma lt_sum_distinct_in_lt_set:
  assumes "finite I" and "sum p I \<noteq> 0"
    and "\<And>i1 i2. i1 \<in> I \<Longrightarrow> i2 \<in> I \<Longrightarrow> p i1 \<noteq> 0 \<Longrightarrow> p i2 \<noteq> 0 \<Longrightarrow> lt (p i1) = lt (p i2) \<Longrightarrow> i1 = i2"
  shows "lt (sum p I) \<in> lt_set (p ` I)"
proof -
  have "\<not> p ` I \<subseteq> {0}"
  proof
    assume "p ` I \<subseteq> {0}"
    hence "sum p I = 0" by (rule sum_poly_mapping_eq_zeroI)
    with assms(2) show False ..
  qed
  have "lt (sum p I) = ord_term_lin.Max (lt_set (p ` I))"
    by (rule lt_sum_distinct_eq_Max, fact+)
  also have "... \<in> lt_set (p ` I)"
  proof (rule ord_term_lin.Max_in)
    from assms(1) show "finite (lt_set (p ` I))" by (simp add: lt_set_def)
  next
    from \<open>\<not> p ` I \<subseteq> {0}\<close> show "lt_set (p ` I) \<noteq> {}" by (simp add: lt_set_def)
  qed
  finally show ?thesis .
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

lemma lt_gr_tt_binomial:
  assumes "is_proper_binomial p"
  shows "tt p \<prec>\<^sub>t lt p"
  using assms by (simp only: lt_gr_tt_iff is_proper_binomial_def not_has_bounded_keys)

lemma keys_proper_binomial:
  assumes "is_proper_binomial p"
  shows "keys p = {lt p, tt p}"
proof -
  from assms have "card (keys p) = 2" and "p \<noteq> 0" and "tt p \<prec>\<^sub>t lt p"
    by (simp only: is_proper_binomial_def, rule proper_binomial_not_0, rule lt_gr_tt_binomial)
  from \<open>tt p \<prec>\<^sub>t lt p\<close> have "lt p \<noteq> tt p" by simp
  from \<open>card (keys p) = 2\<close> obtain s t where keys_p: "keys p = {s, t}" and "s \<noteq> t" by (rule card_2_E)
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
  have "s \<noteq> t" by (rule is_pbdE3, fact)
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
  hence "c \<noteq> 0" by (rule is_pbdE1)
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
  hence "c \<noteq> 0" by (rule is_pbdE1)
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

subsubsection \<open>Sets of Monomials and Binomials\<close>
  
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
    
lemma monomial_set_pmdl:
  fixes f :: "'t \<Rightarrow>\<^sub>0 'b::field"
  assumes "is_monomial_set G" and "f \<in> pmdl G" and "v \<in> keys f"
  shows "\<exists>g\<in>G. lt g adds\<^sub>t v"
  using \<open>f \<in> pmdl G\<close> \<open>v \<in> keys f\<close>
proof (induct f rule: pmdl_induct)
  case module_0
  have "keys 0 = {}" by (simp only: keys_eq_empty_iff)
  with \<open>v \<in> keys 0\<close> show ?case by auto
next
  case (module_plus a b c s)
  have "v \<in> keys (a + monom_mult c s b)" by fact
  also have "... \<subseteq> (keys a) \<union> (keys (monom_mult c s b))" by (rule keys_add_subset)
  finally have "v \<in> (keys a) \<union> (keys (monom_mult c s b))" .
  hence "v \<in> keys a \<or> v \<in> keys (monom_mult c s b)" by simp
  thus ?case
  proof
    assume "v \<in> keys a"
    thus ?thesis by (rule \<open>v \<in> keys a \<Longrightarrow> (\<exists>g\<in>G. lt g adds\<^sub>t v)\<close>)
  next
    assume "v \<in> keys (monom_mult c s b)"
    show ?thesis
    proof
      from \<open>is_monomial_set G\<close> \<open>b \<in> G\<close> have "is_monomial b" by (rule is_monomial_setD)
      then obtain d u where "d \<noteq> 0" and b_def: "b = monomial d u" by (rule is_monomial_monomial)
      from \<open>d \<noteq> 0\<close> have "lt b = u" unfolding b_def by (rule lt_monomial)
      have "monom_mult c s b = monomial (c * d) (s \<oplus> u)" unfolding b_def monom_mult_monomial ..
      with \<open>v \<in> keys (monom_mult c s b)\<close> have v: "v \<in> keys (monomial (c * d) (s \<oplus> u))" by simp
      show "lt b adds\<^sub>t v"
      proof (cases "c = 0")
        case True
        hence "c * d = 0" by simp
        hence "monomial (c * d) (s \<oplus> u) = 0" by (rule monomial_0I)
        hence "keys (monomial (c * d) (s \<oplus> u)) = {}" by simp
        with v have "v \<in> {}" by simp
        thus ?thesis ..
      next
        case False
        with \<open>d \<noteq> 0\<close> have "c * d \<noteq> 0" by simp
        hence "keys (monomial (c * d) (s \<oplus> u)) = {s \<oplus> u}" by (rule keys_of_monomial)
        with v have "v = s \<oplus> u" by simp
        thus ?thesis unfolding \<open>lt b = u\<close> by (simp add: term_simps)
      qed
    qed fact
  qed
qed

subsection \<open>Monicity\<close>
  
definition monic :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)" where
  "monic p = monom_mult (1 / lc p) 0 p"

definition monic_set :: "('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) set" where
  "monic_set = image monic"
  
definition is_monic_set :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> bool" where
  "is_monic_set B \<equiv> (\<forall>b\<in>B. b \<noteq> 0 \<longrightarrow> lc b = 1)"

lemma lookup_monic: "lookup (monic p) v = (lookup p v) / lc p"
proof -
  have "lookup (monic p) (0 \<oplus> v) = (1 / lc p) * (lookup p v)" unfolding monic_def
    by (rule lookup_monom_mult_plus)
  thus ?thesis by (simp add: term_simps)
qed

lemma lookup_monic_lt:
  assumes "p \<noteq> 0"
  shows "lookup (monic p) (lt p) = 1"
  unfolding monic_def
proof -
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  hence "1 / lc p \<noteq> 0" by simp
  let ?q = "monom_mult (1 / lc p) 0 p"
  have "lookup ?q (0 \<oplus> lt p) = (1 / lc p) * (lookup p (lt p))" by (rule lookup_monom_mult_plus)
  also have "... = (1 / lc p) * lc p" unfolding lc_def ..
  also have "... = 1" using \<open>lc p \<noteq> 0\<close> by simp
  finally have "lookup ?q (0 \<oplus> lt p) = 1" .
  thus "lookup ?q (lt p) = 1" by (simp add: term_simps)
qed
  
lemma monic_0 [simp]: "monic 0 = 0"
  unfolding monic_def by (rule monom_mult_zero_right)

lemma monic_0_iff: "(monic p = 0) \<longleftrightarrow> (p = 0)"
proof
  assume "monic p = 0"
  show "p = 0"
  proof (rule ccontr)
    assume "p \<noteq> 0"
    hence "lookup (monic p) (lt p) = 1" by (rule lookup_monic_lt)
    with \<open>monic p = 0\<close> have "lookup 0 (lt p) = (1::'b)" by simp
    thus False by simp
  qed
next
  assume p0: "p = 0"
  show "monic p = 0" unfolding p0 by (fact monic_0)
qed
  
lemma keys_monic [simp]: "keys (monic p) = keys p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True monic_0 ..
next
  case False
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  thm in_keys_iff
  show ?thesis
    by (rule set_eqI, simp add: in_keys_iff lookup_monic \<open>lc p \<noteq> 0\<close> del: lookup_not_eq_zero_eq_in_keys)
qed

lemma lt_monic [simp]: "lt (monic p) = lt p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True monic_0 ..
next
  case False
  have "lt (monom_mult (1 / lc p) 0 p) = 0 \<oplus> lt p"
  proof (rule lt_monom_mult)
    from False have "lc p \<noteq> 0" by (rule lc_not_0)
    thus "1 / lc p \<noteq> 0" by simp
  qed fact
  thus ?thesis by (simp add: monic_def term_simps)
qed

lemma lc_monic:
  assumes "p \<noteq> 0"
  shows "lc (monic p) = 1"
  using assms by (simp add: lc_def lookup_monic_lt)

lemma mult_lc_monic:
  assumes "p \<noteq> 0"
  shows "monom_mult (lc p) 0 (monic p) = p" (is "?q = p")
proof (rule poly_mapping_eqI)
  fix v
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  have "lookup ?q (0 \<oplus> v) = (lc p) * (lookup (monic p) v)" by (rule lookup_monom_mult_plus)
  also have "... = (lc p) * ((lookup p v) / lc p)" by (simp add: lookup_monic)
  also have "... = lookup p v" using \<open>lc p \<noteq> 0\<close> by simp
  finally show "lookup ?q v = lookup p v" by (simp add: term_simps)
qed

lemma is_monic_setI:
  assumes "\<And>b. b \<in> B \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> lc b = 1"
  shows "is_monic_set B"
  unfolding is_monic_set_def using assms by auto

lemma is_monic_setD:
  assumes "is_monic_set B" and "b \<in> B" and "b \<noteq> 0"
  shows "lc b = 1"
  using assms unfolding is_monic_set_def by auto

lemma Keys_monic_set [simp]: "Keys (monic_set A) = Keys A"
  by (simp add: Keys_def monic_set_def)
    
lemma monic_set_is_monic_set: "is_monic_set (monic_set A)"
proof (rule is_monic_setI)
  fix p
  assume pin: "p \<in> monic_set A" and "p \<noteq> 0"
  from pin obtain p' where p_def: "p = monic p'" and "p' \<in> A" unfolding monic_set_def ..
  from \<open>p \<noteq> 0\<close> have "p' \<noteq> 0" unfolding p_def monic_0_iff .
  thus "lc p = 1" unfolding p_def by (rule lc_monic)
qed
  
lemma monic_set_pmdl [simp]: "pmdl (monic_set B) = pmdl B"
proof
  show "pmdl (monic_set B) \<subseteq> pmdl B"
  proof
    fix p
    assume "p \<in> pmdl (monic_set B)"
    thus "p \<in> pmdl B"
    proof (induct p rule: pmdl_induct)
      case base: module_0
      show ?case by (fact pmdl.module_0)
    next
      case ind: (module_plus a b c t)
      from ind(3) obtain b' where b_def: "b = monic b'" and "b' \<in> B" unfolding monic_set_def ..
      have eq: "b = monom_mult (1 / lc b') 0 b'" by (simp only: b_def monic_def)
      show ?case unfolding eq monom_mult_assoc
        by (rule pmdl.module_closed_plus, fact, rule monom_mult_in_pmdl, fact)
    qed
  qed
next
  show "pmdl B \<subseteq> pmdl (monic_set B)"
  proof
    fix p
    assume "p \<in> pmdl B"
    thus "p \<in> pmdl (monic_set B)"
    proof (induct p rule: pmdl_induct)
      case base: module_0
      show ?case by (fact pmdl.module_0)
    next
      case ind: (module_plus a b c t)
      show ?case
      proof (cases "b = 0")
        case True
        from ind(2) show ?thesis by (simp add: True)
      next
        case False
        let ?b = "monic b"
        from ind(3) have "?b \<in> monic_set B" unfolding monic_set_def by (rule imageI)
        have "a + monom_mult c t (monom_mult (lc b) 0 ?b) \<in> pmdl (monic_set B)"
          unfolding monom_mult_assoc
          by (rule pmdl.module_closed_plus, fact, rule monom_mult_in_pmdl, fact)
        thus ?thesis unfolding mult_lc_monic[OF False] .
      qed
    qed
  qed
qed

lemma monic_has_bounded_keys:
  assumes "has_bounded_keys n p"
  shows "has_bounded_keys n (monic p)"
  using assms by (simp only: has_bounded_keys_def keys_monic)
    
lemma monic_set_has_bounded_keys:
  assumes "has_bounded_keys_set n A"
  shows "has_bounded_keys_set n (monic_set A)"
proof (rule has_bounded_keys_setI)
  fix a
  assume "a \<in> monic_set A"
  then obtain a' where a_def: "a = monic a'" and "a' \<in> A" unfolding monic_set_def by (rule imageE)
  from assms \<open>a' \<in> A\<close> have "has_bounded_keys n a'" by (rule has_bounded_keys_setD)
  thus "has_bounded_keys n a" unfolding a_def by (rule monic_has_bounded_keys)
qed

end (* ordered_term *)

end (* theory *)
