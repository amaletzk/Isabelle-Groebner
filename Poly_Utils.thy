text \<open>Some further general properties of (ordered) multivariate polynomials. This theory can be
  regarded an extension of theory Abstract_Poly.thy.\<close>

theory Poly_Utils
imports "Polynomials.Abstract_Poly" General_Utils
begin
  
section \<open>Further Properties of Multivariate Polynomials\<close>

context comm_powerprod
begin

lemma keys_of_monomial:
  assumes "c \<noteq> 0"
  shows "keys (monomial c t) = {t}"
  using assms by simp

lemma monomial_uminus:
  shows "- monomial c s = monomial (-c) s"
  by (transfer, rule ext, simp add: PP_Poly_Mapping.when_def)

definition poly_mapping_of_pp :: "'a \<Rightarrow> ('a, 'b::{one,zero}) poly_mapping" where
  "poly_mapping_of_pp t = monomial 1 t"
  
lemma keys_poly_mapping_of_pp:
  shows "keys ((poly_mapping_of_pp t)::('a, 'b::{zero_neq_one}) poly_mapping) = {t}"
  by (simp add: poly_mapping_of_pp_def)
    
lemma lookup_poly_mapping_of_pp:
  shows "lookup (poly_mapping_of_pp t) t = 1"
  by (simp add: poly_mapping_of_pp_def)

lemma poly_mapping_of_pp_nonzero:
  shows "poly_mapping_of_pp t \<noteq> (0::('a, 'b::{zero_neq_one}) poly_mapping)"
proof
  assume "poly_mapping_of_pp t = (0::('a, 'b) poly_mapping)"
  hence "keys ((poly_mapping_of_pp t)::('a, 'b) poly_mapping) = {}" by simp
  thus False unfolding keys_poly_mapping_of_pp by simp
qed
  
lemma poly_mapping_of_pp_inj:
  assumes "poly_mapping_of_pp s = ((poly_mapping_of_pp t)::('a, 'b::{zero_neq_one}) poly_mapping)"
  shows "s = t"
proof -
  have "{s} = keys ((poly_mapping_of_pp s)::('a, 'b) poly_mapping)" unfolding keys_poly_mapping_of_pp ..
  also have "... = keys ((poly_mapping_of_pp t)::('a, 'b) poly_mapping)" unfolding assms ..
  finally have "{s} = {t}" by (simp add: keys_poly_mapping_of_pp)
  thus ?thesis by simp
qed

subsection \<open>@{const keys}\<close>

lemma in_keys_plusI1:
  assumes "t \<in> keys p" and "t \<notin> keys q"
  shows "t \<in> keys (p + q)"
  using assms unfolding in_keys_iff lookup_add by simp

lemma in_keys_plusI2:
  assumes "t \<in> keys q" and "t \<notin> keys p"
  shows "t \<in> keys (p + q)"
  using assms unfolding in_keys_iff lookup_add by simp

lemma keys_plus_eqI:
  assumes "keys p \<inter> keys q = {}"
  shows "keys (p + q) = (keys p \<union> keys q)"
proof (rule, rule keys_add_subset, rule)
  fix t
  assume "t \<in> keys p \<union> keys q"
  thus "t \<in> keys (p + q)"
  proof
    assume "t \<in> keys p"
    moreover from assms this have "t \<notin> keys q" by auto
    ultimately show ?thesis by (rule in_keys_plusI1)
  next
    assume "t \<in> keys q"
    moreover from assms this have "t \<notin> keys p" by auto
    ultimately show ?thesis by (rule in_keys_plusI2)
  qed
qed

lemma keys_uminus':
  shows "keys (-p) \<subseteq> keys p"
proof
  fix t
  assume "t \<in> keys (-p)"
  hence "lookup (-p) t \<noteq> 0" unfolding in_keys_iff .
  hence "- lookup p t \<noteq> 0" by simp
  hence "lookup p t \<noteq> 0" by simp
  thus "t \<in> keys p" unfolding in_keys_iff .
qed
  
lemma keys_uminus:
  shows "keys (-p) = keys p"
  using keys_uminus'[of p] keys_uminus'[of "-p"] by simp

lemma keys_minus:
  shows "keys (p - q) \<subseteq> (keys p \<union> keys (q::'a \<Rightarrow>\<^sub>0 'b::ab_group_add))"
  using keys_add_subset[of p "-q"] keys_uminus[of q] by simp
    
lemma keys_monom_multI:
  assumes "s \<in> keys p" and "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "t + s \<in> keys (monom_mult c t p)"
  using assms unfolding in_keys_iff lookup_monom_mult by simp
    
lemma keys_monom_multE:
  assumes "s \<in> keys (monom_mult c t p)"
  obtains x where "x \<in> keys p" and "s = t + x"
proof -
  from assms have "t adds s \<and> lookup p (s - t) \<noteq> 0" by (transfer, auto split: if_splits)
  hence a: "t adds s" and b: "lookup p (s - t) \<noteq> 0" by simp_all
  from a obtain x where s: "s = t + x" by (rule addsE)
  have "s - t = x" unfolding s by simp
  with b have "lookup p x \<noteq> 0" by simp
  show ?thesis
  proof
    from \<open>lookup p x \<noteq> 0\<close> show "x \<in> keys p" unfolding in_keys_iff .
  qed fact
qed

lemma keys_monom_mult_subset: "keys (monom_mult c t p) \<subseteq> (op + t) ` (keys p)"
proof
  fix s
  assume "s \<in> keys (monom_mult c t p)"
  then obtain x where "x \<in> keys p" and "s = t + x" by (rule keys_monom_multE)
  thus "s \<in> (op + t) ` (keys p)" unfolding image_iff ..
qed

lemma keys_monom_mult:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "keys (monom_mult c t p) = (op + t) ` (keys p)"
proof (rule, fact keys_monom_mult_subset, rule)
  fix s
  assume "s \<in> op + t ` keys p"
  hence "\<exists>x\<in>keys p. s = t + x" unfolding image_iff .
  then obtain x where "x \<in> keys p" and s: "s = t + x" ..
  from \<open>x \<in> keys p\<close> assms show "s \<in> keys (monom_mult c t p)" unfolding s by (rule keys_monom_multI)
qed

lemma poly_mapping_keys_eqI:
  assumes a1: "keys p = keys q" and a2: "\<And>t. t \<in> keys p \<Longrightarrow> lookup p t = lookup q t"
  shows "p = q"
proof (rule poly_mapping_eqI)
  fix t
  show "lookup p t = lookup q t"
  proof (cases "t \<in> keys p")
    case True
    thus ?thesis by (rule a2)
  next
    case False
    moreover from this have "t \<notin> keys q" unfolding a1 .
    ultimately have "lookup p t = 0" and "lookup q t = 0" unfolding in_keys_iff by simp_all
    thus ?thesis by simp
  qed
qed

subsection \<open>Sums\<close>

lemma lookup_sum: "lookup (\<Sum>a\<in>A. f a) t = (\<Sum>a\<in>A. lookup (f a) t)"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct A)
    case empty
    show ?case by simp
  next
    case (insert a A)
    show ?case
      by (simp only: comm_monoid_add_class.sum.insert[OF insert(1) insert(2)] lookup_add insert(3))
  qed
next
  case False
  thus ?thesis by simp
qed

lemma lookup_sum_list: "lookup (sum_list ps) t = sum_list (map (\<lambda>p. lookup p t) ps)"
proof (induct ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  thus ?case by (simp add: lookup_add)
qed

lemma poly_mapping_sum_monomials:
  fixes p::"('a, 'b::comm_monoid_add) poly_mapping"
  shows "(\<Sum>t\<in>keys p. monomial (lookup p t) t) = p"
proof (induct p rule: poly_mapping_plus_induct)
  case 1
  show ?case by simp
next
  case step: (2 p c t)
  from step(2) have "lookup p t = 0" by simp
  have *: "keys (monomial c t + p) = insert t (keys p)"
  proof -
    from step(1) have a: "keys (monomial c t) = {t}" by simp
    with step(2) have "keys (monomial c t) \<inter> keys p = {}" by simp
    hence "keys (monomial c t + p) = {t} \<union> keys p" by (simp only: a keys_plus_eqI)
    thus ?thesis by simp
  qed
  have **: "(\<Sum>ta\<in>keys p. monomial ((c when t = ta) + lookup p ta) ta) = (\<Sum>ta\<in>keys p. monomial (lookup p ta) ta)"
  proof (rule comm_monoid_add_class.sum.cong, rule refl)
    fix s
    assume "s \<in> keys p"
    with step(2) have "t \<noteq> s" by auto
    thus "monomial ((c when t = s) + lookup p s) s = monomial (lookup p s) s" by simp
  qed
    show ?case by (simp only: * comm_monoid_add_class.sum.insert[OF finite_keys step(2)],
                   simp add: lookup_add lookup_single \<open>lookup p t = 0\<close> ** step(3))
qed

lemma (in -) times_sum_monomials:
  fixes q::"('a::comm_powerprod, 'b::semiring_0) poly_mapping"
  shows "q * p = (\<Sum>t\<in>keys q. monom_mult (lookup q t) t p)"
  by (simp only: times_monomial_left[symmetric] sum_distrib_right[symmetric] poly_mapping_sum_monomials)

lemma monom_mult_sum: "monom_mult (\<Sum>c\<in>C. f c) t p = (\<Sum>c\<in>C. monom_mult (f c) t p)"
proof (cases "finite C")
  case True
  thus ?thesis
  proof (induct C)
    case empty
    show ?case by (simp add: monom_mult_left0)
  next
    case (insert c C)
    show ?case
      by (simp only: comm_monoid_add_class.sum.insert[OF insert(1) insert(2)] monom_mult_dist_left insert(3))
  qed
next
  case False
  thus ?thesis by (simp add: monom_mult_left0)
qed

subsection \<open>@{const monom_mult}\<close>

lemma lookup_monom_mult_const: "lookup (monom_mult c 0 p) t = c * lookup p t"
proof -
  have "lookup (monom_mult c 0 p) t = lookup (monom_mult c 0 p) (0 + t)" by simp
  also have "... = c * lookup p t" by (rule lookup_monom_mult)
  finally show ?thesis .
qed

lemma monom_mult_inj_1:
  assumes "monom_mult c1 t p = monom_mult c2 t p"
    and "(p::('a, 'b::semiring_no_zero_divisors_cancel) poly_mapping) \<noteq> 0"
  shows "c1 = c2"
proof -
  from assms(2) have "keys p \<noteq> {}" by simp
  then obtain s where "s \<in> keys p" by blast
  hence *: "lookup p s \<noteq> 0" by simp
  from assms(1) have "lookup (monom_mult c1 t p) (t + s) = lookup (monom_mult c2 t p) (t + s)" by simp
  hence "c1 * lookup p s = c2 * lookup p s" by (simp only: lookup_monom_mult)
  with * show ?thesis by auto
qed

lemma (in ordered_powerprod) monom_mult_inj_2:
  assumes "monom_mult c t1 p = monom_mult c t2 p"
    and "c \<noteq> 0" and "(p::('a, 'b::semiring_no_zero_divisors) poly_mapping) \<noteq> 0"
  shows "t1 = t2"
proof -
  from assms(1) have "lp (monom_mult c t1 p) = lp (monom_mult c t2 p)" by simp
  with \<open>c \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have "t1 + lp p = t2 + lp p" by (simp add: lp_mult)
  thus ?thesis by simp
qed

lemma monom_mult_inj_3:
  assumes "monom_mult c t p1 = monom_mult c t (p2::('a, 'b::semiring_no_zero_divisors_cancel) poly_mapping)"
    and "c \<noteq> 0"
  shows "p1 = p2"
proof (rule poly_mapping_eqI)
  fix s
  from assms(1) have "lookup (monom_mult c t p1) (t + s) = lookup (monom_mult c t p2) (t + s)" by simp
  hence "c * lookup p1 s = c * lookup p2 s" by (simp only: lookup_monom_mult)
  with assms(2) show "lookup p1 s = lookup p2 s" by simp
qed

subsection \<open>Sub-Polynomials\<close>

definition subpoly :: "('a, 'b) poly_mapping \<Rightarrow> ('a, 'b::zero) poly_mapping \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  where "subpoly p q \<longleftrightarrow> (\<forall>t\<in>(keys p). lookup p t = lookup q t)"

lemma subpolyI:
  assumes "\<And>t. t \<in> keys p \<Longrightarrow> lookup p t = lookup q t"
  shows "p \<sqsubseteq> q"
  unfolding subpoly_def using assms by auto

lemma subpolyE:
  assumes "p \<sqsubseteq> q" and "t \<in> keys p"
  shows "lookup p t = lookup q t"
  using assms unfolding subpoly_def by auto

lemma subpoly_keys:
  assumes "p \<sqsubseteq> q"
  shows "keys p \<subseteq> keys q"
proof
  fix t
  assume "t \<in> keys p"
  hence "lookup p t \<noteq> 0" unfolding in_keys_iff .
  from assms \<open>t \<in> keys p\<close> have "lookup p t = lookup q t" by (rule subpolyE)
  with \<open>lookup p t \<noteq> 0\<close> show "t \<in> keys q" unfolding in_keys_iff by simp
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

lemma zero_subpoly: "0 \<sqsubseteq> p"
  by (rule subpolyI, simp)

lemma monomial_subpoly: "(monomial (lookup p t) t) \<sqsubseteq> p" (is "?q \<sqsubseteq> p")
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
  from keys_single[of t] \<open>s \<in> keys ?q\<close> have "s = t" by (smt empty_iff insert_iff) 
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

lemma except_subpoly: "except p S \<sqsubseteq> p"
proof (rule subpolyI)
  fix s
  assume "s \<in> keys (except p S)"
  hence "s \<notin> S" unfolding keys_except ..
  thus "lookup (except p S) s = lookup p s" by (rule lookup_except_eq_idI)
qed

end (* comm_powerprod *)

subsection \<open>Ideals and Linear Hulls\<close>

lemma poly_mapping_of_pp_in_pidealI:
  assumes "(f::('a::comm_powerprod, 'b::field) poly_mapping) \<in> pideal F" and "keys f = {t}"
  shows "poly_mapping_of_pp t \<in> pideal F"
proof -
  define c where "c \<equiv> lookup f t"
  from assms(2) have f_eq: "f = monomial c t" unfolding c_def
    by (metis (mono_tags, lifting) Diff_insert_absorb cancel_comm_monoid_add_class.add_cancel_right_right
        plus_except insert_absorb insert_not_empty keys_eq_empty_iff keys_except)
  from assms(2) have "c \<noteq> 0" by (simp add: c_def)
  hence "poly_mapping_of_pp t = monom_mult (1 / c) 0 f" by (simp add: f_eq monom_mult_monomial poly_mapping_of_pp_def)
  also from assms(1) have "... \<in> pideal F" by (rule pideal_closed_monom_mult)
  finally show ?thesis .
qed

lemma replace_pideal:
  assumes "q \<in> (pideal B)"
  shows "pideal (replace p q B) \<subseteq> pideal (B::('a::comm_powerprod, 'b::semiring_1) poly_mapping set)"
  unfolding replace_def
  by (rule pideal_insert_subset, rule pideal_mono, rule remove_subset, fact)
    
lemma remove_0_stable_pideal: "pideal (remove 0 B) = pideal B"
  unfolding remove_def by (fact pideal_minus_singleton_zero)

lemma in_pideal_listE:
  assumes "distinct bs" and "p \<in> (pideal (set bs))"
  obtains qs where "length qs = length bs" and "p = (\<Sum>(q, b)\<leftarrow>zip qs bs. q * b)"
proof -
  have "finite (set bs)" ..
  from this assms(2) obtain q where p: "p = (\<Sum>b\<in>set bs. (q b) * b)" by (rule in_pideal_finiteE)
  let ?qs = "map q bs"
  show ?thesis
  proof
    show "length ?qs = length bs" by simp
  next
    from assms(1) have *: "distinct (zip ?qs bs)" by (rule distinct_zipI2)
    have inj: "inj_on (\<lambda>x. (q x, x)) (set bs)" by (rule, simp)
    show "p = (\<Sum>(q, b)\<leftarrow>zip ?qs bs. q * b)"
      by (simp add: sum_list_distinct_conv_sum_set[OF *] set_zip_map1 p comm_monoid_add_class.sum.reindex[OF inj])
  qed
qed

lemma in_pideal_listI: "(\<Sum>(q, b)\<leftarrow>zip qs bs. q * b) \<in> pideal (set bs)"
proof (induct qs arbitrary: bs)
  case Nil
  show ?case by (simp add: zero_in_pideal)
next
  case step: (Cons q qs)
  show ?case
  proof (simp add: zip_Cons1 zero_in_pideal split: list.split, intro allI impI)
    fix a as
    have "(\<Sum>(x, y)\<leftarrow>zip qs as. x * y) \<in> pideal (insert a (set as))" (is "?x \<in> ?A")
      by (rule, fact step, rule pideal_mono, auto)
    show "q * a + ?x \<in> ?A" by (rule pideal_closed_plus, rule times_in_pideal, simp, fact)
  qed
qed

lemma replace_phull:
  fixes B::"('a::comm_powerprod, 'b::semiring_1) poly_mapping set" and p q
  assumes "q \<in> (phull B)"
  shows "phull (replace p q B) \<subseteq> phull B"
  unfolding replace_def
  by (rule phull_insert_subset, rule phull_mono, rule remove_subset, fact)
    
lemma remove_0_stable_phull: "phull (remove 0 B) = phull B"
  unfolding remove_def by (fact phull_minus_singleton_zero)

text \<open>In the following lemma, the distinctness-condition could be removed, but then the proof gets
  harder.\<close>
lemma in_phull_listE:
  assumes "distinct bs" and "p \<in> (phull (set bs))"
  obtains cs where "length cs = length bs" and "p = (\<Sum>(c, b)\<leftarrow>zip cs bs. monom_mult c 0 b)"
proof -
  have "finite (set bs)" ..
  from this assms(2) obtain c where p: "p = (\<Sum>b\<in>set bs. monom_mult (c b) 0 b)" by (rule in_phull_finiteE)
  let ?cs = "map c bs"
  show ?thesis
  proof
    show "length ?cs = length bs" by simp
  next
    from assms(1) have *: "distinct (zip ?cs bs)" by (rule distinct_zipI2)
    have inj: "inj_on (\<lambda>x. (c x, x)) (set bs)" by (rule, simp)
    show "p = (\<Sum>(q, b)\<leftarrow>zip ?cs bs. monom_mult q 0 b)"
      by (simp add: sum_list_distinct_conv_sum_set[OF *] set_zip_map1 p comm_monoid_add_class.sum.reindex[OF inj])
  qed
qed

lemma in_phull_listI: "(\<Sum>(c, b)\<leftarrow>zip cs bs. monom_mult c 0 b) \<in> phull (set bs)"
proof (induct cs arbitrary: bs)
  case Nil
  show ?case by (simp add: zero_in_phull)
next
  case step: (Cons c cs)
  show ?case
  proof (simp add: zip_Cons1 zero_in_phull split: list.split, intro allI impI)
    fix a and as::"('a, 'b) poly_mapping list"
    have "(\<Sum>(x, y)\<leftarrow>zip cs as. monom_mult x 0 y) \<in> phull (insert a (set as))" (is "?x \<in> ?A")
      by (rule, fact step, rule phull_mono, auto)
    show "monom_mult c 0 a + ?x \<in> ?A" by (rule phull_closed_plus, rule monom_mult_in_phull, simp, fact)
  qed
qed
    
subsection \<open>Bounded Support\<close>
  
definition has_bounded_keys :: "nat \<Rightarrow> ('a, 'b::zero) poly_mapping \<Rightarrow> bool" where
  "has_bounded_keys n p \<longleftrightarrow> card (keys p) \<le> n"

definition has_bounded_keys_set :: "nat \<Rightarrow> ('a, 'b::zero) poly_mapping set \<Rightarrow> bool" where
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
    
subsection \<open>Monomials and Binomials\<close>
  
definition is_monomial :: "('a, 'b::zero) poly_mapping \<Rightarrow> bool" where "is_monomial p \<longleftrightarrow> card (keys p) = 1"
  
definition is_binomial :: "('a, 'b::zero) poly_mapping \<Rightarrow> bool"
  where "is_binomial p \<longleftrightarrow> (card (keys p) = 1 \<or> card (keys p) = 2)"

definition is_proper_binomial :: "('a, 'b::zero) poly_mapping \<Rightarrow> bool"
  where "is_proper_binomial p \<longleftrightarrow> card (keys p) = 2"
    
definition binomial :: "'b::comm_monoid_add \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('a, 'b) poly_mapping"
  where "binomial c s d t = monomial c s + monomial d t"
    
definition is_monomial_set :: "('a, 'b::zero) poly_mapping set \<Rightarrow> bool"
  where "is_monomial_set A \<longleftrightarrow> (\<forall>p\<in>A. is_monomial p)"

definition is_binomial_set :: "('a, 'b::zero) poly_mapping set \<Rightarrow> bool"
  where "is_binomial_set A \<longleftrightarrow> (\<forall>p\<in>A. is_binomial p)"

text \<open>@{term is_pbd} stands for "is proper binomial data".\<close>
definition is_pbd :: "'b::zero \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_pbd c s d t \<longleftrightarrow> (c \<noteq> 0 \<and> d \<noteq> 0 \<and> s \<noteq> t)"
    
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

lemma monomial_is_monomial:
  assumes "c \<noteq> 0"
  shows "is_monomial (monomial c t)"
  using keys_single[of t c] assms unfolding is_monomial_def by simp
    
lemma poly_mapping_of_pp_is_monomial: "is_monomial ((poly_mapping_of_pp t)::('a::comm_powerprod, 'b::zero_neq_one) poly_mapping)"
  unfolding poly_mapping_of_pp_def by (rule monomial_is_monomial, simp)

lemma is_monomial_monomial:
  assumes "is_monomial p"
  obtains c t where "c \<noteq> 0" and "p = monomial c t"
proof -
  from assms have "card (keys p) = 1" unfolding is_monomial_def .
  then obtain t where sp: "keys p = {t}" by (rule card_1_singletonE)
  let ?c = "lookup p t"
  from sp have "?c \<noteq> 0" by fastforce
  show ?thesis
  proof
    show "p = monomial ?c t"
    proof (intro poly_mapping_keys_eqI)
      from sp show "keys p = keys (monomial ?c t)" using \<open>?c \<noteq> 0\<close> by simp
    next
      fix s
      assume "s \<in> keys p"
      with sp have "s = t" by simp
      show "lookup p s = lookup (monomial ?c t) s" unfolding \<open>s = t\<close> by simp
    qed
  qed fact
qed
  
lemma is_monomial_uminus: "is_monomial (-p) \<longleftrightarrow> is_monomial p"
  unfolding is_monomial_def keys_uminus ..
    
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
    
lemma monomial_not_0:
  assumes "is_monomial p"
  shows "p \<noteq> 0"
  using assms unfolding is_monomial_def by auto

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
  hence "u = s \<or> u = t" unfolding binomial_def lookup_add lookup_single PP_Poly_Mapping.when_def
    by (smt monoid_add_class.add.right_neutral) 
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
  fixes c::"'b::field" and s::"'a::comm_powerprod" and d a t u
  assumes "is_pbd c s d t" and "a \<noteq> 0"
  shows "is_pbd (a * c) (u + s) (a * d) (u + t)"
  using assms unfolding is_pbd_def by auto
    
lemma monom_mult_binomial:
  fixes c d a s t u
  shows "monom_mult a u (binomial c s d t) = binomial (a * c) (u + s) (a * d) (u + t)"
  unfolding binomial_def monom_mult_dist_right monom_mult_monomial ..
  
section \<open>Further Properties of Ordered Polynomials\<close>
  
context ordered_powerprod
begin

subsection \<open>Ideals and Linear Hulls\<close>

text \<open>The following lemma also holds in context @{locale comm_powerprod}, but then one needs the
  additional assumption that function @{const monom_mult} is injective in its second argument (the
  power-product), provided the other two arguments (coefficient, polynomial) are non-zero.\<close>
lemma in_pideal_in_phull:
  fixes B::"('a::comm_powerprod, 'b::semiring_1_no_zero_divisors) poly_mapping set"
    and A::"('a, 'b) poly_mapping set"
    and q::"('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping"
  assumes "\<And>b t. b \<in> B \<Longrightarrow> t \<in> keys (q b) \<Longrightarrow> monom_mult 1 t b \<in> A"
  shows "(\<Sum>b\<in>B. q b * b) \<in> phull A" (is "?p \<in> _")
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
      have "(THE t. a = monom_mult 1 t b) = t" sorry
      with * have "lookup (q b) t \<noteq> 0" by simp
      hence "t \<in> keys (q b)" by simp
      show "\<exists>b2\<in>B - {0}. \<exists>t. a = monom_mult 1 t b2 \<and> t \<in> keys (q b2)" by (rule, rule, rule, fact+)
    qed
  next
    show "finite ?A'" by (rule, simp add: True, simp)
  qed

  have "?p = (\<Sum>b\<in>?B. q b * b)"
  proof (cases "0 \<in> B")
    case True
    show ?thesis by (simp add: sum.remove[OF \<open>finite B\<close> True])
  next
    case False
    hence "?B = B" by simp
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>a\<in>?A. monom_mult (?c a) 0 a)"
  proof (simp only: monom_mult_sum sum.commute[of _ _ ?A], rule sum.cong, rule)
    fix b
    assume "b \<in> ?B"
    hence "b \<in> B" and "b \<noteq> 0" by auto
    have "q b * b = (\<Sum>t\<in>keys (q b). monom_mult (lookup (q b) t) t b)" by (rule times_sum_monomials)
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
          by (simp add: monom_mult_left0)
      qed (simp only: monom_mult_left0)
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
      thus "monom_mult (f a b) 0 a = 0" by (simp add: monom_mult_left0)
    qed (rule)
    finally show "q b * b = (\<Sum>a\<in>?A. monom_mult (f a b) 0 a)" .
  qed
  finally have *: "?p = (\<Sum>a\<in>?A. monom_mult (?c a) 0 a)" .

  have "?p \<in> phull ?A" unfolding * by (rule sum_in_phullI)
  thus ?thesis
  proof
    show "phull ?A \<subseteq> phull A" by (rule phull_mono, auto)
  qed
next                             
  case False
  thus ?thesis by (simp add: zero_in_phull)
qed

subsection \<open>Leading Power-Products and -Coefficients\<close>

lemma lp_le:
  assumes a: "\<And>s. t \<prec> s \<Longrightarrow> lookup p s = 0"
  shows "lp p \<preceq> t"
proof (cases "p = 0")
  case True
  thus ?thesis using zero_min[of t] by (simp add: lp_def)
next
  case False
  hence "keys p \<noteq> {}" using keys_eq_empty_iff[of p] by simp
  have "\<forall>s\<in>keys p. s \<preceq> t"
  proof
    fix s::"'a"
    assume "s \<in> keys p"
    hence "lookup p s \<noteq> 0" unfolding keys_def by simp
    hence "\<not> t \<prec> s" using a[of s] by auto
    thus "s \<preceq> t" by simp
  qed
  with lp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Max_le_iff[OF finite_keys[of p] \<open>keys p \<noteq> {}\<close>]
    show ?thesis by simp
qed
   
lemma lp_le_iff: "lp p \<preceq> t \<longleftrightarrow> (\<forall>s. t \<prec> s \<longrightarrow> lookup p s = 0)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro allI impI)
    fix s
    note \<open>lp p \<preceq> t\<close>
    also assume "t \<prec> s"
    finally have "lp p \<prec> s" .
    hence "\<not> s \<preceq> lp p" by simp
    with lp_max[of p s] show "lookup p s = 0" by blast
  qed
next
  assume ?R
  thus ?L using lp_le by auto
qed

lemma lp_plus_eqI:
  assumes "lp p \<prec> lp q"
  shows "lp (p + q) = lp q"
proof (cases "q = 0")
  case True
  with assms have "lp p \<prec> 0" by (simp add: lp_def)
  with zero_min[of "lp p"] show ?thesis by simp
next
  case False
  show ?thesis
  proof (intro lp_eqI)
    from lp_gr[of p "lp q" "lp p"] \<open>lp p \<prec> lp q\<close> have "lookup p (lp q) = 0" by blast
    with lookup_add[of p q "lp q"] lc_not_0[OF False] show "lookup (p + q) (lp q) \<noteq> 0"
      unfolding lc_def by simp
  next
    fix s
    assume "lookup (p + q) s \<noteq> 0"
    show "s \<preceq> lp q"
    proof (rule ccontr)
      assume "\<not> s \<preceq> lp q"
      hence qs: "lp q \<prec> s" by simp
      hence "lp p \<prec> s" using \<open>lp p \<prec> lp q\<close> by simp
      with lp_gr[of p s "lp p"] have "lookup p s = 0" by blast
      also from qs lp_gr[of q s "lp q"] have "lookup q s = 0" by blast
      ultimately show False using \<open>lookup (p + q) s \<noteq> 0\<close> lookup_add[of p q s] by auto
    qed
  qed
qed
    
lemma lp_plus_precE:
  assumes "lp p \<prec> lp (p + (q::('a, 'b::comm_monoid_add) poly_mapping))"
  shows "lp p \<prec> lp q"
proof (rule ccontr)
  assume "\<not> lp p \<prec> lp q"
  hence "lp p = lp q \<or> lp q \<prec> lp p" by auto
  thus False
  proof
    assume lp_eq: "lp p = lp q"
    have "lp (p + q) \<preceq> lp p"
    proof (rule lp_le)
      fix s
      assume "lp p \<prec> s"
      with lp_gr[of p s "lp p"] have "lookup p s = 0" by blast
      from \<open>lp p \<prec> s\<close> have "lp q \<prec> s" using lp_eq by simp
      with lp_gr[of q s "lp q"] have "lookup q s = 0" by blast
      with \<open>lookup p s = 0\<close> show "lookup (p + q) s = 0" using lookup_add[of p q s] by simp
    qed
    with assms show False by simp
  next
    assume "lp q \<prec> lp p"
    from lp_plus_eqI[OF this] assms show False by (simp add: add.commute)
  qed
qed
  
lemma lp_plus_precI:
  fixes p q :: "('a, 'b::ring) poly_mapping"
  assumes "p + q \<noteq> 0" and lp_eq: "lp q = lp p" and lc_eq: "lc q = - lc p"
  shows "lp (p + q) \<prec> lp p"
proof (rule ccontr)
  assume "\<not> lp (p + q) \<prec> lp p"
  hence "lp (p + q) = lp p \<or> lp p \<prec> lp (p + q)" by auto
  thus False
  proof
    assume "lp (p + q) = lp p"
    have "lookup (p + q) (lp p) = (lookup p (lp p)) + (lookup q (lp q))" unfolding lp_eq lookup_add ..
    also have "... = lc p + lc q" unfolding lc_def ..
    also have "... = 0" unfolding lc_eq by simp
    finally have "lookup (p + q) (lp p) = 0" .
    hence "lp (p + q) \<noteq> lp p" using lc_not_0[OF \<open>p + q \<noteq> 0\<close>] unfolding lc_def by auto
    with \<open>lp (p + q) = lp p\<close> show False by simp
  next
    assume "lp p \<prec> lp (p + q)"
    have "lp p \<prec> lp q" by (rule lp_plus_precE, fact+)
    hence "lp p \<noteq> lp q" by simp
    with lp_eq show False by simp
  qed
qed
    
lemma lp_max_keys:
  assumes "t \<in> keys p"
  shows "t \<preceq> lp p"
proof (rule lp_max)
  from assms show "lookup p t \<noteq> 0" by simp
qed

lemma lp_eqI_keys:
  assumes "t \<in> keys p" and a2: "\<And>s. s \<in> keys p \<Longrightarrow> s \<preceq> t"
  shows "lp p = t"
  by (rule lp_eqI, simp_all only: in_keys_iff[symmetric], fact+)
    
lemma lp_gr_keys:
  assumes "s \<in> keys p" and "t \<prec> s"
  shows "t \<prec> lp p"
proof (rule lp_gr)
  from assms(1) show "lookup p s \<noteq> 0" by simp
qed fact

lemma lp_uminus:
  fixes p
  assumes "p \<noteq> 0"
  shows "lp (-p) = lp p"
proof -
  from assms have "-p \<noteq> 0" by simp
  with assms show ?thesis unfolding lp_def keys_uminus by simp
qed

lemma lc_uminus:
  fixes p
  assumes "p \<noteq> 0"
  shows "lc (-p) = - lc p"
  unfolding lc_def lp_uminus[OF assms] lookup_uminus by simp
    
lemma lp_poly_mapping_of_pp:
  shows "lp ((poly_mapping_of_pp t)::('a, 'b::{zero_neq_one}) poly_mapping) = t"
  unfolding poly_mapping_of_pp_def by (rule lp_monomial, simp)
    
lemma lc_poly_mapping_of_pp:
  shows "lc ((poly_mapping_of_pp t)::('a, 'b::{zero_neq_one}) poly_mapping) = 1"
  unfolding poly_mapping_of_pp_def by (rule lc_monomial, simp)
  
definition lp_set :: "('a, 'b::zero) poly_mapping set \<Rightarrow> 'a set" where
  "lp_set F = lp ` (F - {0})"

definition lc_set :: "('a, 'b::zero) poly_mapping set \<Rightarrow> 'b set" where
  "lc_set F = lc ` (F - {0})"
  
lemma lp_setI:
  assumes "f \<in> F" and "f \<noteq> 0"
  shows "lp f \<in> lp_set F"
  unfolding lp_set_def using assms by simp

lemma lp_setE:
  assumes "t \<in> lp_set F"
  obtains f where "f \<in> F" and "f \<noteq> 0" and "lp f = t"
  using assms unfolding lp_set_def by auto
    
lemma lp_set_iff:
  shows "t \<in> lp_set F \<longleftrightarrow> (\<exists>f\<in>F. f \<noteq> 0 \<and> lp f = t)"
  unfolding lp_set_def by auto

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
  
subsection \<open>Trailing Power-Products and -Coefficients\<close>

definition tp::"('a, 'b::zero) poly_mapping \<Rightarrow> 'a" where
  "tp p \<equiv> (if p = 0 then 0 else ordered_powerprod_lin.Min (keys p))"

definition tc::"('a, 'b::zero) poly_mapping \<Rightarrow> 'b" where
  "tc p \<equiv> lookup p (tp p)"
  
lemma tp_alt:
  assumes "p \<noteq> 0"
  shows "tp p = ordered_powerprod_lin.Min (keys p)"
using assms unfolding tp_def by simp

lemma tp_min_keys:
  assumes "t \<in> keys p"
  shows "tp p \<preceq> t"
proof -
  from assms have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  from tp_alt[OF this] ordered_powerprod_lin.Min_le[OF finite_keys assms] show ?thesis by simp
qed

lemma tp_min:
  assumes "lookup p t \<noteq> 0"
  shows "tp p \<preceq> t"
proof -
  from assms have t_in: "t \<in> keys p" unfolding keys_def by simp
  thus ?thesis by (rule tp_min_keys)
qed
  
lemma tp_in_keys:
  assumes "p \<noteq> 0"
  shows "tp p \<in> keys p"
  unfolding tp_alt[OF assms]
  by (rule ordered_powerprod_lin.Min_in, fact finite_keys, simp add: assms)

lemma tp_eqI:
  assumes a1: "t \<in> keys p" and a2: "\<And>s. s \<in> keys p \<Longrightarrow> t \<preceq> s"
  shows "tp p = t"
proof -
  from a1 have "keys p \<noteq> {}" by auto
  hence "p \<noteq> 0" by simp
  from a1 have "tp p \<preceq> t" by (rule tp_min_keys)
  moreover have "t \<preceq> tp p" by (rule a2, rule tp_in_keys, fact \<open>p \<noteq> 0\<close>)
  ultimately show ?thesis by simp
qed

lemma tp_gr:
  assumes a: "\<And>s. s \<in> keys p \<Longrightarrow> t \<prec> s" and "p \<noteq> 0"
  shows "t \<prec> tp p"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" using keys_eq_empty_iff[of p] by simp
  show ?thesis by (rule a, rule tp_in_keys, fact \<open>p \<noteq> 0\<close>)
qed

lemma tp_less:
  assumes "s \<in> keys p" and "s \<prec> t"
  shows "tp p \<prec> t"
proof -
  from \<open>s \<in> keys p\<close> have "tp p \<preceq> s" by (rule tp_min_keys)
  also have "... \<prec> t" by fact
  finally show "tp p \<prec> t" .
qed
  
lemma tp_ge:
  assumes a: "\<And>s. s \<prec> t \<Longrightarrow> lookup p s = 0" and "p \<noteq> 0"
  shows "t \<preceq> tp p"
proof -
  from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" using keys_eq_empty_iff[of p] by simp
  have "\<forall>s\<in>keys p. t \<preceq> s"
  proof
    fix s::"'a"
    assume "s \<in> keys p"
    hence "lookup p s \<noteq> 0" unfolding keys_def by simp
    hence "\<not> s \<prec> t" using a[of s] by auto
    thus "t \<preceq> s" by simp
  qed
  with tp_alt[OF \<open>p \<noteq> 0\<close>] ordered_powerprod_lin.Min_ge_iff[OF finite_keys[of p] \<open>keys p \<noteq> {}\<close>]
    show ?thesis by simp
qed
  
lemma tp_ge_keys:
  assumes a: "\<And>s. s \<in> keys p \<Longrightarrow> t \<preceq> s" and "p \<noteq> 0"
  shows "t \<preceq> tp p"
  by (rule a, rule tp_in_keys, fact)
    
lemma tp_ge_iff: "t \<preceq> tp p \<longleftrightarrow> ((p \<noteq> 0 \<or> t = 0) \<and> (\<forall>s. s \<prec> t \<longrightarrow> lookup p s = 0))" (is "?L \<longleftrightarrow> (?A \<and> ?B)")
proof
  assume ?L
  show "?A \<and> ?B"
  proof (intro conjI allI impI)
    show "p \<noteq> 0 \<or> t = 0"
    proof (cases "p = 0")
      case True
      show ?thesis
      proof (rule disjI2)
        from \<open>?L\<close> True have "t \<preceq> 0" by (simp add: tp_def)
        with zero_min[of t] show "t = 0" by simp
      qed
    next
      case False
      thus ?thesis ..
    qed
  next
    fix s
    assume "s \<prec> t"
    also note \<open>t \<preceq> tp p\<close>
    finally have "s \<prec> tp p" .
    hence "\<not> tp p \<preceq> s" by simp
    with tp_min[of p s] show "lookup p s = 0" by blast
  qed
next
  assume "?A \<and> ?B"
  hence ?A and ?B by simp_all
  show ?L
  proof (cases "p = 0")
    case True
    with \<open>?A\<close> have "t = 0" by simp
    with True show ?thesis by (simp add: tp_def)
  next
    case False
    from \<open>?B\<close> show ?thesis using tp_ge[OF _ False] by auto
  qed
qed

lemma tc_not_0:
  assumes "p \<noteq> 0"
  shows "tc p \<noteq> 0"
  unfolding tc_def in_keys_iff[symmetric] using assms by (rule tp_in_keys)

lemma tp_monomial:
  assumes "c \<noteq> 0"
  shows "tp (monomial c t) = t"
proof (rule tp_eqI)
  from keys_of_monomial[OF assms, of t] show "t \<in> keys (monomial c t)" by simp
next
  fix s
  assume "s \<in> keys (monomial c t)"
  with keys_of_monomial[OF assms, of t] have "s = t" by simp
  thus "t \<preceq> s" by simp
qed

lemma tc_monomial:
  assumes "c \<noteq> 0"
  shows "tc (monomial c t) = c"
  unfolding tc_def tp_monomial[OF assms] by (simp add: lookup_single)


lemma lp_eq_tp_monomial:
  assumes "is_monomial p"
  shows "lp p = tp p"
proof -
  from assms obtain c t where "c \<noteq> 0" and p: "p = monomial c t" by (rule is_monomial_monomial)
  from \<open>c \<noteq> 0\<close> have "lp p = t" and "tp p = t" unfolding p by (rule lp_monomial, rule tp_monomial)
  thus ?thesis by simp
qed

lemma tp_monom_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "tp (monom_mult c t p) = t + tp p"
proof (intro tp_eqI, rule keys_monom_multI, rule tp_in_keys, fact, fact)
  fix s
  assume "s \<in> keys (monom_mult c t p)"
  then obtain x where "x \<in> keys p" and s: "s = t + x" by (rule keys_monom_multE)
  show "t + tp p \<preceq> s" unfolding s add.commute[of t] by (rule plus_monotone, rule tp_min_keys, fact)
qed

lemma tc_monom_mult:
  fixes c::"'b::semiring_no_zero_divisors"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows "tc (monom_mult c t p) = c * tc p"
  unfolding tc_def tp_monom_mult[OF assms] lookup_monom_mult ..
  
lemma tp_plus_eqI:
  fixes p q
  assumes "p \<noteq> 0" and "tp p \<prec> tp q"
  shows "tp (p + q) = tp p"
proof (intro tp_eqI)
  from tp_less[of "tp p" q "tp q"] \<open>tp p \<prec> tp q\<close> have "tp p \<notin> keys q" by blast
  with lookup_add[of p q "tp p"] tc_not_0[OF \<open>p \<noteq> 0\<close>] show "tp p \<in> keys (p + q)"
    unfolding in_keys_iff tc_def by simp
next
  fix s
  assume "s \<in> keys (p + q)"
  show "tp p \<preceq> s"
  proof (rule ccontr)
    assume "\<not> tp p \<preceq> s"
    hence sp: "s \<prec> tp p" by simp
    hence "s \<prec> tp q" using \<open>tp p \<prec> tp q\<close> by simp
    with tp_less[of s q "tp q"] have "s \<notin> keys q" by blast
    moreover from sp tp_less[of s p "tp p"] have "s \<notin> keys p" by blast
    ultimately show False using \<open>s \<in> keys (p + q)\<close> keys_add_subset[of p q] by auto
  qed
qed
    
lemma tp_plus_precE:
  fixes p q
  assumes "p + q \<noteq> 0" and tp: "tp (p + q) \<prec> tp p"
  shows "tp q \<prec> tp p"
proof (cases "p = 0")
  case True
  with tp show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "\<not> tp q \<prec> tp p"
    hence "tp p = tp q \<or> tp p \<prec> tp q" by auto
    thus False
    proof
      assume tp_eq: "tp p = tp q"
      have "tp p \<preceq> tp (p + q)"
      proof (rule tp_ge_keys)
        fix s
        assume "s \<in> keys (p + q)"
        hence "s \<in> keys p \<union> keys q"
        proof
          show "keys (p + q) \<subseteq> keys p \<union> keys q" by (fact keys_add_subset)
        qed
        thus "tp p \<preceq> s"
        proof
          assume "s \<in> keys p"
          thus ?thesis by (rule tp_min_keys)
        next
          assume "s \<in> keys q"
          thus ?thesis unfolding tp_eq by (rule tp_min_keys)
        qed
      qed (fact \<open>p + q \<noteq> 0\<close>)
      with tp show False by simp
    next
      assume "tp p \<prec> tp q"
      from tp_plus_eqI[OF False this] tp show False by (simp add: ac_simps)
    qed
  qed
qed
  
lemma tp_plus_precI:
  fixes p q :: "('a, 'b::ring) poly_mapping"
  assumes "p + q \<noteq> 0" and tp_eq: "tp q = tp p" and tc_eq: "tc q = - tc p"
  shows "tp p \<prec> tp (p + q)"
proof (rule ccontr)
  assume "\<not> tp p \<prec> tp (p + q)"
  hence "tp p = tp (p + q) \<or> tp (p + q) \<prec> tp p" by auto
  thus False
  proof
    assume "tp p = tp (p + q)"
    have "lookup (p + q) (tp p) = (lookup p (tp p)) + (lookup q (tp q))" unfolding tp_eq lookup_add ..
    also have "... = tc p + tc q" unfolding tc_def ..
    also have "... = 0" unfolding tc_eq by simp
    finally have "lookup (p + q) (tp p) = 0" .
    hence "tp (p + q) \<noteq> tp p" using tc_not_0[OF \<open>p + q \<noteq> 0\<close>] unfolding tc_def by auto
    with \<open>tp p = tp (p + q)\<close> show False by simp
  next
    assume "tp (p + q) \<prec> tp p"
    have "tp q \<prec> tp p" by (rule tp_plus_precE, fact+)
    hence "tp q \<noteq> tp p" by simp
    with tp_eq show False by simp
  qed
qed

lemma tp_uminus:
  fixes p
  assumes "p \<noteq> 0"
  shows "tp (-p) = tp p"
proof -
  from assms have "-p \<noteq> 0" by simp
  with assms show ?thesis unfolding tp_def keys_uminus by simp
qed

lemma tc_uminus:
  fixes p
  assumes "p \<noteq> 0"
  shows "tc (-p) = - tc p"
  unfolding tc_def tp_uminus[OF assms] lookup_uminus by simp
    
lemma tp_poly_mapping_of_pp: "tp ((poly_mapping_of_pp t)::('a, 'b::{zero_neq_one}) poly_mapping) = t"
  unfolding poly_mapping_of_pp_def by (rule tp_monomial, simp)
    
lemma tc_poly_mapping_of_pp: "tc ((poly_mapping_of_pp t)::('a, 'b::{zero_neq_one}) poly_mapping) = 1"
  unfolding poly_mapping_of_pp_def by (rule tc_monomial, simp)

lemma lp_geq_tp: "tp p \<preceq> lp p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True lp_def tp_def by simp
next
  case False
  show ?thesis by (rule lp_max_keys, rule tp_in_keys, fact False)
qed

lemma lp_gr_tp_iff: "(tp p \<prec> lp p) \<longleftrightarrow> (\<not> has_bounded_keys 1 p)"
  unfolding not_has_bounded_keys
proof
  assume "tp p \<prec> lp p"
  hence "tp p \<noteq> lp p" by simp
  show "1 < card (keys p)"
  proof (rule ccontr)
    assume "\<not> 1 < card (keys p)"
    hence "card (keys p) = 0 \<or> card (keys p) = 1" by linarith
    hence "lp p = tp p"
    proof
      assume "card (keys p) = 0"
      hence "keys p = {}" using finite_keys[of p] by simp
      hence "p = 0" using keys_eq_empty_iff[of p] by simp
      show ?thesis unfolding \<open>p = 0\<close> lp_def tp_def by simp
    next
      assume "card (keys p) = 1"
      hence "is_monomial p" unfolding is_monomial_def .
      thus "lp p = tp p" by (rule lp_eq_tp_monomial)
    qed
    with \<open>tp p \<noteq> lp p\<close> show False by simp
  qed
next
  assume "1 < card (keys p)"
  hence "2 \<le> card (keys p)" by simp
  then obtain A where "card A = 2" and sp: "A \<subseteq> keys p" by (rule card_geq_ex_subset)
  from \<open>card A = 2\<close> obtain s t where "s \<noteq> t" and A: "A = {s, t}" by (rule card_2_E)
  from sp have "s \<in> keys p" and "t \<in> keys p" unfolding A by simp_all
  from \<open>s \<noteq> t\<close> have "s \<prec> t \<or> t \<prec> s" by auto
  thus "tp p \<prec> lp p"
  proof
    assume "s \<prec> t"
    also from \<open>t \<in> keys p\<close> have "... \<preceq> lp p" by (rule lp_max_keys)
    finally have "s \<prec> lp p" .
    with \<open>s \<in> keys p\<close> show ?thesis by (rule tp_less)
  next
    assume "t \<prec> s"
    also from \<open>s \<in> keys p\<close> have "... \<preceq> lp p" by (rule lp_max_keys)
    finally have "t \<prec> lp p" .
    with \<open>t \<in> keys p\<close> show ?thesis by (rule tp_less)
  qed
qed

lemma lp_eq_tp_iff: "lp p = tp p \<longleftrightarrow> has_bounded_keys 1 p" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<longleftrightarrow> (tp p \<preceq> lp p \<and> \<not> tp p \<prec> lp p)" by auto
  also from lp_geq_tp[of p] have "... \<longleftrightarrow> \<not> tp p \<prec> lp p" by simp
  finally show ?thesis by (simp add: lp_gr_tp_iff)
qed
  
subsection \<open>@{term lower}, @{term higher}, @{term tail}\<close>

lemma lp_higher:
  assumes "t \<prec> lp p"
  shows "lp (higher p t) = lp p"
proof (rule lp_eqI_keys, simp_all add: keys_higher, rule conjI, rule lp_in_keys, rule)
  assume "p = 0"
  hence "lp p = 0" by (simp add: lp_def)
  with zero_min[of t] assms show False by simp
next
  fix s
  assume "s \<in> keys p \<and> t \<prec> s"
  hence "s \<in> keys p" ..
  thus "s \<preceq> lp p" by (rule lp_max_keys)
qed fact

lemma lc_higher:
  assumes "t \<prec> lp p"
  shows "lc (higher p t) = lc p"
  by (simp add: lc_def lp_higher assms lookup_higher)

lemma higher_0_iff: "higher p t = 0 \<longleftrightarrow> lp p \<preceq> t"
  by (simp add: higher_eq_zero_iff lp_le_iff)

lemma higher_id_iff: "higher p t = p \<longleftrightarrow> (p = 0 \<or> t \<prec> tp p)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (cases "p = 0")
    case True
    thus ?thesis ..
  next
    case False
    show ?thesis
    proof (rule disjI2, rule tp_gr)
      fix s
      assume "s \<in> keys p"
      hence "lookup p s \<noteq> 0" by simp
      from \<open>?L\<close> have "lookup (higher p t) s = lookup p s" by simp
      hence "lookup p s = (if t \<prec> s then lookup p s else 0)" by (simp only: lookup_higher)
      hence "\<not> t \<prec> s \<Longrightarrow> lookup p s = 0" by simp
      with \<open>lookup p s \<noteq> 0\<close> show "t \<prec> s" by auto
    qed fact
  qed
next
  assume ?R
  show ?L
  proof (cases "p = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with \<open>?R\<close> have "t \<prec> tp p" by simp
    show ?thesis
    proof (rule poly_mapping_eqI, simp add: lookup_higher, intro impI)
      fix s
      assume "\<not> t \<prec> s"
      hence "s \<preceq> t" by simp
      from this \<open>t \<prec> tp p\<close> have "s \<prec> tp p" by simp
      hence "\<not> tp p \<preceq> s" by simp
      with tp_min[of p s] show "lookup p s = 0" by blast
    qed
  qed
qed

lemma tp_lower:
  assumes "tp p \<prec> t"
  shows "tp (lower p t) = tp p"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof (rule tp_eqI, simp_all add: keys_lower, rule, rule tp_in_keys)
    fix s
    assume "s \<in> keys p \<and> s \<prec> t"
    hence "s \<in> keys p" ..
    thus "tp p \<preceq> s" by (rule tp_min_keys)
  qed fact+
qed

lemma tc_lower:
  assumes "tp p \<prec> t"
  shows "tc (lower p t) = tc p"
  by (simp add: tc_def tp_lower assms lookup_lower)

lemma lp_lower: "lp (lower p t) \<preceq> lp p"
proof (cases "lower p t = 0")
  case True
  thus ?thesis by (simp add: lp_def zero_min)
next
  case False
  show ?thesis
  proof (rule lp_le, simp add: lookup_lower, rule impI, rule ccontr)
    fix s
    assume "lookup p s \<noteq> 0"
    hence "s \<preceq> lp p" by (rule lp_max)
    moreover assume "lp p \<prec> s"
    ultimately show False by simp
  qed
qed

lemma lp_lower_eq_iff: "lp (lower p t) = lp p \<longleftrightarrow> (lp p = 0 \<or> lp p \<prec> t)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (rule ccontr, simp, elim conjE)
    assume "lp p \<noteq> 0"
    hence "0 \<prec> lp p"
      using zero_min ordered_powerprod_axioms ordered_powerprod_lin.dual_order.not_eq_order_implies_strict
      by blast
    assume "\<not> lp p \<prec> t"
    hence "t \<preceq> lp p" by simp
    have "lp (lower p t) \<prec> lp p"
    proof (cases "lower p t = 0")
      case True
      thus ?thesis using \<open>0 \<prec> lp p\<close> by (simp add: lp_def)
    next
      case False
      show ?thesis
      proof (rule lp_less)
        fix s
        assume "lp p \<preceq> s"
        with \<open>t \<preceq> lp p\<close> have "\<not> s \<prec> t" by simp
        thus "lookup (lower p t) s = 0" by (simp add: lookup_lower)
      qed fact
    qed
    with \<open>?L\<close> show False by simp
  qed
next
  assume ?R
  show ?L
  proof (cases "lp p = 0")
    case True
    hence "lp p \<preceq> lp (lower p t)" by (simp add: zero_min)
    with lp_lower[of p t] show ?thesis by simp
  next
    case False
    with \<open>?R\<close> have "lp p \<prec> t" by simp
    show ?thesis
    proof (rule lp_eqI_keys, simp_all add: keys_lower, rule conjI, rule lp_in_keys, rule)
      assume "p = 0"
      hence "lp p = 0" by (simp add: lp_def)
      with False show False ..
    next
      fix s
      assume "s \<in> keys p \<and> s \<prec> t"
      hence "s \<in> keys p" ..
      thus "s \<preceq> lp p" by (rule lp_max_keys)
    qed fact
  qed
qed

lemma tp_higher:
  assumes "t \<prec> lp p"
  shows "tp p \<preceq> tp (higher p t)"
proof (rule tp_ge_keys, simp add: keys_higher)
  fix s
  assume "s \<in> keys p \<and> t \<prec> s"
  hence "s \<in> keys p" ..
  thus "tp p \<preceq> s" by (rule tp_min_keys)
next
  show "higher p t \<noteq> 0"
  proof (simp add: higher_eq_zero_iff, intro exI conjI)
    have "p \<noteq> 0"
    proof
      assume "p = 0"
      hence "lp p \<preceq> t" by (simp add: lp_def zero_min)
      with assms show False by simp
    qed
    thus "lp p \<in> keys p" by (rule lp_in_keys)
  qed fact
qed

lemma tp_higher_eq_iff: "tp (higher p t) = tp p \<longleftrightarrow> ((lp p \<preceq> t \<and> tp p = 0) \<or> t \<prec> tp p)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (rule ccontr, simp, elim conjE)
    assume a: "lp p \<preceq> t \<longrightarrow> tp p \<noteq> 0"
    assume "\<not> t \<prec> tp p"
    hence "tp p \<preceq> t" by simp
    have "tp p \<prec> tp (higher p t)"
    proof (cases "higher p t = 0")
      case True
      with \<open>?L\<close> have "tp p = 0" by (simp add: tp_def)
      with a have "t \<prec> lp p" by auto
      have "lp p \<noteq> 0"
      proof
        assume "lp p = 0"
        with \<open>t \<prec> lp p\<close> show False using zero_min[of t] by auto
      qed
      hence "p \<noteq> 0" by (auto simp add: lp_def)
      from \<open>t \<prec> lp p\<close> have "higher p t \<noteq> 0" by (simp add: higher_0_iff)
      from this True show ?thesis ..
    next
      case False
      show ?thesis
      proof (rule tp_gr)
        fix s
        assume "s \<in> keys (higher p t)"
        hence "t \<prec> s" by (simp add: keys_higher)
        with \<open>tp p \<preceq> t\<close> show "tp p \<prec> s" by simp
      qed fact
    qed
    with \<open>?L\<close> show False by simp
  qed
next
  assume ?R
  show ?L
  proof (cases "lp p \<preceq> t \<and> tp p = 0")
    case True
    hence "lp p \<preceq> t" and "tp p = 0" by simp_all
    from \<open>lp p \<preceq> t\<close> have "higher p t = 0" by (simp add: higher_0_iff)
    with \<open>tp p = 0\<close> show ?thesis by (simp add: tp_def)
  next
    case False
    with \<open>?R\<close> have "t \<prec> tp p" by simp
    show ?thesis
    proof (rule tp_eqI, simp_all add: keys_higher, rule conjI, rule tp_in_keys, rule)
      assume "p = 0"
      hence "tp p = 0" by (simp add: tp_def)
      with \<open>t \<prec> tp p\<close> zero_min[of t] show False by simp
    next
      fix s
      assume "s \<in> keys p \<and> t \<prec> s"
      hence "s \<in> keys p" ..
      thus "tp p \<preceq> s" by (rule tp_min_keys)
    qed fact
  qed
qed

lemma in_keys_monom_mult_leq:
  assumes "s \<in> keys (monom_mult c t p)"
  shows "s \<preceq> t + lp p"
proof -
  from keys_monom_mult_subset assms have "s \<in> (op + t) ` (keys p)" ..
  then obtain u where "u \<in> keys p" and "s = t + u" ..
  from \<open>u \<in> keys p\<close> have "u \<preceq> lp p" by (rule lp_max_keys)
  thus "s \<preceq> t + lp p" unfolding \<open>s = t + u\<close> by (metis add.commute plus_monotone)
qed

lemma in_keys_monom_mult_geq:
  assumes "s \<in> keys (monom_mult c t p)"
  shows "t + tp p \<preceq> s"
proof -
  from keys_monom_mult_subset assms have "s \<in> (op + t) ` (keys p)" ..
  then obtain u where "u \<in> keys p" and "s = t + u" ..
  from \<open>u \<in> keys p\<close> have "tp p \<preceq> u" by (rule tp_min_keys)
  thus "t + tp p \<preceq> s" unfolding \<open>s = t + u\<close> by (metis add.commute plus_monotone)
qed

lemma lower_0_iff:
  shows "lower p t = 0 \<longleftrightarrow> (p = 0 \<or> t \<preceq> tp p)"
  by (auto simp add: lower_eq_zero_iff tp_ge_iff)

lemma lower_id_iff: "lower p t = p \<longleftrightarrow> (p = 0 \<or> lp p \<prec> t)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (cases "p = 0")
    case True
    thus ?thesis ..
  next
    case False
    show ?thesis
    proof (rule disjI2, rule lp_less)
      fix s
      assume "t \<preceq> s"
      from \<open>?L\<close> have "lookup (lower p t) s = lookup p s" by simp
      hence "lookup p s = (if s \<prec> t then lookup p s else 0)" by (simp only: lookup_lower)
      hence "t \<preceq> s \<Longrightarrow> lookup p s = 0" by (meson ordered_powerprod_lin.leD)
      with \<open>t \<preceq> s\<close> show "lookup p s = 0" by simp
    qed fact
  qed
next
  assume ?R
  show ?L
  proof (cases "p = 0", simp)
    case False
    with \<open>?R\<close> have "lp p \<prec> t" by simp
    show ?thesis
    proof (rule poly_mapping_eqI, simp add: lookup_lower, intro impI)
      fix s
      assume "\<not> s \<prec> t"
      hence "t \<preceq> s" by simp
      with \<open>lp p \<prec> t\<close> have "lp p \<prec> s" by simp
      hence "\<not> s \<preceq> lp p" by simp
      with lp_max[of p s] show "lookup p s = 0" by blast
    qed
  qed
qed
    
lemma lower_higher_commute: "higher (lower p s) t = lower (higher p t) s"
  by (rule poly_mapping_eqI, simp add: lookup_higher lookup_lower)

lemma lp_lower_higher:
  assumes "t \<prec> lp (lower p s)"
  shows "lp (lower (higher p t) s) = lp (lower p s)"
  by (simp add: lower_higher_commute[symmetric] lp_higher[OF assms])

lemma lc_lower_higher:
  assumes "t \<prec> lp (lower p s)"
  shows "lc (lower (higher p t) s) = lc (lower p s)"
  using assms by (simp add: lc_def lp_lower_higher lookup_lower lookup_higher)

lemma lp_tail_max:
  assumes "tail p \<noteq> 0" and "s \<in> keys p" and "s \<prec> lp p"
  shows "s \<preceq> lp (tail p)"
proof (rule lp_max_keys, simp add: keys_tail assms(2))
  from assms(3) show "s \<noteq> lp p" by auto
qed

lemma tp_tail:
  assumes "tail p \<noteq> 0"
  shows "tp (tail p) = tp p"
proof (rule tp_eqI, simp_all add: keys_tail)
  from assms have "p \<noteq> 0" using tail_zero by auto
  show "tp p \<in> keys p \<and> tp p \<noteq> lp p"
  proof (rule conjI, rule tp_in_keys, fact)
    have "tp p \<prec> lp p"
      by (metis assms lower_0_iff tail_def ordered_powerprod_lin.le_less_linear)
    thus "tp p \<noteq> lp p" by simp
  qed
next
  fix s
  assume "s \<in> keys p \<and> s \<noteq> lp p"
  hence "s \<in> keys p" ..
  thus "tp p \<preceq> s" by (rule tp_min_keys)
qed

lemma tc_tail:
  assumes "tail p \<noteq> 0"
  shows "tc (tail p) = tc p"
proof (simp add: tc_def tp_tail[OF assms] lookup_tail_2, rule)
  assume "tp p = lp p"
  moreover have "tp p \<prec> lp p"
    by (metis assms lower_0_iff tail_def ordered_powerprod_lin.le_less_linear)
  ultimately show "lookup p (lp p) = 0" by simp
qed

lemma tp_tail_min:
  assumes "s \<in> keys p"
  shows "tp (tail p) \<preceq> s"
proof (cases "tail p = 0")
  case True
  hence "tp (tail p) = 0" by (simp add: tp_def)
  thus ?thesis by (simp add: zero_min)
next
  case False
  from assms show ?thesis by (simp add: tp_tail[OF False], rule tp_min_keys)
qed
  
lemma tail_0D:
  assumes "tail p = 0"
  shows "has_bounded_keys 1 p"
proof -
  from assms have "keys (tail p) = {}" by simp
  hence "keys p \<subseteq> {lp p}" by (simp add: keys_tail)
  thus ?thesis unfolding has_bounded_keys_def
    by (metis One_nat_def card.insert card_empty finite.emptyI insert_absorb order_class.le_less subset_singleton_iff zero_le_one)
qed

lemma tail_eq_0_iff_has_bounded_keys_1: "(tail p = 0) \<longleftrightarrow> has_bounded_keys 1 p" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  hence "(\<forall>s. s \<prec> lp p \<longrightarrow> lookup p s = 0)" by (simp add: tail_def lower_eq_zero_iff)
  hence "\<And>s. s \<in> keys p \<Longrightarrow> lp p \<preceq> s" unfolding in_keys_iff using ordered_powerprod_lin.leI by auto
  hence a: "\<And>s. s \<in> keys p \<Longrightarrow> s = lp p" using lp_max_keys by force
  show ?R unfolding has_bounded_keys_def
  proof (rule ccontr)
    assume "\<not> card (keys p) \<le> 1"
    hence "card (keys p) \<ge> 2" by simp
    then obtain A where "card A = 2" and "A \<subseteq> keys p" by (rule card_geq_ex_subset) 
    from \<open>card A = 2\<close> obtain s t where "s \<noteq> t" and A_eq: "A = {s, t}" by (rule card_2_E)
    from \<open>A \<subseteq> keys p\<close> have "s \<in> keys p" by (rule in_mono[rule_format], simp add: A_eq)
    hence "s = lp p" by (rule a)
    from \<open>A \<subseteq> keys p\<close> have "t \<in> keys p" by (rule in_mono[rule_format], simp add: A_eq)
    hence "t = lp p" by (rule a)
    with \<open>s \<noteq> t\<close> \<open>s = lp p\<close> show False by simp
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

lemma tail_monom_mult:
  "tail (monom_mult c t p) = monom_mult (c::'b::semiring_no_zero_divisors) t (tail p)"
proof (cases "p = 0")
  case True
  hence "tail p = 0" and "monom_mult c t p = 0" by (simp_all add: monom_mult_right0)
  thus ?thesis by (simp add: monom_mult_right0)
next
  case False
  show ?thesis
  proof (cases "c = 0")
    case True
    hence "monom_mult c t p = 0" and "monom_mult c t (tail p) = 0" by (simp_all add: monom_mult_left0)
    thus ?thesis by simp
  next
    case False
    let ?a = "monom_mult c t p"
    let ?b = "monom_mult c t (tail p)"
    from \<open>p \<noteq> 0\<close> False have "?a \<noteq> 0" by (simp add: monom_mult_0_iff)
    from False \<open>p \<noteq> 0\<close> have lp_a: "lp ?a = t + lp p" by (rule lp_mult)
    show ?thesis
    proof (rule poly_mapping_eqI, simp add: lookup_tail lp_a, intro conjI impI)
      fix s
      assume "s \<prec> t + lp p"
      show "lookup (monom_mult c t p) s = lookup (monom_mult c t (tail p)) s"
      proof (cases "t adds s")
        case True
        then obtain u where "s = t + u" by (rule addsE)
        from \<open>s \<prec> t + lp p\<close> have "u \<prec> lp p" unfolding \<open>s = t + u\<close> by (rule ord_strict_canc_left) 
        hence "lookup p u = lookup (tail p) u" by (simp add: lookup_tail)
        thus ?thesis by (simp add: \<open>s = t + u\<close> lookup_monom_mult)
      next
        case False
        hence "lookup ?a s = 0"
          by (simp add: monom_mult.rep_eq)
        moreover have "lookup ?b s = 0"
          proof (rule ccontr, simp only: in_keys_iff[symmetric] keys_monom_mult[OF \<open>c \<noteq> 0\<close>])
          assume "s \<in> op + t ` keys (tail p)"
          then obtain u where "s = t + u" by auto
          hence "t adds s" by simp
          with False show False ..
        qed
        ultimately show ?thesis by simp
      qed
    next
      fix s
      assume "\<not> s \<prec> t + lp p"
      hence "t + lp p \<preceq> s" by simp
      show "lookup (monom_mult c t (tail p)) s = 0"
      proof (rule ccontr, simp only: in_keys_iff[symmetric] keys_monom_mult[OF False])
        assume "s \<in> op + t ` keys (tail p)"
        then obtain u where "u \<in> keys (tail p)" and "s = t + u" by auto
        from \<open>t + lp p \<preceq> s\<close> have "lp p \<preceq> u" unfolding \<open>s = t + u\<close> by (rule ord_canc_left)
        from \<open>u \<in> keys (tail p)\<close> have "u \<in> keys p" and "u \<noteq> lp p" by (simp_all add: keys_tail)
        from \<open>u \<in> keys p\<close> have "u \<preceq> lp p" by (rule lp_max_keys)
        with \<open>lp p \<preceq> u\<close> have "u = lp p " by simp
        with \<open>u \<noteq> lp p\<close> show False ..
      qed
    qed
  qed
qed
  
text \<open>The following lemma is the analogue of @{thm leading_monomial_tail}.\<close>
lemma trailing_monomial_higher:
  assumes "p \<noteq> 0"
  shows "p = (higher p (tp p)) + monomial (tc p) (tp p)"
proof (rule poly_mapping_eqI, simp only: lookup_add)
  fix t
  show "lookup p t = lookup (higher p (tp p)) t + lookup (monomial (tc p) (tp p)) t"
  proof (cases "tp p \<preceq> t")
    case True
    show ?thesis
    proof (cases "t = tp p")
      assume "t = tp p"
      hence "\<not> tp p \<prec> t" by simp
      hence "lookup (higher p (tp p)) t = 0" by (simp add: lookup_higher)
      moreover from \<open>t = tp p\<close> have "lookup (monomial (tc p) (tp p)) t = tc p" by (simp add: lookup_single)
      moreover from \<open>t = tp p\<close> have "lookup p t = tc p" by (simp add: tc_def)
      ultimately show ?thesis by simp
    next
      assume "t \<noteq> tp p"
      from this True have "tp p \<prec> t" by simp
      hence "lookup (higher p (tp p)) t = lookup p t" by (simp add: lookup_higher)
      moreover from \<open>t \<noteq> tp p\<close> have "lookup (monomial (tc p) (tp p)) t = 0" by (simp add: lookup_single)
      ultimately show ?thesis by simp
    qed
  next
    case False
    hence "t \<prec> tp p" by simp
    hence "tp p \<noteq> t" by simp
    from False have "\<not> tp p \<prec> t" by simp
    have "lookup p t = 0"
    proof (rule ccontr)
      assume "lookup p t \<noteq> 0"
      from tp_min[OF this] False show False by simp
    qed
    moreover from \<open>tp p \<noteq> t\<close> have "lookup (monomial (tc p) (tp p)) t = 0" by (simp add: lookup_single)
    moreover from \<open>\<not> tp p \<prec> t\<close> have "lookup (higher p (tp p)) t = 0" by (simp add: lookup_higher)
    ultimately show ?thesis by simp
  qed
qed

lemma keys_plus_eq_lp_tp_D:
  assumes "keys (p + q) = {lp p, tp q}" and "lp q \<prec> lp p" and "tp q \<prec> tp (p::('a, 'b::comm_monoid_add) poly_mapping)"
  shows "tail p + higher q (tp q) = 0"
proof -
  note assms(3)
  also have "... \<preceq> lp p" by (rule lp_geq_tp)
  finally have "tp q \<prec> lp p" .
  hence "lp p \<noteq> tp q" by simp
  have "q \<noteq> 0"
  proof
    assume "q = 0"
    hence "tp q = 0" by (simp add: tp_def)
    with \<open>q = 0\<close> assms(1) have "keys p = {lp p, 0}" by simp
    hence "0 \<in> keys p" by simp
    hence "tp p \<preceq> tp q" unfolding \<open>tp q = 0\<close> by (rule tp_min_keys)
    with assms(3) show False by simp
  qed
  hence "tc q \<noteq> 0" by (rule tc_not_0)
  have "p = monomial (lc p) (lp p) + tail p" by (rule leading_monomial_tail)
  moreover from \<open>q \<noteq> 0\<close> have "q = higher q (tp q) + monomial (tc q) (tp q)" by (rule trailing_monomial_higher)
  ultimately have pq: "p + q = (monomial (lc p) (lp p) + monomial (tc q) (tp q)) + (tail p + higher q (tp q))"
    (is "_ = (?m1 + ?m2) + ?b") by (simp add: algebra_simps)
  have keys_m1: "keys ?m1 = {lp p}"
  proof (rule keys_of_monomial, rule lc_not_0, rule)
    assume "p = 0"
    with assms(2) have "lp q \<prec> 0" by (simp add: lp_def)
    with zero_min[of "lp q"] show False by simp
  qed
  moreover from \<open>tc q \<noteq> 0\<close> have keys_m2: "keys ?m2 = {tp q}" by (rule keys_of_monomial)
  ultimately have keys_m1_m2: "keys (?m1 + ?m2) = {lp p, tp q}"
    using \<open>lp p \<noteq> tp q\<close> keys_plus_eqI[of ?m1 ?m2] by auto
  show ?thesis
  proof (rule ccontr)
    assume "?b \<noteq> 0"
    hence "keys ?b \<noteq> {}" by simp
    then obtain t where "t \<in> keys ?b" by blast
    hence t_in: "t \<in> keys (tail p) \<union> keys (higher q (tp q))"
      using keys_add_subset[of "tail p" "higher q (tp q)"] by blast
    hence "t \<noteq> lp p"
    proof (rule, simp add: keys_tail, simp add: keys_higher, elim conjE)
      assume "t \<in> keys q"
      hence "t \<preceq> lp q" by (rule lp_max_keys)
      from this assms(2) show ?thesis by simp
    qed
    moreover from t_in have "t \<noteq> tp q"
    proof (rule, simp add: keys_tail, elim conjE)
      assume "t \<in> keys p"
      hence "tp p \<preceq> t" by (rule tp_min_keys)
      with assms(3) show ?thesis by simp
    next
      assume "t \<in> keys (higher q (tp q))"
      thus ?thesis by (auto simp only: keys_higher)
    qed
    ultimately have "t \<notin> keys (?m1 + ?m2)" by (simp add: keys_m1_m2)
    moreover from in_keys_plusI2[OF \<open>t \<in> keys ?b\<close> this] have "t \<in> keys (?m1 + ?m2)"
      by (simp only: keys_m1_m2 pq[symmetric] assms(1))
    ultimately show False ..
  qed
qed

subsection \<open>Monomials and Binomials\<close>

lemma lp_gr_tp_binomial:
  assumes "is_proper_binomial p"
  shows "tp p \<prec> lp p"
  using assms by (simp only: lp_gr_tp_iff is_proper_binomial_def not_has_bounded_keys)

lemma keys_monomial:
  assumes "is_monomial p"
  shows "keys p = {lp p}"
  using assms by (metis is_monomial_monomial lp_monomial keys_of_monomial)

lemma keys_proper_binomial:
  assumes "is_proper_binomial p"
  shows "keys p = {lp p, tp p}"
proof -
  from assms have "card (keys p) = 2" and "p \<noteq> 0" and "tp p \<prec> lp p"
    by (simp only: is_proper_binomial_def, rule proper_binomial_not_0, rule lp_gr_tp_binomial)
  from \<open>tp p \<prec> lp p\<close> have "lp p \<noteq> tp p" by simp
  from \<open>card (keys p) = 2\<close> obtain s t where keys_p: "keys p = {s, t}" and "s \<noteq> t" by (rule card_2_E)
  with lp_in_keys[OF \<open>p \<noteq> 0\<close>] tp_in_keys[OF \<open>p \<noteq> 0\<close>] \<open>lp p \<noteq> tp p\<close> show ?thesis by auto
qed

corollary keys_binomial:
  assumes "is_binomial p"
  shows "keys p = {lp p, tp p}"
proof -
  from assms have "is_monomial p \<or> is_proper_binomial p" by (simp only: is_binomial_alt)
  thus ?thesis
  proof
    assume "is_monomial p"
    hence "lp p = tp p" and "keys p = {lp p}" by (rule lp_eq_tp_monomial, rule keys_monomial)
    thus ?thesis by simp
  next
    assume "is_proper_binomial p"
    thus ?thesis by (rule keys_proper_binomial)
  qed
qed

lemma monomial_eq_itself:
  assumes "is_monomial p"
  shows "monomial (lc p) (lp p) = p"
proof -
  from assms have "p \<noteq> 0" by (rule monomial_not_0)
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  hence keys1: "keys (monomial (lc p) (lp p)) = {lp p}" by (rule keys_of_monomial)
  show ?thesis
    by (rule poly_mapping_keys_eqI, simp only: keys_monomial[OF assms] keys1,
        simp only: keys1 lookup_single PP_Poly_Mapping.when_def, auto simp add: lc_def)
qed

lemma binomial_eq_itself:
  assumes "is_proper_binomial p"
  shows "binomial (lc p) (lp p) (tc p) (tp p) = p"
proof -
  from assms have "p \<noteq> 0" by (rule proper_binomial_not_0)
  hence "lc p \<noteq> 0" and "tc p \<noteq> 0" by (rule lc_not_0, rule tc_not_0)
  from assms have "tp p \<prec> lp p" by (rule lp_gr_tp_binomial)
  hence "tp p \<noteq> lp p" by simp
  with \<open>lc p \<noteq> 0\<close> \<open>tc p \<noteq> 0\<close> have pbd: "is_pbd (lc p) (lp p) (tc p) (tp p)" by (simp add: is_pbd_def)
  hence keys1: "keys (binomial (lc p) (lp p) (tc p) (tp p)) = {lp p, tp p}" by (rule keys_binomial_pbd)
  show ?thesis
    by (rule poly_mapping_keys_eqI, simp only: keys_proper_binomial[OF assms] keys1, simp add: keys1 lookup_binomial,
        elim disjE, simp add: lookup_binomial[OF pbd] lc_def[symmetric],
        simp add: lookup_binomial[OF pbd] \<open>tp p \<noteq> lp p\<close> tc_def[symmetric])
qed

text \<open>@{term is_obd} stands for "is ordered binomial data".\<close>
definition is_obd :: "'b::zero \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_obd c s d t \<longleftrightarrow> (c \<noteq> 0 \<and> d \<noteq> 0 \<and> t \<prec> s)"
    
lemma obd_imp_pbd:
  assumes "is_obd c s d t"
  shows "is_pbd c s d t"
  using assms unfolding is_obd_def is_pbd_def by auto
    
lemma pbd_imp_obd:
  assumes "is_pbd c s d t"
  shows "is_obd c s d t \<or> is_obd d t c s"
proof -
  have "s \<noteq> t" by (rule is_pbdE3, fact)
  hence "s \<prec> t \<or> t \<prec> s" by auto
  thus ?thesis
  proof
    assume "s \<prec> t"
    with \<open>is_pbd c s d t\<close> have "is_obd d t c s" unfolding is_pbd_def is_obd_def by simp
    thus ?thesis ..
  next
    assume "t \<prec> s"
    with \<open>is_pbd c s d t\<close> have "is_obd c s d t" unfolding is_pbd_def is_obd_def by simp
    thus ?thesis ..
  qed
qed

lemma is_obd_mult:
  fixes c::"'b::field" and d a s t u
  assumes "is_obd c s d t" and "a \<noteq> 0"
  shows "is_obd (a * c) (u + s) (a * d) (u + t)"
  using assms plus_monotone_strict_left[of t s u] unfolding is_obd_def by auto

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
  
lemma lp_binomial:
  assumes "is_obd c s d t"
  shows "lp (binomial c s d t) = s"
proof -
  have pbd: "is_pbd c s d t" by (rule obd_imp_pbd, fact)
  hence "c \<noteq> 0" by (rule is_pbdE1)
  show ?thesis
  proof (intro lp_eqI)
    from \<open>c \<noteq> 0\<close> show "lookup (binomial c s d t) s \<noteq> 0" unfolding lookup_binomial[OF pbd] by simp
  next
    fix u
    assume "lookup (binomial c s d t) u \<noteq> 0"
    hence "u \<in> keys (binomial c s d t)" by simp
    hence "u \<in> {s, t}" unfolding keys_binomial_pbd[OF pbd] .
    hence "u = s \<or> u = t" by simp
    thus "u \<preceq> s"
    proof
      assume "u = s"
      thus "u \<preceq> s" by simp
    next
      assume "u = t"
      from \<open>is_obd c s d t\<close> have "u \<prec> s" unfolding \<open>u = t\<close> is_obd_def by simp
      thus "u \<preceq> s" by simp
    qed
  qed
qed

lemma lc_binomial:
  assumes "is_obd c s d t"
  shows "lc (binomial c s d t) = c"
  unfolding lc_def lp_binomial[OF assms] lookup_binomial[OF assms[THEN obd_imp_pbd]] by simp

lemma tp_binomial:
  assumes "is_obd c s d t"
  shows "tp (binomial c s d t) = t"
proof -
  from assms have pbd: "is_pbd c s d t" by (rule obd_imp_pbd)
  hence "c \<noteq> 0" by (rule is_pbdE1)
  show ?thesis
  proof (intro tp_eqI)
    from \<open>c \<noteq> 0\<close> show "t \<in> keys (binomial c s d t)" unfolding keys_binomial_pbd[OF pbd] by simp
  next
    fix u
    assume "u \<in> keys (binomial c s d t)"
    hence "u \<in> {s, t}" unfolding keys_binomial_pbd[OF pbd] .
    hence "u = s \<or> u = t" by simp
    thus "t \<preceq> u"
    proof
      assume "u = s"
      from \<open>is_obd c s d t\<close> have "t \<prec> u" unfolding \<open>u = s\<close> is_obd_def by simp
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
  thus ?thesis unfolding tc_def tp_binomial[OF assms] lookup_binomial[OF assms[THEN obd_imp_pbd]] by simp
qed

lemma is_monomial_monomial_ordered:
  assumes "is_monomial p"
  obtains c t where "c \<noteq> 0" and "lc p = c" and "lp p = t" and "p = monomial c t"
proof -
  from assms obtain c t where "c \<noteq> 0" and p_eq: "p = monomial c t" by (rule is_monomial_monomial)
  from \<open>c \<noteq> 0\<close> have "lc p = c" and "lp p = t" unfolding p_eq by (rule lc_monomial, rule lp_monomial)
  from \<open>c \<noteq> 0\<close> this p_eq show ?thesis ..
qed

lemma monomial_plus_not_0:
  assumes "c \<noteq> 0" and "lp p \<prec> t"
  shows "monomial c t + p \<noteq> 0"
proof
  assume "monomial c t + p = 0"
  hence "0 = lookup (monomial c t + p) t" by simp
  also have "... = c + lookup p t" by (simp add: lookup_add)
  also have "... = c"
  proof -
    from assms(2) have "\<not> t \<preceq> lp p" by simp
    with lp_max[of p t] have "lookup p t = 0" by blast
    thus ?thesis by simp
  qed
  finally show False using \<open>c \<noteq> 0\<close> by simp
qed

lemma lp_monomial_plus:
  assumes "c \<noteq> (0::'b::comm_monoid_add)" and "lp p \<prec> t"
  shows "lp (monomial c t + p) = t"
proof -
  have eq: "lp (monomial c t) = t" by (simp only: lp_monomial[OF \<open>c \<noteq> 0\<close>])
  moreover have "lp (p + monomial c t) = lp (monomial c t)" by (rule lp_plus_eqI, simp only: eq, fact)
  ultimately show ?thesis by (simp add: add.commute)
qed

lemma lc_monomial_plus:
  assumes "c \<noteq> (0::'b::comm_monoid_add)" and "lp p \<prec> t"
  shows "lc (monomial c t + p) = c"
proof -
  from assms(2) have "\<not> t \<preceq> lp p" by simp
  with lp_max[of p t] have "lookup p t = 0" by blast
  thus ?thesis by (simp add: lc_def lp_monomial_plus[OF assms] lookup_add)
qed

lemma tp_monomial_plus:
  assumes "p \<noteq> (0::('a, 'b::comm_monoid_add) poly_mapping)" and "lp p \<prec> t"
  shows "tp (monomial c t + p) = tp p"
proof (cases "c = 0")
  case True
  thus ?thesis by (simp add: monomial_0I)
next
  case False
  have eq: "tp (monomial c t) = t" by (simp only: tp_monomial[OF \<open>c \<noteq> 0\<close>])
  moreover have "tp (p + monomial c t) = tp p"
  proof (rule tp_plus_eqI, fact, simp only: eq)
    from lp_geq_tp[of p] assms(2) show "tp p \<prec> t" by simp
  qed
  ultimately show ?thesis by (simp add: ac_simps)
qed

lemma tc_monomial_plus:
  assumes "p \<noteq> (0::('a, 'b::comm_monoid_add) poly_mapping)" and "lp p \<prec> t"
  shows "tc (monomial c t + p) = tc p"
proof (simp add: tc_def tp_monomial_plus[OF assms] lookup_add lookup_single PP_Poly_Mapping.when_def,
    rule impI)
  assume "t = tp p"
  with assms(2) have "lp p \<prec> tp p" by simp
  with lp_geq_tp[of p] show "c + lookup p (tp p) = lookup p (tp p)" by simp
qed

lemma tail_monomial_plus:
  assumes "c \<noteq> (0::'b::comm_monoid_add)" and "lp p \<prec> t"
  shows "tail (monomial c t + p) = p" (is "tail ?q = _")
proof -
  from assms have "lp ?q = t" by (rule lp_monomial_plus)
  moreover have "lower (monomial c t) t = 0"
    by (simp add: lower_0_iff, rule disjI2, simp add: tp_monomial[OF \<open>c \<noteq> 0\<close>])
  ultimately show ?thesis by (simp add: tail_def lower_plus lower_id_iff, intro disjI2 assms(2))
qed

lemma keys_2_lp:
  assumes "keys p = {s, t}" and "t \<preceq> s"
  shows "lp p = s"
  by (rule lp_eqI_keys, simp_all add: assms(1), auto simp add: assms(2))

lemma keys_2_tp:
  assumes "keys p = {s, t}" and "t \<preceq> s"
  shows "tp p = t"
  by (rule tp_eqI, simp_all add: assms(1), auto simp add: assms(2))

lemma keys_2_plus:
  assumes "keys p = {s, t}" and "keys q = {t, u}" and "u \<prec> t" and "t \<prec> s" and "lookup p t + lookup q t = 0"
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
    from \<open>u \<prec> t\<close> \<open>t \<prec> s\<close> have "u \<prec> s" by simp
    have "s \<in> keys (p + q)"
    proof (rule in_keys_plusI1, simp add: assms(1), simp add: assms(2), rule conjI)
      from \<open>t \<prec> s\<close> show "s \<noteq> t" by simp
    next
      from \<open>u \<prec> s\<close> show "s \<noteq> u" by simp
    qed
    moreover have "u \<in> keys (p + q)"
    proof (rule in_keys_plusI2, simp add: assms(2), simp add: assms(1), rule conjI)
      from \<open>u \<prec> s\<close> show "u \<noteq> s" by simp
    next
      from \<open>u \<prec> t\<close> show "u \<noteq> t" by simp
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
    
lemma monomial_set_pideal:
  fixes f :: "('a, 'b::field) poly_mapping"
  assumes "is_monomial_set G" and "f \<in> pideal G" and "t \<in> keys f"
  shows "\<exists>g\<in>G. lp g adds t"
  using \<open>f \<in> pideal G\<close> \<open>t \<in> keys f\<close>
proof (induct f rule: pideal_induct)
  case pideal_0
  have "keys 0 = {}" by (simp only: keys_eq_empty_iff)
  with \<open>t \<in> keys 0\<close> show ?case by auto
next
  case (pideal_plus a b c s)
  have "t \<in> keys (a + monom_mult c s b)" by fact
  also have "... \<subseteq> (keys a) \<union> (keys (monom_mult c s b))" by (rule keys_add_subset)
  finally have "t \<in> (keys a) \<union> (keys (monom_mult c s b))" .
  hence "t \<in> keys a \<or> t \<in> keys (monom_mult c s b)" by simp
  thus ?case
  proof
    assume "t \<in> keys a"
    thus ?thesis by (rule \<open>t \<in> keys a \<Longrightarrow> (\<exists>g\<in>G. lp g adds t)\<close>)
  next
    assume "t \<in> keys (monom_mult c s b)"
    show ?thesis
    proof
      from \<open>is_monomial_set G\<close> \<open>b \<in> G\<close> have "is_monomial b" by (rule is_monomial_setD)
      then obtain d u where "d \<noteq> 0" and b_def: "b = monomial d u" by (rule is_monomial_monomial)
      from \<open>d \<noteq> 0\<close> have "lp b = u" unfolding b_def by (rule lp_monomial)
      have "monom_mult c s b = monomial (c * d) (s + u)" unfolding b_def monom_mult_monomial ..
      with \<open>t \<in> keys (monom_mult c s b)\<close> have t: "t \<in> keys (monomial (c * d) (s + u))" by simp
      show "lp b adds t"
      proof (cases "c = 0")
        case True
        hence "c * d = 0" by simp
        hence "monomial (c * d) (s + u) = 0" by (rule monomial_0I)
        hence "keys (monomial (c * d) (s + u)) = {}" by simp
        with t have "t \<in> {}" by simp
        thus ?thesis ..
      next
        case False
        with \<open>d \<noteq> 0\<close> have "c * d \<noteq> 0" by simp
        hence "keys (monomial (c * d) (s + u)) = {s + u}" by (rule keys_of_monomial)
        with t have "t = s + u" by simp
        thus ?thesis unfolding \<open>lp b = u\<close> by simp
      qed
    qed fact
  qed
qed

subsection \<open>Monicity\<close>
  
definition monic :: "('a, 'b) poly_mapping \<Rightarrow> ('a, 'b::field) poly_mapping" where
  "monic p = monom_mult (1 / lc p) 0 p"

definition monic_set :: "('a, 'b) poly_mapping set \<Rightarrow> ('a, 'b::field) poly_mapping set" where
  "monic_set = image monic"
  
definition is_monic_set :: "('a, 'b::field) poly_mapping set \<Rightarrow> bool" where
  "is_monic_set B \<equiv> (\<forall>b\<in>B. b \<noteq> 0 \<longrightarrow> lc b = 1)"

lemma lookup_monic:
  shows "lookup (monic p) t = (lookup p t) / lc p"
proof -
  have "lookup (monic p) (0 + t) = (1 / lc p) * (lookup p t)" unfolding monic_def
    by (rule lookup_monom_mult)
  thus ?thesis by simp
qed

lemma lookup_monic_lp:
  assumes "p \<noteq> 0"
  shows "lookup (monic p) (lp p) = 1"
  unfolding monic_def
proof -
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  hence "1 / lc p \<noteq> 0" by simp
  let ?q = "monom_mult (1 / lc p) 0 p"
  have "lookup ?q (0 + lp p) = (1 / lc p) * (lookup p (lp p))" by (rule lookup_monom_mult)
  also have "... = (1 / lc p) * lc p" unfolding lc_def ..
  also have "... = 1" using \<open>lc p \<noteq> 0\<close> by simp
  finally have "lookup ?q (0 + lp p) = 1" .
  thus "lookup ?q (lp p) = 1" by simp
qed
  
lemma monic_0 [simp]:
  shows "monic 0 = 0"
  unfolding monic_def by (rule monom_mult_right0)

lemma monic_0_iff:
  shows "(monic p = 0) \<longleftrightarrow> (p = 0)"
proof
  assume "monic p = 0"
  show "p = 0"
  proof (rule ccontr)
    assume "p \<noteq> 0"
    hence "lookup (monic p) (lp p) = 1" by (rule lookup_monic_lp)
    with \<open>monic p = 0\<close> have "lookup 0 (lp p) = (1::'b)" by simp
    thus False by simp
  qed
next
  assume p0: "p = 0"
  show "monic p = 0" unfolding p0 by (fact monic_0)
qed
  
lemma keys_monic:
  shows "keys (monic p) = keys p"
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

lemma lp_monic:
  shows "lp (monic p) = lp p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True monic_0 ..
next
  case False
  have "lp (monom_mult (1 / lc p) 0 p) = 0 + lp p"
  proof (rule lp_mult)
    from False have "lc p \<noteq> 0" by (rule lc_not_0)
    thus "1 / lc p \<noteq> 0" by simp
  qed fact
  thus ?thesis unfolding monic_def by simp
qed

lemma lc_monic:
  assumes "p \<noteq> 0"
  shows "lc (monic p) = 1"
  using assms unfolding lc_def by (simp add: lp_monic lookup_monic_lp)

lemma mult_lc_monic:
  assumes "p \<noteq> 0"
  shows "monom_mult (lc p) 0 (monic p) = p" (is "?q = p")
proof (rule poly_mapping_eqI)
  fix t
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  have "lookup ?q (0 + t) = (lc p) * (lookup (monic p) t)" by (rule lookup_monom_mult)
  also have "... = (lc p) * ((lookup p t) / lc p)" by (simp add: lookup_monic)
  also have "... = lookup p t" using \<open>lc p \<noteq> 0\<close> by simp
  finally show "lookup ?q t = lookup p t" by simp
qed
  
lemma is_monic_setD:
  fixes B b
  assumes "is_monic_set B" and "b \<in> B" and "b \<noteq> 0"
  shows "lc b = 1"
  using assms unfolding is_monic_set_def by auto
    
lemma monic_set_is_monic_set:
  shows "is_monic_set (monic_set A)"
  unfolding is_monic_set_def
proof (intro ballI impI)
  fix p
  assume pin: "p \<in> monic_set A" and "p \<noteq> 0"
  from pin obtain p' where p_def: "p = monic p'" and "p' \<in> A" unfolding monic_set_def ..
  from \<open>p \<noteq> 0\<close> have "p' \<noteq> 0" unfolding p_def monic_0_iff .
  thus "lc p = 1" unfolding p_def by (rule lc_monic)
qed
  
lemma monic_set_pideal:
  shows "pideal (monic_set B) = pideal B"
proof
  show "pideal (monic_set B) \<subseteq> pideal B"
  proof
    fix p
    assume "p \<in> pideal (monic_set B)"
    thus "p \<in> pideal B"
    proof (induct p rule: pideal_induct)
      case base: pideal_0
      show ?case by (fact zero_in_pideal)
    next
      case ind: (pideal_plus a b c t)
      from ind(3) obtain b' where b_def: "b = monic b'" and "b' \<in> B" unfolding monic_set_def ..
      have eq: "b = monom_mult (1 / lc b') 0 b'" by (simp only: b_def monic_def)
      show ?case unfolding eq monom_mult_assoc
        by (rule pideal_closed_plus, fact, rule monom_mult_in_pideal, fact)
    qed
  qed
next
  show "pideal B \<subseteq> pideal (monic_set B)"
  proof
    fix p
    assume "p \<in> pideal B"
    thus "p \<in> pideal (monic_set B)"
    proof (induct p rule: pideal_induct)
      case base: pideal_0
      show ?case by (fact zero_in_pideal)
    next
      case ind: (pideal_plus a b c t)
      show ?case
      proof (cases "b = 0")
        case True
        from ind(2) show ?thesis unfolding True monom_mult_right0 by simp
      next
        case False
        let ?b = "monic b"
        from ind(3) have "?b \<in> monic_set B" unfolding monic_set_def by (rule imageI)
        have "a + monom_mult c t (monom_mult (lc b) 0 ?b) \<in> pideal (monic_set B)"
          unfolding monom_mult_assoc
          by (rule pideal_closed_plus, fact, rule monom_mult_in_pideal, fact)
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

subsection \<open>Multiplication\<close>

lemma in_keys_times_leq:
  assumes "t \<in> keys (p * q)"
  shows "t \<preceq> lp p + lp q"
proof -
  from assms obtain u v where "u \<in> keys p" and "v \<in> keys q" and "t = u + v"
    by (rule in_keys_timesE)
  from \<open>u \<in> keys p\<close> have "u \<preceq> lp p" by (rule lp_max_keys)
  from \<open>v \<in> keys q\<close> have "v \<preceq> lp q" by (rule lp_max_keys)
  hence "t \<preceq> u + lp q" unfolding \<open>t = u + v\<close> by (metis add.commute plus_monotone)
  also from \<open>u \<preceq> lp p\<close> have "... \<preceq> lp p + lp q" by (rule plus_monotone)
  finally show ?thesis .
qed

lemma in_keys_times_geq:
  assumes "t \<in> keys (p * q)"
  shows "tp p + tp q \<preceq> t"
proof -
  from assms obtain u v where "u \<in> keys p" and "v \<in> keys q" and "t = u + v"
    by (rule in_keys_timesE)
  from \<open>u \<in> keys p\<close> have "tp p \<preceq> u" by (rule tp_min_keys)
  from \<open>v \<in> keys q\<close> have "tp q \<preceq> v" by (rule tp_min_keys)
  hence "tp p + tp q \<preceq> tp p + v" by (metis add.commute plus_monotone)
  also from \<open>tp p \<preceq> u\<close> have "... \<preceq> t" unfolding \<open>t = u + v\<close> by (rule plus_monotone)
  finally show ?thesis .
qed

lemma lookup_times_lp_lp: "lookup (p * q) (lp p + lp q) = lc p * lc q"
proof (induct p rule: poly_mapping_tail_induct)
  case 0
  show ?case by (simp add: lc_def)
next
  case step: (tail p)
  from step(1) have "lc p \<noteq> 0" by (rule lc_not_0)
  let ?t = "lp p + lp q"
  show ?case
  proof (cases "is_monomial p")
    case True
    then obtain c t where "c \<noteq> 0" and "lp p = t" and "lc p = c" and p_eq: "p = monomial c t"
      by (rule is_monomial_monomial_ordered)
    hence "p * q = monom_mult (lc p) (lp p) q" by (simp add: times_monomial_left)
    thus ?thesis by (simp add: lookup_monom_mult lc_def)
  next
    case False
    have "lp (tail p) \<noteq> lp p"
    proof (simp add: tail_def lp_lower_eq_iff, rule)
      assume "lp p = 0"
      have "keys p \<subseteq> {lp p}"
      proof (rule, simp)
        fix s
        assume "s \<in> keys p"
        hence "s \<preceq> lp p" by (rule lp_max_keys)
        moreover have "lp p \<preceq> s" unfolding \<open>lp p = 0\<close> by (rule zero_min)
        ultimately show "s = lp p" by simp
      qed
      hence "card (keys p) = 0 \<or> card (keys p) = 1" using subset_singletonD by fastforce
      thus False
      proof
        assume "card (keys p) = 0"
        hence "p = 0" by (meson card_0_eq keys_eq_empty_iff finite_keys) 
        with step(1) show False ..
      next
        assume "card (keys p) = 1"
        with False show False unfolding is_monomial_def ..
      qed
    qed
    with lp_lower[of p "lp p"] have "lp (tail p) \<prec> lp p" unfolding tail_def by simp
    have eq: "lookup ((tail p) * q) ?t = 0"
    proof (rule ccontr)
      assume "lookup ((tail p) * q) ?t \<noteq> 0"
      hence "?t \<in> keys ((tail p) * q)" by simp
      hence "?t \<preceq> lp (tail p) + lp q" by (rule in_keys_times_leq)
      hence "lp p \<preceq> lp (tail p)" by (rule ord_canc)
      also have "... \<prec> lp p" by fact
      finally show False ..
    qed
    from step(2) have "lookup (monom_mult (lc p) (lp p) q) ?t = lc p * lc q"
      by (simp only: lookup_monom_mult lc_def)
    thus ?thesis by (simp add: times_tail_rec_left[of p q] lookup_add eq)
  qed
qed

lemma lookup_times_tp_tp: "lookup (p * q) (tp p + tp q) = tc p * tc q"
proof (induct p rule: poly_mapping_tail_induct)
  case 0
  show ?case by (simp add: tc_def)
next
  case step: (tail p)
  from step(1) have "lc p \<noteq> 0" by (rule lc_not_0)
  let ?t = "tp p + tp q"
  show ?case
  proof (cases "is_monomial p")
    case True
    then obtain c t where "c \<noteq> 0" and "lp p = t" and "lc p = c" and p_eq: "p = monomial c t"
      by (rule is_monomial_monomial_ordered)
    from \<open>c \<noteq> 0\<close> have "tp p = t" and "tc p = c" by (simp_all add: p_eq tp_monomial tc_monomial)
    with p_eq have "p * q = monom_mult (tc p) (tp p) q" by (simp add: times_monomial_left)
    thus ?thesis by (simp add: lookup_monom_mult tc_def)
  next
    case False
    with has_bounded_keys_1_D[of p] step(1) have "\<not> has_bounded_keys 1 p" by auto
    hence "tp p \<prec> lp p" by (simp add: lp_gr_tp_iff)
    hence tp_tail: "tp (tail p) = tp p" and tc_tail: "tc (tail p) = tc p" unfolding tail_def
      by (rule tp_lower, rule tc_lower)
    have eq: "lookup (monom_mult (lc p) (lp p) q) ?t = 0"
    proof (rule ccontr)
      assume "lookup (monom_mult (lc p) (lp p) q) ?t \<noteq> 0"
      hence "?t \<in> keys (monom_mult (lc p) (lp p) q)" by simp
      hence "lp p + tp q \<preceq> ?t" by (rule in_keys_monom_mult_geq)
      hence "lp p \<preceq> tp p" by (rule ord_canc)
      also have "... \<prec> lp p" by fact
      finally show False ..
    qed
    from step(2) have "lookup (tail p * q) ?t = tc p * tc q" by (simp only: tp_tail tc_tail)
    thus ?thesis by (simp add: times_tail_rec_left[of p q] lookup_add eq)
  qed
qed

lemma lp_times:
  assumes "p \<noteq> 0" and "q \<noteq> (0::('a, 'b::semiring_no_zero_divisors) poly_mapping)"
  shows "lp (p * q) = lp p + lp q"
proof (rule lp_eqI_keys, simp only: in_keys_iff lookup_times_lp_lp)
  from assms(1) have "lc p \<noteq> 0" by (rule lc_not_0)
  moreover from assms(2) have "lc q \<noteq> 0" by (rule lc_not_0)
  ultimately show "lc p * lc q \<noteq> 0" by simp
qed (rule in_keys_times_leq)

lemma tp_times:
  assumes "p \<noteq> 0" and "q \<noteq> (0::('a, 'b::semiring_no_zero_divisors) poly_mapping)"
  shows "tp (p * q) = tp p + tp q"
proof (rule tp_eqI, simp only: in_keys_iff lookup_times_tp_tp)
  from assms(1) have "tc p \<noteq> 0" by (rule tc_not_0)
  moreover from assms(2) have "tc q \<noteq> 0" by (rule tc_not_0)
  ultimately show "tc p * tc q \<noteq> 0" by simp
qed (rule in_keys_times_geq)

lemma lc_times_poly_mapping': "lc (p * q) = lc p * lc (q::('a, 'b::semiring_no_zero_divisors) poly_mapping)"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: lc_def)
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    thus ?thesis by (simp add: lc_def)
  next
    case False
    with \<open>p \<noteq> 0\<close> show ?thesis by (simp add: lc_def lp_times lookup_times_lp_lp)
  qed
qed

lemma tc_times_poly_mapping': "tc (p * q) = tc p * tc (q::('a, 'b::semiring_no_zero_divisors) poly_mapping)"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: tc_def)
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    thus ?thesis by (simp add: tc_def)
  next
    case False
    with \<open>p \<noteq> 0\<close> show ?thesis by (simp add: tc_def tp_times lookup_times_tp_tp)
  qed
qed

lemma times_not_0:
  assumes "p \<noteq> 0" and "q \<noteq> (0::('a, 'b::semiring_no_zero_divisors) poly_mapping)"
  shows "p * q \<noteq> 0"
proof
  assume "p * q = 0"
  hence "0 = lc (p * q)" by (simp add: lc_def)
  also have "... = lc p * lc q" by (rule lc_times_poly_mapping')
  finally have "lc p * lc q = 0" by simp
  moreover from assms(1) have "lc p \<noteq> 0" by (rule lc_not_0)
  moreover from assms(2) have "lc q \<noteq> 0" by (rule lc_not_0)
  ultimately show False by simp
qed

end (* ordered_powerprod *)
  
end (* theory *)
