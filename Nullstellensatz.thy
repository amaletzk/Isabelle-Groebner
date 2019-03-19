(* Author: Alexander Maletzky *)

section \<open>Hilbert's Nullstellensatz\<close>

theory Nullstellensatz
  imports "HOL-Computational_Algebra.Fundamental_Theorem_Algebra" Univariate_PM
begin

text \<open>We prove the geometric version of Hilbert's Nullstellensatz, i.e. the precise correspondence
  between algebraic varieties and radical ideals.\<close>

subsection \<open>Algebraically Closed Fields\<close>

lemma prod_eq_zeroE:
  assumes "prod f I = (0::'a::{semiring_no_zero_divisors,comm_monoid_mult,zero_neq_one})"
  obtains i where "finite I" and "i \<in> I" and "f i = 0"
proof -
  have "finite I"
  proof (rule ccontr)
    assume "infinite I"
    with assms show False by simp
  qed
  moreover from this assms obtain i where "i \<in> I" and "f i = 0"
  proof (induct I arbitrary: thesis)
    case empty
    from empty(2) show ?case by simp
  next
    case (insert j I)
    from insert.hyps(1, 2) have "f j * prod f I = prod f (insert j I)" by simp
    also have "\<dots> = 0" by fact
    finally have "f j = 0 \<or> prod f I = 0" by simp
    thus ?case
    proof
      assume "f j = 0"
      with _ show ?thesis by (rule insert.prems) simp
    next
      assume "prod f I = 0"
      then obtain i where "i \<in> I" and "f i = 0" using insert.hyps(3) by blast
      from _ this(2) show ?thesis by (rule insert.prems) (simp add: \<open>i \<in> I\<close>)
    qed
  qed
  ultimately show ?thesis ..
qed

lemma degree_prod_eq:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> f i \<noteq> 0"
  shows "Polynomial.degree (prod f I :: _::semiring_no_zero_divisors poly) = (\<Sum>i\<in>I. Polynomial.degree (f i))"
  using assms
proof (induct I)
  case empty
  show ?case by simp
next
  case (insert j J)
  have 1: "f i \<noteq> 0" if "i \<in> J" for i
  proof (rule insert.prems)
    from that show "i \<in> insert j J" by simp
  qed
  hence eq: "Polynomial.degree (prod f J) = (\<Sum>i\<in>J. Polynomial.degree (f i))" by (rule insert.hyps)
  from insert.hyps(1, 2) have "Polynomial.degree (prod f (insert j J)) = Polynomial.degree (f j * prod f J)"
    by simp
  also have "\<dots> = Polynomial.degree (f j) + Polynomial.degree (prod f J)"
  proof (rule degree_mult_eq)
    show "f j \<noteq> 0" by (rule insert.prems) simp
  next
    show "prod f J \<noteq> 0"
    proof
      assume "prod f J = 0"
      then obtain i where "i \<in> J" and "f i = 0" by (rule prod_eq_zeroE)
      from this(1) have "f i \<noteq> 0" by (rule 1)
      thus False using \<open>f i = 0\<close> ..
    qed
  qed
  also from insert.hyps(1, 2) have "\<dots> = (\<Sum>i\<in>insert j J. Polynomial.degree (f i))" by (simp add: eq)
  finally show ?case .
qed

class alg_closed_field =
  assumes alg_closed_field_axiom: "\<And>p::'a::field poly. 0 < Polynomial.degree p \<Longrightarrow> \<exists>z. poly p z = 0"
begin

lemma rootE:
  assumes "0 < Polynomial.degree p"
  obtains z where "poly p z = (0::'a)"
proof -
  from assms have "\<exists>z. poly p z = 0" by (rule alg_closed_field_axiom)
  then obtain z where "poly p z = 0" ..
  thus ?thesis ..
qed

lemma infinite_UNIV: "infinite (UNIV::'a set)"
proof
  assume fin: "finite (UNIV::'a set)"
  define p where "p = (\<Prod>a\<in>UNIV. [:- a, 1::'a:]) + [:-1:]"
  have "Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:]) = (\<Sum>a\<in>UNIV. Polynomial.degree [:- a, 1::'a:])"
    using fin by (rule degree_prod_eq) simp
  also have "\<dots> = (\<Sum>a\<in>(UNIV::'a set). 1)" by simp
  also have "\<dots> = card (UNIV::'a set)" by simp
  also from fin have "\<dots> > 0" by (rule finite_UNIV_card_ge_0)
  finally have "0 < Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" .
  hence "Polynomial.degree [:-1:] < Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" by simp
  hence "Polynomial.degree p = Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" unfolding p_def
    by (rule degree_add_eq_left)
  also have "\<dots> > 0" by fact
  finally have "0 < Polynomial.degree p" .
  then obtain z where "poly p z = 0" by (rule rootE)
  hence "(\<Prod>a\<in>UNIV. (z - a)) = 1" by (simp add: p_def poly_prod)
  thus False by (metis UNIV_I cancel_comm_monoid_add_class.diff_cancel fin one_neq_zero prod_zero_iff)
qed

lemma linear_factorsE:
  fixes p :: "'a poly"
  obtains c A m where "finite A" and "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A" and "c = 0 \<longleftrightarrow> p = 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)"
proof -
  obtain c A m where fin: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and *: "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A"
  proof (induct p arbitrary: thesis rule: poly_root_induct[where P="\<lambda>_. True"])
    case 0
    show ?case
    proof (rule 0)
      show "0 = Polynomial.smult 0 (\<Prod>a\<in>{}. [:- a, 1:] ^ (\<lambda>_. 0) a)" by simp
    qed simp_all
  next
    case (no_roots p)
    have "Polynomial.degree p = 0"
    proof (rule ccontr)
      assume "Polynomial.degree p \<noteq> 0"
      hence "0 < Polynomial.degree p" by simp
      then obtain z where "poly p z = 0" by (rule rootE)
      moreover have "poly p z \<noteq> 0" by (rule no_roots) blast
      ultimately show False by simp
    qed
    then obtain c where p: "p = [:c:]" by (rule degree_eq_zeroE)
    show ?case
    proof (rule no_roots)
      show "p = Polynomial.smult c (\<Prod>a\<in>{}. [:- a, 1:] ^ (\<lambda>_. 0) a)" by (simp add: p)
    qed simp_all
  next
    case (root a p)
    obtain A c m where 1: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
      and 2: "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A" by (rule root.hyps) blast
    define m' where "m' = (\<lambda>x. if x = a then Suc (m x) else m x)"
    show ?case
    proof (rule root.prems)
      from 1 show "finite (insert a A)" by simp
    next
      have "[:a, - 1:] * p = [:- a, 1:] * (- p)" by simp
      also have "\<dots> = [:- a, 1:] * (Polynomial.smult (- c) (\<Prod>a\<in>A. [:- a, 1:] ^ m a))"
        by (simp add: p)
      also have "\<dots> = Polynomial.smult (- c) ([:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a))"
        by (simp only: mult_smult_right ac_simps)
      also have "[:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a) = (\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a)"
      proof (cases "a \<in> A")
        case True
        with 1 have "(\<Prod>a\<in>A. [:- a, 1:] ^ m a) = [:- a, 1:] ^ m a * (\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m a)"
          by (simp add: prod.remove)
        also from refl have "(\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m a) = (\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m' a)"
          by (rule prod.cong) (simp add: m'_def)
        finally have "[:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a) =
                          ([:- a, 1:] * [:- a, 1:] ^ m a) * (\<Prod>a\<in>A - {a}. [:- a, 1:] ^ m' a)"
          by (simp only: mult.assoc)
        also have "[:- a, 1:] * [:- a, 1:] ^ m a = [:- a, 1:] ^ m' a" by (simp add: m'_def)
        finally show ?thesis using 1 by (simp add: prod.insert_remove)
      next
        case False
        with 1 have "(\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a) = [:- a, 1:] ^ m' a * (\<Prod>a\<in>A. [:- a, 1:] ^ m' a)"
          by simp
        also from refl have "(\<Prod>a\<in>A. [:- a, 1:] ^ m' a) = (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
        proof (rule prod.cong)
          fix x
          assume "x \<in> A"
          with False have "x \<noteq> a" by blast
          thus "[:- x, 1:] ^ m' x = [:- x, 1:] ^ m x" by (simp add: m'_def)
        qed
        finally have "(\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a) = [:- a, 1:] ^ m' a * (\<Prod>a\<in>A. [:- a, 1:] ^ m a)" .
        also from False have "m' a = 1" by (simp add: m'_def 2)
        finally show ?thesis by simp
      qed
      finally show "[:a, - 1:] * p = Polynomial.smult (- c) (\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a)" .
    next
      fix x
      show "m' x = 0 \<longleftrightarrow> x \<notin> insert a A" by (simp add: m'_def 2)
    qed
  qed
  moreover have "c = 0 \<longleftrightarrow> p = 0"
  proof
    assume "p = 0"
    hence "[:c:] = 0 \<or> (\<Prod>a\<in>A. [:- a, 1:] ^ m a) = 0" by (simp add: p)
    thus "c = 0"
    proof
      assume "[:c:] = 0"
      thus ?thesis by simp
    next
      assume "(\<Prod>a\<in>A. [:- a, 1:] ^ m a) = 0"
      then obtain a where "[:- a, 1:] ^ m a = 0" by (rule prod_eq_zeroE)
      thus ?thesis by simp
    qed
  qed (simp add: p)
  moreover {
    fix z
    have "0 < m z" if "z \<in> A" by (rule ccontr) (simp add: * that)
    hence "poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)" by (auto simp: p poly_prod * fin elim: prod_eq_zeroE)
  }
  ultimately show ?thesis ..
qed

end (* alg_closed_field *)

instance complex :: alg_closed_field
  by standard (rule fundamental_theorem_of_algebra, simp add: constant_degree)

subsection \<open>Ideals and Varieties\<close>

definition variety_of :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> ('x \<Rightarrow> 'a::comm_semiring_1) set"
  where "variety_of F = {a. \<forall>f\<in>F. eval_pm a f = 0}"

definition ideal_of :: "('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set"
  where "ideal_of A = {f. \<forall>a\<in>A. eval_pm a f = 0}"

definition radical :: "('a \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('a::comm_powerprod \<Rightarrow>\<^sub>0 'b::semiring_1) set" ("\<surd>(_)" [999] 999)
  where "radical F = {f. \<exists>m. f ^ m \<in> F}"

abbreviation "\<V> \<equiv> variety_of"
abbreviation "\<I> \<equiv> ideal_of"

lemma variety_ofI: "(\<And>f. f \<in> F \<Longrightarrow> eval_pm a f = 0) \<Longrightarrow> a \<in> \<V> F"
  by (simp add: variety_of_def)

lemma variety_ofD: "a \<in> \<V> F \<Longrightarrow> f \<in> F \<Longrightarrow> eval_pm a f = 0"
  by (simp add: variety_of_def)

lemma variety_of_antimono: "F \<subseteq> G \<Longrightarrow> \<V> G \<subseteq> \<V> F"
  by (auto simp: variety_of_def)

lemma variety_of_ideal [simp]: "\<V> (ideal F) = \<V> F"
proof
  show "\<V> (ideal F) \<subseteq> \<V> F" by (intro variety_of_antimono ideal.span_superset)
next
  show "\<V> F \<subseteq> \<V> (ideal F)"
  proof (intro subsetI variety_ofI)
    fix a f
    assume "a \<in> \<V> F" and "f \<in> ideal F"
    from this(2) show "eval_pm a f = 0"
    proof (induct f rule: ideal.span_induct_alt)
      case base
      show ?case by simp
    next
      case (step c f g)
      with \<open>a \<in> \<V> F\<close> show ?case by (auto simp: eval_pm_plus eval_pm_times dest: variety_ofD)
    qed
  qed
qed

lemma ideal_ofI: "(\<And>a. a \<in> A \<Longrightarrow> eval_pm a f = 0) \<Longrightarrow> f \<in> \<I> A"
  by (simp add: ideal_of_def)

lemma ideal_ofD: "f \<in> \<I> A \<Longrightarrow> a \<in> A \<Longrightarrow> eval_pm a f = 0"
  by (simp add: ideal_of_def)

lemma ideal_of_antimono: "A \<subseteq> B \<Longrightarrow> \<I> B \<subseteq> \<I> A"
  by (auto simp: ideal_of_def)

lemma ideal_ideal_of [simp]: "ideal (\<I> A) = \<I> A"
  unfolding ideal.span_eq_iff
proof (rule ideal.subspaceI)
  show "0 \<in> \<I> A" by (rule ideal_ofI) simp
next
  fix f g
  assume "f \<in> \<I> A"
  hence f: "eval_pm a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  assume "g \<in> \<I> A"
  hence g: "eval_pm a g = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "f + g \<in> \<I> A" by (rule ideal_ofI) (simp add: eval_pm_plus f g)
next
  fix c f
  assume "f \<in> \<I> A"
  hence f: "eval_pm a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "c * f \<in> \<I> A" by (rule ideal_ofI) (simp add: eval_pm_times f)
qed

lemma variety_of_ideal_of_variety [simp]: "\<V> (\<I> (\<V> F)) = \<V> F" (is "_ = ?V")
proof
  have "F \<subseteq> \<I> (\<V> F)" by (auto intro!: ideal_ofI dest: variety_ofD)
  thus "\<V> (\<I> ?V) \<subseteq> ?V" by (rule variety_of_antimono)
next
  show "?V \<subseteq> \<V> (\<I> ?V)" by (auto intro!: variety_ofI dest: ideal_ofD)
qed

lemma ideal_of_inj_on: "inj_on \<I> (range (\<V>::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1) set \<Rightarrow> _))"
proof (rule inj_onI)
  fix A B :: "('x \<Rightarrow> 'a) set"
  assume "A \<in> range \<V>"
  then obtain F where A: "A = \<V> F" ..
  assume "B \<in> range \<V>"
  then obtain G where B: "B = \<V> G" ..
  assume "\<I> A = \<I> B"
  hence "\<V> (\<I> A) = \<V> (\<I> B)" by simp
  thus "A = B" by (simp add: A B)
qed

lemma ideal_of_variety_of_ideal [simp]: "\<I> (\<V> (\<I> A)) = \<I> A" (is "_ = ?I")
proof
  have "A \<subseteq> \<V> (\<I> A)" by (auto intro!: variety_ofI dest: ideal_ofD)
  thus "\<I> (\<V> ?I) \<subseteq> ?I" by (rule ideal_of_antimono)
next
  show "?I \<subseteq> \<I> (\<V> ?I)" by (auto intro!: ideal_ofI dest: variety_ofD)
qed

lemma variety_of_inj_on: "inj_on \<V> (range (\<I>::('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> _))"
proof (rule inj_onI)
  fix F G :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set"
  assume "F \<in> range \<I>"
  then obtain A where F: "F = \<I> A" ..
  assume "G \<in> range \<I>"
  then obtain B where G: "G = \<I> B" ..
  assume "\<V> F = \<V> G"
  hence "\<I> (\<V> F) = \<I> (\<V> G)" by simp
  thus "F = G" by (simp add: F G)
qed

lemma radicalI: "f ^ m \<in> F \<Longrightarrow> f \<in> \<surd>F"
  by (auto simp: radical_def)

lemma radicalE:
  assumes "f \<in> \<surd>F"
  obtains m where "f ^ m \<in> F"
  using assms by (auto simp: radical_def)

lemma radical_mono: "F \<subseteq> G \<Longrightarrow> \<surd>F \<subseteq> \<surd>G"
  by (auto elim!: radicalE intro: radicalI)

lemma radical_superset: "F \<subseteq> \<surd>F"
proof
  fix f
  assume "f \<in> F"
  hence "f ^ 1 \<in> F" by simp
  thus "f \<in> \<surd>F" by (rule radicalI)
qed

lemma radical_idem [simp]: "\<surd>\<surd>F = \<surd>F"
proof
  show "\<surd>\<surd>F \<subseteq> \<surd>F" by (auto elim!: radicalE intro: radicalI simp flip: power_mult)
qed (fact radical_superset)

lemma ideal_radical_ideal [simp]: "ideal (\<surd>ideal F) = \<surd>ideal F" (is "_ = ?R")
  unfolding ideal.span_eq_iff
proof (rule ideal.subspaceI)
  have "0 ^ 1 \<in> ideal F" by (simp add: ideal.span_zero)
  thus "0 \<in> ?R" by (rule radicalI)
next
  fix a b
  assume "a \<in> ?R"
  then obtain m where "a ^ m \<in> ideal F" by (rule radicalE)
  have a: "a ^ k \<in> ideal F" if "m \<le> k" for k
  proof -
    from \<open>a ^ m \<in> _\<close> have "a ^ (k - m + m) \<in> ideal F" by (simp only: power_add ideal.span_scale)
    with that show ?thesis by simp
  qed
  assume "b \<in> ?R"
  then obtain n where "b ^ n \<in> ideal F" by (rule radicalE)
  have b: "b ^ k \<in> ideal F" if "n \<le> k" for k
  proof -
    from \<open>b ^ n \<in> _\<close> have "b ^ (k - n + n) \<in> ideal F" by (simp only: power_add ideal.span_scale)
    with that show ?thesis by simp
  qed
  have "(a + b) ^ (m + n) \<in> ideal F" unfolding binomial_ring
  proof (rule ideal.span_sum)
    fix k
    show "of_nat (m + n choose k) * a ^ k * b ^ (m + n - k) \<in> ideal F"
    proof (cases "k \<le> m")
      case True
      hence "n \<le> m + n - k" by simp
      hence "b ^ (m + n - k) \<in> ideal F" by (rule b)
      thus ?thesis by (rule ideal.span_scale)
    next
      case False
      hence "m \<le> k" by simp
      hence "a ^ k \<in> ideal F" by (rule a)
      hence "of_nat (m + n choose k) * b ^ (m + n - k) * a ^ k \<in> ideal F" by (rule ideal.span_scale)
      thus ?thesis by (simp only: ac_simps)
    qed
  qed
  thus "a + b \<in> ?R" by (rule radicalI)
next
  fix c a
  assume "a \<in> ?R"
  then obtain m where "a ^ m \<in> ideal F" by (rule radicalE)
  hence "(c * a) ^ m \<in> ideal F" by (simp only: power_mult_distrib ideal.span_scale)
  thus "c * a \<in> ?R" by (rule radicalI)
qed

lemma radical_ideal_of [simp]: "\<surd>\<I> A = \<I> (A::(_ \<Rightarrow> _::semiring_1_no_zero_divisors) set)"
proof
  show "\<surd>\<I> A \<subseteq> \<I> A" by (auto elim!: radicalE dest!: ideal_ofD intro!: ideal_ofI simp: eval_pm_power)
qed (fact radical_superset)

lemma variety_of_radical_ideal [simp]: "\<V> (\<surd>ideal F) = \<V> (F::(_ \<Rightarrow>\<^sub>0 _::semiring_1_no_zero_divisors) set)"
proof
  have "F \<subseteq> ideal F" by (rule ideal.span_superset)
  also have "\<dots> \<subseteq> \<surd>ideal F" by (rule radical_superset)
  finally show "\<V> (\<surd>ideal F) \<subseteq> \<V> F" by (rule variety_of_antimono)
next
  show "\<V> F \<subseteq> \<V> (\<surd>ideal F)"
  proof (intro subsetI variety_ofI)
    fix a f
    assume "a \<in> \<V> F"
    hence "a \<in> \<V> (ideal F)" by simp
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    with \<open>a \<in> \<V> (ideal F)\<close> have "eval_pm a (f ^ m) = 0" by (rule variety_ofD)
    thus "eval_pm a f = 0" by (simp add: eval_pm_power)
  qed
qed

subsection \<open>Nullstellensatz\<close>

lemma weak_Nullstellensatz_aux:
  assumes "F \<subseteq> P[insert x X]" and "x \<notin> X" and "1 \<notin> ideal F"
  obtains a::"'a::alg_closed_field" where "1 \<notin> eval_pm (\<lambda>_. monomial a 0) ` focus {x} ` ideal F"
proof (cases "ideal F \<inter> P[{x}] \<subseteq> {0}")
  case True
  then show ?thesis sorry
next
  case False
  then obtain f where "f \<in> ideal F" and "f \<in> P[{x}]" and "f \<noteq> 0" by blast
  then show ?thesis sorry
qed

thm indets_eval_pm_focus_subset

theorem weak_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]" and "\<V> F = {}"
  shows "(1::_ \<Rightarrow>\<^sub>0 'a::alg_closed_field) \<in> ideal F"
  sorry

thm ideal_eq_UNIV_iff_contains_one

theorem Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]" and "(f::_ \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<I> (\<V> F)"
  shows "f \<in> \<surd>ideal F"
  sorry

theorem strong_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "\<I> (\<V> F) = \<surd>ideal (F::(_ \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
proof (intro subset_antisym subsetI)
  fix f
  assume "f \<in> \<I> (\<V> F)"
  with assms show "f \<in> \<surd>ideal F" by (rule Nullstellensatz)
qed (metis ideal_ofI variety_ofD variety_of_radical_ideal)

lemma radical_ideal_iff:
  assumes "finite X" and "F \<subseteq> P[X]" and "y \<notin> X" and "y \<notin> indets f"
  shows "f \<in> \<surd>ideal F \<longleftrightarrow> 1 \<in> ideal (insert (1 - punit.monom_mult 1 (Poly_Mapping.single y 1) f) F)"
  sorry

end (* theory *)
