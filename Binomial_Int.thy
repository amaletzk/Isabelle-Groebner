section \<open>Integer Binomial Coefficients\<close>

theory Binomial_Int
  imports Main HOL.Rat
begin

text \<open>Restore original sort constraints:\<close>
setup \<open>Sign.add_const_constraint (@{const_name gbinomial}, SOME @{typ "'a::{semidom_divide,semiring_char_0} \<Rightarrow> nat \<Rightarrow> 'a"})\<close>

lemma gbinomial_0_left: "0 gchoose k = (if k = 0 then 1 else 0)"
  by (cases k) simp_all

lemma gbinomial_eq_0_int:
  assumes "n < k"
  shows "(int n) gchoose k = 0"
proof -
  have "\<exists>a\<in>{0..<k}. int n - int a = 0"
  proof
    show "int n - int n = 0" by simp
  next
    from assms show "n \<in> {0..<k}" by simp
  qed
  with finite_atLeastLessThan have eq: "prod (\<lambda>i. int n - int i) {0..<k} = 0" by (rule prod_zero)
  show ?thesis by (simp add: gbinomial_prod_rev eq)
qed

corollary gbinomial_eq_0: "0 \<le> a \<Longrightarrow> a < int k \<Longrightarrow> a gchoose k = 0"
  by (metis nat_eq_iff2 nat_less_iff gbinomial_eq_0_int)

lemma int_binomial: "int (n choose k) = (int n) gchoose k"
proof (cases "k \<le> n")
  case True
  from refl have eq: "(\<Prod>i = 0..<k. int (n - i)) = (\<Prod>i = 0..<k. int n - int i)"
  proof (rule prod.cong)
    fix i
    assume "i \<in> {0..<k}"
    with True show "int (n - i) = int n - int i" by simp
  qed
  show ?thesis
    by (simp add: gbinomial_binomial[symmetric] gbinomial_prod_rev zdiv_int eq)
next
  case False
  thus ?thesis by (simp add: gbinomial_eq_0_int)
qed

lemma falling_fact_pochhammer: "prod (\<lambda>i. a - int i) {0..<k} = (- 1) ^ k * pochhammer (- a) k"
  by (cases k)
    (simp_all add: pochhammer_minus,
     simp_all add: pochhammer_prod_rev
       power_mult_distrib [symmetric] atLeastLessThanSuc_atLeastAtMost
       prod.atLeast_Suc_atMost_Suc_shift of_nat_diff)

lemma falling_fact_pochhammer': "prod (\<lambda>i. a - int i) {0..<k} = pochhammer (a - int k + 1) k"
  by (cases k)
    (simp_all add: pochhammer_minus,
     simp_all add: pochhammer_prod_rev
       power_mult_distrib [symmetric] atLeastLessThanSuc_atLeastAtMost
       prod.atLeast_Suc_atMost_Suc_shift of_nat_diff)

lemma gbinomial_int_pochhammer: "(a::int) gchoose k = (- 1) ^ k * pochhammer (- a) k div fact k"
  by (simp only: gbinomial_prod_rev falling_fact_pochhammer)

lemma gbinomial_int_pochhammer': "a gchoose k = pochhammer (a - int k + 1) k div fact k"
  by (simp only: gbinomial_prod_rev falling_fact_pochhammer')

lemma fact_dvd_pochhammer: "fact k dvd pochhammer (a::int) k"
proof -
  have dvd: "y \<noteq> 0 \<Longrightarrow> ((of_int (x div y))::'a::field_char_0) = of_int x / of_int y \<Longrightarrow> y dvd x"
    for x y :: int
    by (smt dvd_triv_left mult.commute nonzero_eq_divide_eq of_int_eq_0_iff of_int_eq_iff of_int_mult)
  show ?thesis
  proof (cases "0 < a")
    case True
    moreover define n where "n = nat (a - 1) + k"
    ultimately have a: "a = int n - int k + 1" by simp
    from fact_nonzero show ?thesis unfolding a
    proof (rule dvd)
      have "of_int (pochhammer (int n - int k + 1) k div fact k) = (of_int (int n gchoose k)::rat)"
        by (simp only: gbinomial_int_pochhammer')
      also have "\<dots> = of_int (int (n choose k))" by (simp only: int_binomial)
      also have "\<dots> = of_nat (n choose k)" by simp
      also have "\<dots> = (of_nat n) gchoose k" by (fact binomial_gbinomial)
      also have "\<dots> = pochhammer (of_nat n - of_nat k + 1) k / fact k"
        by (fact gbinomial_pochhammer')
      also have "\<dots> = pochhammer (of_int (int n - int k + 1)) k / fact k" by simp
      also have "\<dots> = (of_int (pochhammer (int n - int k + 1) k)) / (of_int (fact k))"
        by (simp only: of_int_fact pochhammer_of_int)
      finally show "of_int (pochhammer (int n - int k + 1) k div fact k) =
                      of_int (pochhammer (int n - int k + 1) k) / rat_of_int (fact k)" .
    qed
  next
    case False
    moreover define n where "n = nat (- a)"
    ultimately have a: "a = - int n" by simp
    from fact_nonzero have "fact k dvd (-1)^k * pochhammer (- int n) k"
    proof (rule dvd)
      have "of_int ((-1)^k * pochhammer (- int n) k div fact k) = (of_int (int n gchoose k)::rat)"
        by (simp only: gbinomial_int_pochhammer)
      also have "\<dots> = of_int (int (n choose k))" by (simp only: int_binomial)
      also have "\<dots> = of_nat (n choose k)" by simp
      also have "\<dots> = (of_nat n) gchoose k" by (fact binomial_gbinomial)
      also have "\<dots> = (-1)^k * pochhammer (- of_nat n) k / fact k"
        by (fact gbinomial_pochhammer)
      also have "\<dots> = (-1)^k * pochhammer (of_int (- int n)) k / fact k" by simp
      also have "\<dots> = (-1)^k * (of_int (pochhammer (- int n) k)) / (of_int (fact k))"
        by (simp only: of_int_fact pochhammer_of_int)
      also have "\<dots> = (of_int ((-1)^k * pochhammer (- int n) k)) / (of_int (fact k))" by simp
      finally show "of_int ((- 1) ^ k * pochhammer (- int n) k div fact k) =
                    of_int ((- 1) ^ k * pochhammer (- int n) k) / rat_of_int (fact k)" .
    qed
    thus ?thesis unfolding a by (metis dvdI dvd_mult_unit_iff' minus_one_mult_self)
  qed
qed

lemma gbinomial_int_negated_upper: "(a gchoose k) = (-1) ^ k * ((int k - a - 1) gchoose k)"
  by (simp add: gbinomial_int_pochhammer pochhammer_minus algebra_simps fact_dvd_pochhammer div_mult_swap)

lemma gbinomial_int_mult_fact: "fact k * (a gchoose k) = (\<Prod>i = 0..<k. a - int i)"
  by (simp only: gbinomial_int_pochhammer' fact_dvd_pochhammer dvd_mult_div_cancel falling_fact_pochhammer')

corollary gbinomial_int_mult_fact': "(a gchoose k) * fact k = (\<Prod>i = 0..<k. a - int i)"
  using gbinomial_int_mult_fact[of k a] by (simp add: ac_simps)

lemma gbinomial_int_binomial:
  "a gchoose k = (if 0 \<le> a then int ((nat a) choose k) else (-1::int)^k * int ((k + (nat (- a)) - 1) choose k))"
  by (auto simp: int_binomial gbinomial_int_negated_upper[of a] int_ops(6))

corollary gbinomial_nneg: "0 \<le> a \<Longrightarrow> a gchoose k = int ((nat a) choose k)"
  by (simp add: gbinomial_int_binomial)

corollary gbinomial_neg: "a < 0 \<Longrightarrow> a gchoose k = (-1::int)^k * int ((k + (nat (- a)) - 1) choose k)"
  by (simp add: gbinomial_int_binomial)

lemma of_int_gbinomial: "of_int (a gchoose k) = (of_int a :: 'a::field_char_0) gchoose k"
proof -
  have of_int_div: "y dvd x \<Longrightarrow> of_int (x div y) = of_int x / (of_int y :: 'a)" for x y :: int by auto
  show ?thesis
    by (simp add: gbinomial_int_pochhammer' gbinomial_pochhammer' of_int_div fact_dvd_pochhammer
        pochhammer_of_int[symmetric])
qed

lemma uminus_one_gbinomial [simp]: "(- 1::int) gchoose k = (- 1) ^ k"
  by (simp add: gbinomial_int_binomial)

lemma gbinomial_int_Suc_Suc: "(x + 1::int) gchoose (Suc k) = (x gchoose k) + (x gchoose (Suc k))"
proof (rule linorder_cases)
  assume 1: "x + 1 < 0"
  hence 2: "x < 0" by simp
  then obtain n where 3: "nat (- x) = Suc n" using not0_implies_Suc by fastforce
  hence 4: "nat (- x - 1) = n" by simp
  show ?thesis
  proof (cases k)
    case 0
    show ?thesis by (simp add: \<open>k = 0\<close>)
  next
    case (Suc k')
    from 1 2 3 4 show ?thesis by (simp add: \<open>k = Suc k'\<close> gbinomial_int_binomial int_distrib(2))
  qed
next
  assume "x + 1 = 0"
  hence "x = - 1" by simp
  thus ?thesis by simp
next
  assume "0 < x + 1"
  hence "0 \<le> x + 1" and "0 \<le> x" and "nat (x + 1) = Suc (nat x)" by simp_all
  thus ?thesis by (simp add: gbinomial_int_binomial)
qed

corollary plus_Suc_gbinomial:
  "(x + (1 + int k)) gchoose (Suc k) = ((x + int k) gchoose k) + ((x + int k) gchoose (Suc k))"
    (is "?l = ?r")
proof -
  have "?l = (x + int k + 1) gchoose (Suc k)" by (simp only: ac_simps)
  also have "\<dots> = ?r" by (fact gbinomial_int_Suc_Suc)
  finally show ?thesis .
qed

lemma gbinomial_int_n_n [simp]: "(int n) gchoose n = 1"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "int (Suc n) gchoose Suc n = (int n + 1) gchoose Suc n" by (simp add: add.commute)
  also have "\<dots> = (int n gchoose n) + (int n gchoose (Suc n))" by (fact gbinomial_int_Suc_Suc)
  finally show ?case by (simp add: Suc gbinomial_eq_0)
qed

lemma gbinomial_int_Suc_n [simp]: "(1 + int n) gchoose n = 1 + int n"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "1 + int (Suc n) gchoose Suc n = (1 + int n) + 1 gchoose Suc n" by simp
  also have "\<dots> = (1 + int n gchoose n) + (1 + int n gchoose (Suc n))" by (fact gbinomial_int_Suc_Suc)
  also have "\<dots> = 1 + int n + (int (Suc n) gchoose (Suc n))" by (simp add: Suc)
  also have "\<dots> = 1 + int (Suc n)" by (simp only: gbinomial_int_n_n)
  finally show ?case .
qed

lemma zbinomial_eq_0_iff [simp]: "a gchoose k = 0 \<longleftrightarrow> (0 \<le> a \<and> a < int k)"
proof
  assume a: "a gchoose k = 0"
  have 1: "b < int k" if "b gchoose k = 0" for b
  proof (rule ccontr)
    assume "\<not> b < int k"
    hence "0 \<le> b" and "k \<le> nat b" by simp_all
    from this(1) have "int ((nat b) choose k) = b gchoose k" by (simp add: gbinomial_int_binomial)
    also have "\<dots> = 0" by (fact that)
    finally show False using \<open>k \<le> nat b\<close> by simp
  qed
  show "0 \<le> a \<and> a < int k"
  proof
    show "0 \<le> a"
    proof (rule ccontr)
      assume "\<not> 0 \<le> a"
      hence "(-1) ^ k * ((int k - a - 1) gchoose k) = a gchoose k"
        by (simp add: gbinomial_int_negated_upper[of a])
      also have "\<dots> = 0" by (fact a)
      finally have "(int k - a - 1) gchoose k = 0" by simp
      hence "int k - a - 1 < int k" by (rule 1)
      with \<open>\<not> 0 \<le> a\<close> show False by simp
    qed
  next
    from a show "a < int k" by (rule 1)
  qed
qed (auto intro: gbinomial_eq_0)

subsection \<open>Sums\<close>

lemma gchoose_rising_sum_nat: "(\<Sum>j\<le>n. int j + int k gchoose k) = (int n + int k + 1) gchoose (Suc k)"
proof -
  have "(\<Sum>j\<le>n. int j + int k gchoose k) = int (\<Sum>j\<le>n. k + j choose k)"
    by (simp add: int_binomial add.commute)
  also have "(\<Sum>j\<le>n. k + j choose k) = (k + n + 1) choose (k + 1)" by (fact choose_rising_sum(1))
  also have "int \<dots> = (int n + int k + 1) gchoose (Suc k)"
    by (simp add: int_binomial ac_simps del: binomial_Suc_Suc)
  finally show ?thesis .
qed

lemma gchoose_rising_sum:
  assumes "0 \<le> n"   \<comment>\<open>Necessary condition.\<close>
  shows "(\<Sum>j=0..n. j + int k gchoose k) = (n + int k + 1) gchoose (Suc k)"
proof -
  from _ refl have "(\<Sum>j=0..n. j + int k gchoose k) = (\<Sum>j\<in>int ` {0..nat n}. j + int k gchoose k)"
  proof (rule sum.cong)
    from assms show "{0..n} = int ` {0..nat n}" by (simp add: image_int_atLeastAtMost)
  qed
  also have "\<dots> = (\<Sum>j\<le>nat n. int j + int k gchoose k)" by (simp add: sum.reindex atMost_atLeast0)
  also have "\<dots> = (int (nat n) + int k + 1) gchoose (Suc k)" by (fact gchoose_rising_sum_nat)
  also from assms have "\<dots> = (n + int k + 1) gchoose (Suc k)" by (simp add: add.assoc add.commute)
  finally show ?thesis .
qed

end (* theory *)
