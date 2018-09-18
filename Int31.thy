(* Author: Alexander Maletzky *)

section \<open>31-Bit Machine Integers\<close>

theory Int31
  imports "HOL-Library.Code_Target_Numeral" "Signature_Groebner/Prelims" Print
begin

subsection \<open>Carrier Sets for Arbitrary Bit-Size\<close>

definition int_carrier :: "nat \<Rightarrow> int set"
  where "int_carrier n = {a. - (2 ^ n) \<le> a \<and> a < 2 ^ n}"

definition sym_interval :: "nat \<Rightarrow> (int set) \<Rightarrow> bool"
  where "sym_interval n A \<longleftrightarrow> (A \<subseteq> int_carrier n \<and> (\<forall>a\<in>A. \<forall>b. abs b \<le> abs a \<longrightarrow> b \<in> A))"

abbreviation uminus_dom :: "nat \<Rightarrow> int set"
  where "uminus_dom n \<equiv> {a. abs a \<in> int_carrier n}"

abbreviation plus_dom :: "nat \<Rightarrow> int set"
  where "plus_dom n \<equiv> {a. 2 * abs a \<in> int_carrier n}"

abbreviation times_dom :: "nat \<Rightarrow> int set"
  where "times_dom n \<equiv> {a. a ^ 2 \<in> int_carrier n}"

subsubsection \<open>@{const sym_interval}\<close>

lemma sym_intervalD:
  assumes "sym_interval n A"
  shows "A \<subseteq> int_carrier n" and "\<And>a b. a \<in> A \<Longrightarrow> abs b \<le> abs a \<Longrightarrow> b \<in> A"
  using assms by (simp_all add: sym_interval_def)

lemma sym_interval_closed_sgn:
  assumes "sym_interval n A" and "a \<in> A"
  shows "sgn a \<in> A"
proof -
  have "abs (sgn a) \<le> abs a" by auto
  with assms show ?thesis by (rule sym_intervalD)
qed

lemma sym_interval_closed_abs:
  assumes "sym_interval n A" and "a \<in> A"
  shows "abs a \<in> A"
proof -
  have "abs (abs a) \<le> abs a" by simp
  with assms show ?thesis by (rule sym_intervalD)
qed

lemma sym_interval_closed_uminus:
  assumes "sym_interval n A" and "a \<in> A"
  shows "- a \<in> A"
proof -
  have "abs (- a) \<le> abs a" by simp
  with assms show ?thesis by (rule sym_intervalD)
qed

lemma sym_interval_closed_divide:
  assumes "sym_interval n A" and "a \<in> A"
  shows "a div b \<in> A"
proof (cases "a = 0")
  case True
  hence "a div b = a" by simp
  show ?thesis unfolding \<open>a div b = a\<close> by (fact assms(2))
next
  case False
  have 1: "nat \<bar>a\<bar> div nat \<bar>b\<bar> \<le> nat \<bar>a\<bar>" by (fact div_le_dividend)
  hence 2: "int (nat \<bar>a\<bar> div nat \<bar>b\<bar>) \<le> \<bar>a\<bar>" by linarith
  have "abs (a div b) \<le> abs a"
  proof (simp add: divide_int_def 2, intro impI)
    assume "\<not> b dvd a"
    have "nat \<bar>a\<bar> div nat \<bar>b\<bar> \<noteq> nat \<bar>a\<bar>"
    proof
      from False have "0 < nat (abs a)" by simp
      moreover assume "nat \<bar>a\<bar> div nat \<bar>b\<bar> = nat \<bar>a\<bar>"
      ultimately have "nat (abs b) = 1" by (simp only: div_eq_dividend_iff)
      hence "abs b = 1" by simp
      hence "abs b dvd abs a" by simp
      hence "b dvd a" by simp
      with \<open>\<not> b dvd a\<close> show False ..
    qed
    with 1 have "nat \<bar>a\<bar> div nat \<bar>b\<bar> < nat \<bar>a\<bar>" by (rule le_neq_implies_less)
    thus "1 + int (nat \<bar>a\<bar> div nat \<bar>b\<bar>) \<le> \<bar>a\<bar>" by linarith
  qed
  with assms show ?thesis by (rule sym_intervalD)
qed

lemma sym_interval_closed_modulo:
  assumes "sym_interval n A" and "a \<in> A" and "b \<in> A"
    \<comment>\<open>Instead of @{prop "a \<in> A"} one could also require @{prop "b \<noteq> 0"}, using @{thm mod_le_divisor}.\<close>
  shows "a mod b \<in> A"
proof -
  have "nat \<bar>a\<bar> mod nat \<bar>b\<bar> \<le> nat \<bar>a\<bar>" by (fact mod_less_eq_dividend)
  hence "int (nat \<bar>a\<bar> mod nat \<bar>b\<bar>) \<le> \<bar>a\<bar>" by linarith
  also have "... \<le> max \<bar>a\<bar> \<bar>b\<bar>" by simp
  finally have *: "int (nat \<bar>a\<bar> mod nat \<bar>b\<bar>) \<le> max \<bar>a\<bar> \<bar>b\<bar>" .
  have "abs (a mod b) \<le> max (abs a) (abs b)"
  proof (simp add: modulo_int_def abs_mult * abs_diff_le_iff diff_le_eq, intro impI conjI)
    note *
    also have "... \<le> \<bar>b\<bar> + max \<bar>a\<bar> \<bar>b\<bar>" by simp
    finally show "int (nat \<bar>a\<bar> mod nat \<bar>b\<bar>) \<le> \<bar>b\<bar> + max \<bar>a\<bar> \<bar>b\<bar>" .
  next
    show "\<bar>b\<bar> \<le> int (nat \<bar>a\<bar> mod nat \<bar>b\<bar>) + max \<bar>a\<bar> \<bar>b\<bar>" by simp
  next
    have "0 \<le> \<bar>a\<bar>" by simp
    also have "... \<le> max \<bar>a\<bar> \<bar>b\<bar>" by simp
    finally show "0 \<le> max \<bar>a\<bar> \<bar>b\<bar>" .
  qed
  hence "abs (a mod b) \<le> abs a \<or> abs (a mod b) \<le> abs b" by auto
  thus ?thesis
  proof
    assume "\<bar>a mod b\<bar> \<le> \<bar>a\<bar>"
    with assms(1, 2) show ?thesis by (rule sym_intervalD)
  next
    assume "\<bar>a mod b\<bar> \<le> \<bar>b\<bar>"
    with assms(1, 3) show ?thesis by (rule sym_intervalD)
  qed
qed

lemma sym_interval_closed_gcd:
  assumes "sym_interval n A" and "a \<in> A" and "b \<in> A"
  shows "gcd a b \<in> A"
proof (cases "a = 0")
  case True
  hence "abs (gcd a b) \<le> abs b" by simp
  with assms(1, 3) show ?thesis by (rule sym_intervalD)
next
  case False
  hence "0 < abs a" by simp
  hence "gcd (abs a) b \<le> abs a" by (rule gcd_le1_int)
  hence "abs (gcd a b) \<le> abs a" by simp
  with assms(1, 2) show ?thesis by (rule sym_intervalD)
qed

subsubsection \<open>Other\<close>

lemma zero_in_int_carrier: "0 \<in> int_carrier n"
  by (simp add: int_carrier_def)

lemma int_carrier_le: "a \<in> int_carrier n \<Longrightarrow> - (2 ^ n) \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> b \<in> int_carrier n"
  by (auto simp: int_carrier_def)

lemma uminus_domI: "abs a < 2 ^ n \<Longrightarrow> a \<in> uminus_dom n"
  by (auto simp: int_carrier_def)

lemma uminus_domD:
  assumes "a \<in> uminus_dom n"
  shows "- (2 ^ n) < a" and "a < 2 ^ n"
  using assms by (auto simp: int_carrier_def)

lemma uminus_dom_subset_int_carrier: "a \<in> uminus_dom n \<Longrightarrow> a \<in> int_carrier n"
  by (auto simp: int_carrier_def)

lemma sym_interval_uminus_dom [simp]: "sym_interval n (uminus_dom n)"
  unfolding sym_interval_def
proof (intro conjI ballI allI impI)
  from uminus_dom_subset_int_carrier show "uminus_dom n \<subseteq> int_carrier n" ..
next
  fix a b :: int
  assume "a \<in> uminus_dom n"
  hence "abs a < 2 ^ n" by (simp add: int_carrier_def)
  assume "abs b \<le> abs a"
  also have "... < 2 ^ n" by fact
  finally show "b \<in> uminus_dom n" by (rule uminus_domI)
qed

lemma plus_domI: "2 * abs a < 2 ^ n \<Longrightarrow> a \<in> plus_dom n"
  by (auto simp: int_carrier_def)

lemma plus_domD:
  assumes "a \<in> plus_dom n"
  shows "- (2 ^ n) < 2 * a" and "2 * a < 2 ^ n"
  using assms by (auto simp: int_carrier_def)

lemma plus_dom_subset_uminus_dom: "a \<in> plus_dom n \<Longrightarrow> a \<in> uminus_dom n"
  by (auto simp: int_carrier_def)

corollary plus_dom_subset_int_carrier: "a \<in> plus_dom n \<Longrightarrow> a \<in> int_carrier n"
  by (intro uminus_dom_subset_int_carrier plus_dom_subset_uminus_dom)

lemma sym_interval_plus_dom [simp]: "sym_interval n (plus_dom n)"
  unfolding sym_interval_def
proof (intro conjI ballI allI impI)
  from plus_dom_subset_int_carrier show "plus_dom n \<subseteq> int_carrier n" ..
next
  fix a b :: int
  assume "a \<in> plus_dom n"
  hence "2 * abs a < 2 ^ n" by (simp add: int_carrier_def)
  assume "abs b \<le> abs a"
  hence "2 * abs b \<le> 2 * abs a" by simp
  also have "... < 2 ^ n" by fact
  finally show "b \<in> plus_dom n" by (rule plus_domI)
qed

lemma times_domI: "a ^ 2 < 2 ^ n \<Longrightarrow> a \<in> times_dom n"
  by (simp add: int_carrier_def) (smt power2_less_0)

lemma times_domD:
  assumes "a \<in> times_dom n"
  shows "- (2 ^ n) < a ^ 2" and "a ^ 2 < 2 ^ n"
  using assms by (simp_all add: int_carrier_def) (smt zero_le_power2)

lemma times_dom_subset_plus_dom:
  assumes "1 < n" and "a \<in> times_dom n"
  shows "a \<in> plus_dom n"
proof (cases "abs a < 2")
  case True
  hence "2 * abs a \<le> 2" by simp
  also from assms(1) have "... < 2 ^ n" by (smt power_one_right power_strict_increasing)
  finally show ?thesis by (rule plus_domI)
next
  case False
  show ?thesis
  proof (simp, rule int_carrier_le)
    from assms(2) show "a ^ 2 \<in> int_carrier n" by simp
  next
    show "- (2 ^ n) \<le> 2 * \<bar>a\<bar>" by (smt zero_less_power)
  next
    from False have "2 \<le> abs a" by simp
    moreover have "0 \<le> abs a" by simp
    ultimately have "abs a * 2 \<le> abs a * abs a" by (rule mult_left_mono)
    thus "2 * abs a \<le> a ^ 2" by (simp add: power_def)
  qed
qed

lemma times_dom_subset_uminus_dom:
  assumes "a \<in> times_dom n"
  shows "a \<in> uminus_dom n"
proof -
  have rl: "b \<le> b ^ 2" for b::int by (smt self_le_power zero_le_power2 zero_less_numeral)
  hence "- a \<le> (- a) ^ 2" .
  also have "... = a ^ 2" by simp
  finally have "- (a ^ 2) \<le> a" by simp
  from assms have "a ^ 2 < 2 ^ n" by (rule times_domD)
  hence "- (2 ^ n) < - (a ^ 2)" by simp
  also have "... \<le> a" by fact
  finally have 1: "- (2 ^ n) < a" .
  note rl
  also from assms have "a ^ 2 < 2 ^ n" by (rule times_domD)
  finally show ?thesis using 1 by (auto simp: int_carrier_def)
qed

corollary times_dom_subset_int_carrier: "a \<in> times_dom n \<Longrightarrow> a \<in> int_carrier n"
  by (intro uminus_dom_subset_int_carrier times_dom_subset_uminus_dom)

lemma sym_interval_times_dom [simp]: "sym_interval n (times_dom n)"
  unfolding sym_interval_def
proof (intro conjI allI ballI impI)
  from times_dom_subset_int_carrier show "times_dom n \<subseteq> int_carrier n" ..
next
  fix a b :: int
  assume "a \<in> times_dom n"
  hence "a ^ 2 < 2 ^ n" by (rule times_domD)
  assume "abs b \<le> abs a"
  moreover have "0 \<le> abs b" by simp
  ultimately have "abs b ^ 2 \<le> abs a ^ 2" by (rule power_mono)
  hence "b ^ 2 \<le> a ^ 2" by simp
  also have "... < 2 ^ n" by fact
  finally show "b \<in> times_dom n" by (rule times_domI)
qed

lemma uminus_dom_closed_plus:
  assumes "a \<in> plus_dom n" and "b \<in> plus_dom n"
  shows "a + b \<in> uminus_dom n"
proof (cases "a \<le> b")
  case True
  from assms(1) have "- (2 ^ n) < 2 * a" by (rule plus_domD)
  also from True have "... \<le> a + b" by simp
  finally have 1: "- (2 ^ n) < a + b" .
  from True have "a + b \<le> 2 * b" by simp
  also from assms(2) have "... < 2 ^ n" by (rule plus_domD)
  finally show ?thesis using 1 by (auto simp: int_carrier_def)
next
  case False
  from assms(2) have "- (2 ^ n) < 2 * b" by (rule plus_domD)
  also from False have "... \<le> a + b" by simp
  finally have 1: "- (2 ^ n) < a + b" .
  from False have "a + b \<le> 2 * a" by simp
  also from assms(1) have "... < 2 ^ n" by (rule plus_domD)
  finally show ?thesis using 1 by (auto simp: int_carrier_def)
qed

corollary int_carrier_closed_plus: "a \<in> plus_dom n \<Longrightarrow> b \<in> plus_dom n \<Longrightarrow> a + b \<in> int_carrier n"
  by (intro uminus_dom_subset_int_carrier uminus_dom_closed_plus)

lemma uminus_dom_closed_minus:
  assumes "a \<in> plus_dom n" and "b \<in> plus_dom n"
  shows "a - b \<in> uminus_dom n"
proof -
  from sym_interval_plus_dom assms(2) have "- b \<in> plus_dom n" by (rule sym_interval_closed_uminus)
  with assms(1) have "a + (- b) \<in> uminus_dom n" by (rule uminus_dom_closed_plus)
  thus ?thesis by simp
qed

corollary int_carrier_closed_minus: "a \<in> plus_dom n \<Longrightarrow> b \<in> plus_dom n \<Longrightarrow> a - b \<in> int_carrier n"
  by (intro uminus_dom_subset_int_carrier uminus_dom_closed_minus)

lemma uminus_dom_closed_times:
  assumes "a \<in> times_dom n" and "b \<in> times_dom n"
  shows "a * b \<in> uminus_dom n"
proof -
  have "abs (a * b) < 2 ^ n"
  proof (cases "abs a \<le> abs b")
    case True
    moreover have "0 \<le> abs b" by simp
    ultimately have "abs b * abs a \<le> abs b * abs b" by (rule mult_left_mono)
    hence "abs (a * b) \<le> b ^ 2" by (simp add: ac_simps abs_mult power_def)
    also from assms(2) have "... < 2 ^ n" by (rule times_domD)
    finally show "abs (a * b) < 2 ^ n" .
  next
    case False
    hence "abs b \<le> abs a" by simp
    moreover have "0 \<le> abs a" by simp
    ultimately have "abs a * abs b \<le> abs a * abs a" by (rule mult_left_mono)
    hence "abs (a * b) \<le> a ^ 2" by (simp add: abs_mult power_def)
    also from assms(1) have "... < 2 ^ n" by (rule times_domD)
    finally show "abs (a * b) < 2 ^ n" .
  qed
  thus ?thesis by (rule uminus_domI)
qed

corollary int_carrier_closed_times: "a \<in> times_dom n \<Longrightarrow> b \<in> times_dom n \<Longrightarrow> a * b \<in> int_carrier n"
  by (intro uminus_dom_subset_int_carrier uminus_dom_closed_times)

subsection \<open>Abstract Type of \<open>n\<close>-Bit Integers\<close>

locale intN =
  fixes n :: nat
    and int_of_intN :: "'a \<Rightarrow> int"
    and intN_of_int :: "int \<Rightarrow> 'a"
  assumes n_gr_one: "1 < n"
    and int_of_intN_inverse: "intN_of_int (int_of_intN x) = x"
    and intN_of_int_inverse: "a \<in> int_carrier n \<Longrightarrow> int_of_intN (intN_of_int a) = a"
begin

definition integer_of_intN :: "'a \<Rightarrow> integer"
  where "integer_of_intN = integer_of_int \<circ> int_of_intN"

definition intN_of_integer :: "integer \<Rightarrow> 'a"
  where "intN_of_integer = intN_of_int \<circ> int_of_integer"

lemma int_of_intN_code: "int_of_intN a = int_of_integer (integer_of_intN a)"
  by (simp add: integer_of_intN_def)

lemma intN_of_int_code: "intN_of_int a = intN_of_integer (integer_of_int a)"
  by (simp add: intN_of_integer_def)

lemma int_of_intN_inject:
  assumes "int_of_intN x = int_of_intN y"
  shows "x = y"
proof -
  have "x = intN_of_int (int_of_intN x)" by (simp only: int_of_intN_inverse)
  also from assms have "... = intN_of_int (int_of_intN y)" by simp
  also have "... = y" by (simp only: int_of_intN_inverse)
  finally show ?thesis .
qed

lemma inj_int_of_intN: "inj int_of_intN"
  by (simp add: inj_def int_of_intN_inject)

subsubsection \<open>Order\<close>

definition less_eq_intN :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<le>n" 50)
  where "less_eq_intN = (\<lambda>x y. int_of_intN x \<le> int_of_intN y)"

definition less_intN :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "<n" 50)
  where "less_intN = (\<lambda>x y. int_of_intN x < int_of_intN y)"

lemma linorder_intN: "class.linorder (\<le>n) (<n)"
  by standard (auto simp: less_eq_intN_def less_intN_def dest: int_of_intN_inject)

subsubsection \<open>Sign, Abs\<close>

definition sym_intervalN :: "'a set \<Rightarrow> bool"
  where "sym_intervalN A \<longleftrightarrow> sym_interval n (int_of_intN ` A)"

definition sgn_intN :: "'a \<Rightarrow> 'a"
  where "sgn_intN = (\<lambda>x. intN_of_int (sgn (int_of_intN x)))"

definition abs_intN :: "'a \<Rightarrow> 'a"
  where "abs_intN = (\<lambda>x. intN_of_int (abs (int_of_intN x)))"

lemma int_of_intN_sgn: "int_of_intN (sgn_intN x) = sgn (int_of_intN x)"
  unfolding sgn_intN_def
  by (rule intN_of_int_inverse, simp add: zsgn_def int_carrier_def)
    (smt n_gr_one power_one_right power_strict_increasing)

lemma
  assumes "x \<in> A" and "sym_intervalN A"
  shows int_of_intN_abs: "int_of_intN (abs_intN x) = abs (int_of_intN x)"
    and sym_intervalN_closed_abs: "abs_intN x \<in> A"
proof -
  from assms(2) have 1: "sym_interval n (int_of_intN ` A)" by (simp only: sym_intervalN_def)
  moreover from assms(1) have 2: "int_of_intN x \<in> int_of_intN ` A" by (rule imageI)
  moreover have "abs (abs (int_of_intN x)) \<le> abs (int_of_intN x)" by simp
  ultimately have "abs (int_of_intN x) \<in> int_of_intN ` A" by (rule sym_intervalD)
  also from 1 have "... \<subseteq> int_carrier n" by (rule sym_intervalD)
  finally show "int_of_intN (abs_intN x) = abs (int_of_intN x)"
    unfolding abs_intN_def by (rule intN_of_int_inverse)
  also from 1 2 have "... \<in> int_of_intN ` A" by (rule sym_interval_closed_abs)
  finally show "abs_intN x \<in> A" using inj_int_of_intN by (simp only: inj_image_mem_iff)
qed

subsubsection \<open>Addition\<close>

definition uminus_domN :: "'a set"
  where "uminus_domN = intN_of_int ` uminus_dom n"

definition plus_domN :: "'a set"
  where "plus_domN = intN_of_int ` plus_dom n"

lemma int_of_intN_uminus_dom: "int_of_intN ` uminus_domN = uminus_dom n"
proof -
  have "int_of_intN ` uminus_domN = (\<lambda>a. int_of_intN (intN_of_int a)) ` uminus_dom n"
    by (simp only: uminus_domN_def image_image)
  also from refl have "... = (\<lambda>a. a) ` uminus_dom n"
  proof (rule image_cong)
    fix a
    assume "a \<in> uminus_dom n"
    hence "a \<in> int_carrier n" by (rule uminus_dom_subset_int_carrier)
    thus "int_of_intN (intN_of_int a) = a" by (rule intN_of_int_inverse)
  qed
  finally show ?thesis by simp
qed

lemma uminus_domN_iff: "x \<in> uminus_domN \<longleftrightarrow> int_of_intN x \<in> uminus_dom n"
proof
  assume "x \<in> uminus_domN"
  hence "int_of_intN x \<in> int_of_intN ` uminus_domN" by (rule imageI)
  thus "int_of_intN x \<in> uminus_dom n" by (simp only: int_of_intN_uminus_dom)
next
  assume "int_of_intN x \<in> uminus_dom n"
  hence "intN_of_int (int_of_intN x) \<in> intN_of_int ` uminus_dom n" by (rule imageI)
  thus "x \<in> uminus_domN" by (simp only: uminus_domN_def int_of_intN_inverse)
qed

lemma sym_interval_uminus_domN [simp]: "sym_intervalN uminus_domN"
  by (simp add: sym_intervalN_def int_of_intN_uminus_dom)

lemma int_of_intN_plus_dom: "int_of_intN ` plus_domN = plus_dom n"
proof -
  have "int_of_intN ` plus_domN = (\<lambda>a. int_of_intN (intN_of_int a)) ` plus_dom n"
    by (simp only: plus_domN_def image_image)
  also from refl have "... = (\<lambda>a. a) ` plus_dom n"
  proof (rule image_cong)
    fix a
    assume "a \<in> plus_dom n"
    hence "a \<in> int_carrier n" by (rule plus_dom_subset_int_carrier)
    thus "int_of_intN (intN_of_int a) = a" by (rule intN_of_int_inverse)
  qed
  finally show ?thesis by simp
qed

lemma plus_domN_iff: "x \<in> plus_domN \<longleftrightarrow> int_of_intN x \<in> plus_dom n"
proof
  assume "x \<in> plus_domN"
  hence "int_of_intN x \<in> int_of_intN ` plus_domN" by (rule imageI)
  thus "int_of_intN x \<in> plus_dom n" by (simp only: int_of_intN_plus_dom)
next
  assume "int_of_intN x \<in> plus_dom n"
  hence "intN_of_int (int_of_intN x) \<in> intN_of_int ` plus_dom n" by (rule imageI)
  thus "x \<in> plus_domN" by (simp only: plus_domN_def int_of_intN_inverse)
qed

lemma sym_interval_plus_domN [simp]: "sym_intervalN plus_domN"
  by (simp add: sym_intervalN_def int_of_intN_plus_dom)

lemma plus_dom_subset_uminus_domN: "plus_domN \<subseteq> uminus_domN"
  unfolding plus_domN_def uminus_domN_def
  by (rule image_mono, rule, rule plus_dom_subset_uminus_dom)

definition zero_intN :: 'a ("0n")
  where "zero_intN = intN_of_int 0"

lemma int_of_intN_zero: "int_of_intN 0n = 0"
  unfolding zero_intN_def using zero_in_int_carrier by (rule intN_of_int_inverse)

lemma intN_of_int_zero: "intN_of_int 0 = 0n"
  by (simp only: int_of_intN_zero[symmetric] int_of_intN_inverse)

definition plus_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+n" 65)
  where "plus_intN = (\<lambda>x y. intN_of_int (int_of_intN x + int_of_intN y))"

lemma int_of_intN_plus:
  assumes "x \<in> plus_domN" and "y \<in> plus_domN"
  shows "int_of_intN (x +n y) = int_of_intN x + int_of_intN y"
  unfolding plus_intN_def
proof (rule intN_of_int_inverse, rule int_carrier_closed_plus)
  from assms(1) show "int_of_intN x \<in> plus_dom n" by (simp only: plus_domN_iff)
next
  from assms(2) show "int_of_intN y \<in> plus_dom n" by (simp only: plus_domN_iff)
qed

lemma uminus_domN_closed_plus:
  assumes "x \<in> plus_domN" and "y \<in> plus_domN"
  shows "x +n y \<in> uminus_domN"
proof -
  from assms(1) have "int_of_intN x \<in> plus_dom n" by (simp only: plus_domN_iff)
  moreover from assms(2) have "int_of_intN y \<in> plus_dom n" by (simp only: plus_domN_iff)
  ultimately have "int_of_intN x + int_of_intN y \<in> uminus_dom n" by (rule uminus_dom_closed_plus)
  with assms show ?thesis by (simp add: int_of_intN_plus uminus_domN_iff)
qed

lemma plus_intN_zero_neutr [simp]: "x +n 0n = x" "0n +n x = x"
  by (simp_all add: plus_intN_def int_of_intN_zero int_of_intN_inverse)

lemma plus_intN_comm [ac_simps]: "x +n y = y +n x"
  by (simp add: plus_intN_def ac_simps int_of_intN_inverse)

definition uminus_intN :: "'a \<Rightarrow> 'a" ("-n _" [81] 80)
  where "uminus_intN = (\<lambda>x. intN_of_int (- int_of_intN x))"

lemma
  assumes "a \<in> A" and "sym_intervalN A"
  shows int_of_intN_uminus: "int_of_intN (-n a) = - (int_of_intN a)"
    and sym_intervalN_closed_uminus: "-n a \<in> A"
proof -
  from assms(2) have 1: "sym_interval n (int_of_intN ` A)" by (simp only: sym_intervalN_def)
  moreover from assms(1) have 2: "int_of_intN a \<in> int_of_intN ` A" by (rule imageI)
  moreover have "abs (- int_of_intN a) \<le> abs (int_of_intN a)" by simp
  ultimately have "- int_of_intN a \<in> int_of_intN ` A" by (rule sym_intervalD)
  also from 1 have "... \<subseteq> int_carrier n" by (rule sym_intervalD)
  finally show "int_of_intN (-n a) = - (int_of_intN a)"
    unfolding uminus_intN_def by (rule intN_of_int_inverse)
  also from 1 2 have "... \<in> int_of_intN ` A" by (rule sym_interval_closed_uminus)
  finally show "-n a \<in> A" using inj_int_of_intN by (simp only: inj_image_mem_iff)
qed

lemma uminus_zero_intN [simp]: "-n 0n = 0n"
  by (simp add: uminus_intN_def int_of_intN_zero intN_of_int_zero)

definition minus_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-n" 65)
  where "minus_intN = (\<lambda>x y. intN_of_int (int_of_intN x - int_of_intN y))"

lemma int_of_intN_minus:
  assumes "x \<in> plus_domN" and "y \<in> plus_domN"
  shows "int_of_intN (x -n y) = int_of_intN x - int_of_intN y"
  unfolding minus_intN_def
proof (rule intN_of_int_inverse, rule int_carrier_closed_minus)
  from assms(1) show "int_of_intN x \<in> plus_dom n" by (simp only: plus_domN_iff)
next
  from assms(2) show "int_of_intN y \<in> plus_dom n" by (simp only: plus_domN_iff)
qed

lemma uminus_domN_closed_minus:
  assumes "x \<in> plus_domN" and "y \<in> plus_domN"
  shows "x -n y \<in> uminus_domN"
proof -
  from assms(1) have "int_of_intN x \<in> plus_dom n" by (simp only: plus_domN_iff)
  moreover from assms(2) have "int_of_intN y \<in> plus_dom n" by (simp only: plus_domN_iff)
  ultimately have "int_of_intN x - int_of_intN y \<in> uminus_dom n" by (rule uminus_dom_closed_minus)
  with assms show ?thesis by (simp add: int_of_intN_minus uminus_domN_iff)
qed

lemma minus_intN_zero_neutr [simp]: "x -n 0n = x"
  by (simp add: minus_intN_def int_of_intN_zero int_of_intN_inverse)

lemma minus_intN_inverse [simp]: "x -n x = 0n"
  by (simp add: minus_intN_def intN_of_int_zero)

lemma add_uminus_conv_diff_intN:
  assumes "x \<in> plus_domN" and "y \<in> plus_domN"
  shows "x +n (-n y) = x -n y"
proof (rule int_of_intN_inject)
  from assms(2) sym_interval_plus_domN have "-n y \<in> plus_domN"
    by (rule sym_intervalN_closed_uminus)
  with assms show "int_of_intN (x +n (-n y)) = int_of_intN (x -n y)"
    by (auto simp: int_of_intN_plus int_of_intN_minus int_of_intN_uminus)
qed

lemma uminus_plusN:
  assumes "x \<in> plus_domN" and "y \<in> plus_domN"
  shows "-n (x +n y) = (-n x) +n (-n y)"
proof (rule int_of_intN_inject)
  from assms have "x +n y \<in> uminus_domN" by (rule uminus_domN_closed_plus)
  moreover from assms(1) sym_interval_plus_domN have "-n x \<in> plus_domN"
    by (rule sym_intervalN_closed_uminus)
  moreover from assms(2) sym_interval_plus_domN have "-n y \<in> plus_domN"
    by (rule sym_intervalN_closed_uminus)
  ultimately show "int_of_intN (-n (x +n y)) = int_of_intN (-n x +n -n y)" using assms
    by (simp add: int_of_intN_uminus int_of_intN_plus)
qed

subsubsection \<open>Multiplication\<close>

definition times_domN :: "'a set"
  where "times_domN = intN_of_int ` times_dom n"

lemma int_of_intN_times_dom: "int_of_intN ` times_domN = times_dom n"
proof -
  have "int_of_intN ` times_domN = (\<lambda>a. int_of_intN (intN_of_int a)) ` times_dom n"
    by (simp only: times_domN_def image_image)
  also from refl have "... = (\<lambda>a. a) ` times_dom n"
  proof (rule image_cong)
    fix a
    assume "a \<in> times_dom n"
    hence "a \<in> int_carrier n" by (rule times_dom_subset_int_carrier)
    thus "int_of_intN (intN_of_int a) = a" by (rule intN_of_int_inverse)
  qed
  finally show ?thesis by simp
qed

lemma times_domN_iff: "x \<in> times_domN \<longleftrightarrow> int_of_intN x \<in> times_dom n"
proof
  assume "x \<in> times_domN"
  hence "int_of_intN x \<in> int_of_intN ` times_domN" by (rule imageI)
  thus "int_of_intN x \<in> times_dom n" by (simp only: int_of_intN_times_dom)
next
  assume "int_of_intN x \<in> times_dom n"
  hence "intN_of_int (int_of_intN x) \<in> intN_of_int ` times_dom n" by (rule imageI)
  thus "x \<in> times_domN" by (simp only: times_domN_def int_of_intN_inverse)
qed

lemma sym_interval_times_domN [simp]: "sym_intervalN times_domN"
  by (simp add: sym_intervalN_def int_of_intN_times_dom)

lemma times_dom_subset_plus_domN: "times_domN \<subseteq> plus_domN"
  unfolding times_domN_def plus_domN_def
proof (rule image_mono, rule)
  fix a
  assume "a \<in> times_dom n"
  with n_gr_one show "a \<in> plus_dom n" by (rule times_dom_subset_plus_dom)
qed

definition one_intN :: 'a ("1n")
  where "one_intN = intN_of_int 1"

lemma int_of_intN_one: "int_of_intN 1n = 1"
  unfolding one_intN_def
  by (rule intN_of_int_inverse, simp add: int_carrier_def)
    (smt n_gr_one one_le_power power_strict_increasing)

lemma intN_of_int_one: "intN_of_int 1 = 1n"
  by (simp add: int_of_intN_one[symmetric] int_of_intN_inverse)

definition times_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*n" 70)
  where "times_intN = (\<lambda>x y. intN_of_int (int_of_intN x * int_of_intN y))"

lemma int_of_intN_times:
  assumes "x \<in> times_domN" and "y \<in> times_domN"
  shows "int_of_intN (x *n y) = int_of_intN x * int_of_intN y"
  unfolding times_intN_def
proof (rule intN_of_int_inverse, rule int_carrier_closed_times)
  from assms(1) show "int_of_intN x \<in> times_dom n" by (simp only: times_domN_iff)
next
  from assms(2) show "int_of_intN y \<in> times_dom n" by (simp only: times_domN_iff)
qed

lemma uminus_domN_closed_times:
  assumes "x \<in> times_domN" and "y \<in> times_domN"
  shows "x *n y \<in> uminus_domN"
proof -
  from assms(1) have "int_of_intN x \<in> times_dom n" by (simp only: times_domN_iff)
  moreover from assms(2) have "int_of_intN y \<in> times_dom n" by (simp only: times_domN_iff)
  ultimately have "int_of_intN x * int_of_intN y \<in> uminus_dom n" by (rule uminus_dom_closed_times)
  with assms show ?thesis by (simp add: int_of_intN_times uminus_domN_iff)
qed

lemma times_intN_zero_annihil [simp]: "x *n 0n = 0n" "0n *n x = 0n"
  by (simp_all add: times_intN_def int_of_intN_zero intN_of_int_zero)

lemma times_intN_one_neutr [simp]: "x *n 1n = x" "1n *n x = x"
  by (simp_all add: times_intN_def int_of_intN_one int_of_intN_inverse)

lemma times_intN_comm [ac_simps]: "x *n y = y *n x"
  by (simp add: times_intN_def ac_simps int_of_intN_inverse)

lemma times_uminusN_left:
  assumes "x \<in> times_domN" and "y \<in> times_domN"
  shows "-n x *n y = -n (x *n y)"
proof (rule int_of_intN_inject)
  from assms have "x *n y \<in> uminus_domN" by (rule uminus_domN_closed_times)
  moreover from assms(1) sym_interval_times_domN have "-n x \<in> times_domN"
    by (rule sym_intervalN_closed_uminus)
  moreover from assms(2) sym_interval_times_domN have "-n y \<in> times_domN"
    by (rule sym_intervalN_closed_uminus)
  ultimately show "int_of_intN (-n x *n y) = int_of_intN (-n (x *n y))" using assms
    by (simp add: int_of_intN_uminus int_of_intN_times)
qed

corollary times_uminusN_right: "x \<in> times_domN \<Longrightarrow> y \<in> times_domN \<Longrightarrow> x *n (-n y) = -n (x *n y)"
  by (simp add: times_uminusN_left times_intN_comm[of x])

lemma uminus_times_uminusN: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> sym_intervalN A \<Longrightarrow> (-n x) *n (-n y) = x *n y"
  by (simp add: times_intN_def int_of_intN_uminus)

definition divide_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "divn" 70)
  where "divide_intN = (\<lambda>x y. if y = 0n then undefined else intN_of_int (int_of_intN x div int_of_intN y))"

lemma
  assumes "x \<in> A" and "y \<noteq> 0n" and "sym_intervalN A"
  shows int_of_intN_divide: "int_of_intN (x divn y) = int_of_intN x div int_of_intN y"
    and sym_intervalN_closed_divide: "x divn y \<in> A"
proof -
  from assms(3) have 1: "sym_interval n (int_of_intN ` A)" by (simp only: sym_intervalN_def)
  moreover from assms(1) have 2: "int_of_intN x \<in> int_of_intN ` A" by (rule imageI)
  ultimately have "int_of_intN x div int_of_intN y \<in> int_of_intN ` A"
    by (rule sym_interval_closed_divide)
  also from 1 have "... \<subseteq> int_carrier n" by (rule sym_intervalD)
  finally have "int_of_intN (intN_of_int (int_of_intN x div int_of_intN y)) =
                int_of_intN x div int_of_intN y"
    by (rule intN_of_int_inverse)
  with assms(2) show "int_of_intN (x divn y) = int_of_intN x div int_of_intN y"
    by (simp add: divide_intN_def)
  also from 1 2 have "... \<in> int_of_intN ` A" by (rule sym_interval_closed_divide)
  finally show "x divn y \<in> A" using inj_int_of_intN by (simp only: inj_image_mem_iff)
qed

definition modulo_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "modn" 70)
  where "modulo_intN = (\<lambda>x y. if y = 0n then undefined else intN_of_int (int_of_intN x mod int_of_intN y))"

lemma
  assumes "x \<in> A" and "y \<in> A" and "y \<noteq> 0n" and "sym_intervalN A"
  shows int_of_intN_modulo: "int_of_intN (x modn y) = int_of_intN x mod int_of_intN y"
    and sym_intervalN_closed_modulo: "x modn y \<in> A"
proof -
  from assms(4) have 1: "sym_interval n (int_of_intN ` A)" by (simp only: sym_intervalN_def)
  moreover from assms(1) have 2: "int_of_intN x \<in> int_of_intN ` A" by (rule imageI)
  moreover from assms(2) have 3: "int_of_intN y \<in> int_of_intN ` A" by (rule imageI)
  ultimately have "int_of_intN x mod int_of_intN y \<in> int_of_intN ` A"
    by (rule sym_interval_closed_modulo)
  also from 1 have "... \<subseteq> int_carrier n" by (rule sym_intervalD)
  finally have "int_of_intN (intN_of_int (int_of_intN x mod int_of_intN y)) =
                int_of_intN x mod int_of_intN y"
    by (rule intN_of_int_inverse)
  with assms(3) show "int_of_intN (x modn y) = int_of_intN x mod int_of_intN y"
    by (simp add: modulo_intN_def)
  also from 1 2 3 have "... \<in> int_of_intN ` A" by (rule sym_interval_closed_modulo)
  finally show "x modn y \<in> A" using inj_int_of_intN by (simp only: inj_image_mem_iff)
qed

definition gcd_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "gcd_intN = (\<lambda>x y. intN_of_int (gcd (int_of_intN x) (int_of_intN y)))"

definition lcm_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "lcm_intN = (\<lambda>x y. intN_of_int (lcm (int_of_intN x) (int_of_intN y)))"

lemma
  assumes "x \<in> A" and "y \<in> A" and "sym_intervalN A"
  shows int_of_intN_gcd: "int_of_intN (gcd_intN x y) = gcd (int_of_intN x) (int_of_intN y)"
    and sym_intervalN_closed_gcd: "gcd_intN x y \<in> A"
proof -
  from assms(3) have 1: "sym_interval n (int_of_intN ` A)" by (simp only: sym_intervalN_def)
  moreover from assms(1) have 2: "int_of_intN x \<in> int_of_intN ` A" by (rule imageI)
  moreover from assms(2) have 3: "int_of_intN y \<in> int_of_intN ` A" by (rule imageI)
  ultimately have "gcd (int_of_intN x) (int_of_intN y) \<in> int_of_intN ` A"
    by (rule sym_interval_closed_gcd)
  also from 1 have "... \<subseteq> int_carrier n" by (rule sym_intervalD)
  finally have "int_of_intN (intN_of_int (gcd (int_of_intN x) (int_of_intN y))) =
                gcd (int_of_intN x) (int_of_intN y)"
    by (rule intN_of_int_inverse)
  with assms(3) show "int_of_intN (gcd_intN x y) = gcd (int_of_intN x) (int_of_intN y)"
    by (simp add: gcd_intN_def)
  also from 1 2 3 have "... \<in> int_of_intN ` A" by (rule sym_interval_closed_gcd)
  finally show "gcd_intN x y \<in> A" using inj_int_of_intN by (simp only: inj_image_mem_iff)
qed

subsubsection \<open>Extended Euclidean Algorithm\<close>

fun euclid_ext_aux_intN_pred :: "('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> bool"
  where "euclid_ext_aux_intN_pred (_, _, _, _, _, r) = (r = 0n)"

fun euclid_ext_aux_intN_base :: "('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> (('a \<times> 'a) \<times> 'a)"
  where "euclid_ext_aux_intN_base (s', _, t', _, r', _) = ((s', t'), r')"

fun euclid_ext_aux_intN_step :: "('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)"
  where "euclid_ext_aux_intN_step (s', s, t', t, r', r) =
            (let q = r' divn r in (s, s' -n q *n s, t, t' -n q *n t, r, r' modn r))"

definition euclid_ext_aux_intN :: "('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> (('a \<times> 'a) \<times> 'a)"
  where "euclid_ext_aux_intN = tailrec.fun euclid_ext_aux_intN_pred euclid_ext_aux_intN_base euclid_ext_aux_intN_step"

definition euclid_ext_aux_intN_dom :: "('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> bool"
  where "euclid_ext_aux_intN_dom = tailrec.dom euclid_ext_aux_intN_pred euclid_ext_aux_intN_step"

lemma euclid_ext_aux_intN_code [code]:
  "euclid_ext_aux_intN (s', s, t', t, r', r) = (
     if r = 0n then ((s', t'), r')
     else let q = r' divn r in euclid_ext_aux_intN (s, s' -n q *n s, t, t' -n q *n t, r, r' modn r))"
  by (simp add: euclid_ext_aux_intN_def tailrec.simps[where x="(s', s, t', t, r', r)"] Let_def)

lemma euclid_ext_aux_intN_domI_aux:
  assumes "fst (snd (snd (snd (snd args)))) \<in> A" and "snd (snd (snd (snd (snd args)))) \<in> A"
    and "sym_intervalN A"
  shows "euclid_ext_aux_intN_dom args"
  using wf_measure[of "\<lambda>(_, _, _, _, _, a). nat (int_of_intN (abs_intN a))"] assms(1, 2)
proof (induct args)
  case (less args)
  obtain s' s t' t r' r where args: "args = (s', s, t', t, r', r)" using prod.exhaust by metis
  have 1: "euclid_ext_aux_intN_dom (s0', s0, t0', t0, r0', r0)"
    if "nat (int_of_intN (abs_intN r0)) < nat (int_of_intN (abs_intN r))" and "r0' \<in> A" and "r0 \<in> A"
    for s0' s0 t0' t0 r0' r0
    using less(1) that by (simp add: args)
  from less(2) have "r' \<in> A" by (simp add: args)
  from less(3) have "r \<in> A" by (simp add: args)
  show ?case unfolding args euclid_ext_aux_intN_dom_def
  proof (rule tailrec.domI)
    assume "\<not> euclid_ext_aux_intN_pred (s', s, t', t, r', r)"
    hence "r \<noteq> 0n" by simp
    have "int_of_intN r \<noteq> 0"
    proof
      assume "int_of_intN r = 0"
      hence "intN_of_int (int_of_intN r) = intN_of_int 0" by (rule arg_cong)
      hence "r = 0n" by (simp only: int_of_intN_inverse intN_of_int_zero)
      with \<open>r \<noteq> 0n\<close> show False ..
    qed
    have "euclid_ext_aux_intN_dom (s, s' -n r' divn r *n s, t, t' -n r' divn r *n t, r, r' modn r)"
    proof (rule 1)
      from \<open>r' \<in> A\<close> \<open>r \<in> A\<close> \<open>r \<noteq> 0n\<close> assms(3) have "r' modn r \<in> A"
        and eq1: "int_of_intN (r' modn r) = int_of_intN r' mod int_of_intN r"
        by (rule sym_intervalN_closed_modulo, rule int_of_intN_modulo)
      from this(1) show "r' modn r \<in> A" .
      hence "int_of_intN (abs_intN (r' modn r)) = abs (int_of_intN (r' modn r))" using assms(3)
        by (rule int_of_intN_abs)
      also have "... = abs (int_of_intN r' mod int_of_intN r)" by (simp only: eq1)
      finally have "int_of_intN (abs_intN (r' modn r)) = abs (int_of_intN r' mod int_of_intN r)" .
      moreover from \<open>r \<in> A\<close> assms(3) have "int_of_intN (abs_intN r) = abs (int_of_intN r)"
        by (rule int_of_intN_abs)
      ultimately show "nat (int_of_intN (abs_intN (r' modn r))) < nat (int_of_intN (abs_intN r))"
        using \<open>int_of_intN r \<noteq> 0\<close> by (simp add: abs_mod_less)
    qed fact
    thus "tailrec.dom euclid_ext_aux_intN_pred euclid_ext_aux_intN_step (euclid_ext_aux_intN_step (s', s, t', t, r', r))"
      by (simp add: euclid_ext_aux_intN_dom_def Let_def)
  qed
qed

corollary euclid_ext_aux_intN_domI:
  assumes "r' \<in> A" and "r \<in> A" and "sym_intervalN A"
  shows "euclid_ext_aux_intN_dom (s', s, t', t, r', r)"
  using _ _ assms(3) by (rule euclid_ext_aux_intN_domI_aux) (simp_all add: assms)

lemma euclid_ext_aux_intN_induct [consumes 1, case_names step]:
  assumes "euclid_ext_aux_intN_dom (s', s, t', t, r', r)"
    and "(\<And>s' s t' t r' r. euclid_ext_aux_intN_dom (s', s, t', t, r', r) \<Longrightarrow>
            (\<And>q. r \<noteq> 0n \<Longrightarrow> q = r' divn r \<Longrightarrow> P (s, s' -n q *n s, t, t' -n q *n t, r, r' modn r)) \<Longrightarrow>
            P (s', s, t', t, r', r))"
  shows "P (s', s, t', t, r', r)"
  using assms(1) unfolding euclid_ext_aux_intN_dom_def
proof (rule tailrec.pinduct)
  fix x :: "'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"
  obtain s0' s0 t0' t0 r0' r0 where x: "x = (s0', s0, t0', t0, r0', r0)" using prod.exhaust by metis
  assume 1: "tailrec.dom euclid_ext_aux_intN_pred euclid_ext_aux_intN_step x"
  assume 2: "\<not> euclid_ext_aux_intN_pred x \<Longrightarrow> P (euclid_ext_aux_intN_step x)"
  show "P x" unfolding x
  proof (rule assms(2))
    from 1 show "euclid_ext_aux_intN_dom (s0', s0, t0', t0, r0', r0)"
      by (simp only: euclid_ext_aux_intN_dom_def x)
  next
    fix q
    assume "r0 \<noteq> 0n" and q: "q = r0' divn r0"
    from this(1) have "\<not> euclid_ext_aux_intN_pred x" by (simp add: x)
    thus "P (s0, s0' -n q *n s0, t0, t0' -n q *n t0, r0, r0' modn r0)" unfolding q sorry
  qed
qed

definition inverse_intN :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "inverse_intN p a = fst (fst (euclid_ext_aux_intN (1n, 0n, 0n, 1n, a, p))) modn p"

end (* intN *)

subsection \<open>Type of 31-Bit Integers\<close>

typedef int31 = "int_carrier 31"
  morphisms int_of_int31 Int31
  using zero_in_int_carrier ..

subsubsection \<open>Type-Class Instances\<close>

instantiation int31 :: equal
begin

definition equal_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> bool" where "equal_int31 = (=)"

instance by standard (simp only: equal_int31_def)

end

instantiation int31 :: ord
begin

definition less_eq_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> bool"
  where "less_eq_int31 = (\<lambda>x y. int_of_int31 x \<le> int_of_int31 y)"

definition less_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> bool"
  where "less_int31 = (\<lambda>x y. int_of_int31 x < int_of_int31 y)"

instance ..

end

instantiation int31 :: sgn
begin

definition sgn_int31 :: "int31 \<Rightarrow> int31"
  where "sgn_int31 = (\<lambda>x. Int31 (sgn (int_of_int31 x)))"

instance ..

end

instantiation int31 :: abs
begin

definition abs_int31 :: "int31 \<Rightarrow> int31"
  where "abs_int31 = (\<lambda>x. Int31 (abs (int_of_int31 x)))"

instance ..

end

instantiation int31 :: zero
begin

definition zero_int31 :: int31
  where "zero_int31 = Int31 0"

instance ..

end

instantiation int31 :: plus
begin

definition plus_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> int31"
  where "plus_int31 = (\<lambda>x y. Int31 (int_of_int31 x + int_of_int31 y))"

instance ..

end

instantiation int31 :: uminus
begin

definition uminus_int31 :: "int31 \<Rightarrow> int31"
  where "uminus_int31 = (\<lambda>x. Int31 (- int_of_int31 x))"

instance ..

end

instantiation int31 :: minus
begin

definition minus_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> int31"
  where "minus_int31 = (\<lambda>x y. Int31 (int_of_int31 x - int_of_int31 y))"

instance ..

end

instantiation int31 :: one
begin

definition one_int31 :: int31
  where "one_int31 = Int31 1"

instance ..

end

instantiation int31 :: times
begin

definition times_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> int31"
  where "times_int31 = (\<lambda>x y. Int31 (int_of_int31 x * int_of_int31 y))"

instance ..

end

instantiation int31 :: divide
begin

definition divide_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> int31"
  where "divide_int31 = (\<lambda>x y. if y = 0 then undefined else Int31 (int_of_int31 x div int_of_int31 y))"

instance ..

end

instantiation int31 :: modulo
begin

definition modulo_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> int31"
  where "modulo_int31 = (\<lambda>x y. if y = 0 then undefined else Int31 (int_of_int31 x mod int_of_int31 y))"

instance ..

end

instantiation int31 :: gcd
begin

definition gcd_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> int31"
  where "gcd_int31 = (\<lambda>x y. Int31 (gcd (int_of_int31 x) (int_of_int31 y)))"

definition lcm_int31 :: "int31 \<Rightarrow> int31 \<Rightarrow> int31"
  where "lcm_int31 = (\<lambda>x y. Int31 (lcm (int_of_int31 x) (int_of_int31 y)))"

instance ..

end

subsubsection \<open>Interpretation of @{locale intN}\<close>

global_interpretation int31: intN 31 int_of_int31 Int31
  rewrites "int31.less_eq_intN = (\<le>)"
    and "int31.less_intN = (<)"
    and "int31.sgn_intN = sgn"
    and "int31.abs_intN = abs"
    and "int31.zero_intN = 0"
    and "int31.plus_intN = (+)"
    and "int31.uminus_intN = uminus"
    and "int31.minus_intN = (-)"
    and "int31.one_intN = 1"
    and "int31.times_intN = ( * )"
    and "int31.divide_intN = (div)"
    and "int31.modulo_intN = (mod)"
    and "int31.gcd_intN = gcd"
    and "int31.lcm_intN = lcm"
  defines integer_of_int31 = int31.integer_of_intN
    and int31_of_integer = int31.intN_of_integer
    and euclid_ext_aux_int31 = int31.euclid_ext_aux_intN
    and inverse_int31 = int31.inverse_intN
proof -
  interpret i31: intN 31 int_of_int31 Int31
    by unfold_locales (simp_all add: int_of_int31_inverse Int31_inverse)
  show "intN 31 int_of_int31 Int31" ..
  show "i31.less_eq_intN = (\<le>)" by (simp only: i31.less_eq_intN_def less_eq_int31_def)
  show "i31.less_intN = (<)" by (simp only: i31.less_intN_def less_int31_def)
  show "i31.sgn_intN = sgn" by (simp only: i31.sgn_intN_def sgn_int31_def)
  show "i31.abs_intN = abs" by (simp only: i31.abs_intN_def abs_int31_def)
  show "i31.zero_intN = 0" by (simp only: i31.zero_intN_def zero_int31_def)
  show "i31.plus_intN = (+)" by (simp only: i31.plus_intN_def plus_int31_def)
  show "i31.uminus_intN = uminus" by (simp only: i31.uminus_intN_def uminus_int31_def)
  show "i31.minus_intN = (-)" by (simp only: i31.minus_intN_def minus_int31_def)
  show "i31.one_intN = 1" by (simp only: i31.one_intN_def one_int31_def)
  show "i31.times_intN = ( * )" by (simp only: i31.times_intN_def times_int31_def)
  show "i31.divide_intN = (div)"
    by (simp only: i31.divide_intN_def divide_int31_def i31.zero_intN_def zero_int31_def)
  show "i31.modulo_intN = (mod)"
    by (simp only: i31.modulo_intN_def modulo_int31_def i31.zero_intN_def zero_int31_def)
  show "i31.gcd_intN = gcd" by (simp only: i31.gcd_intN_def gcd_int31_def)
  show "i31.lcm_intN = lcm" by (simp only: i31.lcm_intN_def lcm_int31_def)
qed

lemmas [code_unfold] = int31.intN_of_int_code int31.int_of_intN_code

instance int31 :: linorder
  using int31.linorder_intN by (rule Orderings.class.Orderings.linorder.of_class.intro)

instantiation int31 :: term_of
begin

definition term_of_int31 :: "int31 \<Rightarrow> term"
  where "term_of_int31 = (\<lambda>x. term_of_class.term_of (integer_of_int31 x))"

instance ..

end

thm int31.int_of_intN_abs int31.sym_intervalN_closed_abs

thm int31.int_of_intN_zero int31.intN_of_int_zero
thm int31.int_of_intN_plus int31.plus_intN_zero_neutr int31.plus_intN_comm
thm int31.int_of_intN_uminus int31.sym_intervalN_closed_uminus int31.uminus_zero_intN
thm int31.int_of_intN_minus int31.minus_intN_zero_neutr int31.minus_intN_inverse
    int31.add_uminus_conv_diff_intN

thm int31.int_of_intN_one int31.intN_of_int_one
thm int31.int_of_intN_times int31.times_intN_zero_annihil int31.times_intN_one_neutr
    int31.times_intN_comm int31.times_uminusN_left int31.times_uminusN_right
    int31.uminus_times_uminusN
thm int31.int_of_intN_divide
thm int31.int_of_intN_modulo

thm int31.int_of_intN_gcd

subsection \<open>Code Generation\<close>

code_printing
  type_constructor int31 \<rightharpoonup>
    (SML) "Int31.int" |
  constant "plus :: int31 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "!((_ : Int31.int) + _)" |
  constant "minus :: int31 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "!((_ : Int31.int) - _)" |
  constant "uminus :: int31 \<Rightarrow> _" \<rightharpoonup>
    (SML) "(~)" |
  constant "times :: int31 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "!((_ : Int31.int) * _)" |
  constant "divide :: int31 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
    (SML) "!(Int31.div ((_ : Int31.int), _))" |
  constant "modulo :: int31 \<Rightarrow> _" \<rightharpoonup>
    (SML) "!(Int31.mod ((_ : Int31.int), _))" |
  constant "0 :: int31" \<rightharpoonup>
    (SML) "!(0 : Int31.int)" |
  constant "1 :: int31" \<rightharpoonup>
    (SML) "!(1 : Int31.int)" |
  constant "HOL.equal :: int31 \<Rightarrow> _" \<rightharpoonup>
    (SML) "!((_ : Int31.int) = _)" |
  constant "integer_of_int31" \<rightharpoonup>
    (SML) "IntInf.fromInt (Int31.toInt _)" |
  constant "int31_of_integer" \<rightharpoonup>
    (SML) "Int31.fromInt (IntInf.toInt _)"

declare [[code drop:
      "uminus :: int31 \<Rightarrow> _"
      "plus :: int31 \<Rightarrow> _"
      "minus :: int31 \<Rightarrow> _"
      "times :: int31 \<Rightarrow> _"
      "divide :: int31 \<Rightarrow> _"
      "modulo :: int31 \<Rightarrow> _"
      "abs :: int31 \<Rightarrow> _"
      "gcd :: int31 \<Rightarrow> _"
      "lcm :: int31 \<Rightarrow> _"
      "int31_of_integer"
      "integer_of_int31"]]

value [code] "- Int31 1"

value [code] "(Int31 32003) div (Int31 537)"

value [code] "timing (((divide (Int31 32003)) ^^ 1000000) (Int31 5637))"

value [code] "(Int31 32003) = (Int31 5637)"

value [code] "timing (inverse_int31 (Int31 32003) ((Int31 32002) * (inverse_int31 (Int31 32003) (Int31 5637))))"

export_code "euclid_ext_aux_int31" in SML module_name Euclid

value [code] "timing (((inverse_int31 (Int31 32003)) ^^ 100000) (Int31 5637))"

value [code] "1 div (1::int31)"

end
