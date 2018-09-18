section \<open>Finite Fields\<close>

theory Finite_Field
  imports "HOL-Computational_Algebra.Euclidean_Algorithm" Int31
begin

text \<open>We introduce types for finite fields of prime order, i.\,e. fields isomorphic to $\mathbb{Z}_p$
  for some prime number $p$.\<close>

subsection \<open>Conversions between @{typ int} and @{typ integer}\<close>

lemma is_unit_int_of_integer: "is_unit (int_of_integer a) \<longleftrightarrow> is_unit a"
  by (metis divide_integer.rep_eq dvd_def dvd_mult_div_cancel integer_eqI one_integer.rep_eq times_integer.rep_eq)

corollary is_unit_integer_of_int: "is_unit (integer_of_int a) \<longleftrightarrow> is_unit a"
proof -
  have "is_unit (integer_of_int a) \<longleftrightarrow> is_unit (int_of_integer (integer_of_int a))"
    by (simp only: is_unit_int_of_integer)
  also have "... \<longleftrightarrow> is_unit a" by simp
  finally show ?thesis .
qed

lemma irreducible_int_of_integerI:
  assumes "irreducible (a::integer)"
  shows "irreducible (int_of_integer a)"
proof (rule irreducibleI)
  from assms(1) have "a \<noteq> 0" by (simp add: irreducible_def)
  thus "int_of_integer a \<noteq> 0" by (simp add: integer_eq_iff)
next
  from assms(1) have "\<not> is_unit a" by (simp add: irreducible_def)
  thus "\<not> is_unit (int_of_integer a)" by (simp only: is_unit_int_of_integer not_False_eq_True)
next
  fix x y :: int
  assume "int_of_integer a = x * y"
  hence "integer_of_int (int_of_integer a) = integer_of_int (x * y)" by (rule arg_cong)
  hence "a = integer_of_int x * integer_of_int y" by simp
  with assms have "is_unit (integer_of_int x) \<or> is_unit (integer_of_int y)" by (rule irreducibleD)
  thus "is_unit x \<or> is_unit y" by (simp only: is_unit_integer_of_int)
qed

lemma irreducible_int_of_integerD:
  assumes "irreducible (int_of_integer a)"
  shows "irreducible (a::integer)"
proof (rule irreducibleI)
  from assms(1) have "int_of_integer a \<noteq> 0" by (simp add: irreducible_def)
  thus "a \<noteq> 0" by (simp add: integer_eq_iff)
next
  from assms(1) have "\<not> is_unit (int_of_integer a)" by (simp add: irreducible_def)
  thus "\<not> is_unit a" by (simp only: is_unit_int_of_integer not_False_eq_True)
next
  fix x y :: integer
  assume "a = x * y"
  hence "int_of_integer a = int_of_integer (x * y)" by (rule arg_cong)
  hence "int_of_integer a = int_of_integer x * int_of_integer y" by simp
  with assms have "is_unit (int_of_integer x) \<or> is_unit (int_of_integer y)" by (rule irreducibleD)
  thus "is_unit x \<or> is_unit y" by (simp only: is_unit_int_of_integer)
qed

corollary irreducible_int_of_integer: "irreducible (int_of_integer a) \<longleftrightarrow> irreducible a"
  by (auto dest: irreducible_int_of_integerI irreducible_int_of_integerD)

corollary irreducible_integer_of_int: "irreducible (integer_of_int a) \<longleftrightarrow> irreducible a"
proof -
  have "irreducible (integer_of_int a) \<longleftrightarrow> irreducible (int_of_integer (integer_of_int a))"
    by (simp only: irreducible_int_of_integer)
  also have "... \<longleftrightarrow> irreducible a" by simp
  finally show ?thesis .
qed

lemma irreducible_intI:
  assumes "2 \<le> a" and "list_all (\<lambda>m. \<not> (int m) dvd a) [2..<nat a]"
  shows "irreducible (a::int)"
proof (rule irreducibleI)
  from assms(1) show "a \<noteq> 0" by simp
  from assms(1) have abs_a: "abs a = a" by simp

  show "\<not> is_unit a"
  proof
    have "1 \<noteq> (0::int)" by simp
    moreover assume "is_unit a"
    ultimately have "abs a \<le> abs 1" by (rule dvd_imp_le_int)
    hence "a \<le> 1" by (simp add: abs_a)
    with assms(1) show False by simp
  qed

  fix x y :: int
  define m where "m = nat (abs x)"
  have int_m: "int m = abs x" by (simp add: m_def)
  assume "a = x * y"
  from this[symmetric] have "a = abs x * abs y" by (simp add: abs_a flip: abs_mult)
  hence *: "int m dvd a" by (simp add: int_m)
  with assms(2) have "m < 2 \<or> nat a \<le> m" by (auto simp: list_all_def)
  thus "is_unit x \<or> is_unit y"
  proof
    assume "m < 2"
    hence "m = 0 \<or> m = 1" by auto
    hence "is_unit x"
    proof
      assume "m = 0"
      hence "x = 0" by (simp add: m_def)
      with assms(1) show ?thesis by (simp add: \<open>a = x * y\<close>)
    next
      assume "m = 1"
      hence "abs x = 1" by (auto simp add: m_def)
      thus ?thesis by (simp add: dvd_if_abs_eq)
    qed
    thus ?thesis ..
  next
    assume "nat a \<le> m"
    hence **: "a \<le> int m" by simp
    from \<open>a \<noteq> 0\<close> have "abs (int m) \<le> abs a" using * by (rule dvd_imp_le_int)
    hence "int m \<le> a" by (simp add: abs_a)
    hence "int m = a" using ** by (rule antisym)
    hence "abs x = a" by (simp add: int_m)
    with \<open>a = abs x * abs y\<close> \<open>a \<noteq> 0\<close> have "abs y = 1" by fastforce
    hence "is_unit y" by (simp add: dvd_if_abs_eq)
    thus ?thesis ..
  qed
qed

corollary irreducible_integerI:
  assumes "2 \<le> p" and "list_all (\<lambda>m. \<not> (int m) dvd (int_of_integer p)) [2..<nat (int_of_integer p)]"
  shows "irreducible (p::integer)"
proof -
  from assms(1) have "2 \<le> int_of_integer p" by (simp add: less_eq_integer.rep_eq)
  hence "irreducible (int_of_integer p)" using assms(2) by (rule irreducible_intI)
  thus ?thesis by (simp only: irreducible_int_of_integer)
qed

lemma gcd_is_unitI_irreducible:
  assumes "irreducible a" and "\<not> a dvd (b::'a::semiring_gcd)"
  shows "is_unit (gcd a b)"
proof -
  from gcd_dvd1 obtain k where a: "a = gcd a b * k" by (rule dvdE)
  with assms(1) have "is_unit (gcd a b) \<or> is_unit k" by (rule irreducibleD)
  thus ?thesis
  proof
    assume "is_unit k"
    then obtain m where "1 = k * m" by (rule dvdE)
    from a have "a * m = gcd a b * k * m" by (rule arg_cong)
    also have "... = gcd a b * (k * m)" by (simp add: ac_simps)
    also have "... = gcd a b" by (simp add: \<open>1 = k * m\<close>[symmetric])
    finally have "gcd a b = a * m" by (rule sym)
    hence "a dvd gcd a b" by (rule dvdI)
    also have "... dvd b" by (fact gcd_dvd2)
    finally have "a dvd b" .
    with assms(2) show ?thesis ..
  qed
qed

subsection \<open>Inverse Modulo $p$\<close>

instantiation integer :: semidom_divide_unit_factor
begin

definition unit_factor_integer :: "integer \<Rightarrow> integer" where "unit_factor_integer = sgn"

context includes integer.lifting
begin

instance proof
  show "unit_factor 0 = (0::integer)" by (simp add: unit_factor_integer_def)
next
  fix a :: integer
  show "is_unit a \<Longrightarrow> unit_factor a = a" unfolding unit_factor_integer_def
    by transfer (auto simp add: abs_eq_iff')
next
  fix a :: integer
  show "a \<noteq> 0 \<Longrightarrow> is_unit (unit_factor a)" unfolding unit_factor_integer_def
    by (metis abs_sgn_eq_1 dvd_abs_iff dvd_refl)
next
  fix a b :: integer
  show "unit_factor (a * b) = unit_factor a * unit_factor b"
    by (simp add: unit_factor_integer_def sgn_mult)
qed

end

end

instantiation integer :: normalization_semidom
begin

definition normalize_integer :: "integer \<Rightarrow> integer" where "normalize_integer = abs"

instance proof
  fix a :: integer
  show "unit_factor a * normalize a = a"
    by (simp add: unit_factor_integer_def normalize_integer_def sgn_mult_abs)
next
  show "normalize 0 = (0::integer)" by (simp add: normalize_integer_def)
qed

end

instance integer :: normalization_euclidean_semiring ..

instantiation integer :: Gcd
begin

definition Gcd_integer :: "integer set \<Rightarrow> integer"
  where "Gcd_integer A = integer_of_int (Gcd (int_of_integer ` A))"

definition Lcm_integer :: "integer set \<Rightarrow> integer"
  where "Lcm_integer A = integer_of_int (Lcm (int_of_integer ` A))"

lemma int_of_Gcd: "int_of_integer (Gcd A) = Gcd (int_of_integer ` A)"
  by (simp add: Gcd_integer_def)

lemma int_of_Lcm: "int_of_integer (Lcm A) = Lcm (int_of_integer ` A)"
  by (simp add: Lcm_integer_def)

instance ..

end

instantiation integer :: semiring_gcd
begin

context includes integer.lifting
begin

instance proof
  fix a b :: integer
  show "gcd a b dvd a" by transfer simp
  show "gcd a b dvd b" by transfer simp
  show "normalize (gcd a b) = gcd a b" unfolding normalize_integer_def by transfer simp
  show "lcm a b = normalize (a * b) div gcd a b" unfolding normalize_integer_def
    by transfer (simp add: lcm_gcd)
next
  fix c a b :: integer
  show "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b" by transfer simp
qed

end

end

instantiation integer :: semiring_Gcd
begin

context includes integer.lifting
begin

instance proof
  fix a::integer and A::"integer set"
  show "a \<in> A \<Longrightarrow> Gcd A dvd a" unfolding Gcd_integer_def by transfer simp
  show "(\<And>b. b \<in> A \<Longrightarrow> a dvd b) \<Longrightarrow> a dvd Gcd A" unfolding Gcd_integer_def by transfer simp
  show "a \<in> A \<Longrightarrow> a dvd Lcm A" unfolding Lcm_integer_def by transfer simp
  show "(\<And>b. b \<in> A \<Longrightarrow> b dvd a) \<Longrightarrow> Lcm A dvd a" unfolding Lcm_integer_def by transfer simp
next
  fix A :: "integer set"
  show "normalize (Gcd A) = Gcd A" unfolding normalize_integer_def Gcd_integer_def by transfer simp
  show "normalize (Lcm A) = Lcm A" unfolding normalize_integer_def Lcm_integer_def by transfer simp
qed

end

end

instantiation integer :: euclidean_ring_gcd
begin

context includes integer.lifting
begin

instance proof
  interpret semiring_Gcd 1 0 times
    "Euclidean_Algorithm.gcd" "Euclidean_Algorithm.lcm"
    "Euclidean_Algorithm.Gcd" "Euclidean_Algorithm.Lcm"
    divide plus minus unit_factor normalize
    rewrites "dvd.dvd ( * ) = Rings.dvd"
    by (fact semiring_Gcd) (simp add: dvd.dvd_def dvd_def fun_eq_iff)
  show [simp]: "(Euclidean_Algorithm.gcd::integer \<Rightarrow> _) = gcd"
  proof (rule ext)+
    fix k l :: integer
    show "Euclidean_Algorithm.gcd k l = gcd k l"
    proof (induct k l rule: eucl_induct)
      case (zero b)
      show ?case by (simp add: normalize_integer_def)
    next
      case (mod k l)
      have "gcd l (k mod l) = gcd l k"
      proof transfer
        fix l k :: int
        show "gcd l (k mod l) = gcd l k"
        proof (cases l "0::int" rule: linorder_cases)
          case less
          then show ?thesis
            using gcd_non_0_int [of "- l" "- k"] by (simp add: ac_simps)
        next
          case equal
          with mod show ?thesis
            by simp
        next
          case greater
          then show ?thesis
            using gcd_non_0_int [of l k] by (simp add: ac_simps)
        qed
      qed
      with mod show ?case by (simp add: Euclidean_Algorithm.gcd_mod ac_simps)
    qed
  qed
  show [simp]: "(Euclidean_Algorithm.Lcm :: integer set \<Rightarrow> _) = Lcm"
    by (auto simp: intro!: ext Lcm_eqI semiring_Gcd_class.dvd_Lcm semiring_Gcd_class.Lcm_least)
  show "(Euclidean_Algorithm.lcm :: integer \<Rightarrow> _) = lcm"
    by (simp add: fun_eq_iff Euclidean_Algorithm.lcm_def semiring_gcd_class.lcm_gcd)
  show "(Euclidean_Algorithm.Gcd :: integer set \<Rightarrow> _) = Gcd"
    by (simp add: fun_eq_iff Euclidean_Algorithm.Gcd_def semiring_Gcd_class.Gcd_Lcm)
qed

end

end

definition inverse_int :: "'a \<Rightarrow> 'a \<Rightarrow> 'a::euclidean_ring_gcd"
  where "inverse_int p a = fst (bezout_coefficients a p) mod p"

lemma inverse_int_gcd:
  assumes "0 \<le> a" and "a < (p::integer)"
  shows "(inverse_int p a * a) mod p = (gcd a p) mod p"
proof -
  from assms have a: "a mod p = a"
    by (rule unique_euclidean_semiring_numeral_class.mod_less)
  have "(gcd a p) mod p = (fst (bezout_coefficients a p) * a + snd (bezout_coefficients a p) * p) mod p"
    by (simp only: bezout_coefficients_fst_snd)
  also have "... = (inverse_int p a * (a mod p)) mod p"
    by (simp add: inverse_int_def mod_mult_eq)
  also have "... = (inverse_int p a * a) mod p" by (simp only: a)
  finally show ?thesis by (simp only:)
qed

corollary inverse_int_irreducible:
  assumes "irreducible p" and "0 < a" and "a < (p::integer)"
  shows "(inverse_int p a * a) mod p = 1"
proof -
  have "\<not> p dvd a"
  proof
    from assms(2) have "int_of_integer a \<noteq> 0"
      by (metis less_numeral_extra(3) of_int_0 of_int_integer_of)
    assume "p dvd a"
    hence "int_of_integer p dvd int_of_integer a" by auto
    with \<open>int_of_integer a \<noteq> 0\<close> have "abs (int_of_integer p) \<le> abs (int_of_integer a)"
      by (rule dvd_imp_le_int)
    hence "abs p \<le> abs a" by (simp flip: abs_integer.rep_eq less_eq_integer.rep_eq)
    also from assms(2) have "... = a" by simp
    finally have "p \<le> a" by simp
    with assms(3) show False by simp
  qed
  with assms(1) have "is_unit (gcd p a)" by (rule gcd_is_unitI_irreducible)
  hence eq: "gcd a p = 1" by (simp only: is_unit_gcd_iff ac_simps)
  from assms(2) have "0 \<le> a" by simp
  hence "(inverse_int p a * a) mod p = (gcd a p) mod p" using assms(3)
    by (rule inverse_int_gcd)
  also have "... = 1 mod p" by (simp only: eq)
  also have "... = 1"
    by (metis assms(2, 3) le_less_trans less_imp_le mod_by_1 not_less_iff_gr_or_eq
              unique_euclidean_semiring_numeral_class.mod_less zero_le_one)
  finally show ?thesis .
qed

subsection \<open>The Finite Field of Order $32003$\<close>

definition "o32003 = (Int31 32003)"

lemma pos_o32003: "0 < o32003"
  by (simp add: o32003_def)

lemma irreducible_o32003: "irreducible o32003"
proof (rule irreducible_integerI)
  show "2 \<le> o32003" by (simp add: o32003_def)
next
  show "list_all (\<lambda>m. \<not> int m dvd int_of_integer o32003) [2..<nat (int_of_integer o32003)]"
    by eval
qed

typedef gf32003 = "{n::int31. 0 \<le> n \<and> n < o32003}"
proof
  from pos_o32003 show "0 \<in> {n. 0 \<le> n \<and> n < o32003}" by simp
qed

setup_lifting type_definition_gf32003

definition GF32003 :: "int31 \<Rightarrow> gf32003" where
  "GF32003 n = Abs_gf32003 (n mod o32003)"

definition "gf32003_of_int = GF32003"

lemma GF32003_Rep [code abstype]: "GF32003 (Rep_gf32003 n) = n"
proof -
  from Rep_gf32003[of n] have "0 \<le> Rep_gf32003 n" and "Rep_gf32003 n < o32003" by simp_all
  hence "Rep_gf32003 n mod o32003 = Rep_gf32003 n"
    by (rule unique_euclidean_semiring_numeral_class.mod_less)
  thus ?thesis by (simp add: GF32003_def Rep_gf32003_inverse)
qed

lemma [code abstract]: "Rep_gf32003 (gf32003_of_int n) = n mod o32003"
  unfolding gf32003_of_int_def GF32003_def
  by (rule Abs_gf32003_inverse, simp add: pos_o32003 pos_mod_sign pos_mod_bound)

instantiation gf32003 :: equal
begin

definition equal_gf32003 :: "gf32003 \<Rightarrow> gf32003 \<Rightarrow> bool" where "equal_gf32003 = (=)"

instance by standard (simp add: equal_gf32003_def)

end

lemma [code]: "HOL.equal m n = ((Rep_gf32003 m) = (Rep_gf32003 n))"
  by (simp add: equal_gf32003_def Rep_gf32003_inject)

subsubsection \<open>Additive Structure\<close>

instantiation gf32003 :: zero
begin

lift_definition zero_gf32003 :: gf32003 is 0 by (simp add: o32003_def)

instance ..

end

instantiation gf32003 :: plus
begin

lift_definition plus_gf32003 :: "gf32003 \<Rightarrow> gf32003 \<Rightarrow> gf32003" is "\<lambda>x y. (x + y) mod o32003"
  by (simp add: pos_o32003 pos_mod_sign pos_mod_bound)

instance ..

end

instantiation gf32003 :: uminus
begin

lift_definition uminus_gf32003 :: "gf32003 \<Rightarrow> gf32003" is "\<lambda>x. if x = 0 then 0 else o32003 - x"
  by (simp add: pos_o32003 pos_mod_sign pos_mod_bound)

instance ..

end

instantiation gf32003 :: minus
begin

lift_definition minus_gf32003 :: "gf32003 \<Rightarrow> gf32003 \<Rightarrow> gf32003" is "\<lambda>x y. if x < y then (o32003 + x) - y else x - y"
  by (simp add: pos_o32003 pos_mod_sign pos_mod_bound)

instance ..

end

instance gf32003 :: ab_group_add
proof
  fix a b c :: gf32003
  show "a + b + c = a + (b + c)"
    by transfer (simp add: add.commute add.left_commute mod_add_right_eq)
next
  fix a b :: gf32003
  have "a + b = b + a \<and> a - b = a + (- b)" by transfer (simp add: add.commute mod_add_right_eq)
  thus "a + b = b + a" and "a - b = a + (- b)" by blast+
next
  fix a :: gf32003
  have "0 + a = a \<and> - a + a = 0"
    by transfer (simp add: mod_add_left_eq unique_euclidean_semiring_numeral_class.mod_less)
  thus "0 + a = a" and "- a + a = 0" by blast+
qed

subsubsection \<open>Multiplicative Structure\<close>

instantiation gf32003 :: one
begin

lift_definition one_gf32003 :: gf32003 is 1 by (simp add: o32003_def)

instance ..

end

instantiation gf32003 :: times
begin

lift_definition times_gf32003 :: "gf32003 \<Rightarrow> gf32003 \<Rightarrow> gf32003" is "\<lambda>x y. (x * y) mod o32003"
  by (simp add: pos_o32003 pos_mod_sign pos_mod_bound)

instance ..

end

instance gf32003 :: comm_ring_1
proof
  fix a b c :: gf32003
  have "a * b * c = a * (b * c) \<and> (a + b) * c = a * c + b * c"
    sorry (*by transfer (simp add: distrib_left mod_add_left_eq mod_add_right_eq mod_mult_right_eq mult.commute mult.left_commute)*)
  thus "a * b * c = a * (b * c)" and "(a + b) * c = a * c + b * c" by blast+
next
  fix a b :: gf32003
  show "a * b = b * a" by transfer (simp add: mult.commute)
next
  fix a :: gf32003
  show "1 * a = a" by transfer (simp add: unique_euclidean_semiring_numeral_class.mod_less)
next
  show "0 \<noteq> (1::gf32003)" by transfer simp
qed

subsubsection \<open>Field Structure\<close>

instantiation gf32003 :: inverse
begin

lift_definition inverse_gf32003 :: "gf32003 \<Rightarrow> gf32003" is "inverse_int31 o32003"
  by (simp add: inverse_int_def pos_o32003 pos_mod_sign pos_mod_bound)

definition divide_gf32003 :: "gf32003 \<Rightarrow> gf32003 \<Rightarrow> gf32003"
  where "divide_gf32003 x y = x * inverse y"

instance ..

end

instance gf32003 :: field
proof
  fix a :: gf32003
  show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1" sorry
(*
  proof transfer
    fix a :: integer
    assume "0 \<le> a \<and> a < o32003" and "a \<noteq> 0"
    hence "0 < a" and "a < o32003" by simp_all
    with irreducible_o32003 show "inverse_int o32003 a * a mod o32003 = 1"
      by (rule inverse_int_irreducible)
  qed
*)
next
  fix a b :: gf32003
  show "a / b = a * inverse b" by (fact divide_gf32003_def)
next
  show "inverse 0 = (0::gf32003)" by transfer (simp add: inverse_int_def bezout_coefficients_left_0)
qed

subsubsection \<open>Code Generation\<close>

code_printing
  constant "o32003" \<rightharpoonup>
    (SML) "!(32003 : Int31.int)"

lemmas [code abstract] = zero_gf32003.rep_eq one_gf32003.rep_eq

value [code] "0::gf32003"

value [code] "gf32003_of_int 25687 + gf32003_of_int 456"

value [code] "- gf32003_of_int 25687"

value [code] "gf32003_of_int 3185 - gf32003_of_int 25687"

value [code] "1::gf32003"

value [code] "(1::gf32003) = (gf32003_of_int 32004)"

value [code] "inverse (32002 / 5637::gf32003)"

export_code "inverse::gf32003 \<Rightarrow> _" in SML module_name Example

end (* theory *)
