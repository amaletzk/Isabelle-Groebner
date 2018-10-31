theory Power_Products_PM
  imports MPoly_PM Number_Classes
begin

section \<open>Power-Products Represented by Polynomial Mappings\<close>

subsection \<open>Natural and Integer-Valued Polynomial Mappings\<close>

lift_definition of_nat_pm :: "('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::semiring_1)" is of_nat_fun
proof -
  fix f::"'a \<Rightarrow> nat"
  have "{x. of_nat_fun f x \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}"
  proof (rule, simp add: of_nat_fun_def)
    fix x
    assume "of_nat (f x) \<noteq> 0"
    have "f x \<noteq> 0"
    proof
      assume "f x = 0"
      hence "of_nat (f x) = 0" by simp
      with \<open>of_nat (f x) \<noteq> 0\<close> show False ..
    qed
    thus "0 < f x" by simp
  qed
  moreover assume "finite {x. f x \<noteq> 0}"
  ultimately show "finite {x. of_nat_fun f x \<noteq> 0}" by (rule finite_subset)
qed

lift_definition of_int_pm :: "('a \<Rightarrow>\<^sub>0 int) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::ring_1)" is of_int_fun
proof -
  fix f::"'a \<Rightarrow> int"
  have "{x. of_int_fun f x \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}"
  proof (rule, simp add: of_int_fun_def, rule)
    fix x
    assume "of_int (f x) \<noteq> 0"
    assume "f x = 0"
    hence "of_int (f x) = 0" by simp
    with \<open>of_int (f x) \<noteq> 0\<close> show False ..
  qed
  moreover assume "finite {x. f x \<noteq> 0}"
  ultimately show "finite {x. of_int_fun f x \<noteq> 0}" by (rule finite_subset)
qed

lift_definition of_rat_pm :: "('a \<Rightarrow>\<^sub>0 rat) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field_char_0)" is of_rat_fun
proof -
  fix f::"'a \<Rightarrow> rat"
  have "{x. of_rat_fun f x \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}" by (rule, simp add: of_rat_fun_def)
  moreover assume "finite {x. f x \<noteq> 0}"
  ultimately show "finite {x. of_rat_fun f x \<noteq> 0}" by (rule finite_subset)
qed

lemma lookup_of_nat_pm: "lookup (of_nat_pm t) x = of_nat (lookup t x)"
  by (simp add: of_nat_fun_def of_nat_pm.rep_eq)

lemma lookup_of_int_pm: "lookup (of_int_pm t) x = of_int (lookup t x)"
  by (simp add: of_int_fun_def of_int_pm.rep_eq)

lemma lookup_of_rat_pm: "lookup (of_rat_pm t) x = of_rat (lookup t x)"
  by (simp add: of_rat_fun_def of_rat_pm.rep_eq)

lift_definition to_nat_pm :: "('a \<Rightarrow>\<^sub>0 'b::floor_ceiling) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 nat)" is to_nat_fun
proof -
  fix f::"'a \<Rightarrow> 'b"
  have "{x. to_nat_fun f x \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}"
  proof (rule, simp add: to_nat_fun_def, rule)
    fix x
    assume "0 < to_nat (f x)"
    hence "to_nat (f x) \<noteq> 0" by simp
    assume "f x = 0"
    hence "to_nat (f x) = 0" by (simp add: to_nat_def)
    with \<open>to_nat (f x) \<noteq> 0\<close> show False ..
  qed
  moreover assume "finite {x. f x \<noteq> 0}"
  ultimately show "finite {x. to_nat_fun f x \<noteq> 0}" by (rule finite_subset)
qed

lift_definition to_int_pm :: "('a \<Rightarrow>\<^sub>0 'b::floor_ceiling) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 int)" is to_int_fun
proof -
  fix f::"'a \<Rightarrow> 'b"
  have "{x. to_int_fun f x \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}" by (rule, simp add: to_int_fun_def, rule, simp)
  moreover assume "finite {x. f x \<noteq> 0}"
  ultimately show "finite {x. to_int_fun f x \<noteq> 0}" by (rule finite_subset)
qed

lemma lookup_to_nat_pm: "lookup (to_nat_pm t) x = to_nat (lookup t x)"
  by (simp add: to_nat_fun_def to_nat_pm.rep_eq)

lemma lookup_to_int_pm: "lookup (to_int_pm t) x = floor (lookup t x)"
  by (simp add: to_int_fun_def to_int_pm.rep_eq)

definition is_nat_pm where "is_nat_pm t = is_nat_fun (lookup t)"
definition is_int_pm where "is_int_pm t = is_int_fun (lookup t)"

lemma is_nat_pmI:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> is_nat (lookup t x)"
  shows "is_nat_pm t"
  unfolding is_nat_pm_def is_nat_fun_def
proof
  fix x
  show "is_nat (lookup t x)"
  proof (cases "x \<in> keys t")
    case True
    thus ?thesis by (rule assms)
  next
    case False
    hence "lookup t x = 0" by simp
    thus ?thesis by (simp add: zero_is_nat)
  qed
qed

lemma is_nat_pmD:
  assumes "is_nat_pm t"
  shows "is_nat (lookup t x)"
  using assms unfolding is_nat_pm_def is_nat_fun_def ..

lemma is_int_pmI:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> is_int (lookup t x)"
  shows "is_int_pm t"
  unfolding is_int_pm_def is_int_fun_def
proof
  fix x
  show "is_int (lookup t x)"
  proof (cases "x \<in> keys t")
    case True
    thus ?thesis by (rule assms)
  next
    case False
    hence "lookup t x = 0" by simp
    thus ?thesis by (simp add: is_int_def)
  qed
qed

lemma is_int_pmD:
  assumes "is_int_pm t"
  shows "is_int (lookup t x)"
  using assms unfolding is_int_pm_def is_int_fun_def ..

lemma nat_pm_is_int_pm:
  assumes "is_nat_pm t"
  shows "is_int_pm t"
proof (rule is_int_pmI)
  fix x
  from assms have "is_nat (lookup t x)" by (rule is_nat_pmD)
  thus "is_int (lookup t x)" by (rule nat_is_int)
qed

lemma int_pm_is_nat_pm:
  assumes "is_int_pm t" and "\<And>x. x \<in> keys t \<Longrightarrow> 0 \<le> lookup t x"
  shows "is_nat_pm t"
  unfolding is_nat_pm_def is_nat_fun_def
proof
  fix x
  show "is_nat (lookup t x)"
  proof (cases "x \<in> keys t")
    case True
    from assms(1) have "is_int (lookup t x)" unfolding is_int_pm_def is_int_fun_def ..
    moreover from True have "0 \<le> lookup t x" by (rule assms(2))
    ultimately show ?thesis by (rule int_is_nat)
  next
    case False
    hence "lookup t x = 0" by simp
    thus ?thesis by (simp add: zero_is_nat)
  qed
qed

lemma of_nat_pm_is_nat_pm: "is_nat_pm (of_nat_pm f)"
  by (simp add: is_nat_pm_def is_nat_fun_def lookup_of_nat_pm of_nat_is_nat)

lemma of_int_pm_is_int_pm: "is_int_pm (of_int_pm f)"
  by (simp add: is_int_pm_def is_int_fun_def lookup_of_int_pm of_int_is_int)

lemma lcs_of_nat_pm:
  assumes "\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1, add_linorder}) \<longleftrightarrow> m \<le> n"
  shows "lcs (of_nat_pm a) (of_nat_pm b) = ((of_nat_pm (lcs a b))::'a \<Rightarrow>\<^sub>0 'b)"
  by (transfer, auto simp add: of_nat_fun_def max_of_nat[OF assms])

lemma gcs_of_nat_pm:
  assumes "\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1, add_linorder}) \<longleftrightarrow> m \<le> n"
  shows "gcs (of_nat_pm a) (of_nat_pm b) = ((of_nat_pm (gcs a b))::'a \<Rightarrow>\<^sub>0 'b)"
  by (rule poly_mapping_eqI, simp add: lookup_gcs_fun of_nat_pm.rep_eq gcs_fun of_nat_fun_def,
      auto simp add: min_of_nat[OF assms])

lemmas lcs_of_nat_pm_linordered_semidom = lcs_of_nat_pm[OF Nat.linordered_nonzero_semiring_class.of_nat_le_iff]
lemmas gcs_of_nat_pm_linordered_semidom = gcs_of_nat_pm[OF Nat.linordered_nonzero_semiring_class.of_nat_le_iff]
  
lemma lcs_is_nat_pm:
  assumes "is_nat_pm f" and "is_nat_pm g"
  shows "is_nat_pm (lcs f g)"
  using assms unfolding is_nat_pm_def lookup_lcs_fun unfolding lcs_fun_def is_nat_fun_def
  using max_is_nat by auto
    
lemma lcs_is_nat_pm':
  assumes "is_nat_pm f" and "is_int_pm g"
  shows "is_nat_pm (lcs f g)"
  using assms unfolding is_nat_pm_def is_int_pm_def lookup_lcs_fun
  unfolding lcs_fun_def is_nat_fun_def is_int_fun_def using max_is_nat' by auto

lemma lcs_is_int_pm:
  assumes "is_int_pm f" and "is_int_pm g"
  shows "is_int_pm (lcs f g)"
  using assms unfolding is_int_pm_def lookup_lcs_fun unfolding lcs_fun_def is_int_fun_def
  using max_is_int by auto

lemma gcs_is_nat_pm:
  assumes "is_nat_pm f" and "is_nat_pm g"
  shows "is_nat_pm (gcs f g)"
  using assms unfolding is_nat_pm_def lookup_gcs_fun unfolding gcs_fun is_nat_fun_def
  using min_is_nat by auto

lemma gcs_is_int_pm:
  assumes "is_int_pm f" and "is_int_pm g"
  shows "is_int_pm (gcs f g)"
  using assms unfolding is_int_pm_def lookup_gcs_fun unfolding gcs_fun is_int_fun_def
  using min_is_int by auto
  
lemma zero_is_nat_pm [simp]: "is_nat_pm 0"
  unfolding is_nat_pm_def lookup_zero is_nat_fun_def using zero_is_nat by simp

lemma of_nat_pm_zero [simp]: "of_nat_pm 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_of_nat_pm)

lemma of_int_pm_zero [simp]: "of_int_pm 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_of_int_pm)
  
lemma plus_is_nat_pm:
  assumes "is_nat_pm f" and "is_nat_pm g"
  shows "is_nat_pm (f + g)"
  using assms unfolding is_nat_pm_def plus_poly_mapping.rep_eq unfolding plus_fun_def is_nat_fun_def
  using plus_is_nat by auto

lemma diff_is_nat_pm:
  assumes "is_int_pm f" and "is_int_pm g"
  shows "is_nat_pm (f - g) \<longleftrightarrow> lookup g \<le> lookup f"
proof -
  from assms have a2: "is_int (lookup f x)" and a3: "is_int (lookup g x)" for x
    by (simp_all add: is_int_pm_def is_int_fun_def)
  show ?thesis
  proof
    assume "is_nat_pm (f - g)"
    hence a1: "is_nat (lookup (f - g) x)" for x unfolding is_nat_pm_def is_nat_fun_def ..
    
    show "lookup g \<le> lookup f" unfolding le_fun_def
    proof
      fix x
      from a1 have "is_nat ((lookup f x) - (lookup g x))" by (simp only: lookup_minus)
      thus "lookup g x \<le> lookup f x" unfolding diff_is_nat[OF a2 a3] .
    qed
  next
    assume "lookup g \<le> lookup f"
    show "is_nat_pm (f - g)" unfolding is_nat_pm_def is_nat_fun_def
    proof
      fix x
      from \<open>lookup g \<le> lookup f\<close> have "lookup g x \<le> lookup f x" unfolding le_fun_def ..
      hence "is_nat ((lookup f x) - (lookup g x))" unfolding diff_is_nat[OF a2 a3] .
      thus "is_nat (lookup (f - g) x)" by (simp only: lookup_minus)
    qed
  qed
qed

lemma plus_is_int_pm:
  assumes "is_int_pm f" and "is_int_pm g"
  shows "is_int_pm (f + g)"
  using assms unfolding is_int_pm_def plus_poly_mapping.rep_eq unfolding plus_fun_def is_int_fun_def
  using plus_is_int by auto

lemma diff_is_int_pm:
  assumes "is_int_pm f" and "is_int_pm g"
  shows "is_int_pm (f - g)"
  using assms unfolding is_int_pm_def lookup_minus is_int_fun_def using diff_is_int by auto

lemma minus_is_int_pm:
  assumes "is_int_pm f"
  shows "is_int_pm (- f)"
  using assms unfolding is_int_pm_def is_int_fun_def using minus_is_int by auto

lemma of_nat_pm_plus: "of_nat_pm (f + g) = of_nat_pm f + of_nat_pm g"
  by (rule poly_mapping_eqI, simp add: lookup_of_nat_pm lookup_add)

lemma of_int_pm_plus: "of_int_pm (f + g) = of_int_pm f + of_int_pm g"
  by (rule poly_mapping_eqI, simp add: lookup_of_int_pm lookup_add)

subsubsection \<open>Composition\<close>

lemma to_int_pm_comp_of_int_pm [simp]: "to_int_pm (of_int_pm t) = t"
  by (rule poly_mapping_eqI, simp add: lookup_to_int_pm lookup_of_int_pm)

lemma to_nat_pm_comp_of_nat_pm [simp]: "to_nat_pm (of_nat_pm t) = t"
  by (rule poly_mapping_eqI, simp add: lookup_to_nat_pm lookup_of_nat_pm to_nat_def)

lemma to_nat_pm_comp_of_int_pm [simp]: "lookup (to_nat_pm (of_int_pm t)) = nat \<circ> (lookup t)"
  by (simp add: to_nat_pm.rep_eq of_int_pm.rep_eq to_nat_fun_comp_of_int_fun)

lemma of_nat_pm_comp_to_nat_pm:
  assumes "is_nat_pm t"
  shows "of_nat_pm (to_nat_pm t) = t"
  using assms
  by (simp add: is_nat_pm_def poly_mapping_eq_iff of_nat_pm.rep_eq to_nat_pm.rep_eq,
      intro of_nat_fun_comp_to_nat_fun)

lemma of_nat_pm_comp_to_nat_pm_eq_to_int_pm:
  assumes "is_nat_pm (t::'a \<Rightarrow>\<^sub>0 'b::floor_ceiling)"
  shows "of_nat_pm (to_nat_pm t) = to_int_pm t"
  using assms
  by (simp add: is_nat_pm_def poly_mapping_eq_iff of_nat_pm.rep_eq to_nat_pm.rep_eq to_int_pm.rep_eq,
      intro of_nat_fun_comp_to_nat_fun_eq_to_int_fun)

lemma of_int_pm_comp_to_int_pm:
  assumes "is_int_pm t"
  shows "of_int_pm (to_int_pm t) = t"
  using assms
  by (simp add: is_int_pm_def poly_mapping_eq_iff of_int_pm.rep_eq to_int_pm.rep_eq,
      intro of_int_fun_comp_to_int_fun)

lemma of_int_pm_comp_of_nat_pm [simp]: "of_int_pm (of_nat_pm t) = of_nat_pm t"
  by (simp add: poly_mapping_eq_iff of_int_pm.rep_eq of_nat_pm.rep_eq, fact of_int_fun_comp_of_nat_fun)

subsection \<open>Order relation on polynomial mappings\<close>

lemma le_of_nat_pm: "of_nat_pm s \<unlhd> ((of_nat_pm t)::'a \<Rightarrow>\<^sub>0 ('b::linordered_semidom)) \<longleftrightarrow> s \<unlhd> t"
  by (simp add: le_pm_def of_nat_pm.rep_eq leq_of_nat_fun)

lemma le_of_int_pm: "of_int_pm s \<unlhd> ((of_int_pm t)::'a \<Rightarrow>\<^sub>0 ('b::linordered_idom)) \<longleftrightarrow> s \<unlhd> t"
  by (simp add: le_pm_def of_int_pm.rep_eq leq_of_int_fun)

lemma le_to_nat_pm:
  assumes "s \<unlhd> t"
  shows "to_nat_pm s \<unlhd> to_nat_pm t"
  using assms by (simp add: le_pm_def to_nat_pm.rep_eq leq_to_nat_fun)

lemma le_to_int_pm:
  assumes "s \<unlhd> t"
  shows "to_int_pm s \<unlhd> to_int_pm t"
  using assms by (simp add: le_pm_def to_int_pm.rep_eq leq_to_int_fun)

subsection \<open>Module-structure of Polynomial Mappings\<close>

lift_definition scalar_mult_pm :: "'b \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::mult_zero)" (infixl "\<cdot>" 70)
  is "\<lambda>k f x. k * (f x)"
  by (rule finite_mult_not_eq_zero_leftI)

text \<open>If @{term t} is interpreted as a power-product, @{term "k \<cdot> t"} corresponds to exponentiation.\<close>

lemmas lookup_scalar [simp] = scalar_mult_pm.rep_eq

lemma scalar_zero_left [simp]: "0 \<cdot> t = 0"
  by (rule poly_mapping_eqI) simp

lemma scalar_zero_right [simp]: "k \<cdot> 0 = 0"
  by (rule poly_mapping_eqI) simp

lemma keys_scalar_subset: "keys (k \<cdot> t) \<subseteq> keys t"
proof
  fix x
  assume "x \<in> keys (k \<cdot> t)"
  hence "lookup (k \<cdot> t) x \<noteq> 0" by (simp del: lookup_scalar)
  thus "x \<in> keys t" using mult_not_zero by force
qed

lemma keys_scalar: "keys ((k::'b::semiring_no_zero_divisors) \<cdot> t) = (if k = 0 then {} else keys t)"
proof (split if_split, intro conjI impI)
  assume "k = 0"
  thus "keys (k \<cdot> t) = {}" by simp
next
  assume "k \<noteq> 0"
  show "keys (k \<cdot> t) = keys t"
  proof
    show "keys t \<subseteq> keys (k \<cdot> t)" by rule (simp add: \<open>k \<noteq> 0\<close> flip: lookup_not_eq_zero_eq_in_keys)
  qed (fact keys_scalar_subset)
qed

lemma scalar_single [simp]: "k \<cdot> Poly_Mapping.single x l = Poly_Mapping.single x (k * l)"
  by (rule poly_mapping_eqI) (simp add: lookup_single when_distrib)

lemma scalar_one_left [simp]: "(1::'b::{mult_zero,monoid_mult}) \<cdot> t = t"
  by (rule poly_mapping_eqI) simp

lemma scalar_distrib_left [algebra_simps]: "(k::'b::semiring_0) \<cdot> (s + t) = k \<cdot> s + k \<cdot> t"
  by (rule poly_mapping_eqI) (simp add: lookup_add distrib_left)

lemma scalar_distrib_right [algebra_simps]: "(k + (l::'b::semiring_0)) \<cdot> t = k \<cdot> t + l \<cdot> t"
  by (rule poly_mapping_eqI) (simp add: lookup_add distrib_right)

lemma scalar_Suc: "(Suc k) \<cdot> t = k \<cdot> t + t"
  by (rule poly_mapping_eqI) (simp add: lookup_add distrib_right)

lemma scalar_uminus_left: "(- k::'b::ring) \<cdot> p = - (k \<cdot> p)"
  by (rule poly_mapping_eqI) auto

lemma scalar_uminus_right: "(k::'b::ring) \<cdot> (- p) = - (k \<cdot> p)"
  by (rule poly_mapping_eqI) auto

lemma scalar_uminus_uminus [simp]: "(- k::'b::ring) \<cdot> (- p) = k \<cdot> p"
  by (simp add: scalar_uminus_left scalar_uminus_right)

lemma scalar_minus_distrib_left [algebra_simps]: "(k::'b::comm_semiring_1_cancel) \<cdot> (p - q) = k \<cdot> p - k \<cdot> q"
  by (rule poly_mapping_eqI) (auto simp add: lookup_minus right_diff_distrib')

lemma scalar_minus_distrib_right [algebra_simps]: "(k - (l::'b::comm_semiring_1_cancel)) \<cdot> f = k \<cdot> f - l \<cdot> f"
  by (rule poly_mapping_eqI) (auto simp add: lookup_minus left_diff_distrib')

lemma deg_pm_scalar: "deg_pm (k \<cdot> t) = (k::'b::semiring_0) * deg_pm t"
proof -
  from keys_scalar_subset finite_keys have "deg_pm (k \<cdot> t) = sum (lookup (k \<cdot> t)) (keys t)"
    by (rule deg_pm_superset)
  also have "\<dots> = k * sum (lookup t) (keys t)" by (simp add: sum_distrib_left)
  also from subset_refl finite_keys have "sum (lookup t) (keys t) = deg_pm t"
    by (rule deg_pm_superset[symmetric])
  finally show ?thesis .
qed

lemma adds_group [simp]: "s adds (t::'a \<Rightarrow>\<^sub>0 'b::ab_group_add)"
proof (rule addsI)
  show "t = s + (t - s)" by simp
qed

lemmas deg_pm_minus_group = deg_pm_minus[OF adds_group]

lemma scalar_is_nat_pm: "is_nat c \<Longrightarrow> is_nat_pm t \<Longrightarrow> is_nat_pm (c \<cdot> t)"
  unfolding is_nat_pm_def is_nat_fun_def using times_is_nat by auto

lemma scalar_is_int_fun: "is_int c \<Longrightarrow> is_int_pm t \<Longrightarrow> is_int_pm (c \<cdot> t)"
  unfolding is_int_pm_def is_int_fun_def using times_is_int by auto

end (* theory *)
