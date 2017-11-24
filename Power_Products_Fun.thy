theory Power_Products_Fun
  imports "HOL-Library.Function_Algebras" Number_Classes
begin
  
section \<open>Natural and Integer-Valued Functions\<close>

lemma lcs_of_nat_fun:
  assumes "\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1, add_linorder}) \<longleftrightarrow> m \<le> n"
  shows "lcs (of_nat_fun a) (of_nat_fun b) = ((of_nat_fun (lcs a b))::'a \<Rightarrow> 'b)"
  unfolding lcs_fun_def of_nat_fun_def by (auto simp add: max_of_nat[OF assms])

lemma gcs_of_nat_fun:
  assumes "\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1, add_linorder}) \<longleftrightarrow> m \<le> n"
  shows "gcs (of_nat_fun a) (of_nat_fun b) = ((of_nat_fun (gcs a b))::'a \<Rightarrow> 'b)"
  unfolding gcs_fun of_nat_fun_def by (auto simp add: min_of_nat[OF assms])

lemmas lcs_of_nat_fun_linordered_semidom = lcs_of_nat_fun[OF Nat.linordered_semidom_class.of_nat_le_iff]
lemmas gcs_of_nat_fun_linordered_semidom = gcs_of_nat_fun[OF Nat.linordered_semidom_class.of_nat_le_iff]
  
lemma lcs_is_nat_fun:
  assumes "is_nat_fun f" and "is_nat_fun g"
  shows "is_nat_fun (lcs f g)"
  unfolding lcs_fun_def using assms unfolding is_nat_fun_def using max_is_nat by auto
    
lemma lcs_is_nat_fun':
  assumes "is_nat_fun f" and "is_int_fun g"
  shows "is_nat_fun (lcs f g)"
  unfolding lcs_fun_def using assms unfolding is_nat_fun_def is_int_fun_def using max_is_nat' by auto

lemma lcs_is_int_fun:
  assumes "is_int_fun f" and "is_int_fun g"
  shows "is_int_fun (lcs f g)"
  unfolding lcs_fun_def using assms unfolding is_int_fun_def using max_is_int by auto

lemma gcs_is_nat_fun:
  assumes "is_nat_fun f" and "is_nat_fun g"
  shows "is_nat_fun (gcs f g)"
  unfolding gcs_fun using assms unfolding is_nat_fun_def using min_is_nat by auto

lemma gcs_is_int_fun:
  assumes "is_int_fun f" and "is_int_fun g"
  shows "is_int_fun (gcs f g)"
  unfolding gcs_fun using assms unfolding is_int_fun_def using min_is_int by auto
  
lemma zero_is_nat_fun: "is_nat_fun 0"
  unfolding is_nat_fun_def zero_fun_def using zero_is_nat by simp

lemma of_nat_fun_zero: "of_nat_fun 0 = 0"
  unfolding of_nat_fun_def zero_fun_def by auto

lemma of_int_fun_zero: "of_int_fun 0 = 0"
  unfolding of_int_fun_def zero_fun_def by auto
  
lemma plus_is_nat_fun:
  assumes "is_nat_fun f" and "is_nat_fun g"
  shows "is_nat_fun (f + g)"
  using assms unfolding is_nat_fun_def plus_fun_def using plus_is_nat by auto

lemma diff_is_nat_fun:
  assumes "is_int_fun f" and "is_int_fun g"
  shows "is_nat_fun (f - g) \<longleftrightarrow> g \<le> f"
proof
  assume a1: "is_nat_fun (f - g)"
  show "g \<le> f" unfolding le_fun_def
  proof
    fix x
    from assms have "is_int (f x)" and "is_int (g x)" unfolding is_int_fun_def by simp_all
    from a1 have "is_nat ((f - g) x)" unfolding is_nat_fun_def ..
    hence "is_nat ((f x) - (g x))" by simp
    thus "g x \<le> f x" unfolding diff_is_nat[OF \<open>is_int (f x)\<close> \<open>is_int (g x)\<close>] .
  qed
next
  assume "g \<le> f"
  show "is_nat_fun (f - g)" unfolding is_nat_fun_def
  proof
    fix x
    from assms have "is_int (f x)" and "is_int (g x)" unfolding is_int_fun_def by simp_all
    from \<open>g \<le> f\<close> have "g x \<le> f x" unfolding le_fun_def ..
    hence "is_nat ((f x) - (g x))" unfolding diff_is_nat[OF \<open>is_int (f x)\<close> \<open>is_int (g x)\<close>] .
    thus "is_nat ((f - g) x)" by simp
  qed
qed

lemma plus_is_int_fun:
  assumes "is_int_fun f" and "is_int_fun g"
  shows "is_int_fun (f + g)"
  using assms unfolding is_int_fun_def plus_fun_def using plus_is_int by auto

lemma diff_is_int_fun:
  assumes "is_int_fun f" and "is_int_fun g"
  shows "is_int_fun (f - g)"
  using assms unfolding is_int_fun_def using diff_is_int by auto

lemma minus_is_int_fun:
  assumes "is_int_fun f"
  shows "is_int_fun (- f)"
  using assms unfolding is_int_fun_def using minus_is_int by auto

lemma of_nat_fun_plus: "of_nat_fun (f + g) = of_nat_fun f + of_nat_fun g"
  unfolding of_nat_fun_def plus_fun_def by auto

lemma of_int_fun_plus: "of_int_fun (f + g) = of_int_fun f + of_int_fun g"
  unfolding of_int_fun_def plus_fun_def by auto
  
subsection \<open>Module-structure of functions\<close>
  
definition scalar_mult_fun :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b::times" (infixl "\<cdot>" 70)
  where "scalar_mult_fun c f = (\<lambda>x. c * (f x))"

definition scalar_add_fun :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b::plus" (infixl "\<oplus>" 70)
  where "scalar_add_fun c f = (\<lambda>x. c + (f x))"

lemma scalar_zero_left: "(0::'a::mult_zero) \<cdot> f = 0" unfolding scalar_mult_fun_def zero_fun_def by simp

lemma scalar_zero_right: "(c::'a::mult_zero) \<cdot> 0 = 0" unfolding scalar_mult_fun_def zero_fun_def by simp
    
lemma scalar_one_left: "(1::'a::monoid_mult) \<cdot> f = f" unfolding scalar_mult_fun_def by simp
    
lemma scalar_distrib_right: "(a + (b::'a::semiring_0)) \<cdot> f = a \<cdot> f + b \<cdot> f"
  unfolding scalar_mult_fun_def plus_fun_def by (simp add: distrib_right)

lemma scalar_distrib_left: "(c::'a::semiring_0) \<cdot> (f + g) = c \<cdot> f + c \<cdot> g"
  unfolding scalar_mult_fun_def plus_fun_def by (simp add: distrib_left)

lemma scalar_uminus_left: "(-c::'a::ring) \<cdot> f = - (c \<cdot> f)" unfolding scalar_mult_fun_def by auto

lemma scalar_uminus_right: "(c::'a::ring) \<cdot> (-f) = - (c \<cdot> f)" unfolding scalar_mult_fun_def by auto

lemma scalar_minus_distrib_right: "(a - (b::'a::comm_semiring_1_cancel)) \<cdot> f = a \<cdot> f - b \<cdot> f"
  unfolding scalar_mult_fun_def plus_fun_def by (auto simp add: left_diff_distrib')

lemma scalar_minus_distrib_left: "(c::'a::comm_semiring_1_cancel) \<cdot> (f - g) = c \<cdot> f - c \<cdot> g"
  unfolding scalar_mult_fun_def plus_fun_def by (auto simp add: right_diff_distrib')
    
lemma scalar_add_zero_left: "(0::'a::monoid_add) \<oplus> f = f" unfolding scalar_add_fun_def by simp

lemma scalar_add_zero_right: "(c::'a::monoid_add) \<oplus> 0 = (\<lambda>x. c)"
  unfolding scalar_add_fun_def zero_fun_def by simp
    
lemma scalar_add_assoc_left: "(a + (b::'a::semigroup_add)) \<oplus> f = a \<oplus> (b \<oplus> f)"
  unfolding scalar_add_fun_def plus_fun_def by (simp add: ac_simps)

lemma scalar_add_assoc_right: "(c::'a::semigroup_add) \<oplus> (f + g) = (c \<oplus> f) + g"
  unfolding scalar_add_fun_def plus_fun_def by (simp add: ac_simps)

lemma scalar_add_alt: "c \<oplus> f = (\<lambda>_. c) + f"
  unfolding scalar_add_fun_def plus_fun_def ..

lemma scalar_is_nat_fun:
  assumes "is_nat c" and "is_nat_fun f"
  shows "is_nat_fun (c \<cdot> f)"
  using assms unfolding is_nat_fun_def scalar_mult_fun_def using times_is_nat by auto

lemma scalar_is_int_fun:
  assumes "is_int c" and "is_int_fun f"
  shows "is_int_fun (c \<cdot> f)"
  using assms unfolding is_int_fun_def scalar_mult_fun_def using times_is_int by auto

lemma scalar_add_is_nat_fun:
  assumes "is_nat c" and "is_nat_fun f"
  shows "is_nat_fun (c \<oplus> f)"
  using assms unfolding is_nat_fun_def scalar_add_fun_def using plus_is_nat by auto

lemma scalar_add_is_int_fun:
  assumes "is_int c" and "is_int_fun f"
  shows "is_int_fun (c \<oplus> f)"
  using assms unfolding is_int_fun_def scalar_add_fun_def using plus_is_int by auto

end (* theory *)