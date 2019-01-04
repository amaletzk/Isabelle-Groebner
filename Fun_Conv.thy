(* Author: Alexander Maletzky *)

section \<open>Conversion between Functions over Numeric Types\<close>

theory Fun_Conv
  imports Polynomials.Power_Products
begin

subsection \<open>Conversions\<close>

definition to_nat :: "'a::floor_ceiling \<Rightarrow> nat" where "to_nat = nat \<circ> floor"
  
definition of_nat_fun :: "('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> 'b::semiring_1" where "of_nat_fun f = of_nat \<circ> f"

definition of_int_fun :: "('a \<Rightarrow> int) \<Rightarrow> 'a \<Rightarrow> 'b::ring_1" where "of_int_fun f = of_int \<circ> f"

definition to_int_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> 'a \<Rightarrow> int" where "to_int_fun f = floor \<circ> f"
  
definition of_rat_fun :: "('a \<Rightarrow> rat) \<Rightarrow> 'a \<Rightarrow> 'b::field_char_0" where "of_rat_fun f = of_rat \<circ> f"

definition to_nat_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> 'a \<Rightarrow> nat" where "to_nat_fun f = to_nat \<circ> f"
  
definition is_int :: "'b::{floor_ceiling} \<Rightarrow> bool" where
  "is_int x = (of_int (floor x) = x)"

definition is_int_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> bool" where
  "is_int_fun f = (\<forall>x. is_int (f x))"

definition is_nat :: "'b::floor_ceiling \<Rightarrow> bool" where
  "is_nat x = (of_nat (to_nat x) = x)"

definition is_nat_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> bool" where
  "is_nat_fun f = (\<forall>x. is_nat (f x))"
  
lemma to_nat_comp_of_nat: "to_nat \<circ> of_nat = id"
  by (auto simp: to_nat_def)

lemma to_nat_of_nat: "to_nat (of_nat x) = x"
  by (auto simp: to_nat_def)

lemma to_int_fun_comp_of_int_fun: "to_int_fun (of_int_fun x) = x"
  unfolding to_int_fun_def of_int_fun_def by force

lemma to_nat_fun_comp_of_nat_fun: "to_nat_fun (of_nat_fun x) = x"
  unfolding to_nat_fun_def of_nat_fun_def to_int_fun_def to_nat_def by force

lemma to_nat_fun_comp_of_int_fun: "to_nat_fun (of_int_fun x) = nat \<circ> x"
  unfolding to_nat_fun_def of_int_fun_def to_nat_def by force

lemma to_int_fun_comp_of_int_fun': "to_int_fun \<circ> of_int_fun = id"
  unfolding comp_def to_int_fun_comp_of_int_fun id_def ..

lemma to_nat_fun_comp_of_nat_fun': "to_nat_fun \<circ> of_nat_fun = id"
  unfolding comp_def to_nat_fun_comp_of_nat_fun id_def ..

lemma nat_comp_of_nat_fun: "nat \<circ> (of_nat_fun f) = f"
  by (simp add: comp_def of_nat_fun_def)

lemma to_nat_comp_of_nat_fun: "to_nat \<circ> (of_nat_fun f) = f"
  by (simp add: comp_def of_nat_fun_def to_nat_of_nat)

lemma of_int_fun_comp_to_int_fun:
  assumes "is_int_fun f"
  shows "of_int_fun (to_int_fun f) = f"
  unfolding of_int_fun_def to_int_fun_def comp_def
proof
  fix x
  from assms show "of_int \<lfloor>f x\<rfloor> = f x" unfolding is_int_fun_def is_int_def ..
qed

lemma of_int_fun_comp_of_nat_fun: "of_int_fun (of_nat_fun f) = of_nat_fun f"
  by (rule, simp add: of_int_fun_def of_nat_fun_def)

lemma of_nat_fun_comp_nat:
  assumes "\<And>x. 0 \<le> f x"
  shows "of_nat_fun (nat \<circ> f) = (f::'a \<Rightarrow> int)"
  unfolding of_nat_fun_def comp_def
proof
  fix x
  from assms[of x] show "int (nat (f x)) = f x" by simp
qed

lemma of_nat_fun_comp_to_nat_fun:
  assumes "is_nat_fun f"
  shows "of_nat_fun (to_nat_fun f) = f"
  unfolding of_nat_fun_def to_nat_fun_def comp_def
proof
  fix x
  from assms show "of_nat (to_nat (f x)) = f x" unfolding is_nat_fun_def is_nat_def ..
qed

lemma of_nat_fun_comp_to_nat_fun_eq_to_int_fun:
  assumes "is_nat_fun (f::'a \<Rightarrow> 'b::floor_ceiling)"
  shows "of_nat_fun (to_nat_fun f) = to_int_fun f"
  unfolding of_nat_fun_def to_nat_fun_def to_nat_def to_int_fun_def comp_def
proof
  fix x
  from assms have "is_nat (f x)" unfolding is_nat_fun_def ..
  hence "of_nat (nat \<lfloor>f x\<rfloor>) = f x" unfolding is_nat_def to_nat_def comp_def .
  hence "\<lfloor>(of_nat (nat \<lfloor>f x\<rfloor>))::'b\<rfloor> = \<lfloor>f x\<rfloor>" by simp
  thus "int (nat \<lfloor>f x\<rfloor>) = \<lfloor>f x\<rfloor>" by simp
qed
  
lemma nat_is_int: "is_nat x \<Longrightarrow> is_int x"
  unfolding is_nat_def is_int_def by (metis floor_of_nat of_int_of_nat_eq)

lemma nat_fun_is_int_fun: "is_nat_fun f \<Longrightarrow> is_int_fun f"
  unfolding is_nat_fun_def is_int_fun_def using nat_is_int by auto

lemma is_nat_geq_zero: "is_nat x \<Longrightarrow> 0 \<le> x"
  unfolding is_nat_def by (metis of_nat_0_le_iff)

lemma int_is_nat:
  assumes "is_int x" and "0 \<le> x"
  shows "is_nat x"
proof -
  from assms(1) have "x = of_int \<lfloor>x\<rfloor>" unfolding is_int_def by auto
  with assms(2) show "is_nat x" unfolding is_nat_def
    by (metis comp_def of_int_le_iff of_int_0 of_nat_nat to_nat_def)
qed

lemma int_fun_is_nat_fun:
  assumes "is_int_fun f" and "\<And>x. 0 \<le> f x"
  shows "is_nat_fun f"
  unfolding is_nat_fun_def
proof
  fix x
  from assms(1) have "is_int (f x)" unfolding is_int_fun_def ..
  moreover from assms(2) have "0 \<le> f x" .
  ultimately show "is_nat (f x)" by (rule int_is_nat)
qed

lemma int_fun_is_nat_funI:
  assumes "is_int_fun f" and "is_nat_fun g" and "g \<le> (f::_ \<Rightarrow> _::preorder)"
  shows "is_nat_fun f"
  using assms(1)
proof (rule int_fun_is_nat_fun)
  fix x
  from assms(2) have "is_nat (g x)" by (simp only: is_nat_fun_def)
  hence "0 \<le> g x" by (rule is_nat_geq_zero)
  also from assms(3) have "\<dots> \<le> f x" by (rule le_funD)
  finally show "0 \<le> (f x)" .
qed

lemma of_nat_is_nat: "is_nat (of_nat n)"
  unfolding is_nat_def to_nat_def by simp
    
lemma of_int_is_int: "is_int (of_int a)"
  unfolding is_int_def by simp

lemma of_nat_fun_is_nat_fun: "is_nat_fun (of_nat_fun f)"
  unfolding is_nat_fun_def of_nat_fun_def comp_def by (simp add: of_nat_is_nat)

lemma of_int_fun_is_int_fun: "is_int_fun (of_int_fun f)"
  unfolding is_int_fun_def of_int_fun_def comp_def by (simp add: of_int_is_int)

lemma max_of_nat:
  "(\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1,ord}) \<longleftrightarrow> m \<le> n) \<Longrightarrow>
      max (of_nat a) (of_nat b) = ((of_nat (max a b::nat))::'b::{semiring_1,ord})"
  by (simp add: max_def)

lemma min_of_nat:
  "(\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1,ord}) \<longleftrightarrow> m \<le> n) \<Longrightarrow>
      min (of_nat a) (of_nat b) = ((of_nat (min a b::nat))::'b::{semiring_1,ord})"
  by (simp add: min_def)

lemmas max_of_nat_linordered_semidom = max_of_nat[OF Nat.linordered_nonzero_semiring_class.of_nat_le_iff]
lemmas min_of_nat_linordered_semidom = min_of_nat[OF Nat.linordered_nonzero_semiring_class.of_nat_le_iff]
    
lemma floor_real_of_rat: "\<lfloor>x\<rfloor> = \<lfloor>real_of_rat x\<rfloor>"
  using real_floor_code by auto

lemma ceil_real_of_rat: "\<lceil>x\<rceil> = \<lceil>real_of_rat x\<rceil>"
  unfolding ceiling_def floor_real_of_rat[of "-x"] by (simp add: of_rat_minus)

lemma leq_of_nat_fun: "of_nat_fun f \<le> ((of_nat_fun g)::'a \<Rightarrow> ('b::linordered_semidom)) \<longleftrightarrow> f \<le> g"
  by (simp add: of_nat_fun_def le_fun_def)

lemma less_of_nat_fun: "of_nat_fun f < ((of_nat_fun g)::'a \<Rightarrow> ('b::linordered_semidom)) \<longleftrightarrow> f < g"
  by (simp add: leq_of_nat_fun Orderings.less_fun_def)

lemma leq_of_int_fun: "of_int_fun f \<le> ((of_int_fun g)::'a \<Rightarrow> ('b::linordered_idom)) \<longleftrightarrow> f \<le> g"
  by (simp add: of_int_fun_def le_fun_def)

lemma less_of_int_fun: "of_int_fun f < ((of_int_fun g)::'a \<Rightarrow> ('b::linordered_idom)) \<longleftrightarrow> f < g"
  by (simp add: leq_of_int_fun Orderings.less_fun_def)

lemma to_nat_mono: "x \<le> y \<Longrightarrow> to_nat x \<le> to_nat y"
  by (auto simp: to_nat_def dest: floor_mono)

lemma to_nat_fun_mono: "f \<le> g \<Longrightarrow> to_nat_fun f \<le> to_nat_fun g"
  by (auto simp: to_nat_fun_def le_fun_def dest: to_nat_mono)

lemma to_int_fun_mono: "f \<le> g \<Longrightarrow> to_int_fun f \<le> to_int_fun g"
  by (auto simp: to_int_fun_def comp_def le_fun_def dest: floor_mono)

lemma is_int_less_iff: "is_int a \<Longrightarrow> is_int b \<Longrightarrow> a < b \<longleftrightarrow> a + 1 \<le> b"
  by (metis floor_unique is_int_def le_less less_add_one less_trans not_less)

subsection \<open>Closure Properties of @{const is_nat} and @{const is_int}\<close>
  
subsubsection \<open>0 and 1\<close>

lemma zero_is_nat: "is_nat 0"
  by (metis of_nat_0 of_nat_is_nat)

lemma one_is_nat: "is_nat 1"
  by (metis of_nat_1 of_nat_is_nat)

lemma zero_is_int: "is_int 0"
  using zero_is_nat by (rule nat_is_int)

lemma one_is_int: "is_int 1"
  using one_is_nat by (rule nat_is_int)

subsubsection \<open>@{const plus} and @{const minus}\<close>

lemma plus_is_nat:
  assumes "is_nat x" and "is_nat y"
  shows "is_nat (x + y)"
  using assms unfolding is_nat_def
proof -
  assume a1: "of_nat (to_nat x) = x"
  assume a2: "of_nat (to_nat y) = y"
  have f3: "to_nat (x + y) = nat \<lfloor>x + y\<rfloor>" by (metis comp_apply to_nat_def)
  have "x + y = of_nat (to_nat x) + of_nat (to_nat y)" using a2 a1 by presburger
  thus "of_nat (to_nat (x + y)) = x + y" using f3 by simp
qed

lemma minus_is_nat: "is_int x \<Longrightarrow> is_int y \<Longrightarrow> is_nat (x - y) \<longleftrightarrow> y \<le> x"
  unfolding is_nat_def is_int_def
  by (metis diff_ge_0_iff_ge int_is_nat is_nat_def of_int_diff of_int_is_int of_nat_0_le_iff)

lemma plus_is_int: "is_int x \<Longrightarrow> is_int y \<Longrightarrow> is_int (x + y)"
  by (metis is_int_def of_int_floor_cancel of_int_add)

lemma minus_is_int:"is_int x \<Longrightarrow> is_int y \<Longrightarrow> is_int (x - y)"
  by (metis is_int_def of_int_floor_cancel of_int_diff)

lemma uminus_is_int: "is_int x \<Longrightarrow> is_int (- x)"
  by (metis is_int_def of_int_floor_cancel of_int_minus)

lemma sum_is_nat: "(\<And>a. a \<in> A \<Longrightarrow> is_nat (f a)) \<Longrightarrow> is_nat (sum f A)"
  by (induct A rule: infinite_finite_induct) (auto intro: zero_is_nat plus_is_nat)

lemma sum_is_int: "(\<And>a. a \<in> A \<Longrightarrow> is_int (f a)) \<Longrightarrow> is_int (sum f A)"
  by (induct A rule: infinite_finite_induct) (auto intro: zero_is_int plus_is_int)

subsubsection \<open>@{const times}\<close>
  
lemma times_is_nat: "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x * y)"
  by (metis is_nat_def of_nat_is_nat of_nat_mult)

lemma times_is_int: "is_int x \<Longrightarrow> is_int y \<Longrightarrow> is_int (x * y)"
  by (metis is_int_def of_int_floor_cancel of_int_mult)

lemma prod_is_nat: "(\<And>a. a \<in> A \<Longrightarrow> is_nat (f a)) \<Longrightarrow> is_nat (prod f A)"
  by (induct A rule: infinite_finite_induct) (auto intro: one_is_nat times_is_nat)

lemma prod_is_int: "(\<And>a. a \<in> A \<Longrightarrow> is_int (f a)) \<Longrightarrow> is_int (prod f A)"
  by (induct A rule: infinite_finite_induct) (auto intro: one_is_int times_is_int)

subsubsection \<open>@{const min} and @{const max}\<close>

lemma min_is_nat:"is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (min x y)"
  by (simp add: min_def)

lemma max_is_nat: "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (max x y)"
  by (simp add: max_def)

lemma max_is_nat': "is_nat x \<Longrightarrow> is_int y \<Longrightarrow> is_nat (max x y)"
  by (metis int_is_nat is_nat_geq_zero le_max_iff_disj max_def)

lemma min_is_int: "is_int x \<Longrightarrow> is_int y \<Longrightarrow> is_int (min x y)"
  by (simp add: min_def)

lemma max_is_int: "is_int x \<Longrightarrow> is_int y \<Longrightarrow> is_int (max x y)"
  by (simp add: max_def)
  
end (* theory *)
