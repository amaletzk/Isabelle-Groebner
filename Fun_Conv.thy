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

definition is_int_fun :: "('a \<Rightarrow> 'b::ring_1) \<Rightarrow> bool" where
  "is_int_fun f \<longleftrightarrow> range f \<subseteq> \<int>"

definition is_nat_fun :: "('a \<Rightarrow> 'b::semiring_1) \<Rightarrow> bool" where
  "is_nat_fun f \<longleftrightarrow> range f \<subseteq> \<nat>"

lemma Ints_alt: "x \<in> \<int> \<longleftrightarrow> of_int \<lfloor>x\<rfloor> = x"
  by (auto elim: Ints_cases)

lemma Nats_alt: "x \<in> \<nat> \<longleftrightarrow> of_nat (to_nat x) = x"
  by (auto simp: to_nat_def Nats_def dest: sym)
  
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

lemma is_int_fun_alt: "is_int_fun f \<longleftrightarrow> (\<forall>x. f x \<in> \<int>)"
  by (auto simp: is_int_fun_def)

lemma is_int_funI: "(\<And>x. f x \<in> \<int>) \<Longrightarrow> is_int_fun f"
  by (simp add: is_int_fun_alt)

lemma is_int_funD: "is_int_fun f \<Longrightarrow> f x \<in> \<int>"
  by (simp add: is_int_fun_alt)

lemma is_nat_fun_alt: "is_nat_fun f \<longleftrightarrow> (\<forall>x. f x \<in> \<nat>)"
  by (auto simp: is_nat_fun_def)

lemma is_nat_funI: "(\<And>x. f x \<in> \<nat>) \<Longrightarrow> is_nat_fun f"
  by (simp add: is_nat_fun_alt)

lemma is_nat_funD: "is_nat_fun f \<Longrightarrow> f x \<in> \<nat>"
  by (simp add: is_nat_fun_alt)

lemma of_int_fun_comp_to_int_fun:
  assumes "is_int_fun f"
  shows "of_int_fun (to_int_fun f) = f"
  unfolding of_int_fun_def to_int_fun_def comp_def
proof
  fix x
  from assms have "f x \<in> \<int>" by (rule is_int_funD)
  thus "of_int \<lfloor>f x\<rfloor> = f x" by (simp only: Ints_alt)
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
  from assms have "f x \<in> \<nat>" by (rule is_nat_funD)
  thus "of_nat (to_nat (f x)) = f x" by (simp only: Nats_alt)
qed

lemma of_nat_fun_comp_to_nat_fun_eq_to_int_fun:
  assumes "is_nat_fun (f::'a \<Rightarrow> 'b::floor_ceiling)"
  shows "of_nat_fun (to_nat_fun f) = to_int_fun f"
  unfolding of_nat_fun_def to_nat_fun_def to_nat_def to_int_fun_def comp_def
proof
  fix x
  from assms have "f x \<in> \<nat>" by (rule is_nat_funD)
  hence "of_nat (nat \<lfloor>f x\<rfloor>) = f x" by (simp only: Nats_alt to_nat_def comp_def)
  hence "\<lfloor>(of_nat (nat \<lfloor>f x\<rfloor>))::'b\<rfloor> = \<lfloor>f x\<rfloor>" by simp
  thus "int (nat \<lfloor>f x\<rfloor>) = \<lfloor>f x\<rfloor>" by simp
qed
  
lemma Nats_imp_Ints: "x \<in> \<nat> \<Longrightarrow> x \<in> \<int>"
  using Nats_subset_Ints ..

lemma nat_fun_is_int_fun: "is_nat_fun f \<Longrightarrow> is_int_fun f"
  unfolding is_nat_fun_def is_int_fun_def using Nats_imp_Ints by auto

lemma Nats_ge_0: "x \<in> \<nat> \<Longrightarrow> 0 \<le> (x::_::linordered_idom)"
  by (simp add: Nats_altdef2)

lemma Ints_imp_Nats: "x \<in> \<int> \<Longrightarrow> 0 \<le> (x::_::linordered_idom) \<Longrightarrow> x \<in> \<nat>"
  by (simp add: Nats_altdef2) 

lemma int_fun_is_nat_fun:
  assumes "is_int_fun f" and "\<And>x. (0::_::linordered_idom) \<le> f x"
  shows "is_nat_fun f"
proof (rule is_nat_funI)
  fix x
  from assms(1) have "f x \<in> \<int>" by (rule is_int_funD)
  moreover from assms(2) have "0 \<le> f x" .
  ultimately show "f x \<in> \<nat>" by (rule Ints_imp_Nats)
qed

lemma int_fun_is_nat_funI:
  assumes "is_int_fun f" and "is_nat_fun g" and "g \<le> (f::_ \<Rightarrow> _::linordered_idom)"
  shows "is_nat_fun f"
  using assms(1)
proof (rule int_fun_is_nat_fun)
  fix x
  from assms(2) have "g x \<in> \<nat>" by (rule is_nat_funD)
  hence "0 \<le> g x" by (rule Nats_ge_0)
  also from assms(3) have "\<dots> \<le> f x" by (rule le_funD)
  finally show "0 \<le> (f x)" .
qed

lemma of_nat_fun_is_nat_fun: "is_nat_fun (of_nat_fun f)"
  by (rule is_nat_funI) (simp add: of_nat_fun_def)

lemma of_int_fun_is_int_fun: "is_int_fun (of_int_fun f)"
  by (rule is_int_funI) (simp add: is_int_fun_def of_int_fun_def)

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

lemma of_nat_to_nat_ge: "x \<in> \<int> \<Longrightarrow> x \<le> of_nat (to_nat (x::_::floor_ceiling))"
  by (metis Ints_imp_Nats Nats_alt linear of_nat_0_le_iff order_trans)

lemma to_nat_fun_mono: "f \<le> g \<Longrightarrow> to_nat_fun f \<le> to_nat_fun g"
  by (auto simp: to_nat_fun_def le_fun_def dest: to_nat_mono)

lemma to_int_fun_mono: "f \<le> g \<Longrightarrow> to_int_fun f \<le> to_int_fun g"
  by (auto simp: to_int_fun_def comp_def le_fun_def dest: floor_mono)

lemma is_int_less_iff: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a < b \<longleftrightarrow> a + 1 \<le> (b::_::floor_ceiling)"
  by (metis floor_unique Ints_alt le_less less_add_one less_trans not_less)

lemma to_nat_zero [simp]: "to_nat 0 = 0"
  by (simp add: to_nat_def)

lemma to_nat_one [simp]: "to_nat 1 = 1"
  by (simp add: to_nat_def)

subsection \<open>Closure Properties of @{const Nats} and @{const Ints}\<close>

subsubsection \<open>@{const plus} and @{const minus}\<close>

lemma Nats_minus: "x \<in> \<int> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> x - y \<in> \<nat> \<longleftrightarrow> y \<le> (x::_::floor_ceiling)"
  unfolding Nats_alt Ints_alt
  by (metis diff_ge_0_iff_ge Ints_imp_Nats Nats_alt of_int_diff Ints_of_int of_nat_0_le_iff)

lemma Nats_sum: "(\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<nat>) \<Longrightarrow> sum f A \<in> \<nat>"
  by (induct A rule: infinite_finite_induct) (auto intro: Nats_0 Nats_add)

lemma Ints_sum: "(\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>) \<Longrightarrow> sum f A \<in> \<int>"
  by (induct A rule: infinite_finite_induct) (auto intro: Ints_0 Ints_add)

lemma to_nat_plus_le: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> to_nat (a + b) \<le> to_nat a + to_nat (b::_::linordered_idom)"
  by (metis (full_types) add_le_same_cancel1 add_le_same_cancel2 Ints_imp_Nats Nats_alt linear
      of_nat_add to_nat_mono to_nat_of_nat trans_le_add1 trans_le_add2)

lemma to_nat_sum_le: "(\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>) \<Longrightarrow> to_nat (sum f A) \<le> (\<Sum>a\<in>A. to_nat (f a))"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  thus ?case by simp
next
  case empty
  thus ?case by simp
next
  case (insert a A)
  have rl: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<int>" by (auto intro: insert.prems)
  hence "sum f A \<in> \<int>" by (rule Ints_sum)
  have "f a \<in> \<int>" by (rule insert.prems) simp
  from insert.hyps(1, 2) have "to_nat (sum f (insert a A)) = to_nat (f a + sum f A)" by simp
  also have "\<dots> \<le> to_nat (f a) + to_nat (sum f A)" by (rule to_nat_plus_le) fact+
  also have "\<dots> \<le> to_nat (f a) + (\<Sum>x\<in>A. to_nat (f x))" by (intro add_left_mono insert.hyps rl)
  also from insert.hyps(1, 2) have "\<dots> = (\<Sum>x\<in>insert a A. to_nat (f x))" by simp
  finally show ?case .
qed

subsubsection \<open>@{const times}\<close>

lemma Nats_prod: "(\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<nat>) \<Longrightarrow> prod f A \<in> \<nat>"
  by (induct A rule: infinite_finite_induct) (auto intro: Nats_1 Nats_mult)

lemma Ints_prod: "(\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>) \<Longrightarrow> prod f A \<in> \<int>"
  by (induct A rule: infinite_finite_induct) (auto intro: Ints_1 Ints_mult)

subsubsection \<open>@{const min} and @{const max}\<close>

lemma Nats_min: "x \<in> \<nat> \<Longrightarrow> y \<in> \<nat> \<Longrightarrow> min x y \<in> \<nat>"
  by (simp add: min_def)

lemma Nats_max: "x \<in> \<nat> \<Longrightarrow> y \<in> \<nat> \<Longrightarrow> max x y \<in> \<nat>"
  by (simp add: max_def)

lemma Nats_max': "x \<in> \<nat> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> max x (y::_::linordered_idom) \<in> \<nat>"
  by (metis Ints_imp_Nats Nats_ge_0 le_max_iff_disj max_def)

lemma Ints_min: "x \<in> \<int> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> min x y \<in> \<int>"
  by (simp add: min_def)

lemma Ints_max: "x \<in> \<int> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> max x y \<in> \<int>"
  by (simp add: max_def)

subsubsection \<open>@{const abs}\<close>

lemma Nats_abs: "x \<in> \<int> \<Longrightarrow> \<bar>x::_::linordered_idom\<bar> \<in> \<nat>"
  by (intro Ints_imp_Nats Ints_abs abs_ge_zero)
  
end (* theory *)
