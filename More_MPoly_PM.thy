(* Author: Alexander Maletzky *)

section \<open>More Stuff about Multivariate Polynomials with Power-Products Represented by Polynomial Mappings\<close>

theory More_MPoly_PM
  imports MPoly_PM
begin

subsection \<open>Order relation on polynomial mappings\<close>

definition le_pm :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::{ord,zero}) \<Rightarrow> bool" (infixl "\<unlhd>" 50)
  where "le_pm s t \<longleftrightarrow> lookup s \<le> lookup t"

lemma le_pmI: "(\<And>x. lookup s x \<le> lookup t x) \<Longrightarrow> s \<unlhd> t"
  unfolding le_pm_def le_fun_def ..

lemma le_pmD: "s \<unlhd> t \<Longrightarrow> lookup s x \<le> lookup t x"
  by (simp add: le_pm_def le_fun_def)

lemma le_pm_refl [simp]: "s \<unlhd> (s::_ \<Rightarrow>\<^sub>0 _::preorder)"
  by (simp add: le_pm_def)

lemma le_pm_antisym: "s \<unlhd> t \<Longrightarrow> t \<unlhd> s \<Longrightarrow> s = (t::_ \<Rightarrow>\<^sub>0 _::order)"
  by (simp only: le_pm_def poly_mapping_eq_iff in_keys_iff)

lemma le_pm_trans [trans]: "s \<unlhd> t \<Longrightarrow> t \<unlhd> u \<Longrightarrow> s \<unlhd> (u::_ \<Rightarrow>\<^sub>0 _::preorder)"
  by (auto simp: le_pm_def dest: order_trans)

lemma le_pm_mono_plus_right: "s \<unlhd> t \<Longrightarrow> s + u \<unlhd> t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add)"
  by (simp add: le_pm_def lookup_plus_fun le_fun_def add_right_mono)

lemma le_pm_mono_plus_left: "s \<unlhd> t \<Longrightarrow> u + s \<unlhd> u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add)"
  by (simp add: le_pm_def lookup_plus_fun le_fun_def add_left_mono)

lemma le_pm_mono_plus: "s \<unlhd> t \<Longrightarrow> u \<unlhd> v \<Longrightarrow> s + u \<unlhd> t + (v::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add)"
  by (simp add: le_pm_def lookup_plus_fun le_fun_def add_mono)

lemma le_pm_increasing: "0 \<unlhd> u \<Longrightarrow> s \<unlhd> t \<Longrightarrow> s \<unlhd> u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  using le_pm_mono_plus[of 0 u s t] by simp

lemma le_pm_increasing2: "0 \<unlhd> u \<Longrightarrow> s \<unlhd> t \<Longrightarrow> s \<unlhd> t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  by (simp add: le_pm_increasing add.commute[of t])

lemma le_pm_decreasing: "u \<unlhd> 0 \<Longrightarrow> s \<unlhd> t \<Longrightarrow> u + s \<unlhd> (t::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  using le_pm_mono_plus[of u 0 s t] by simp

lemma le_pm_decreasing2: "u \<unlhd> 0 \<Longrightarrow> s \<unlhd> t \<Longrightarrow> s + u \<unlhd> (t::_ \<Rightarrow>\<^sub>0 _::ordered_comm_monoid_add)"
  using le_pm_mono_plus[of s t u 0] by simp

lemma zero_le_pm: "0 \<unlhd> (t::_ \<Rightarrow>\<^sub>0 _::add_linorder_min)"
  by (simp add: le_pmI)

lemma le_pm_mono_minus: "s \<unlhd> t \<Longrightarrow> s - u \<unlhd> t - (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_group_add)"
  by (simp add: le_pm_def lookup_minus_fun)

lemma adds_pmI: "s \<unlhd> t \<Longrightarrow> s adds (t::'a \<Rightarrow>\<^sub>0 'b::add_linorder)"
  by (simp add: le_pm_def, intro adds_poly_mappingI)

lemma adds_pm: "s adds t \<longleftrightarrow> s \<unlhd> (t::'a \<Rightarrow>\<^sub>0 'b::add_linorder_min)"
  by (simp add: adds_poly_mapping le_pm_def)

lemma gcs_le_pm:
  shows "gcs s t \<unlhd> s" and "gcs s t \<unlhd> t"
  by (simp_all add: gcs_leq_fun_1 gcs_leq_fun_2 le_pm_def lookup_gcs_fun)

lemma gcs_ge_pm: "u \<unlhd> s \<Longrightarrow> u \<unlhd> t \<Longrightarrow> u \<unlhd> gcs s t"
  by (simp add: leq_gcs_fun le_pm_def lookup_gcs_fun)

lemma lcs_ge_pm:
  shows "s \<unlhd> lcs s t" and "t \<unlhd> lcs s t"
  by (simp_all add: leq_lcs_fun_1 leq_lcs_fun_2 le_pm_def lookup_lcs_fun)

lemma lcs_le_pm: "s \<unlhd> u \<Longrightarrow> t \<unlhd> u \<Longrightarrow> lcs s t \<unlhd> u"
  by (simp add: lcs_leq_fun le_pm_def lookup_lcs_fun)

lemma gcs_add_distrib_left: "gcs s t + u = gcs (s + u) (t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_gcs_fun lookup_add gcs_fun min_add_distrib_left)

lemma gcs_add_distrib_right: "u + gcs s t = gcs (u + s) (u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_gcs_fun lookup_add gcs_fun min_add_distrib_right)

lemma lcs_add_distrib_left: "lcs s t + u = lcs (s + u) (t + (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_lcs_fun lookup_add lcs_fun_def max_add_distrib_left)

lemma lcs_add_distrib_right: "u + lcs s t = lcs (u + s) (u + (t::_ \<Rightarrow>\<^sub>0 _::ordered_ab_semigroup_add_imp_le))"
  by (rule poly_mapping_eqI) (simp only: lookup_lcs_fun lookup_add lcs_fun_def max_add_distrib_right)

lemma gcs_diff_distrib_left: "gcs s t - u = gcs (s - u) (t - (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_group_add))"
  by (rule poly_mapping_eqI) (simp only: lookup_gcs_fun lookup_minus gcs_fun min_diff_distrib_left)

lemma lcs_diff_distrib_left: "lcs s t - u = lcs (s - u) (t - (u::_ \<Rightarrow>\<^sub>0 _::ordered_ab_group_add))"
  by (rule poly_mapping_eqI) (simp only: lookup_lcs_fun lookup_minus lcs_fun_def max_diff_distrib_left)

lemma deg_pm_mono_le: "s \<unlhd> t \<Longrightarrow> deg_pm s \<le> deg_pm (t::'a \<Rightarrow>\<^sub>0 'b::add_linorder)"
  unfolding le_pm_def by (transfer) (auto intro!: deg_fun_leq simp: supp_fun_def)

lemma le_deg_pm_antisym:
  assumes "s \<unlhd> t" and "deg_pm t \<le> deg_pm (s::'a \<Rightarrow>\<^sub>0 'b::add_linorder)"
  shows "s = t"
proof (rule ccontr)
  assume "s \<noteq> t"
  have fin: "finite (keys s \<union> keys t)" by simp
  with _ have "deg_pm s = (\<Sum>x\<in>keys s \<union> keys t. lookup s x)" by (rule deg_pm_superset) simp
  also from fin have "\<dots> < (\<Sum>x\<in>keys s \<union> keys t. lookup t x)"
  proof (rule sum_strict_mono_ex1)
    from assms(1) show "\<forall>x\<in>keys s \<union> keys t. lookup s x \<le> lookup t x"
      by (auto dest: le_pmD)
  next
    from \<open>s \<noteq> t\<close> obtain x where neq: "lookup s x \<noteq> lookup t x" by (auto simp flip: lookup_inject)
    moreover from assms(1) have "lookup s x \<le> lookup t x" by (rule le_pmD)
    ultimately have "lookup s x < lookup t x" by simp
    moreover from neq have "x \<in> keys s \<union> keys t" by (auto simp: in_keys_iff)
    ultimately show "\<exists>x\<in>keys s \<union> keys t. lookup s x < lookup t x" ..
  qed
  also from _ fin have "\<dots> = deg_pm t" by (rule deg_pm_superset[symmetric]) simp
  finally have "deg_pm s < deg_pm t" .
  with assms(2) show False by simp
qed

lemma times_le_interval:
  assumes "x \<le> y + a * z" and "x \<le> y + b * z" and "a \<le> c" and "c \<le> (b::'b::{linorder,ordered_ring})"
  shows "x \<le> y + c * z"
proof (cases "0 \<le> z")
  case True
  from assms(3) True have "y + a * z \<le> y + c * z" by (simp add: add_left_mono mult_right_mono)
  with assms(1) show ?thesis by (rule order_trans)
next
  case False
  hence "z \<le> 0" by simp
  with assms(4) have "y + b * z \<le> y + c * z" by (simp add: add_left_mono mult_right_mono_neg)
  with assms(2) show ?thesis by (rule order_trans)
qed

corollary times_le_interval':
  "x \<le> a * z \<Longrightarrow> x \<le> b * z \<Longrightarrow> a \<le> c \<Longrightarrow> c \<le> (b::'b::{linorder,ordered_ring}) \<Longrightarrow> x \<le> c * z"
  using times_le_interval[of x 0 a z b c] by simp

lemma map_scale_le_interval:
  assumes "x \<unlhd> y + a \<cdot> z" and "x \<unlhd> y + b \<cdot> z" and "a \<le> c" and "c \<le> (b::'b::{linorder,ordered_ring})"
  shows "x \<unlhd> y + c \<cdot> z"
proof (rule le_pmI)
  fix k
  from assms(1) have "lookup x k \<le> lookup (y + a \<cdot> z) k" by (rule le_pmD)
  hence *: "lookup x k \<le> lookup y k + a * lookup z k" by (simp add: lookup_add)
  from assms(2) have "lookup x k \<le> lookup (y + b \<cdot> z) k" by (rule le_pmD)
  hence "lookup x k \<le> lookup y k + b * lookup z k" by (simp add: lookup_add)
  with * have "lookup x k \<le> lookup y k + c * lookup z k" using assms(3, 4) by (rule times_le_interval)
  thus "lookup x k \<le> lookup (y + c \<cdot> z) k" by (simp add: lookup_add)
qed

corollary map_scale_le_interval':
  "x \<unlhd> a \<cdot> z \<Longrightarrow> x \<unlhd> b \<cdot> z \<Longrightarrow> a \<le> c \<Longrightarrow> c \<le> (b::'b::{linorder,ordered_ring}) \<Longrightarrow> x \<unlhd> c \<cdot> z"
  using map_scale_le_interval[of x 0 a z b c] by simp

end (* theory *)