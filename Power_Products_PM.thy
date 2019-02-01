section \<open>Power-Products Represented by Polynomial Mappings\<close>

theory Power_Products_PM
  imports MPoly_PM Fun_Conv
begin

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

(* OBSOLETE? *)
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

(* OBSOLETE? *)
lift_definition of_rat_pm :: "('a \<Rightarrow>\<^sub>0 rat) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field_char_0)" is of_rat_fun
proof -
  fix f::"'a \<Rightarrow> rat"
  have "{x. of_rat_fun f x \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}" by (rule, simp add: of_rat_fun_def)
  moreover assume "finite {x. f x \<noteq> 0}"
  ultimately show "finite {x. of_rat_fun f x \<noteq> 0}" by (rule finite_subset)
qed

lemma lookup_of_nat_pm: "lookup (of_nat_pm t) x = of_nat (lookup t x)"
  by (simp add: of_nat_fun_def of_nat_pm.rep_eq)

lemma keys_of_nat_pm_subset: "keys (of_nat_pm t) \<subseteq> keys t"
  by (auto simp add: lookup_of_nat_pm simp flip: lookup_not_eq_zero_eq_in_keys intro!: gr0I)

lemma keys_of_nat_pm [simp]: "keys ((of_nat_pm t)::_ \<Rightarrow>\<^sub>0 _::semiring_char_0) = keys t"
  by (auto simp add: lookup_of_nat_pm simp flip: lookup_not_eq_zero_eq_in_keys)

lemma lookup_of_int_pm: "lookup (of_int_pm t) x = of_int (lookup t x)"
  by (simp add: of_int_fun_def of_int_pm.rep_eq)

lemma lookup_of_rat_pm: "lookup (of_rat_pm t) x = of_rat (lookup t x)"
  by (simp add: of_rat_fun_def of_rat_pm.rep_eq)

lemma of_nat_pm_injective [simp]: "of_nat_pm s = ((of_nat_pm t)::_ \<Rightarrow>\<^sub>0 _::semiring_char_0) \<longleftrightarrow> s = t"
  by (metis lookup_of_nat_pm of_nat_eq_iff poly_mapping_eqI)

lemma inj_of_nat_pm: "inj (of_nat_pm::_ \<Rightarrow> (_ \<Rightarrow>\<^sub>0 _::semiring_char_0))"
  by (simp add: inj_def)

lemma of_int_pm_injective [simp]: "of_int_pm s = ((of_int_pm t)::_ \<Rightarrow>\<^sub>0 _::ring_char_0) \<longleftrightarrow> s = t"
  by (metis lookup_of_int_pm of_int_eq_iff poly_mapping_eqI)

lemma inj_of_int_pm: "inj (of_int_pm::_ \<Rightarrow> (_ \<Rightarrow>\<^sub>0 _::ring_char_0))"
  by (simp add: inj_def)

lemma deg_of_nat_pm: "deg_pm (of_nat_pm t) = (of_nat (deg_pm t) :: _::semiring_char_0)"
  by (simp add: deg_pm_superset[OF subset_refl finite_keys] of_nat_pm.rep_eq of_nat_fun_def)

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
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> lookup t x \<in> \<nat>"
  shows "is_nat_pm t"
  unfolding is_nat_pm_def
proof (rule is_nat_funI)
  fix x
  show "lookup t x \<in> \<nat>"
  proof (cases "x \<in> keys t")
    case True
    thus ?thesis by (rule assms)
  next
    case False
    thus ?thesis by simp
  qed
qed

lemma is_nat_pmD: "is_nat_pm t \<Longrightarrow> lookup t x \<in> \<nat>"
  unfolding is_nat_pm_def by (drule is_nat_funD)

lemma is_int_pmI:
  assumes "\<And>x. x \<in> keys t \<Longrightarrow> lookup t x \<in> \<int>"
  shows "is_int_pm t"
  unfolding is_int_pm_def
proof (rule is_int_funI)
  fix x
  show "lookup t x \<in> \<int>"
  proof (cases "x \<in> keys t")
    case True
    thus ?thesis by (rule assms)
  next
    case False
    thus ?thesis by simp
  qed
qed

lemma is_int_pmD: "is_int_pm t \<Longrightarrow> lookup t x \<in> \<int>"
  unfolding is_int_pm_def by (drule is_int_funD)

lemma nat_pm_is_int_pm:
  assumes "is_nat_pm t"
  shows "is_int_pm t"
proof (rule is_int_pmI)
  fix x
  from assms have "lookup t x \<in> \<nat>" by (rule is_nat_pmD)
  thus "lookup t x \<in> \<int>" by (rule Nats_imp_Ints)
qed

lemma int_pm_is_nat_pm:
  assumes "is_int_pm t" and "\<And>x. x \<in> keys t \<Longrightarrow> (0::_::linordered_idom) \<le> lookup t x"
  shows "is_nat_pm t"
  unfolding is_nat_pm_def
proof (rule is_nat_funI)
  fix x
  show "lookup t x \<in> \<nat>"
  proof (cases "x \<in> keys t")
    case True
    from assms(1) have "lookup t x \<in> \<int>" by (rule is_int_pmD)
    moreover from True have "0 \<le> lookup t x" by (rule assms(2))
    ultimately show ?thesis by (rule Ints_imp_Nats)
  next
    case False
    thus ?thesis by simp
  qed
qed

lemma int_pm_is_nat_pmI:
  assumes "is_int_pm f" and "is_nat_pm g" and "g \<unlhd> (f::_ \<Rightarrow>\<^sub>0 _::linordered_idom)"
  shows "is_nat_pm f"
  using assms(1)
proof (rule int_pm_is_nat_pm)
  fix x
  from assms(2) have "lookup g x \<in> \<nat>" by (rule is_nat_pmD)
  hence "0 \<le> lookup g x" by (rule Nats_ge_0)
  also from assms(3) have "\<dots> \<le> lookup f x" by (rule le_pmD)
  finally show "0 \<le> lookup f x" .
qed

lemma of_nat_pm_is_nat_pm: "is_nat_pm (of_nat_pm f)"
  unfolding is_nat_pm_def by (rule is_nat_funI) (simp add: lookup_of_nat_pm)

lemma of_int_pm_is_int_pm: "is_int_pm (of_int_pm f)"
  unfolding is_int_pm_def by (rule is_int_funI) (simp add: lookup_of_int_pm)

lemma of_nat_pm_is_int_pm: "is_int_pm (of_nat_pm f)"
  using of_nat_pm_is_nat_pm by (rule nat_pm_is_int_pm)

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
  
lemma lcs_is_nat_pm: "is_nat_pm f \<Longrightarrow> is_nat_pm g \<Longrightarrow> is_nat_pm (lcs f g)"
  by (auto simp: is_nat_pm_def lookup_lcs_fun lcs_fun_def intro: is_nat_funI Nats_max is_nat_funD)
    
lemma lcs_is_nat_pm': "is_nat_pm f \<Longrightarrow> is_int_pm g \<Longrightarrow> is_nat_pm (lcs f (g::_ \<Rightarrow>\<^sub>0 _::linordered_idom))"
  by (auto simp: is_nat_pm_def is_int_pm_def lookup_lcs_fun lcs_fun_def
          intro: is_nat_funI Nats_max' is_nat_funD is_int_funD)

lemma lcs_is_int_pm: "is_int_pm f \<Longrightarrow> is_int_pm g \<Longrightarrow> is_int_pm (lcs f g)"
  by (auto simp: is_int_pm_def lookup_lcs_fun lcs_fun_def intro: is_int_funI Ints_max is_int_funD)

lemma gcs_is_nat_pm: "is_nat_pm f \<Longrightarrow> is_nat_pm g \<Longrightarrow> is_nat_pm (gcs f g)"
  by (auto simp: is_nat_pm_def lookup_gcs_fun gcs_fun intro: is_nat_funI Nats_min is_nat_funD)

lemma gcs_is_int_pm: "is_int_pm f \<Longrightarrow> is_int_pm g \<Longrightarrow> is_int_pm (gcs f g)"
  by (auto simp: is_int_pm_def lookup_gcs_fun gcs_fun intro: is_int_funI Ints_min is_int_funD)
  
lemma zero_is_nat_pm [simp]: "is_nat_pm 0"
  unfolding is_nat_pm_def by (rule is_nat_funI) simp

lemma zero_is_int_pm [simp]: "is_int_pm 0"
  using zero_is_nat_pm by (rule nat_pm_is_int_pm)

lemma of_nat_pm_zero [simp]: "of_nat_pm 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_of_nat_pm)

lemma of_int_pm_zero [simp]: "of_int_pm 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_of_int_pm)

lemma of_nat_pm_single: "of_nat_pm (Poly_Mapping.single x e) = Poly_Mapping.single x (of_nat e)"
  by (rule poly_mapping_eqI) (simp add: lookup_of_nat_pm lookup_single when_distrib)
  
lemma plus_is_nat_pm: "is_nat_pm f \<Longrightarrow> is_nat_pm g \<Longrightarrow> is_nat_pm (f + g)"
  by (simp add: is_nat_pm_def plus_poly_mapping.rep_eq plus_fun_def is_nat_fun_alt)

lemma minus_is_nat_pm:
  assumes "is_int_pm f" and "is_int_pm g"
  shows "is_nat_pm (f - g) \<longleftrightarrow> lookup g \<le> lookup (f::_ \<Rightarrow>\<^sub>0 _::floor_ceiling)"
proof -
  from assms have a2: "lookup f x \<in> \<int>" and a3: "lookup g x \<in> \<int>" for x
    by (simp_all add: is_int_pm_def is_int_fun_alt)
  show ?thesis
  proof
    assume "is_nat_pm (f - g)"
    hence a1: "lookup (f - g) x \<in> \<nat>" for x by (rule is_nat_pmD)
    
    show "lookup g \<le> lookup f" unfolding le_fun_def
    proof
      fix x
      from a1 have "(lookup f x) - (lookup g x) \<in> \<nat>" by (simp only: lookup_minus)
      thus "lookup g x \<le> lookup f x" unfolding Nats_minus[OF a2 a3] .
    qed
  next
    assume "lookup g \<le> lookup f"
    show "is_nat_pm (f - g)"
    proof (rule is_nat_pmI)
      fix x
      from \<open>lookup g \<le> lookup f\<close> have "lookup g x \<le> lookup f x" unfolding le_fun_def ..
      hence "(lookup f x) - (lookup g x) \<in> \<nat>" unfolding Nats_minus[OF a2 a3] .
      thus "lookup (f - g) x \<in> \<nat>" by (simp only: lookup_minus)
    qed
  qed
qed

lemma plus_is_int_pm: "is_int_pm f \<Longrightarrow> is_int_pm g \<Longrightarrow> is_int_pm (f + g)"
  by (simp add: is_int_pm_def plus_poly_mapping.rep_eq plus_fun_def is_int_fun_alt)

lemma minus_is_int_pm: "is_int_pm f \<Longrightarrow> is_int_pm g \<Longrightarrow> is_int_pm (f - g)"
  by (simp add: is_int_pm_def lookup_minus is_int_fun_alt)

lemma uminus_is_int_pm: "is_int_pm f \<Longrightarrow> is_int_pm (- f)"
  by (simp add: is_int_pm_def is_int_fun_alt)

lemma of_nat_pm_plus: "of_nat_pm (f + g) = of_nat_pm f + of_nat_pm g"
  by (rule poly_mapping_eqI, simp add: lookup_of_nat_pm lookup_add)

lemma of_nat_pm_minus: "g adds f \<Longrightarrow> of_nat_pm (f - g) = of_nat_pm f - of_nat_pm g"
  by (metis add_minus_2 addsE of_nat_pm_plus)

lemma of_int_pm_plus: "of_int_pm (f + g) = of_int_pm f + of_int_pm g"
  by (rule poly_mapping_eqI, simp add: lookup_of_int_pm lookup_add)

lemma Nats_deg: "is_nat_pm t \<Longrightarrow> deg_pm t \<in> \<nat>"
  by (auto simp: deg_pm_superset[OF subset_refl finite_keys] intro: Nats_sum dest: is_nat_pmD)

lemma Ints_deg: "is_int_pm t \<Longrightarrow> deg_pm t \<in> \<int>"
  by (auto simp: deg_pm_superset[OF subset_refl finite_keys] intro: Ints_sum dest: is_int_pmD)

lemma map_scale_is_nat_pm: "c \<in> \<nat> \<Longrightarrow> is_nat_pm t \<Longrightarrow> is_nat_pm (c \<cdot> t)"
  by (auto simp: is_nat_pm_def is_nat_fun_alt)

lemma map_scale_is_int_pm: "c \<in> \<int> \<Longrightarrow> is_int_pm t \<Longrightarrow> is_int_pm (c \<cdot> t)"
  by (auto simp: is_int_pm_def is_int_fun_alt)

lemma of_nat_pm_map_scale: "of_nat_pm (c \<cdot> t) = of_nat c \<cdot> of_nat_pm t"
  by (rule poly_mapping_eqI) (simp add: lookup_of_nat_pm)

subsubsection \<open>Composition\<close>

lemma to_int_pm_comp_of_int_pm [simp]: "to_int_pm (of_int_pm t) = t"
  by (rule poly_mapping_eqI, simp add: lookup_to_int_pm lookup_of_int_pm)

lemma to_nat_pm_comp_of_nat_pm [simp]: "to_nat_pm (of_nat_pm t) = t"
  by (rule poly_mapping_eqI, simp add: lookup_to_nat_pm lookup_of_nat_pm to_nat_def)

lemma to_nat_pm_comp_of_int_pm [simp]: "lookup (to_nat_pm (of_int_pm t)) = nat \<circ> (lookup t)"
  by (simp add: to_nat_pm.rep_eq of_int_pm.rep_eq to_nat_fun_comp_of_int_fun)

lemma of_nat_pm_comp_to_nat_pm: "is_nat_pm t \<Longrightarrow> of_nat_pm (to_nat_pm t) = t"
  by (simp add: is_nat_pm_def poly_mapping_eq_iff of_nat_pm.rep_eq to_nat_pm.rep_eq,
      intro of_nat_fun_comp_to_nat_fun)

lemma of_nat_pm_comp_to_nat_pm_eq_to_int_pm:
  "is_nat_pm (t::_ \<Rightarrow>\<^sub>0 _::floor_ceiling) \<Longrightarrow> of_nat_pm (to_nat_pm t) = to_int_pm t"
  by (simp add: is_nat_pm_def poly_mapping_eq_iff of_nat_pm.rep_eq to_nat_pm.rep_eq to_int_pm.rep_eq,
      intro of_nat_fun_comp_to_nat_fun_eq_to_int_fun)

lemma of_int_pm_comp_to_int_pm: "is_int_pm t \<Longrightarrow> of_int_pm (to_int_pm t) = t"
  by (simp add: is_int_pm_def poly_mapping_eq_iff of_int_pm.rep_eq to_int_pm.rep_eq,
      intro of_int_fun_comp_to_int_fun)

lemma of_int_pm_comp_of_nat_pm [simp]: "of_int_pm (of_nat_pm t) = of_nat_pm t"
  by (simp add: poly_mapping_eq_iff of_int_pm.rep_eq of_nat_pm.rep_eq, fact of_int_fun_comp_of_nat_fun)

lemma to_nat_deg_pm_le:
  assumes "is_int_pm t"
  shows "to_nat (deg_pm t) \<le> deg_pm (to_nat_pm t)"
proof -
  from subset_refl finite_keys have "deg_pm t = sum (lookup t) (keys t)" by (rule deg_pm_superset)
  also have "to_nat \<dots> \<le> (\<Sum>x\<in>keys t. to_nat (lookup t x))" by (intro to_nat_sum_le is_int_pmD assms)
  also have "\<dots> = sum (lookup (to_nat_pm t)) (keys t)" by (simp flip: lookup_to_nat_pm)
  also have "\<dots> = deg_pm (to_nat_pm t)"
    by (rule sym, rule deg_pm_superset)
        (auto simp add: in_keys_iff lookup_to_nat_pm simp del: lookup_not_eq_zero_eq_in_keys)
  finally show ?thesis .
qed

subsection \<open>Order relation on polynomial mappings\<close>

lemma le_of_nat_pm: "of_nat_pm s \<unlhd> ((of_nat_pm t)::_ \<Rightarrow>\<^sub>0 _::linordered_semidom) \<longleftrightarrow> s \<unlhd> t"
  by (simp add: le_pm_def of_nat_pm.rep_eq leq_of_nat_fun)

lemma zero_le_of_nat_pm: "0 \<unlhd> ((of_nat_pm t)::_ \<Rightarrow>\<^sub>0 _::linordered_semidom)"
  using le_of_nat_pm zero_le_pm by force

lemma le_of_int_pm: "of_int_pm s \<unlhd> ((of_int_pm t)::_ \<Rightarrow>\<^sub>0 _::linordered_idom) \<longleftrightarrow> s \<unlhd> t"
  by (simp add: le_pm_def of_int_pm.rep_eq leq_of_int_fun)

lemma to_nat_pm_mono: "s \<unlhd> t \<Longrightarrow> to_nat_pm s \<unlhd> to_nat_pm t"
  by (simp add: le_pm_def to_nat_pm.rep_eq to_nat_fun_mono)

lemma to_int_pm_mono: "s \<unlhd> t \<Longrightarrow> to_int_pm s \<unlhd> to_int_pm t"
  by (simp add: le_pm_def to_int_pm.rep_eq to_int_fun_mono)

lemma leD_to_int_pm:
  assumes "to_int_pm s \<unlhd> to_int_pm t" and "is_int_pm s" and "is_int_pm t"
  shows "s \<unlhd> t"
proof -
  from assms(2) have "s = of_int_pm (to_int_pm s)" by (simp only: of_int_pm_comp_to_int_pm)
  also from assms(1) have "\<dots> \<unlhd> of_int_pm (to_int_pm t)" by (simp only: le_of_int_pm)
  also from assms(3) have "\<dots> = t" by (simp only: of_int_pm_comp_to_int_pm)
  finally show ?thesis .
qed

lemma of_nat_to_nat_ge_pm: "is_int_pm t \<Longrightarrow> t \<unlhd> of_nat_pm (to_nat_pm t)"
  by (auto intro!: le_pmI of_nat_to_nat_ge is_int_pmD simp: lookup_of_nat_pm lookup_to_nat_pm)

end (* theory *)
