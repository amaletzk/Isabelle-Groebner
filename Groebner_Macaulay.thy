(* Author: Alexander Maletzky *)

theory Groebner_Macaulay
  imports Power_Products_PM Reduced_GB Macaulay_Matrix
begin

text \<open>Relationship between Gr\"obner bases and Macaulay matrices, following
  @{cite "Wiesinger-Widi2015"}.\<close>

subsection \<open>Gr\"obner Bases\<close>

context ordered_powerprod
begin

definition reduced_Macaulay_list :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "reduced_Macaulay_list ps = comp_min_basis_aux (Macaulay_list ps) []"

text \<open>It is important to note that in @{const reduced_Macaulay_list} there is no need to remove
  duplicate leading power-products (because there are none), nor to make the polynomials monic
  (because they already are).\<close>

lemma reduced_Macaulay_list_subset_Macaulay_list:
  "set (reduced_Macaulay_list ps) \<subseteq> set (Macaulay_list ps)"
  by (simp only: reduced_Macaulay_list_def, rule comp_min_basis_aux_Nil_subset)

lemma reduced_Macaulay_list_not_zero: "0 \<notin> set (reduced_Macaulay_list ps)"
  using Macaulay_list_not_zero reduced_Macaulay_list_subset_Macaulay_list by auto
                                                               
lemma reduced_Macaulay_list_is_monic_set: "is_monic_set (set (reduced_Macaulay_list ps))"
proof (rule is_monic_setI)
  fix b
  assume "b \<in> set (reduced_Macaulay_list ps)"
  with reduced_Macaulay_list_subset_Macaulay_list have "b \<in> set (Macaulay_list ps)" ..
  moreover assume "b \<noteq> 0"
  ultimately show "lc b = 1" by (rule is_monic_setD[OF Macaulay_list_is_monic_set])
qed

end (* ordered_powerprod *)

context gd_powerprod
begin

lemma reduced_Macaulay_list_is_minimal_basis: "is_minimal_basis (set (reduced_Macaulay_list ps))"
proof (rule is_minimal_basisI)
  fix p
  assume "p \<in> set (reduced_Macaulay_list ps)"
  with reduced_Macaulay_list_not_zero show "p \<noteq> 0" by auto
next
  fix p q
  assume "p \<in> set (reduced_Macaulay_list ps)" and q_in: "q \<in> set (reduced_Macaulay_list ps)"
    and "p \<noteq> q"
  from reduced_Macaulay_list_subset_Macaulay_list this(1) have p_in: "p \<in> set (Macaulay_list ps)" ..
  from q_in have "q \<in> set (comp_min_basis_aux (Macaulay_list ps) [])"
    by (simp only: reduced_Macaulay_list_def)
  moreover note p_in
  moreover from \<open>p \<noteq> q\<close> have "q \<noteq> p" ..
  ultimately show "\<not> lp p adds lp q"
  proof (rule comp_min_basis_aux_Nil_nadds)
    show "0 \<notin> set (Macaulay_list ps)" by (fact Macaulay_list_not_zero)
  next
    fix x y :: "('a, 'b) poly_mapping"
    assume "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)"
    moreover assume "x \<noteq> y"
    ultimately show "lp x \<noteq> lp y" by (rule Macaulay_list_distinct_lp)
  qed
qed

lemma pideal_reduced_Macaulay_list:
  assumes "is_Groebner_basis (set (Macaulay_list ps))"
  shows "pideal (set (reduced_Macaulay_list ps)) = pideal (set ps)"
proof -
  have "pideal (set (reduced_Macaulay_list ps)) = pideal (set (Macaulay_list ps))"
    unfolding reduced_Macaulay_list_def by (rule comp_min_basis_aux_Nil_pideal, fact assms,
        fact Macaulay_list_not_zero, fact Macaulay_list_distinct_lp)
  also have "... = pideal (set ps)" by (simp only: pideal_Macaulay_list)
  finally show ?thesis .
qed

lemma Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pideal (set ps) = pideal G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (Macaulay_list ps))"
proof (simp only: GB_alt_3_finite[OF finite_set] pideal_Macaulay_list, intro ballI impI)
  fix f
  assume "f \<in> pideal (set ps)"
  also from assms(2) have "... = pideal G" .
  finally have "f \<in> pideal G" .
  assume "f \<noteq> 0"
  with assms(1) \<open>f \<in> pideal G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by (rule GB_adds_lp)
  from assms(3) \<open>g \<in> G\<close> have "g \<in> phull (set ps)" ..
  from this \<open>g \<noteq> 0\<close> obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lp g = lp g'"
    by (rule Macaulay_list_lp)
  show "\<exists>g\<in>set (Macaulay_list ps). g \<noteq> 0 \<and> lp g adds lp f"
  proof (rule, rule)
    from \<open>lp g adds lp f\<close> show "lp g' adds lp f" by (simp only: \<open>lp g = lp g'\<close>)
  qed fact+
qed

lemma reduced_Macaulay_list_lp:
  assumes "p \<in> phull (set ps)" and "p \<noteq> 0"
  obtains g where "g \<in> set (reduced_Macaulay_list ps)" and "g \<noteq> 0" and "lp g adds lp p"
proof -
  from assms obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lp p = lp g'"
    by (rule Macaulay_list_lp)
  obtain g where "g \<in> set (reduced_Macaulay_list ps)" and "lp g adds lp g'"
  proof (simp only: reduced_Macaulay_list_def, rule comp_min_basis_aux_Nil_adds)
    show "g' \<in> set (Macaulay_list ps)" by fact
  next
    show "0 \<notin> set (Macaulay_list ps)" by (fact Macaulay_list_not_zero)
  next
    fix x y
    assume "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)" and "x \<noteq> y"
    thus "lp x \<noteq> lp y" by (rule Macaulay_list_distinct_lp)
  qed

  from this(1) show ?thesis
  proof
    from \<open>g \<in> set (reduced_Macaulay_list ps)\<close> reduced_Macaulay_list_not_zero show "g \<noteq> 0" by auto
  next
    from \<open>lp g adds lp g'\<close> show "lp g adds lp p" by (simp only: \<open>lp p = lp g'\<close>)
  qed
qed

lemma reduced_Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pideal (set ps) = pideal G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (reduced_Macaulay_list ps))"
  unfolding reduced_Macaulay_list_def
  apply (rule comp_min_basis_aux_Nil_GB)
  subgoal by (rule Macaulay_list_is_GB, fact, fact, fact)
  subgoal by (fact Macaulay_list_not_zero)
  subgoal by (fact Macaulay_list_distinct_lp)
  done

lemma reduced_Macaulay_list_is_reduced_GB:
  assumes "finite F" and "pideal (set ps) = pideal F" and "reduced_GB F \<subseteq> phull (set ps)"
  shows "set (reduced_Macaulay_list ps) = reduced_GB F"
proof -
  from assms(1) have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_finite)
  hence "is_Groebner_basis (reduced_GB F)" by (rule reduced_GB_D1)
  have aux: "pideal (reduced_GB F) = pideal (set ps)"
    by (simp only: assms(2), rule reduced_GB_pideal_finite, fact)
  have pideal: "pideal (set (reduced_Macaulay_list ps)) = pideal (reduced_GB F)"
    unfolding aux
    by (rule pideal_reduced_Macaulay_list, rule Macaulay_list_is_GB, fact, simp only: aux, fact)
  show ?thesis
  proof (rule minimal_basis_is_reduced_GB, fact reduced_Macaulay_list_is_minimal_basis,
        fact reduced_Macaulay_list_is_monic_set, fact, rule is_reduced_GB_subsetI, fact,
        rule reduced_Macaulay_list_is_GB, fact, simp only: aux, fact,
        fact reduced_Macaulay_list_is_monic_set)
    fix a b :: "('a, 'b) poly_mapping"
    let ?c = "a - b"
    let ?S = "Keys (set ps)"
    let ?ts = "pps_to_list ?S"
    let ?A = "Macaulay_mat ps"
    let ?E = "row_echelon ?A"
    have "card ?S = dim_col ?E" by simp

    assume "b \<in> set (reduced_Macaulay_list ps)"
    with reduced_Macaulay_list_subset_Macaulay_list have "b \<in> set (Macaulay_list ps)" ..
    moreover obtain f where pf: "pivot_fun ?E f (dim_col ?E)" by (rule row_echelon_pivot_fun)
    ultimately obtain i1 where "i1 < dim_row ?E" and b: "b = mat_to_polys (Keys_to_list ps) ?E ! i1"
      and "f i1 < dim_col ?E" by (rule in_Macaulay_listE)
    from \<open>card ?S = dim_col ?E\<close> pf this(1) this(3) have lpb: "lp b = ?ts ! (f i1)"
      by (simp only: b Keys_to_list_eq_pps_to_list, rule lp_row_to_poly_pivot_fun)
    from \<open>b \<in> set (Macaulay_list ps)\<close> have "b \<in> phull (set (Macaulay_list ps))"
      by (rule generator_in_phull)
    hence "b \<in> phull (set ps)" by (simp only: phull_Macaulay_list)

    assume "a \<in> reduced_GB F"
    from assms(3) this have "a \<in> phull (set ps)" ..
    from this \<open>b \<in> phull (set ps)\<close> have "?c \<in> phull (set ps)" by (rule phull_closed_minus)
    moreover assume "?c \<noteq> 0"
    ultimately obtain r where "r \<in> set (Macaulay_list ps)" and "r \<noteq> 0" and "lp ?c = lp r"
      by (rule Macaulay_list_lp)
    from this(1) pf obtain i2 where "i2 < dim_row ?E" and r: "r = mat_to_polys (Keys_to_list ps) ?E ! i2"
      and "f i2 < dim_col ?E" by (rule in_Macaulay_listE)
    from \<open>card ?S = dim_col ?E\<close> pf this(1) this(3) have lpr: "lp r = ?ts ! (f i2)"
      by (simp only: r Keys_to_list_eq_pps_to_list, rule lp_row_to_poly_pivot_fun)

    assume "lp ?c \<in> keys b"
    hence "(?ts ! (f i2)) \<in> keys (mat_to_polys ?ts ?E ! i1)"
      by (simp only: \<open>lp ?c = lp r\<close> lpr b[symmetric] Keys_to_list_eq_pps_to_list[symmetric])
    with \<open>card ?S = dim_col ?E\<close> pf \<open>i2 < dim_row ?E\<close> \<open>i1 < dim_row ?E\<close> \<open>f i2 < dim_col ?E\<close> have "i2 = i1"
      by (rule lp_row_to_poly_pivot_in_keysD)
    hence "r = b" by (simp only: r b)
    hence "lp ?c = lp b" by (simp only: \<open>lp ?c = lp r\<close>)

    moreover assume "lp ?c \<prec> lp b"
    ultimately show False by simp
  next
    show "pideal (reduced_GB F) = pideal (set (reduced_Macaulay_list ps))" by (simp only: pideal)
  qed fact
qed

end (* gd_powerprod *)

subsection \<open>Bounds\<close>

context pm_powerprod
begin

abbreviation Polys where "Polys n \<equiv> dgrad_p_set varnum n"

definition deg_set :: "nat \<Rightarrow> nat \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat) set"
  where "deg_set n d = {t. varnum t \<le> n \<and> deg_pm t \<le> d}"

definition deg_shifts :: "nat \<Rightarrow> nat \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_1) list"
  where "deg_shifts n d fs = concat (map (\<lambda>f. (map (\<lambda>t. monom_mult 1 t f) (pps_to_list (deg_set n d)))) fs)"

lemma keys_subset_deg_setI:
  assumes "p \<in> Polys n" and "poly_deg p \<le> d"
  shows "keys p \<subseteq> deg_set n d"
proof
  fix t
  assume "t \<in> keys p"
  hence "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
  from this assms(2) have "deg_pm t \<le> d" by (rule le_trans)
  moreover from assms(1) \<open>t \<in> keys p\<close> have "varnum t \<le> n" by (rule dgrad_p_setD)
  ultimately show "t \<in> deg_set n d" by (simp add: deg_set_def)
qed

lemma finite_deg_set: "finite (deg_set n d)"
proof (induct d)
  case 0
  show ?case by (simp add: deg_set_def)
next
  case (Suc d)
  have eq: "deg_set n (Suc d) = deg_set n d \<union> {t. varnum t \<le> n \<and> deg_pm t = Suc d}" (is "_ = _ \<union> ?A")
    by (auto simp add: deg_set_def)
  have "?A \<subseteq> (\<Union>x\<in>{y. elem_index y < n}. (+) (Poly_Mapping.single x 1) ` deg_set n d)" (is "_ \<subseteq> ?B")
  proof (rule, simp, elim conjE)
    fix t::"'n \<Rightarrow>\<^sub>0 nat"
    assume "varnum t \<le> n" and "deg_pm t = Suc d"
    from this(2) have "deg_pm t \<noteq> 0" by simp
    hence "keys t \<noteq> {}" by simp
    then obtain x where "x \<in> keys t" by blast
    hence "lookup t x \<noteq> 0" by (simp only: lookup_not_eq_zero_eq_in_keys)
    then obtain d' where "lookup t x = Suc d'" using not0_implies_Suc by blast
    show "\<exists>x. elem_index x < n \<and> t \<in> (+) (Poly_Mapping.single x (Suc 0)) ` deg_set n d"
    proof (intro exI conjI)
      from \<open>x \<in> keys t\<close> have "elem_index x < varnum t" by (rule elem_index_less_varnum)
      from this \<open>varnum t \<le> n\<close> show "elem_index x < n" by simp
    next
      let ?x = "Poly_Mapping.single x (Suc 0)"
      have "deg_pm ?x = (\<Sum>k\<in>keys ?x. lookup ?x k)"
        by (rule deg_pm_superset, fact subset_refl, fact finite_keys)
      hence "deg_pm ?x = Suc 0" by simp
      have "?x adds t"
      proof (rule adds_pmI, rule le_pmI, simp add: lookup_single when_def, rule impI)
        fix y
        assume "x = y"
        with \<open>lookup t x = Suc d'\<close> have "lookup t y = Suc d'" by simp
        thus "Suc 0 \<le> lookup t y" by simp
      qed
      show "t \<in> (+) (monomial (Suc 0) x) ` deg_set n d"
      proof
        from \<open>?x adds t\<close> show "t = Poly_Mapping.single x (Suc 0) + (t - ?x)"
          by (metis add.commute adds_minus)
      next
        show "t - ?x \<in> deg_set n d"
        proof (simp add: deg_set_def, rule)
          from dickson_grading_varnum \<open>?x adds t\<close> have "varnum (t - ?x) \<le> varnum t"
            by (rule dickson_grading_minus)
          from this \<open>varnum t \<le> n\<close> show "varnum (t - ?x) \<le> n" by (rule le_trans)
        next
          from \<open>?x adds t\<close> obtain s where "t = ?x + s" ..
          have "Suc d = deg_pm t" by (simp only: \<open>deg_pm t = Suc d\<close>)
          also have "... = deg_pm ?x + deg_pm s" by (simp add: \<open>t = ?x + s\<close> deg_pm_plus)
          also have "... = Suc (deg_pm s)" by (simp add: \<open>deg_pm ?x = Suc 0\<close>)
          finally show "deg_pm (t - ?x) \<le> d" by (simp add: \<open>t = ?x + s\<close>)
        qed
      qed
    qed
  qed
  moreover from finite_nat_seg have "finite ?B"
  proof (rule finite_UN_I)
    fix x
    from Suc show "finite ((+) (Poly_Mapping.single x 1) ` deg_set n d)" by (rule finite_imageI)
  qed
  ultimately have "finite ?A" by (rule finite_subset)
  with Suc show ?case by (simp add: eq)
qed

lemma zero_in_deg_set: "0 \<in> deg_set n d"
  by (simp add: deg_set_def)

lemma set_deg_shifts: "set (deg_shifts n d fs) = (\<Union>f\<in>set fs. (\<lambda>t. monom_mult 1 t f) ` (deg_set n d))"
  by (simp add: deg_shifts_def set_pps_to_list[OF finite_deg_set])

lemma set_deg_shifts_2: "set (deg_shifts n d fs) = (\<Union>t\<in>deg_set n d. monom_mult 1 t ` set fs)"
  by (auto simp add: set_deg_shifts)

corollary set_deg_shifts_singleton: "set (deg_shifts n d [f]) = (\<lambda>t. monom_mult 1 t f) ` (deg_set n d)"
  by (simp add: set_deg_shifts)

lemma deg_shifts_superset: "set fs \<subseteq> set (deg_shifts n d fs)"
proof -
  have "set fs = (monom_mult 1 0) ` set fs" by (simp add: image_cong monom_mult_left1)
  also from zero_in_deg_set have "... \<subseteq> set (deg_shifts n d fs)"
    by (simp only: set_deg_shifts_2, rule UN_upper)
  finally show ?thesis .
qed

lemma deg_shifts_mono:
  assumes "set fs \<subseteq> set gs"
  shows "set (deg_shifts n d fs) \<subseteq> set (deg_shifts n d gs)"
  using assms by (auto simp add: set_deg_shifts)

lemma pideal_deg_shifts [simp]: "pideal (set (deg_shifts n d fs)) = pideal (set fs)"
proof
  show "pideal (set (deg_shifts n d fs)) \<subseteq> pideal (set fs)"
    by (rule pideal_subset_pidealI, simp add: set_deg_shifts_2 UN_subset_iff,
        intro ballI image_subsetI monom_mult_in_pideal)
next
  from deg_shifts_superset show "pideal (set fs) \<subseteq> pideal (set (deg_shifts n d fs))"
    by (rule pideal_mono)
qed

definition is_cofactor_bound :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_0) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_cofactor_bound F b \<longleftrightarrow> 
    (\<forall>p\<in>pideal F. \<exists>q. p = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f\<in>F. q f \<noteq> 0 \<longrightarrow> poly_deg (q f) \<le> poly_deg p + b))"

text \<open>@{const is_cofactor_bound} is only true for @{emph \<open>finite\<close>} sets \<open>F\<close>.\<close>

definition is_GB_bound :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_GB_bound F b \<longleftrightarrow> (\<forall>g\<in>reduced_GB F. poly_deg g \<le> b)"

definition truncate_p :: "('n \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b)"
  where "truncate_p V p = p"

lemma is_cofactor_boundI:
  assumes "\<And>p. p \<in> pideal F \<Longrightarrow> \<exists>q. p = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f\<in>F. q f \<noteq> 0 \<longrightarrow> poly_deg (q f) \<le> poly_deg p + b)"
  shows "is_cofactor_bound F b"
  unfolding is_cofactor_bound_def using assms by blast

lemma is_cofactor_boundE:
  assumes "is_cofactor_bound F b" and "p \<in> pideal F"
  obtains q where "p = (\<Sum>f\<in>F. q f * f)"
    and "\<And>f. f \<in> F \<Longrightarrow> q f \<noteq> 0 \<Longrightarrow>
             dgrad_p_set_le varnum {q f} (insert p F) \<and> poly_deg (q f) \<le> poly_deg p + b"
  using assms unfolding is_cofactor_bound_def sorry (*by blast*)

(* For proving the above lemma we need to formalize the evaluation homomorphism. *)

lemma is_GB_boundI:
  assumes "\<And>g. g \<in> reduced_GB F \<Longrightarrow> poly_deg g \<le> b"
  shows "is_GB_bound F b"
  unfolding is_GB_bound_def using assms by blast

lemma is_GB_boundE:
  assumes "is_GB_bound F b" and "g \<in> reduced_GB F"
  shows "poly_deg g \<le> b"
  using assms unfolding is_GB_bound_def by blast

theorem thm_2_3_6:
  assumes "set fs \<subseteq> Polys n" and "is_cofactor_bound (set fs) b1" and "is_GB_bound (set fs) b2"
  shows "set (reduced_Macaulay_list (deg_shifts n (b1 + b2) fs)) = reduced_GB (set fs)"
proof (rule reduced_Macaulay_list_is_reduced_GB)
  let ?H = "phull (set (deg_shifts n (b1 + b2) fs))"
  have "1 \<noteq> (0::'a)" by simp
  from dickson_grading_varnum assms(1) have "reduced_GB (set fs) \<subseteq> Polys n"
    by (rule reduced_GB_dgrad_p_set)
  show "reduced_GB (set fs) \<subseteq> ?H"
  proof
    fix g
    assume "g \<in> reduced_GB (set fs)"
    hence "g \<in> pideal (reduced_GB (set fs))" by (rule generator_in_pideal)
    hence "g \<in> pideal (set fs)" by (simp add: reduced_GB_pideal_finite)
    with assms(2) obtain q where g: "g = (\<Sum>f\<in>(set fs). q f * f)"
      and 1: "\<And>f. f \<in> set fs \<Longrightarrow> q f \<noteq> 0 \<Longrightarrow>
                dgrad_p_set_le varnum {q f} (insert g (set fs)) \<and> poly_deg (q f) \<le> poly_deg g + b1"
      by (rule is_cofactor_boundE, blast)
    show "g \<in> ?H" unfolding g
    proof (rule phull_closed_sum)
      fix f
      assume "f \<in> set fs"
      show "q f * f \<in> ?H"
      proof (cases "f = 0 \<or> q f = 0")
        case True
        thus ?thesis by (auto simp add: zero_in_phull)
      next
        case False
        hence "f \<noteq> 0" and "q f \<noteq> 0" by simp_all
        from \<open>f \<in> set fs\<close> this(2)
        have "dgrad_p_set_le varnum {q f} (insert g (set fs)) \<and> poly_deg (q f) \<le> poly_deg g + b1"
          by (rule 1)
        hence "dgrad_p_set_le varnum {q f} (insert g (set fs))" and "poly_deg (q f) \<le> poly_deg g + b1"
          by simp_all
        note this(1)
        moreover have "insert g (set fs) \<subseteq> Polys n" by (rule insert_subsetI, rule set_rev_mp, fact+)
        ultimately have "{q f} \<subseteq> Polys n" by (rule dgrad_p_set_le_dgrad_p_set)
        hence "q f \<in> Polys n" by simp
        from assms(3) \<open>g \<in> reduced_GB (set fs)\<close> have "poly_deg g \<le> b2" by (rule is_GB_boundE)
        with \<open>poly_deg (q f) \<le> poly_deg g + b1\<close> have "poly_deg (q f) \<le> b1 + b2" by simp
        with \<open>q f \<in> Polys n\<close> have "keys (q f) \<subseteq> deg_set n (b1 + b2)" by (rule keys_subset_deg_setI)
        with finite_deg_set have "q f * f = (\<Sum>t\<in>deg_set n (b1 + b2). monom_mult (lookup (q f) t) t f)"
          unfolding times_sum_monomials
        proof (rule sum.mono_neutral_left)
          show "\<forall>t\<in>deg_set n (b1 + b2) - keys (q f). monom_mult (lookup (q f) t) t f = 0"
            by (rule, simp add: monom_mult_left0)
        qed
        thm sum.reindex
        also have "... = (\<Sum>t\<in>deg_set n (b1 + b2). monom_mult (lookup (q f) t) 0 (monom_mult 1 t f))"
          by (simp add: monom_mult_assoc)
        also have "... = (\<Sum>t\<in>deg_set n (b1 + b2).
                    ((\<lambda>f0. monom_mult (lookup (q f) (lp f0 - lp f)) 0 f0) \<circ> (\<lambda>t. monom_mult 1 t f)) t)"
          by (rule sum.cong, fact refl, simp add: lp_monom_mult[OF \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close>])
        also have "... = (\<Sum>f0\<in>set (deg_shifts n (b1 + b2) [f]).
                                        monom_mult (lookup (q f) (lp f0 - lp f)) 0 f0)"
        proof (simp only: set_deg_shifts_singleton, rule sum.reindex[symmetric], rule inj_onI)
          fix s t
          assume "monom_mult 1 s f = monom_mult 1 t f"
          thus "s = t" using \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close> by (rule monom_mult_inj_2)
        qed
        finally have "q f * f \<in> phull (set (deg_shifts n (b1 + b2) [f]))" by (simp add: sum_in_phullI)
        thus ?thesis
        proof
          show "phull (set (deg_shifts n (b1 + b2) [f])) \<subseteq> ?H"
            by (rule phull_mono, rule deg_shifts_mono, simp add: \<open>f \<in> set fs\<close>)
        qed
      qed
    qed
  qed
qed simp_all

theorem thm_2_3_7:
  assumes "set fs \<subseteq> Polys n" and "is_cofactor_bound (set fs) b"
  shows "1 \<in> pideal (set fs) \<longleftrightarrow> 1 \<in> set (Macaulay_list (deg_shifts n b fs))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  hence "pideal (set fs) = UNIV" by (simp only: pideal_eq_UNIV_iff_contains_one)
  hence eq: "reduced_GB (set fs) = {1}"
    by (simp only: pideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set[OF dickson_grading_varnum assms(1)])
  have "is_GB_bound (set fs) 0" by (rule is_GB_boundI, simp add: eq poly_deg_def)
  with assms have "set (reduced_Macaulay_list (deg_shifts n (b + 0) fs)) = reduced_GB (set fs)"
    by (rule thm_2_3_6)
  hence "{1} = set (reduced_Macaulay_list (deg_shifts n b fs))" by (simp add: eq)
  also have "... \<subseteq> set (Macaulay_list (deg_shifts n b fs))"
    by (fact reduced_Macaulay_list_subset_Macaulay_list)
  finally show ?R by simp
next
  assume ?R
  also have "... \<subseteq> phull (set (Macaulay_list (deg_shifts n b fs)))" by (rule generator_subset_phull)
  also have "... = phull (set (deg_shifts n b fs))" by (fact phull_Macaulay_list)
  also have "... \<subseteq> pideal (set (deg_shifts n b fs))" by (fact phull_subset_pideal)
  finally show ?L by simp
qed

theorem Hermann_bound:
  assumes "finite F" and "F \<subseteq> Polys n"
  shows "is_cofactor_bound F (\<Sum>j=0..<n. (card F * maxdeg F)^(2^j))"
  sorry

theorem Dube_bound:
  assumes "finite F" and "F \<subseteq> Polys n"
  shows "is_GB_bound F (2 * ((maxdeg F)^2 div 2 + maxdeg F)^(2^(n - 1)))"
  sorry

end (* pm_powerprod *)

end (* theory *)
