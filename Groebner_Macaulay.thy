(* Author: Alexander Maletzky *)

theory Groebner_Macaulay
  imports MPoly_PM Groebner_Bases.Reduced_GB Groebner_Bases.Macaulay_Matrix
begin

text \<open>Relationship between Gr\"obner bases and Macaulay matrices, following
  @{cite "Wiesinger-Widi2015"}.\<close>

subsection \<open>Gr\"obner Bases\<close>

context ordered_term
begin

definition reduced_Macaulay_list :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
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

end (* ordered_term *)

context gd_term
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
  ultimately show "\<not> lt p adds\<^sub>t lt q"
  proof (rule comp_min_basis_aux_Nil_nadds)
    show "0 \<notin> set (Macaulay_list ps)" by (fact Macaulay_list_not_zero)
  next
    fix x y :: "'t \<Rightarrow>\<^sub>0 'b"
    assume "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)"
    moreover assume "x \<noteq> y"
    ultimately show "lt x \<noteq> lt y" by (rule Macaulay_list_distinct_lt)
  qed
qed

lemma pmdl_reduced_Macaulay_list:
  assumes "is_Groebner_basis (set (Macaulay_list ps))"
  shows "pmdl (set (reduced_Macaulay_list ps)) = pmdl (set ps)"
proof -
  have "pmdl (set (reduced_Macaulay_list ps)) = pmdl (set (Macaulay_list ps))"
    unfolding reduced_Macaulay_list_def by (rule comp_min_basis_aux_Nil_pmdl, fact assms,
        fact Macaulay_list_not_zero, fact Macaulay_list_distinct_lt)
  also have "... = pmdl (set ps)" by (simp only: pmdl_Macaulay_list)
  finally show ?thesis .
qed

lemma Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pmdl (set ps) = pmdl G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (Macaulay_list ps))"
proof (simp only: GB_alt_3_finite[OF finite_set] pmdl_Macaulay_list, intro ballI impI)
  fix f
  assume "f \<in> pmdl (set ps)"
  also from assms(2) have "... = pmdl G" .
  finally have "f \<in> pmdl G" .
  assume "f \<noteq> 0"
  with assms(1) \<open>f \<in> pmdl G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f" by (rule GB_adds_lt)
  from assms(3) \<open>g \<in> G\<close> have "g \<in> phull (set ps)" ..
  from this \<open>g \<noteq> 0\<close> obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lt g = lt g'"
    by (rule Macaulay_list_lt)
  show "\<exists>g\<in>set (Macaulay_list ps). g \<noteq> 0 \<and> lt g adds\<^sub>t lt f"
  proof (rule, rule)
    from \<open>lt g adds\<^sub>t lt f\<close> show "lt g' adds\<^sub>t lt f" by (simp only: \<open>lt g = lt g'\<close>)
  qed fact+
qed

lemma reduced_Macaulay_list_lp:
  assumes "p \<in> phull (set ps)" and "p \<noteq> 0"
  obtains g where "g \<in> set (reduced_Macaulay_list ps)" and "g \<noteq> 0" and "lt g adds\<^sub>t lt p"
proof -
  from assms obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lt p = lt g'"
    by (rule Macaulay_list_lt)
  obtain g where "g \<in> set (reduced_Macaulay_list ps)" and "lt g adds\<^sub>t lt g'"
  proof (simp only: reduced_Macaulay_list_def, rule comp_min_basis_aux_Nil_adds)
    show "g' \<in> set (Macaulay_list ps)" by fact
  next
    show "0 \<notin> set (Macaulay_list ps)" by (fact Macaulay_list_not_zero)
  next
    fix x y
    assume "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)" and "x \<noteq> y"
    thus "lt x \<noteq> lt y" by (rule Macaulay_list_distinct_lt)
  qed

  from this(1) show ?thesis
  proof
    from \<open>g \<in> set (reduced_Macaulay_list ps)\<close> reduced_Macaulay_list_not_zero show "g \<noteq> 0" by auto
  next
    from \<open>lt g adds\<^sub>t lt g'\<close> show "lt g adds\<^sub>t lt p" by (simp only: \<open>lt p = lt g'\<close>)
  qed
qed

lemma reduced_Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pmdl (set ps) = pmdl G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (reduced_Macaulay_list ps))"
  unfolding reduced_Macaulay_list_def
  apply (rule comp_min_basis_aux_Nil_GB)
  subgoal by (rule Macaulay_list_is_GB, fact, fact, fact)
  subgoal by (fact Macaulay_list_not_zero)
  subgoal by (fact Macaulay_list_distinct_lt)
  done

lemma reduced_Macaulay_list_is_reduced_GB:
  assumes "finite F" and "pmdl (set ps) = pmdl F" and "reduced_GB F \<subseteq> phull (set ps)"
  shows "set (reduced_Macaulay_list ps) = reduced_GB F"
proof -
  from assms(1) have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_finite)
  hence "is_Groebner_basis (reduced_GB F)" by (rule reduced_GB_D1)
  have aux: "pmdl (reduced_GB F) = pmdl (set ps)"
    by (simp only: assms(2), rule reduced_GB_pmdl_finite, fact)
  have pmdl: "pmdl (set (reduced_Macaulay_list ps)) = pmdl (reduced_GB F)"
    unfolding aux
    by (rule pmdl_reduced_Macaulay_list, rule Macaulay_list_is_GB, fact, simp only: aux, fact)
  show ?thesis
  proof (rule minimal_basis_is_reduced_GB, fact reduced_Macaulay_list_is_minimal_basis,
        fact reduced_Macaulay_list_is_monic_set, fact, rule is_reduced_GB_subsetI, fact,
        rule reduced_Macaulay_list_is_GB, fact, simp only: aux, fact,
        fact reduced_Macaulay_list_is_monic_set)
    fix a b :: "'t \<Rightarrow>\<^sub>0 'b"
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
    from \<open>card ?S = dim_col ?E\<close> pf this(1) this(3) have ltb: "lt b = ?ts ! (f i1)"
      by (simp only: b Keys_to_list_eq_pps_to_list, rule lt_row_to_poly_pivot_fun)
    from \<open>b \<in> set (Macaulay_list ps)\<close> have "b \<in> phull (set (Macaulay_list ps))"
      by (rule phull.generator_in_module)
    hence "b \<in> phull (set ps)" by (simp only: phull_Macaulay_list)

    assume "a \<in> reduced_GB F"
    from assms(3) this have "a \<in> phull (set ps)" ..
    from this \<open>b \<in> phull (set ps)\<close> have "?c \<in> phull (set ps)" by (rule phull.module_closed_minus)
    moreover assume "?c \<noteq> 0"
    ultimately obtain r where "r \<in> set (Macaulay_list ps)" and "r \<noteq> 0" and "lt ?c = lt r"
      by (rule Macaulay_list_lt)
    from this(1) pf obtain i2 where "i2 < dim_row ?E" and r: "r = mat_to_polys (Keys_to_list ps) ?E ! i2"
      and "f i2 < dim_col ?E" by (rule in_Macaulay_listE)
    from \<open>card ?S = dim_col ?E\<close> pf this(1) this(3) have ltr: "lt r = ?ts ! (f i2)"
      by (simp only: r Keys_to_list_eq_pps_to_list, rule lt_row_to_poly_pivot_fun)

    assume "lt ?c \<in> keys b"
    hence "(?ts ! (f i2)) \<in> keys (mat_to_polys ?ts ?E ! i1)"
      by (simp only: \<open>lt ?c = lt r\<close> ltr b[symmetric] Keys_to_list_eq_pps_to_list[symmetric])
    with \<open>card ?S = dim_col ?E\<close> pf \<open>i2 < dim_row ?E\<close> \<open>i1 < dim_row ?E\<close> \<open>f i2 < dim_col ?E\<close> have "i2 = i1"
      by (rule lt_row_to_poly_pivot_in_keysD)
    hence "r = b" by (simp only: r b)
    hence "lt ?c = lt b" by (simp only: \<open>lt ?c = lt r\<close>)

    moreover assume "lt ?c \<prec>\<^sub>t lt b"
    ultimately show False by simp
  next
    show "pmdl (reduced_GB F) = pmdl (set (reduced_Macaulay_list ps))" by (simp only: pmdl)
  qed fact
qed

end (* gd_term *)

subsection \<open>Bounds\<close>

context pm_powerprod
begin

definition is_cofactor_bound :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::ring_1) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_cofactor_bound F b \<longleftrightarrow>
    (\<forall>p\<in>ideal F. \<exists>q. p = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f\<in>F. q f \<noteq> 0 \<longrightarrow> poly_deg (q f) \<le> poly_deg p + b))"

text \<open>Note that @{const is_cofactor_bound} is only true for @{emph \<open>finite\<close>} sets \<open>F\<close>.\<close>

definition is_GB_bound :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_GB_bound F b \<longleftrightarrow> (\<forall>g\<in>punit.reduced_GB F. poly_deg g \<le> b)"

lemma is_cofactor_boundI:
  assumes "\<And>p. p \<in> ideal F \<Longrightarrow> \<exists>q. p = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f\<in>F. q f \<noteq> 0 \<longrightarrow> poly_deg (q f) \<le> poly_deg p + b)"
  shows "is_cofactor_bound F b"
  unfolding is_cofactor_bound_def using assms by blast

lemma is_cofactor_boundE:
  assumes "is_cofactor_bound F b" and "(p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_ring_1) \<in> ideal F"
  obtains q where "p = (\<Sum>f\<in>F. q f * f)"
    and "\<And>f. f \<in> F \<Longrightarrow> q f \<noteq> 0 \<Longrightarrow>
             indets (q f) \<subseteq> UNION (insert p F) indets \<and> poly_deg (q f) \<le> poly_deg p + b"
proof (cases "p = 0")
  case True
  define q where "q = (\<lambda>f::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b. 0::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b)"
  show ?thesis
  proof
    show "p = (\<Sum>f\<in>F. q f * f)" by (simp add: True q_def)
  next
    fix f
    assume "q f \<noteq> 0"
    thus "indets (q f) \<subseteq> UNION (insert p F) indets \<and> poly_deg (q f) \<le> poly_deg p + b"
      by (simp only: q_def)
  qed
next
  case False
  from assms obtain q0
    where p: "p = (\<Sum>f\<in>F. q0 f * f)"
    and q0: "\<And>f. f \<in> F \<Longrightarrow> q0 f \<noteq> 0 \<Longrightarrow> poly_deg (q0 f) \<le> poly_deg p + b"
    using assms unfolding is_cofactor_bound_def by blast
  define sub where "sub = (\<lambda>x::'x. if x \<in> (\<Union>t\<in>Keys (insert p F). keys t) then
                                     monomial (1::'b) (Poly_Mapping.single x (1::nat))
                                   else 1)"
  have 1: "x \<in> indets p \<Longrightarrow> sub x = monomial 1 (monomial 1 x)" for x
  proof (simp add: sub_def, rule)
    assume "x \<in> indets p"
    then obtain t where "t \<in> keys p" and "x \<in> keys t" by (rule in_indetsE)
    from this(1) have "t \<in> Keys (insert p F)" by (simp add: Keys_insert)
    moreover assume "\<forall>t\<in>Keys (insert p F). lookup t x = 0"
    ultimately have "lookup t x = 0" by blast
    with \<open>x \<in> keys t\<close> show "monomial 1 (monomial (Suc 0) x) = 1" unfolding in_keys_iff ..
  qed
  have 2: "f \<in> F \<Longrightarrow> x \<in> indets f \<Longrightarrow> sub x = monomial 1 (monomial 1 x)" for f x
  proof (simp add: sub_def, rule)
    assume "f \<in> F"
    assume "x \<in> indets f"
    then obtain t where "t \<in> keys f" and "x \<in> keys t" by (rule in_indetsE)
    from this(1) \<open>f \<in> F\<close> have "t \<in> Keys F" by (rule in_KeysI)
    hence "t \<in> Keys (insert p F)" by (simp add: Keys_insert)
    moreover assume "\<forall>t\<in>Keys (insert p F). lookup t x = 0"
    ultimately have "lookup t x = 0" by blast
    with \<open>x \<in> keys t\<close> show "monomial 1 (monomial (Suc 0) x) = 1" unfolding in_keys_iff ..
  qed
  define q where "q = (\<lambda>f. poly_subst sub (q0 f))"
  show ?thesis
  proof
    from 1 have "p = poly_subst sub p" by (rule poly_subst_id[symmetric])
    also have "... = (\<Sum>f\<in>F. q f * (poly_subst sub f))"
      by (simp only: p poly_subst_sum poly_subst_times q_def)
    also from refl have "... = (\<Sum>f\<in>F. q f * f)"
    proof (rule sum.cong)
      fix f
      assume "f \<in> F"
      have "poly_subst sub f = f" by (rule poly_subst_id, rule 2, rule \<open>f \<in> F\<close>)
      thus "q f * poly_subst sub f = q f * f" by simp
    qed
    finally show "p = (\<Sum>f\<in>F. q f * f)" .
  next
    fix f
    assume "f \<in> F" and "q f \<noteq> 0"
    show "indets (q f) \<subseteq> UNION (insert p F) indets \<and> poly_deg (q f) \<le> poly_deg p + b"
    proof
      show "indets (q f) \<subseteq> UNION (insert p F) indets"
      proof
        fix x
        assume "x \<in> indets (q f)"
        then obtain y where "x \<in> indets (sub y)" unfolding q_def by (rule in_indets_poly_substE)
        hence y: "y \<in> UNION (Keys (insert p F)) keys"
          and "x \<in> indets (monomial (1::'b) (monomial (1::nat) y))"
          by (simp_all add: sub_def split: if_splits)
        from this(2) have "x = y" by (simp add: indets_monomial)
        with y show "x \<in> UNION (insert p F) indets" by (simp add: indets_def Keys_def)
      qed
    next
      have "poly_deg (q f) \<le> poly_deg (q0 f)" unfolding q_def
      proof (rule poly_deg_poly_subst_le)
        fix x
        show "poly_deg (sub x) \<le> 1" by (simp add: sub_def poly_deg_monomial deg_pm_single)
      qed
      also from \<open>f \<in> F\<close> have "... \<le> poly_deg p + b"
      proof (rule q0)
        from \<open>q f \<noteq> 0\<close> show "q0 f \<noteq> 0" by (auto simp add: q_def)
      qed
      finally show "poly_deg (q f) \<le> poly_deg p + b" .
    qed
  qed
qed

lemma is_GB_boundI:
  assumes "\<And>g. g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> b"
  shows "is_GB_bound F b"
  unfolding is_GB_bound_def using assms by blast

lemma is_GB_boundE:
  assumes "is_GB_bound F b" and "g \<in> punit.reduced_GB F"
  shows "poly_deg g \<le> b"
  using assms unfolding is_GB_bound_def by blast

context
  fixes X :: "'x set"
  assumes fin_X: "finite X"
begin

definition deg_shifts :: "nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_1) list"
  where "deg_shifts d fs = concat (map (\<lambda>f. (map (\<lambda>t. punit.monom_mult 1 t f) (punit.pps_to_list (deg_le_sect X d)))) fs)"

lemma set_deg_shifts:
  shows "set (deg_shifts d fs) = (\<Union>f\<in>set fs. (\<lambda>t. punit.monom_mult 1 t f) ` (deg_le_sect X d))"
proof -
  from fin_X have *: "finite (deg_le_sect X d)" by (rule finite_deg_le_sect)
  show ?thesis by (simp add: deg_shifts_def punit.set_pps_to_list[OF *])
qed

lemma set_deg_shifts_2: "set (deg_shifts d fs) = (\<Union>t\<in>deg_le_sect X d. punit.monom_mult 1 t ` set fs)"
  by (auto simp add: set_deg_shifts)

corollary set_deg_shifts_singleton:
  "set (deg_shifts d [f]) = (\<lambda>t. punit.monom_mult 1 t f) ` (deg_le_sect X d)"
  by (simp add: set_deg_shifts)

lemma deg_shifts_superset: "set fs \<subseteq> set (deg_shifts d fs)"
proof -
  have "set fs = (punit.monom_mult 1 0) ` set fs" by (simp add: image_cong)
  also from zero_in_deg_set have "... \<subseteq> set (deg_shifts d fs)"
    by (simp only: set_deg_shifts_2, rule UN_upper)
  finally show ?thesis .
qed

lemma deg_shifts_mono:
  assumes "set fs \<subseteq> set gs"
  shows "set (deg_shifts d fs) \<subseteq> set (deg_shifts d gs)"
  using assms by (auto simp add: set_deg_shifts)

lemma pideal_deg_shifts [simp]: "ideal (set (deg_shifts d fs)) = ideal (set fs)"
proof
  show "ideal (set (deg_shifts d fs)) \<subseteq> ideal (set fs)"
    by (rule ideal.module_subset_moduleI, simp add: set_deg_shifts_2 UN_subset_iff,
        intro ballI image_subsetI, metis ideal.smult_in_module times_monomial_left)
next
  from deg_shifts_superset show "ideal (set fs) \<subseteq> ideal (set (deg_shifts d fs))"
    by (rule ideal.module_mono)
qed

lemma PPs_eq_dgrad_set:
  assumes "elem_index ` X = {..<n}"
  shows ".[X] = dgrad_set varnum n"
proof -
  have "varnum t \<le> n" if "keys t \<subseteq> X" for t::"'x \<Rightarrow>\<^sub>0 nat"
  proof (cases "keys t = {}")
    case True
    thus ?thesis by (simp add: varnum_def)
  next
    case False
    moreover {
      fix x
      assume "x \<in> keys t"
      hence "x \<in> X" using that ..
      hence "elem_index x \<in> elem_index ` X" by (rule imageI)
      hence "elem_index x < n" by (simp add: assms)
    }
    ultimately show ?thesis by (simp add: varnum_def Suc_le_eq)
  qed
  moreover have "x \<in> X" if "varnum t \<le> n" and "x \<in> keys t" for x and t::"'x \<Rightarrow>\<^sub>0 nat"
  proof -
    from that(2) have "keys t \<noteq> {}" by blast
    with that(1) have "\<forall>x\<in>keys t. elem_index x < n" by (simp add: varnum_def Suc_le_eq)
    hence "elem_index x < n" using that(2) ..
    hence "elem_index x \<in> elem_index ` X" by (simp add: assms)
    thus ?thesis by (simp only: inj_image_mem_iff[OF inj_elem_index])
  qed
  ultimately show ?thesis by (auto simp: PPs_def dgrad_set_def)
qed

corollary Polys_eq_dgrad_p_set: "elem_index ` X = {..<n} \<Longrightarrow> P[X] = punit.dgrad_p_set varnum n"
  by (simp add: Polys_def punit.dgrad_p_set_def PPs_eq_dgrad_set)

theorem thm_2_3_6:
  assumes "elem_index ` X = {..<n}" and "set fs \<subseteq> P[X]" and "is_cofactor_bound (set fs) b1"
    and "is_GB_bound (set fs) b2"
  shows "set (punit.reduced_Macaulay_list (deg_shifts (b1 + b2) fs)) = punit.reduced_GB (set fs)"
proof (rule punit.reduced_Macaulay_list_is_reduced_GB)
  let ?H = "punit.phull (set (deg_shifts (b1 + b2) fs))"
  have "1 \<noteq> (0::'a)" by simp
  note dickson_grading_varnum
  moreover have "finite (punit.component_of_term ` Keys (set fs))" by simp
  ultimately have "punit.reduced_GB (set fs) \<subseteq> P[X]"
    using assms(2) unfolding Polys_eq_dgrad_p_set[OF assms(1)] by (rule punit.reduced_GB_dgrad_p_set)
  show "punit.reduced_GB (set fs) \<subseteq> ?H"
  proof
    fix g
    assume "g \<in> punit.reduced_GB (set fs)"
    hence "g \<in> ideal (punit.reduced_GB (set fs))" by (rule ideal.generator_in_module)
    hence "g \<in> ideal (set fs)" using punit.reduced_GB_pmdl_finite by auto
    with assms(3) obtain q where g: "g = (\<Sum>f\<in>(set fs). q f * f)"
      and 1: "\<And>f. f \<in> set fs \<Longrightarrow> q f \<noteq> 0 \<Longrightarrow>
                indets (q f) \<subseteq> UNION (insert g (set fs)) indets \<and> poly_deg (q f) \<le> poly_deg g + b1"
      by (rule is_cofactor_boundE, blast)
    show "g \<in> ?H" unfolding g
    proof (rule punit.phull.module_closed_sum)
      fix f
      assume "f \<in> set fs"
      show "q f * f \<in> ?H"
      proof (cases "f = 0 \<or> q f = 0")
        case True
        thus ?thesis by (auto simp add: punit.phull.module_0)
      next
        case False
        hence "f \<noteq> 0" and "q f \<noteq> 0" by simp_all
        from \<open>f \<in> set fs\<close> this(2)
        have "indets (q f) \<subseteq> UNION (insert g (set fs)) indets \<and> poly_deg (q f) \<le> poly_deg g + b1"
          by (rule 1)
        hence "indets (q f) \<subseteq> UNION (insert g (set fs)) indets" and "poly_deg (q f) \<le> poly_deg g + b1"
          by simp_all
        note this(1)
        also have "UNION (insert g (set fs)) indets \<subseteq> X"
        proof
          fix x
          assume "x \<in> UNION (insert g (set fs)) indets"
          then obtain p where "p \<in> insert g (set fs)" and "x \<in> indets p" ..
          note this(1)
          also have "insert g (set fs) \<subseteq> P[X]" by (rule insert_subsetI, rule set_rev_mp, fact+)
          finally have "indets p \<subseteq> X" by (rule PolysD)
          with \<open>x \<in> indets p\<close> show "x \<in> X" ..
        qed
        finally have "q f \<in> P[X]" by (rule PolysI_alt)
        from assms(4) \<open>g \<in> punit.reduced_GB (set fs)\<close> have "poly_deg g \<le> b2" by (rule is_GB_boundE)
        with \<open>poly_deg (q f) \<le> poly_deg g + b1\<close> have "poly_deg (q f) \<le> b1 + b2" by simp
        with \<open>q f \<in> P[X]\<close> have "keys (q f) \<subseteq> deg_le_sect X (b1 + b2)" by (rule keys_subset_deg_le_sectI)
        with finite_deg_le_sect[OF fin_X]
        have "q f * f = (\<Sum>t\<in>deg_le_sect X (b1 + b2). punit.monom_mult (lookup (q f) t) t f)"
          unfolding punit.mult_scalar_sum_monomials[simplified]
        proof (rule sum.mono_neutral_left)
          show "\<forall>t\<in>deg_le_sect X (b1 + b2) - keys (q f). punit.monom_mult (lookup (q f) t) t f = 0"
            by (rule, simp)
        qed
        also have "... = (\<Sum>t\<in>deg_le_sect X (b1 + b2). punit.monom_mult (lookup (q f) t) 0 (punit.monom_mult 1 t f))"
          by (simp add: punit.monom_mult_assoc)
        also have "... = (\<Sum>t\<in>deg_le_sect X (b1 + b2).
                    ((\<lambda>f0. punit.monom_mult (lookup (q f) (punit.lp f0 - punit.lp f)) 0 f0) \<circ> (\<lambda>t. punit.monom_mult 1 t f)) t)"
          by (rule sum.cong, fact refl, simp add: punit.lt_monom_mult[OF \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close>])
        also have "... = (\<Sum>f0\<in>set (deg_shifts (b1 + b2) [f]).
                                        punit.monom_mult (lookup (q f) (punit.lp f0 - punit.lp f)) 0 f0)"
        proof (simp only: set_deg_shifts_singleton, rule sum.reindex[symmetric], rule inj_onI)
          fix s t
          assume "punit.monom_mult 1 s f = punit.monom_mult 1 t f"
          thus "s = t" using \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close> by (rule punit.monom_mult_inj_2)
        qed
        finally have "q f * f \<in> punit.phull (set (deg_shifts (b1 + b2) [f]))"
          by (simp add: punit.phull.sum_in_moduleI)
        also have "... \<subseteq> ?H" by (rule punit.phull.module_mono, rule deg_shifts_mono, simp add: \<open>f \<in> set fs\<close>)
        finally show ?thesis .
      qed
    qed
  qed
qed simp_all

theorem thm_2_3_7:
  assumes "elem_index ` X = {..<n}" and "set fs \<subseteq> P[X]" and "is_cofactor_bound (set fs) b"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow> 1 \<in> set (punit.Macaulay_list (deg_shifts b fs))" (is "?L \<longleftrightarrow> ?R")
proof
  from assms(1, 2) have *: "set fs \<subseteq> punit.dgrad_p_set varnum n" by (simp only: Polys_eq_dgrad_p_set)
  assume ?L
  hence "ideal (set fs) = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one)
  hence eq: "punit.reduced_GB (set fs) = {1}"
    by (simp only: ideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set[OF dickson_grading_varnum *])
  have "is_GB_bound (set fs) 0" by (rule is_GB_boundI, simp add: eq poly_deg_def)
  with assms have "set (punit.reduced_Macaulay_list (deg_shifts (b + 0) fs)) = punit.reduced_GB (set fs)"
    by (rule thm_2_3_6)
  hence "{1} = set (punit.reduced_Macaulay_list (deg_shifts b fs))" by (simp add: eq)
  also have "... \<subseteq> set (punit.Macaulay_list (deg_shifts b fs))"
    by (fact punit.reduced_Macaulay_list_subset_Macaulay_list)
  finally show ?R by simp
next
  assume ?R
  also have "... \<subseteq> punit.phull (set (punit.Macaulay_list (deg_shifts b fs)))"
    by (rule punit.phull.generator_subset_module)
  also have "... = punit.phull (set (deg_shifts b fs))" by (fact punit.phull_Macaulay_list)
  also have "... \<subseteq> ideal (set (deg_shifts b fs))" using punit.phull_subset_module by force
  finally show ?L by simp
qed

text \<open>The first assumptions of Theorems \<open>thm_2_3_6\<close> and \<open>thm_2_3_7\<close>, @{prop "elem_index ` X = {..<n}"},
  could be avoided if Lemma \<open>reduced_GB_dgrad_p_set\<close> were known for arbitrary sets of indeterminates,
  not only for sets of that particular shape.\<close>

theorem Hermann_bound:
  assumes "finite F" and "F \<subseteq> P[X]"
  shows "is_cofactor_bound F (\<Sum>j=0..<n. (card F * maxdeg F) ^ (2 ^ j))"
  sorry

theorem Dube_bound:
  assumes "finite F" and "F \<subseteq> P[X]"
  shows "is_GB_bound F (2 * ((maxdeg F)\<^sup>2 div 2 + maxdeg F) ^ (2 ^ (n - 1)))"
  sorry

end

end (* pm_powerprod *)

end (* theory *)
