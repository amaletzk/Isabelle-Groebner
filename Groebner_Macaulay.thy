(* Author: Alexander Maletzky *)

theory Groebner_Macaulay
  imports Groebner_PM Groebner_Bases.Macaulay_Matrix
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
    (\<forall>p\<in>ideal F. \<exists>q. p = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f\<in>F. poly_deg (q f) \<le> poly_deg p + b))"

text \<open>Note that @{const is_cofactor_bound} is only true for @{emph \<open>finite\<close>} sets \<open>F\<close>.\<close>

definition is_GB_bound :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_GB_bound F b \<longleftrightarrow> (\<exists>G. punit.is_Groebner_basis G \<and> ideal G = ideal F \<and>
                                UNION G indets \<subseteq> UNION F indets \<and> (\<forall>g\<in>G. poly_deg g \<le> b))"

lemma is_cofactor_boundI:
  assumes "\<And>p. p \<in> ideal F \<Longrightarrow> \<exists>q. p = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f\<in>F. poly_deg (q f) \<le> poly_deg p + b)"
  shows "is_cofactor_bound F b"
  unfolding is_cofactor_bound_def using assms by blast

lemma is_cofactor_boundE:
  assumes "is_cofactor_bound F b" and "(p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::comm_ring_1) \<in> ideal F"
  obtains q where "p = (\<Sum>f\<in>F. q f * f)"
    and "\<And>f. indets (q f) \<subseteq> UNION (insert p F) indets" and "\<And>f. poly_deg (q f) \<le> poly_deg p + b"
proof (cases "p = 0")
  case True
  define q where "q = (\<lambda>f::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b. 0::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b)"
  show ?thesis
  proof
    show "p = (\<Sum>f\<in>F. q f * f)" by (simp add: True q_def)
  next
    fix f
    show "indets (q f) \<subseteq> UNION (insert p F) indets" and "poly_deg (q f) \<le> poly_deg p + b"
      by (simp_all add: q_def)
  qed
next
  case False
  let ?X = "UNION (insert p F) indets"
  from assms obtain q0
    where p: "p = (\<Sum>f\<in>F. q0 f * f)" and q0: "\<And>f. f \<in> F \<Longrightarrow> poly_deg (q0 f) \<le> poly_deg p + b"
    using assms unfolding is_cofactor_bound_def by blast
  define sub where "sub = (\<lambda>x::'x. if x \<in> (\<Union>t\<in>Keys (insert p F). keys t) then
                                     monomial (1::'b) (Poly_Mapping.single x (1::nat))
                                   else 1)"
  have 1: "sub x = monomial 1 (monomial 1 x)" if "x \<in> indets p" for x
  proof (simp add: sub_def, rule)
    from that obtain t where "t \<in> keys p" and "x \<in> keys t" by (rule in_indetsE)
    from this(1) have "t \<in> Keys (insert p F)" by (simp add: Keys_insert)
    moreover assume "\<forall>t\<in>Keys (insert p F). lookup t x = 0"
    ultimately have "lookup t x = 0" by blast
    with \<open>x \<in> keys t\<close> show "monomial 1 (monomial (Suc 0) x) = 1" unfolding in_keys_iff ..
  qed
  have 2: "sub x = monomial 1 (monomial 1 x)" if "f \<in> F" and "x \<in> indets f" for f x
  proof (simp add: sub_def, rule)
    from that(2) obtain t where "t \<in> keys f" and "x \<in> keys t" by (rule in_indetsE)
    from this(1) that(1) have "t \<in> Keys F" by (rule in_KeysI)
    hence "t \<in> Keys (insert p F)" by (simp add: Keys_insert)
    moreover assume "\<forall>t\<in>Keys (insert p F). lookup t x = 0"
    ultimately have "lookup t x = 0" by blast
    with \<open>x \<in> keys t\<close> show "monomial 1 (monomial (Suc 0) x) = 1" unfolding in_keys_iff ..
  qed
  define q where "q = (\<lambda>f. if f \<in> F then poly_subst sub (q0 f) else 0)"
  show ?thesis
  proof
    from 1 have "p = poly_subst sub p" by (rule poly_subst_id[symmetric])
    also have "... = (\<Sum>f\<in>F. q f * (poly_subst sub f))"
      by (simp add: p poly_subst_sum poly_subst_times q_def cong: sum.cong)
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
    have "indets (q f) \<subseteq> ?X \<and> poly_deg (q f) \<le> poly_deg p + b"
    proof (cases "f \<in> F")
      case True
      hence qf: "q f = poly_subst sub (q0 f)" by (simp add: q_def)
      show ?thesis
      proof
        show "indets (q f) \<subseteq> ?X"
        proof
          fix x
          assume "x \<in> indets (q f)"
          then obtain y where "x \<in> indets (sub y)" unfolding qf by (rule in_indets_poly_substE)
          hence y: "y \<in> UNION (Keys (insert p F)) keys"
            and "x \<in> indets (monomial (1::'b) (monomial (1::nat) y))"
            by (simp_all add: sub_def split: if_splits)
          from this(2) have "x = y" by (simp add: indets_monomial)
          with y show "x \<in> UNION (insert p F) indets" by (simp add: indets_def Keys_def)
        qed
      next
        have "poly_deg (q f) \<le> poly_deg (q0 f)" unfolding qf
        proof (rule poly_deg_poly_subst_le)
          fix x
          show "poly_deg (sub x) \<le> 1" by (simp add: sub_def poly_deg_monomial deg_pm_single)
        qed
        also from \<open>f \<in> F\<close> have "... \<le> poly_deg p + b" by (rule q0)
        finally show "poly_deg (q f) \<le> poly_deg p + b" .
      qed
    next
      case False
      thus ?thesis by (simp add: q_def)
    qed
    thus "indets (q f) \<subseteq> ?X" and "poly_deg (q f) \<le> poly_deg p + b" by simp_all
  qed
qed

lemma is_GB_boundI:
  "punit.is_Groebner_basis G \<Longrightarrow> ideal G = ideal F \<Longrightarrow> UNION G indets \<subseteq> UNION F indets \<Longrightarrow>
    (\<And>g. g \<in> G \<Longrightarrow> poly_deg g \<le> b) \<Longrightarrow> is_GB_bound F b"
  unfolding is_GB_bound_def by blast

lemma is_GB_boundE:
  assumes "is_GB_bound F b"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F"
    and "UNION G indets \<subseteq> UNION F indets" and "\<And>g. g \<in> G \<Longrightarrow> poly_deg g \<le> b"
  using assms unfolding is_GB_bound_def by blast

lemma is_GB_boundE_Polys:
  assumes "is_GB_bound F b" and "F \<subseteq> P[X]"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F"
    and "G \<subseteq> P[X]" and "\<And>g. g \<in> G \<Longrightarrow> poly_deg g \<le> b"
proof -
  from assms(1) obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F"
    and "UNION G indets \<subseteq> UNION F indets" and "\<And>g. g \<in> G \<Longrightarrow> poly_deg g \<le> b"
    by (rule is_GB_boundE) blast
  from this(1, 2) _ this(4) show ?thesis
  proof
    show "G \<subseteq> P[X]"
    proof
      fix g
      assume "g \<in> G"
      hence "indets g \<subseteq> UNION G indets" by fastforce
      also have "\<dots> \<subseteq> UNION F indets" by fact
      also have "\<dots> \<subseteq> X"
      proof
        fix x
        assume "x \<in> UNION F indets"
        then obtain f where "f \<in> F" and "x \<in> indets f" ..
        from this(1) assms(2) have "f \<in> P[X]" ..
        hence "indets f \<subseteq> X" by (rule PolysD)
        with \<open>x \<in> indets f\<close> show "x \<in> X" ..
      qed
      finally show "g \<in> P[X]" by (rule PolysI_alt)
    qed
  qed
qed

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

lemma phull_deg_shifts_superset:
  assumes "set fs \<subseteq> P[X]" and "G \<subseteq> P[X]" and "ideal G = ideal (set fs)"
    and "is_cofactor_bound (set fs) b1" and "\<And>g::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field. g \<in> G \<Longrightarrow> poly_deg g \<le> b2"
  shows "G \<subseteq> punit.phull (set (deg_shifts (b1 + b2) fs))" (is "_ \<subseteq> ?H")
proof
  fix g
  assume "g \<in> G"
  hence "g \<in> ideal G" by (rule ideal.generator_in_module)
  hence "g \<in> ideal (set fs)" by (simp only: assms(3))
  with assms(4) obtain q where g: "g = (\<Sum>f\<in>(set fs). q f * f)"
    and 1: "\<And>f. indets (q f) \<subseteq> UNION (insert g (set fs)) indets" and 2: "\<And>f. poly_deg (q f) \<le> poly_deg g + b1"
    by (rule is_cofactor_boundE) blast
  have "1 \<noteq> (0::'a)" by simp
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
      note 1
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
      from \<open>g \<in> G\<close> have "poly_deg g \<le> b2" by (rule assms(5))
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

theorem thm_2_3_6:
  assumes "finite X" and "set fs \<subseteq> P[X]" and "is_cofactor_bound (set fs) b1" and "is_GB_bound (set fs) b2"
  shows "punit.is_Groebner_basis (set (punit.reduced_Macaulay_list (deg_shifts (b1 + b2) fs)))"
proof -
  from assms(4, 2) obtain G where "punit.is_Groebner_basis G" and ideal_G: "ideal G = ideal (set fs)"
    and indets_sub: "G \<subseteq> P[X]" and deg_le: "\<And>g. g \<in> G \<Longrightarrow> poly_deg g \<le> b2"
    by (rule is_GB_boundE_Polys) blast
  from this(1) show ?thesis
  proof (rule punit.reduced_Macaulay_list_is_GB)
    from assms(2) \<open>G \<subseteq> P[X]\<close> ideal_G assms(3) deg_le show "G \<subseteq> punit.phull (set (deg_shifts (b1 + b2) fs))"
      by (rule phull_deg_shifts_superset)
  qed (simp add: ideal_G)
qed

lemma thm_2_3_6_reduced_GB_aux:
  assumes "finite X" and "set fs \<subseteq> P[X]" and "is_cofactor_bound (set fs) b1"
    and "\<And>g. g \<in> punit.reduced_GB (set fs) \<Longrightarrow> poly_deg g \<le> b2"
  shows "set (punit.reduced_Macaulay_list (deg_shifts (b1 + b2) fs)) = punit.reduced_GB (set fs)"
proof (rule punit.reduced_Macaulay_list_is_reduced_GB)
  show "punit.reduced_GB (set fs) \<subseteq> local.punit.phull (set (deg_shifts (b1 + b2) fs))"
    using assms(2) _ _ assms(3, 4)
  proof (rule phull_deg_shifts_superset)
    from assms(1, 2) show "punit.reduced_GB (set fs) \<subseteq> P[X]"
      and "ideal (punit.reduced_GB (set fs)) = ideal (set fs)"
      by (rule reduced_GB_Polys, rule reduced_GB_ideal_Polys)
  qed
qed simp_all

text \<open>For obtaining reduced Gr\"obner bases, the order relation must be graded:\<close>
theorem thm_2_3_6_reduced_GB:
  assumes "finite X" and "set fs \<subseteq> P[X]" and "is_cofactor_bound (set fs) b1" and "is_GB_bound (set fs) b2"
    and "\<And>s t. s \<in> .[X] \<Longrightarrow> t \<in> .[X] \<Longrightarrow> s \<preceq> t \<Longrightarrow> deg_pm s \<le> deg_pm t"
  shows "set (punit.reduced_Macaulay_list (deg_shifts (b1 + b2) fs)) = punit.reduced_GB (set fs)"
  using assms(1, 2, 3)
proof (rule thm_2_3_6_reduced_GB_aux)
  fix g
  assume "g \<in> punit.reduced_GB (set fs)" (is "_ \<in> ?G")
  from assms(1, 2) have "0 \<notin> ?G" and 1: "punit.is_reduced_GB ?G" and 2: "ideal ?G = ideal (set fs)"
    and "?G \<subseteq> P[X]"
    by (rule reduced_GB_nonzero_Polys, rule reduced_GB_is_reduced_GB_Polys,
        rule reduced_GB_ideal_Polys, rule reduced_GB_Polys)
  from \<open>g \<in> ?G\<close> this(4) have "g \<in> P[X]" ..
  hence "keys g \<subseteq> .[X]" by (rule PolysD)
  from assms(4, 2) obtain G where GB_G: "punit.is_Groebner_basis G" and ideal_G: "ideal G = ideal (set fs)"
    and indets_sub: "G \<subseteq> P[X]" and deg_le: "\<And>g. g \<in> G \<Longrightarrow> poly_deg g \<le> b2"
    by (rule is_GB_boundE_Polys) blast
  from \<open>g \<in> ?G\<close> \<open>0 \<notin> ?G\<close> have "g \<noteq> 0" by blast
  from \<open>g \<in> ?G\<close> have "g \<in> ideal ?G" by (rule ideal.generator_in_module)
  hence "g \<in> ideal G" by (simp only: ideal_G 2)
  with GB_G obtain g' where "g' \<in> G" and "g' \<noteq> 0" and a1: "punit.lt g' adds punit.lt g"
    using \<open>g \<noteq> 0\<close> by (rule punit.GB_adds_lt[simplified])
  from 1 have "punit.is_Groebner_basis ?G" by (rule punit.reduced_GB_D1)
  moreover from \<open>g' \<in> G\<close> have "g' \<in> ideal ?G" by (simp add: 2 ideal.generator_in_module flip: ideal_G)
  ultimately obtain g'' where "g'' \<in> ?G" and "g'' \<noteq> 0" and a2: "punit.lt g'' adds punit.lt g'"
    using \<open>g' \<noteq> 0\<close> by (rule punit.GB_adds_lt[simplified])
  from a2 a1 have a3: "punit.lt g'' adds punit.lt g" by (rule adds_trans)
  from \<open>g \<noteq> 0\<close> have "punit.lt g \<in> keys g" by (rule punit.lt_in_keys)
  have "g'' = g"
  proof (rule ccontr)
    assume "g'' \<noteq> g"
    with \<open>g'' \<in> ?G\<close> have "g'' \<in> ?G - {g}" by simp
    from 1 have "punit.is_auto_reduced ?G" by (rule punit.reduced_GB_D2)
    hence "\<not> punit.is_red (?G - {g}) g" using \<open>g \<in> ?G\<close> by (rule punit.is_auto_reducedD)
    moreover from \<open>g'' \<in> ?G - {g}\<close> \<open>g'' \<noteq> 0\<close> \<open>punit.lt g \<in> keys g\<close> a3 have "punit.is_red (?G - {g}) g"
      by (rule punit.is_red_addsI[simplified])
    ultimately show False ..
  qed
  have "poly_deg g \<le> deg_pm (punit.lt g)"
  proof (rule poly_deg_leI)
    fix t
    assume "t \<in> keys g"
    hence "t \<in> .[X]" using \<open>keys g \<subseteq> .[X]\<close> ..
    moreover from \<open>punit.lt g \<in> keys g\<close> \<open>keys g \<subseteq> .[X]\<close> have "punit.lt g \<in> .[X]" ..
    moreover from \<open>t \<in> keys g\<close> have "t \<preceq> punit.lt g" by (rule punit.lt_max_keys)
    ultimately show "deg_pm t \<le> deg_pm (punit.lt g)" by (rule assms(5))
  qed
  also from a2 a1 have "punit.lt g = punit.lt g'" unfolding \<open>g'' = g\<close> by (rule adds_antisym)
  finally have "poly_deg g \<le> deg_pm (punit.lt g')" .
  also from \<open>g' \<noteq> 0\<close> have "\<dots> \<le> poly_deg g'" by (intro poly_deg_max_keys punit.lt_in_keys)
  also from \<open>g' \<in> G\<close> have "\<dots> \<le> b2" by (rule deg_le)
  finally show "poly_deg g \<le> b2" .
qed

theorem thm_2_3_7:
  assumes "finite X" and "set fs \<subseteq> P[X]" and "is_cofactor_bound (set fs) b"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow> 1 \<in> set (punit.Macaulay_list (deg_shifts b fs))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  hence "ideal (set fs) = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one)
  with assms(1, 2) have eq: "punit.reduced_GB (set fs) = {1}" (is "?G = _")
    by (simp only: ideal_eq_UNIV_iff_reduced_GB_eq_one_Polys)
  moreover have "set (punit.reduced_Macaulay_list (deg_shifts (b + 0) fs)) = punit.reduced_GB (set fs)"
    using assms by (rule thm_2_3_6_reduced_GB_aux) (simp add: eq)
  ultimately have "{1} = set (punit.reduced_Macaulay_list (deg_shifts b fs))" by simp
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

theorem Hermann_bound:
  assumes "finite F" and "F \<subseteq> P[X]"
  shows "is_cofactor_bound F (\<Sum>j=0..<card X. (card F * maxdeg F) ^ (2 ^ j))"
  sorry

theorem Dube_bound:
  assumes "finite F" and "F \<subseteq> P[X]"
  shows "is_GB_bound F (2 * ((maxdeg F)\<^sup>2 div 2 + maxdeg F) ^ (2 ^ (card X - 1)))"
  sorry

end

end (* pm_powerprod *)

end (* theory *)
