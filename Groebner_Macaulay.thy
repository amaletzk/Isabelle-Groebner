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
  where "reduced_Macaulay_list ps = comp_min_basis (Macaulay_list ps)"

text \<open>It is important to note that in @{const reduced_Macaulay_list} there is no need to make the
  polynomials monic (because they already are).\<close>

lemma reduced_Macaulay_list_subset_Macaulay_list:
  "set (reduced_Macaulay_list ps) \<subseteq> set (Macaulay_list ps)"
  by (simp only: reduced_Macaulay_list_def, rule comp_min_basis_subset)

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

lemma reduced_Macaulay_list_is_minimal_basis: "is_minimal_basis (set (reduced_Macaulay_list ps))"
proof (rule is_minimal_basisI)
  fix p
  assume "p \<in> set (reduced_Macaulay_list ps)"
  with reduced_Macaulay_list_not_zero show "p \<noteq> 0" by auto
next
  fix p q
  assume "q \<in> set (reduced_Macaulay_list ps)" and "p \<in> set (reduced_Macaulay_list ps)"
    and [symmetric]: "p \<noteq> q"
  thus "\<not> lt p adds\<^sub>t lt q" unfolding reduced_Macaulay_list_def
    by (rule comp_min_basis_nadds)
qed

end (* ordered_term *)

context gd_term
begin

lemma pmdl_reduced_Macaulay_list:
  assumes "is_Groebner_basis (set (Macaulay_list ps))"
  shows "pmdl (set (reduced_Macaulay_list ps)) = pmdl (set ps)"
proof -
  have "pmdl (set (reduced_Macaulay_list ps)) = pmdl (set (Macaulay_list ps))"
    unfolding reduced_Macaulay_list_def using assms by (rule comp_min_basis_pmdl)
  also have "\<dots> = pmdl (set ps)" by (simp only: pmdl_Macaulay_list)
  finally show ?thesis .
qed

lemma Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pmdl (set ps) = pmdl G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (Macaulay_list ps))"
proof (simp only: GB_alt_3_finite[OF finite_set] pmdl_Macaulay_list, intro ballI impI)
  fix f
  assume "f \<in> pmdl (set ps)"
  also from assms(2) have "\<dots> = pmdl G" .
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

lemma reduced_Macaulay_list_lt:
  assumes "p \<in> phull (set ps)" and "p \<noteq> 0"
  obtains g where "g \<in> set (reduced_Macaulay_list ps)" and "g \<noteq> 0" and "lt g adds\<^sub>t lt p"
proof -
  from assms obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lt p = lt g'"
    by (rule Macaulay_list_lt)
  from this(1, 2) obtain g where "g \<in> set (reduced_Macaulay_list ps)" and "lt g adds\<^sub>t lt g'"
    unfolding reduced_Macaulay_list_def by (rule comp_min_basis_adds)
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
proof -
  from assms have "is_Groebner_basis (set (Macaulay_list ps))" by (rule Macaulay_list_is_GB)
  thus ?thesis unfolding reduced_Macaulay_list_def by (rule comp_min_basis_GB)
qed

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

definition is_GB_cofactor_bound :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_GB_cofactor_bound F b \<longleftrightarrow>
    (\<exists>G. punit.is_Groebner_basis G \<and> ideal G = ideal F \<and> UNION G indets \<subseteq> UNION F indets \<and>
      (\<forall>g\<in>G. \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)))"

definition is_hom_GB_bound :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_hom_GB_bound F b \<longleftrightarrow> ((\<forall>f\<in>F. homogeneous f) \<longrightarrow> (\<forall>g\<in>punit.reduced_GB F. poly_deg g \<le> b))"

lemma is_GB_cofactor_boundI:
  assumes "punit.is_Groebner_basis G" and "ideal G = ideal F" and "UNION G indets \<subseteq> UNION F indets"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
  shows "is_GB_cofactor_bound F b"
  unfolding is_GB_cofactor_bound_def using assms by blast

lemma is_GB_cofactor_boundE:
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "is_GB_cofactor_bound F b"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "UNION G indets \<subseteq> UNION F indets"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                          (\<forall>f. indets (q f) \<subseteq> UNION F indets \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
proof -
  let ?X = "UNION F indets"
  from assms obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "UNION G indets \<subseteq> ?X"
    and 1: "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
    by (auto simp: is_GB_cofactor_bound_def)
  from this(1, 2, 3) show ?thesis
  proof
    fix g
    assume "g \<in> G"
    show "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                (\<forall>f. indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    proof (cases "g = 0")
      case True
      define q where "q = (\<lambda>f::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b. 0::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b)"
      show ?thesis
      proof (intro exI conjI allI)
        show "g = (\<Sum>f\<in>{}. q f * f)" by (simp add: True q_def)
      qed (simp_all add: q_def)
    next
      case False
      let ?X = "UNION F indets"
      from \<open>g \<in> G\<close> have "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
        by (rule 1)
      then obtain F' q0 where "finite F'" and "F' \<subseteq> F" and g: "g = (\<Sum>f\<in>F'. q0 f * f)"
        and q0: "\<And>f. f \<in> F' \<Longrightarrow> poly_deg (q0 f * f) \<le> b" by blast
      define sub where "sub = (\<lambda>x::'x. if x \<in> ?X then
                                         monomial (1::'b) (Poly_Mapping.single x (1::nat))
                                       else 1)"
      have 1: "sub x = monomial 1 (monomial 1 x)" if "x \<in> indets g" for x
      proof (simp add: sub_def, rule)
        from that \<open>g \<in> G\<close> have "x \<in> UNION G indets" by blast
        also have "\<dots> \<subseteq> ?X" by fact
        finally obtain f where "f \<in> F" and "x \<in> indets f" ..
        assume "\<forall>f\<in>F. x \<notin> indets f"
        hence "x \<notin> indets f" using \<open>f \<in> F\<close> ..
        thus "monomial 1 (monomial (Suc 0) x) = 1" using \<open>x \<in> indets f\<close> ..
      qed
      have 2: "sub x = monomial 1 (monomial 1 x)" if "f \<in> F'" and "x \<in> indets f" for f x
      proof (simp add: sub_def, rule)
        assume "\<forall>f\<in>F. x \<notin> indets f"
        moreover from that(1) \<open>F' \<subseteq> F\<close> have "f \<in> F" ..
        ultimately have "x \<notin> indets f" ..
        thus "monomial 1 (monomial (Suc 0) x) = 1" using that(2) ..
      qed
      have 3: "poly_subst sub f = f" if "f \<in> F'" for f by (rule poly_subst_id, rule 2, rule that)
      define q where "q = (\<lambda>f. if f \<in> F' then poly_subst sub (q0 f) else 0)"
      show ?thesis
      proof (intro exI allI conjI impI)
        from 1 have "g = poly_subst sub g" by (rule poly_subst_id[symmetric])
        also have "\<dots> = (\<Sum>f\<in>F'. q f * (poly_subst sub f))"
          by (simp add: g poly_subst_sum poly_subst_times q_def cong: sum.cong)
        also from refl have "\<dots> = (\<Sum>f\<in>F'. q f * f)"
        proof (rule sum.cong)
          fix f
          assume "f \<in> F'"
          hence "poly_subst sub f = f" by (rule 3)
          thus "q f * poly_subst sub f = q f * f" by simp
        qed
        finally show "g = (\<Sum>f\<in>F'. q f * f)" .
      next
        fix f
        have "indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b"
        proof (cases "f \<in> F'")
          case True
          hence qf: "q f = poly_subst sub (q0 f)" by (simp add: q_def)
          show ?thesis
          proof
            show "indets (q f) \<subseteq> ?X"
            proof
              fix x
              assume "x \<in> indets (q f)"
              then obtain y where "x \<in> indets (sub y)" unfolding qf by (rule in_indets_poly_substE)
              hence y: "y \<in> ?X" and "x \<in> indets (monomial (1::'b) (monomial (1::nat) y))"
                by (simp_all add: sub_def split: if_splits)
              from this(2) have "x = y" by (simp add: indets_monomial)
              with y show "x \<in> ?X" by (simp only:)
            qed
          next
            from \<open>f \<in> F'\<close> have "poly_subst sub f = f" by (rule 3)
            hence "poly_deg (q f * f) = poly_deg (q f * poly_subst sub f)" by (simp only:)
            also have "\<dots> = poly_deg (poly_subst sub (q0 f * f))" by (simp only: qf poly_subst_times)
            also have "\<dots> \<le> poly_deg (q0 f * f)"
            proof (rule poly_deg_poly_subst_le)
              fix x
              show "poly_deg (sub x) \<le> 1" by (simp add: sub_def poly_deg_monomial deg_pm_single)
            qed
            also from \<open>f \<in> F'\<close> have "\<dots> \<le> b" by (rule q0)
            finally show "poly_deg (q f * f) \<le> b" .
          qed
        next
          case False
          thus ?thesis by (simp add: q_def)
        qed
        thus "indets (q f) \<subseteq> ?X" and "poly_deg (q f * f) \<le> b" by simp_all

        assume "f \<notin> F'"
        thus "q f = 0" by (simp add: q_def)
      qed fact+
    qed
  qed
qed

lemma is_GB_cofactor_boundE_Polys:
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "is_GB_cofactor_bound F b" and "F \<subseteq> P[X]"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
proof -
  let ?X = "UNION F indets"
  have "?X \<subseteq> X"
  proof
    fix x
    assume "x \<in> ?X"
    then obtain f where "f \<in> F" and "x \<in> indets f" ..
    from this(1) assms(2) have "f \<in> P[X]" ..
    hence "indets f \<subseteq> X" by (rule PolysD)
    with \<open>x \<in> indets f\<close> show "x \<in> X" ..
  qed
  from assms(1) obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F"
    and 1: "UNION G indets \<subseteq> ?X"
    and 2: "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    by (rule is_GB_cofactor_boundE) blast
  from this(1, 2) show ?thesis
  proof
    show "G \<subseteq> P[X]"
    proof
      fix g
      assume "g \<in> G"
      hence "indets g \<subseteq> UNION G indets" by blast
      also have "\<dots> \<subseteq> ?X" by fact
      also have "\<dots> \<subseteq> X" by fact
      finally show "g \<in> P[X]" by (rule PolysI_alt)
    qed
  next
    fix g
    assume "g \<in> G"
    hence "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                  (\<forall>f. indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
      by (rule 2)
    then obtain F' q where "finite F'" and "F' \<subseteq> F" and "g = (\<Sum>f\<in>F'. q f * f)"
      and "\<And>f. indets (q f) \<subseteq> ?X" and "\<And>f. poly_deg (q f * f) \<le> b" and "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0"
      by blast
    show "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                  (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    proof (intro exI allI conjI impI)
      fix f
      from \<open>indets (q f) \<subseteq> ?X\<close> \<open>?X \<subseteq> X\<close> have "indets (q f) \<subseteq> X" by (rule subset_trans)
      thus "q f \<in> P[X]" by (rule PolysI_alt)
    qed fact+
  qed
qed

lemma is_GB_cofactor_boundE_finite_Polys:
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "is_GB_cofactor_bound F b" and "finite F" and "F \<subseteq> P[X]"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>q. g = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)"
proof -
  from assms(1, 3) obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and 1: "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    by (rule is_GB_cofactor_boundE_Polys) blast
  from this(1, 2, 3) show ?thesis
  proof
    fix g
    assume "g \<in> G"
    hence "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
      by (rule 1)
    then obtain F' q where "F' \<subseteq> F" and g: "g = (\<Sum>f\<in>F'. q f * f)"
      and "\<And>f. q f \<in> P[X]" and "\<And>f. poly_deg (q f * f) \<le> b" and 2: "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0" by blast
    show "\<exists>q. g = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)"
    proof (intro exI conjI impI allI)
      from assms(2) \<open>F' \<subseteq> F\<close> have "(\<Sum>f\<in>F'. q f * f) = (\<Sum>f\<in>F. q f * f)"
      proof (intro sum.mono_neutral_left ballI)
        fix f
        assume "f \<in> F - F'"
        hence "f \<notin> F'" by simp
        hence "q f = 0" by (rule 2)
        thus "q f * f = 0" by simp
      qed
      thus "g = (\<Sum>f\<in>F. q f * f)" by (simp only: g)
    qed fact+
  qed
qed

lemma is_hom_GB_boundI:
  "(\<And>g. (\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> b) \<Longrightarrow> is_hom_GB_bound F b"
  unfolding is_hom_GB_bound_def by blast

lemma is_hom_GB_boundD:
  "is_hom_GB_bound F b \<Longrightarrow> (\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> b"
  unfolding is_hom_GB_bound_def by blast

lemma (in hom_ord_pm_powerprod) hom_GB_bound_is_GB_cofactor_bound:
  assumes "finite X" and "F \<subseteq> P[X]" and "x \<notin> X" and "hom_ord.is_hom_GB_bound x (homogenize x ` F) b"
  shows "is_GB_cofactor_bound F b"
proof -
  let ?F = "homogenize x ` F"
  define Y where "Y = \<Union> (indets ` F)"
  define G where "G = dehomogenize x ` (hom_ord.punit.reduced_GB x ?F)"
  have "Y \<subseteq> X"
  proof
    fix x
    assume "x \<in> Y"
    then obtain f where "f \<in> F" and "x \<in> indets f" unfolding Y_def ..
    from this(1) assms(2) have "f \<in> P[X]" ..
    hence "indets f \<subseteq> X" by (rule PolysD)
    with \<open>x \<in> indets f\<close> show "x \<in> X" ..
  qed
  hence "finite Y" using assms(1) by (rule finite_subset)
  moreover have "F \<subseteq> P[Y]" by (auto simp: Y_def Polys_alt)
  moreover from \<open>Y \<subseteq> X\<close> assms(3) have "x \<notin> Y" by blast
  ultimately have "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[Y]"
    unfolding G_def by (rule dehomogenize_reduced_GB)+
  from this(1, 2) show ?thesis
  proof (rule is_GB_cofactor_boundI)
    from \<open>G \<subseteq> P[Y]\<close> show "\<Union> (indets ` G) \<subseteq> \<Union> (indets ` F)" by (auto simp: Y_def Polys_alt)
  next
    fix g
    assume "g \<in> G"
    then obtain g' where g': "g' \<in> hom_ord.punit.reduced_GB x ?F"
      and g: "g = dehomogenize x g'" unfolding G_def ..
    have "f \<in> ?F \<Longrightarrow> homogeneous f" for f by (auto simp: homogeneous_homogenize)
    with assms(4) have "poly_deg g' \<le> b" using g' by (rule hom_ord.is_hom_GB_boundD)
    from g' have "g' \<in> ideal (hom_ord.punit.reduced_GB x ?F)"
      by (rule ideal.generator_in_module)
    also have "\<dots> = ideal ?F"
    proof (rule hom_ord.reduced_GB_ideal_Polys)
      from \<open>finite Y\<close> show "finite (insert x Y)" by simp
    next
      show "?F \<subseteq> P[insert x Y]"
      proof
        fix f0
        assume "f0 \<in> ?F"
        then obtain f where "f \<in> F" and f0: "f0 = homogenize x f" ..
        from this(1) \<open>F \<subseteq> P[Y]\<close> have "f \<in> P[Y]" ..
        thus "f0 \<in> P[insert x Y]" unfolding f0 by (rule homogenize_in_Polys)
      qed
    qed
    finally have "g' \<in> ideal ?F" .
    with \<open>\<And>f. f \<in> ?F \<Longrightarrow> homogeneous f\<close> obtain F0 q where "finite F0" and "F0 \<subseteq> ?F"
      and g': "g' = (\<Sum>f\<in>F0. q f * f)" and deg_le: "\<And>f. poly_deg (q f * f) \<le> poly_deg g'"
      by (rule homogeneous_idealE) blast+
    from this(2) obtain F' where "F' \<subseteq> F" and F0: "F0 = homogenize x ` F'"
      and inj_on: "inj_on (homogenize x) F'" by (rule subset_imageE_inj)
    have dehom: "dehomogenize x f = f" if "f \<in> F'" for f
    proof -
      from that \<open>F' \<subseteq> F\<close> have "f \<in> F" ..
      hence "indets f \<subseteq> Y" unfolding Y_def by blast
      with \<open>x \<notin> Y\<close> have "x \<notin> indets f" by blast
      thus ?thesis by simp
    qed
    show "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
    proof (intro exI conjI ballI)
      from inj_on \<open>finite F0\<close> show "finite F'" by (simp only: finite_image_iff F0)
    next
      show "g = (\<Sum>f\<in>F'. (dehomogenize x \<circ> q \<circ> homogenize x) f * f)"
        using inj_on by (simp add: g g' F0 dehomogenize_sum dehomogenize_times sum.reindex dehom)
    next
      fix f
      assume "f \<in> F'"
      hence "poly_deg ((dehomogenize x \<circ> q \<circ> homogenize x) f * f) =
              poly_deg (dehomogenize x (q (homogenize x f) * homogenize x f))"
        by (simp add: dehomogenize_times dehom)
      also have "\<dots> \<le> poly_deg (q (homogenize x f) * homogenize x f)"
        by (rule poly_deg_dehomogenize_le)
      also have "\<dots> \<le> poly_deg g'" by (rule deg_le)
      also have "\<dots> \<le> b" by fact
      finally show "poly_deg ((dehomogenize x \<circ> q \<circ> homogenize x) f * f) \<le> b" .
    qed fact
  qed
qed

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
    unfolding is_cofactor_bound_def by blast
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
    also have "\<dots> = (\<Sum>f\<in>F. q f * (poly_subst sub f))"
      by (simp add: p poly_subst_sum poly_subst_times q_def cong: sum.cong)
    also from refl have "\<dots> = (\<Sum>f\<in>F. q f * f)"
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
        also from \<open>f \<in> F\<close> have "\<dots> \<le> poly_deg p + b" by (rule q0)
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
  where "deg_shifts d fs = concat (map (\<lambda>f. (map (\<lambda>t. punit.monom_mult 1 t f)
                                        (punit.pps_to_list (deg_le_sect X (d - poly_deg f))))) fs)"

lemma set_deg_shifts:
  "set (deg_shifts d fs) = (\<Union>f\<in>set fs. (\<lambda>t. punit.monom_mult 1 t f) ` (deg_le_sect X (d - poly_deg f)))"
proof -
  from fin_X have "finite (deg_le_sect X d0)" for d0 by (rule finite_deg_le_sect)
  thus ?thesis by (simp add: deg_shifts_def punit.set_pps_to_list)
qed

corollary set_deg_shifts_singleton:
  "set (deg_shifts d [f]) = (\<lambda>t. punit.monom_mult 1 t f) ` (deg_le_sect X (d - poly_deg f))"
  by (simp add: set_deg_shifts)

lemma deg_shifts_superset: "set fs \<subseteq> set (deg_shifts d fs)"
proof -
  have "set fs = (\<Union>f\<in>set fs. {punit.monom_mult 1 0 f})" by simp
  also have "\<dots> \<subseteq> set (deg_shifts d fs)" unfolding set_deg_shifts using subset_refl
  proof (rule UN_mono)
    fix f
    assume "f \<in> set fs"
    have "punit.monom_mult 1 0 f \<in> (\<lambda>t. punit.monom_mult 1 t f) ` deg_le_sect X (d - poly_deg f)"
      using zero_in_deg_le_sect by (rule imageI)
    thus "{punit.monom_mult 1 0 f} \<subseteq> (\<lambda>t. punit.monom_mult 1 t f) ` deg_le_sect X (d - poly_deg f)"
      by simp
  qed
  finally show ?thesis .
qed

lemma deg_shifts_mono:
  assumes "set fs \<subseteq> set gs"
  shows "set (deg_shifts d fs) \<subseteq> set (deg_shifts d gs)"
  using assms by (auto simp add: set_deg_shifts)

lemma ideal_deg_shifts [simp]: "ideal (set (deg_shifts d fs)) = ideal (set fs)"
proof
  show "ideal (set (deg_shifts d fs)) \<subseteq> ideal (set fs)"
    by (rule ideal.module_subset_moduleI, simp add: set_deg_shifts UN_subset_iff,
        intro ballI image_subsetI, metis ideal.smult_in_module times_monomial_left)
next
  from deg_shifts_superset show "ideal (set fs) \<subseteq> ideal (set (deg_shifts d fs))"
    by (rule ideal.module_mono)
qed

theorem thm_2_3_6:
  assumes "set fs \<subseteq> P[X]" and "is_GB_cofactor_bound (set fs) b"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list (deg_shifts b fs)))"
proof -
  from assms(2) finite_set assms(1) obtain G where "punit.is_Groebner_basis G"
    and ideal_G: "ideal G = ideal (set fs)" and G_sub: "G \<subseteq> P[X]"
    and 1: "\<And>g. g \<in> G \<Longrightarrow> \<exists>q. g = (\<Sum>f\<in>set fs. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)"
    by (rule is_GB_cofactor_boundE_finite_Polys) blast
  from this(1) show ?thesis
  proof (rule punit.Macaulay_list_is_GB)
    show "G \<subseteq> punit.phull (set (deg_shifts b fs))" (is "_ \<subseteq> ?H")
    proof
      fix g
      assume "g \<in> G"
      hence "\<exists>q. g = (\<Sum>f\<in>set fs. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)" by (rule 1)
      then obtain q where g: "g = (\<Sum>f\<in>set fs. q f * f)" and "\<And>f. q f \<in> P[X]"
        and "\<And>f. poly_deg (q f * f) \<le> b" by blast
      show "g \<in> ?H" unfolding g
      proof (rule punit.phull.module_closed_sum)
        fix f
        assume "f \<in> set fs"
        have "1 \<noteq> (0::'a)" by simp
        show "q f * f \<in> ?H"
        proof (cases "f = 0 \<or> q f = 0")
          case True
          thus ?thesis by (auto simp add: punit.phull.module_0)
        next
          case False
          hence "q f \<noteq> 0" and "f \<noteq> 0" by simp_all
          with \<open>poly_deg (q f * f) \<le> b\<close> have "poly_deg (q f) \<le> b - poly_deg f"
            by (simp add: poly_deg_times)
          with \<open>q f \<in> P[X]\<close> have "keys (q f) \<subseteq> deg_le_sect X (b - poly_deg f)"
            by (rule keys_subset_deg_le_sectI)
          with finite_deg_le_sect[OF fin_X]
          have "q f * f = (\<Sum>t\<in>deg_le_sect X (b - poly_deg f). punit.monom_mult (lookup (q f) t) t f)"
            unfolding punit.mult_scalar_sum_monomials[simplified] by (rule sum.mono_neutral_left) simp
          also have "\<dots> = (\<Sum>t\<in>deg_le_sect X (b - poly_deg f).
                              punit.monom_mult (lookup (q f) t) 0 (punit.monom_mult 1 t f))"
            by (simp add: punit.monom_mult_assoc)
          also have "\<dots> = (\<Sum>t\<in>deg_le_sect X (b - poly_deg f).
                          ((\<lambda>f0. punit.monom_mult (lookup (q f) (punit.lp f0 - punit.lp f)) 0 f0) \<circ>
                          (\<lambda>t. punit.monom_mult 1 t f)) t)"
            using refl by (rule sum.cong) (simp add: punit.lt_monom_mult[OF \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close>])
          also have "\<dots> = (\<Sum>f0\<in>set (deg_shifts b [f]).
                                          punit.monom_mult (lookup (q f) (punit.lp f0 - punit.lp f)) 0 f0)"
            unfolding set_deg_shifts_singleton
          proof (intro sum.reindex[symmetric] inj_onI)
            fix s t
            assume "punit.monom_mult 1 s f = punit.monom_mult 1 t f"
            thus "s = t" using \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close> by (rule punit.monom_mult_inj_2)
          qed
          finally have "q f * f \<in> punit.phull (set (deg_shifts b [f]))"
            by (simp add: punit.phull.sum_in_moduleI)
          also have "\<dots> \<subseteq> ?H" by (rule punit.phull.module_mono, rule deg_shifts_mono, simp add: \<open>f \<in> set fs\<close>)
          finally show ?thesis .
        qed
      qed
    qed
  qed (simp add: ideal_G)
qed

theorem thm_2_3_7:
  assumes "set fs \<subseteq> P[X]" and "is_GB_cofactor_bound (set fs) b"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow> 1 \<in> set (punit.Macaulay_list (deg_shifts b fs))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  let ?G = "set (punit.Macaulay_list (deg_shifts b fs))"
  from assms have "punit.is_Groebner_basis ?G" by (rule thm_2_3_6)
  moreover from \<open>?L\<close> have "1 \<in> ideal ?G" by (simp add: punit.pmdl_Macaulay_list[simplified])
  moreover have "1 \<noteq> (0::_ \<Rightarrow>\<^sub>0 'a)" by simp
  ultimately obtain g where "g \<in> ?G" and "g \<noteq> 0" and "punit.lt g adds punit.lt (1::_ \<Rightarrow>\<^sub>0 'a)"
    by (rule punit.GB_adds_lt[simplified])
  from this(3) have lp_g: "punit.lt g = 0" by (simp add: punit.lt_monomial adds_zero flip: single_one)
  from punit.Macaulay_list_is_monic_set \<open>g \<in> ?G\<close> \<open>g \<noteq> 0\<close> have lc_g: "punit.lc g = 1"
    by (rule punit.is_monic_setD)
  have "g = 1"
  proof (rule poly_mapping_eqI)
    fix t
    show "lookup g t = lookup 1 t"
    proof (cases "t = 0")
      case True
      thus ?thesis using lc_g by (simp add: lookup_one punit.lc_def lp_g)
    next
      case False
      with zero_min[of t] have "\<not> t \<preceq> punit.lt g" by (simp add: lp_g)
      with punit.lt_max_keys have "t \<notin> keys g" by blast
      with False show ?thesis by (simp add: lookup_one)
    qed
  qed
  with \<open>g \<in> ?G\<close> show "1 \<in> ?G" by simp
next
  assume ?R
  also have "\<dots> \<subseteq> punit.phull (set (punit.Macaulay_list (deg_shifts b fs)))"
    by (rule punit.phull.generator_subset_module)
  also have "\<dots> = punit.phull (set (deg_shifts b fs))" by (fact punit.phull_Macaulay_list)
  also have "\<dots> \<subseteq> ideal (set (deg_shifts b fs))" using punit.phull_subset_module by force
  finally show ?L by simp
qed

theorem Dube_bound:
  fixes F
  defines "d \<equiv> rat_of_nat (maxdeg F)"
  defines "n \<equiv> card X"
  assumes "finite F" and "F \<subseteq> P[X]"
  shows "is_hom_GB_bound F (nat \<lfloor>(2 * (d\<^sup>2 / 2 + d) ^ (2 ^ (n - 2)))\<rfloor>)"
          (* TODO: The exponents can be replaced by rational numbers, even if "n < 2". *)
  sorry

end

end (* pm_powerprod *)

lemma (in hom_ord_pm_powerprod) Dube_cofactor_bound:
  fixes F X
  defines "d \<equiv> rat_of_nat (maxdeg F)"
  defines "n \<equiv> card X"
  assumes "finite X" and "X \<noteq> UNIV" and "finite F" and "F \<subseteq> P[X]"
  shows "is_GB_cofactor_bound F (nat \<lfloor>(2 * (d\<^sup>2 / 2 + d) ^ (2 ^ (n - 1)))\<rfloor>)"
proof -
  from assms(4) obtain x where "x \<notin> X" by blast
  with assms(3, 6) show ?thesis
  proof (rule hom_GB_bound_is_GB_cofactor_bound)
    let ?F = "homogenize x ` F"
    let ?X = "insert x X"
    let ?d = "rat_of_nat (maxdeg ?F)"
    from assms(3) have "finite ?X" by simp
    moreover from assms(5) have "finite ?F" by (rule finite_imageI)
    moreover have "?F \<subseteq> P[?X]"
    proof
      fix f'
      assume "f' \<in> ?F"
      then obtain f where "f \<in> F" and f': "f' = homogenize x f" ..
      from this(1) assms(6) have "f \<in> P[X]" ..
      thus "f' \<in> P[?X]" unfolding f' by (rule homogenize_in_Polys)
    qed
    ultimately have "hom_ord.is_hom_GB_bound x ?F (nat \<lfloor>2 * (?d\<^sup>2 / 2 + ?d) ^ 2 ^ (card ?X - 2)\<rfloor>)"
      by (rule hom_ord.Dube_bound)
    moreover have "?d = d" unfolding d_def
    proof (intro arg_cong[where f=rat_of_nat] maxdeg_homogenize notI)
      assume "x \<in> \<Union> (indets ` F)"
      with assms(6) \<open>x \<notin> X\<close> show False by (auto simp: Polys_alt)
    qed
    moreover from assms(3) \<open>x \<notin> X\<close> have "card ?X = n + 1" by (simp add: n_def)
    ultimately show "hom_ord.is_hom_GB_bound x ?F (nat \<lfloor>2 * (d\<^sup>2 / 2 + d) ^ 2 ^ (n - 1)\<rfloor>)" by simp
  qed
qed

end (* theory *)
