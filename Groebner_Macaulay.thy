(* Author: Alexander Maletzky *)

section \<open>Computing Gr\"obner Bases by Triangularizing Macaulay Matrices\<close>

theory Groebner_Macaulay
  imports Groebner_PM Groebner_Bases.Macaulay_Matrix
begin

text \<open>Relationship between Gr\"obner bases and Macaulay matrices, following
  @{cite "Wiesinger-Widi2015"}.\<close>

subsection \<open>Gr\"obner Bases\<close>

lemma (in gd_term) Macaulay_list_is_GB:
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

lemma (in extended_ord_pm_powerprod) hom_GB_bound_is_GB_cofactor_bound:
  assumes "finite X" and "F \<subseteq> P[X]" and "extended_ord.is_hom_GB_bound (homogenize None ` extend_indets ` F) b"
  shows "is_GB_cofactor_bound F b"
proof -
  let ?F = "homogenize None ` extend_indets ` F"
  define Y where "Y = \<Union> (indets ` F)"
  define G where "G = restrict_indets ` (extended_ord.punit.reduced_GB ?F)"
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
  ultimately have "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[Y]"
    unfolding G_def by (rule restrict_indets_reduced_GB)+
  from this(1, 2) show ?thesis
  proof (rule is_GB_cofactor_boundI)
    from \<open>G \<subseteq> P[Y]\<close> show "\<Union> (indets ` G) \<subseteq> \<Union> (indets ` F)" by (auto simp: Y_def Polys_alt)
  next
    fix g
    assume "g \<in> G"
    then obtain g' where g': "g' \<in> extended_ord.punit.reduced_GB ?F"
      and g: "g = restrict_indets g'" unfolding G_def ..
    have "f \<in> ?F \<Longrightarrow> homogeneous f" for f by (auto simp: homogeneous_homogenize)
    with assms(3) have "poly_deg g' \<le> b" using g' by (rule extended_ord.is_hom_GB_boundD)
    from g' have "g' \<in> ideal (extended_ord.punit.reduced_GB ?F)"
      by (rule ideal.generator_in_module)
    also have "\<dots> = ideal ?F"
    proof (rule extended_ord.reduced_GB_ideal_Polys)
      from \<open>finite Y\<close> show "finite (insert None (Some ` Y))" by simp
    next
      show "?F \<subseteq> P[insert None (Some ` Y)]"
      proof
        fix f0
        assume "f0 \<in> ?F"
        then obtain f where "f \<in> F" and f0: "f0 = homogenize None (extend_indets f)" by blast
        from this(1) \<open>F \<subseteq> P[Y]\<close> have "f \<in> P[Y]" ..
        hence "extend_indets f \<in> P[Some ` Y]" by (auto simp: indets_extend_indets Polys_alt)
        thus "f0 \<in> P[insert None (Some ` Y)]" unfolding f0 by (rule homogenize_in_Polys)
      qed
    qed
    finally have "g' \<in> ideal ?F" .
    with \<open>\<And>f. f \<in> ?F \<Longrightarrow> homogeneous f\<close> obtain F0 q where "finite F0" and "F0 \<subseteq> ?F"
      and g': "g' = (\<Sum>f\<in>F0. q f * f)" and deg_le: "\<And>f. poly_deg (q f * f) \<le> poly_deg g'"
      by (rule homogeneous_idealE) blast+
    from this(2) obtain F' where "F' \<subseteq> F" and F0: "F0 = homogenize None ` extend_indets ` F'"
      and inj_on: "inj_on (homogenize None \<circ> extend_indets) F'"
      unfolding image_comp by (rule subset_imageE_inj)
    show "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
    proof (intro exI conjI ballI)
      from inj_on \<open>finite F0\<close> show "finite F'" by (simp only: finite_image_iff F0 image_comp)
    next
      from inj_on show "g = (\<Sum>f\<in>F'. (restrict_indets \<circ> q \<circ> homogenize None \<circ> extend_indets) f * f)"
        by (simp add: g g' F0 restrict_indets_sum restrict_indets_times sum.reindex image_comp)
    next
      fix f
      assume "f \<in> F'"
      have "poly_deg ((restrict_indets \<circ> q \<circ> homogenize None \<circ> extend_indets) f * f) =
              poly_deg (restrict_indets (q (homogenize None (extend_indets f)) * homogenize None (extend_indets f)))"
        by (simp add: restrict_indets_times)
      also have "\<dots> \<le> poly_deg (q (homogenize None (extend_indets f)) * homogenize None (extend_indets f))"
        by (rule poly_deg_restrict_indets_le)
      also have "\<dots> \<le> poly_deg g'" by (rule deg_le)
      also have "\<dots> \<le> b" by fact
      finally show "poly_deg ((restrict_indets \<circ> q \<circ> homogenize None \<circ> extend_indets) f * f) \<le> b" .
    qed fact
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

lemma thm_2_3_6:
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

lemma thm_2_3_7:
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

end

lemma thm_2_3_6_indets:
  assumes "is_GB_cofactor_bound (set fs) b"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list (deg_shifts (UNION (set fs) indets) b fs)))"
  using _ _ assms
proof (rule thm_2_3_6)
  from finite_set show "finite (UNION (set fs) indets)" by (simp add: finite_indets)
next
  show "set fs \<subseteq> P[UNION (set fs) indets]" by (auto simp: Polys_alt)
qed

lemma thm_2_3_7_indets:
  assumes "is_GB_cofactor_bound (set fs) b"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow> 1 \<in> set (punit.Macaulay_list (deg_shifts (UNION (set fs) indets) b fs))"
  using _ _ assms
proof (rule thm_2_3_7)
  from finite_set show "finite (UNION (set fs) indets)" by (simp add: finite_indets)
next
  show "set fs \<subseteq> P[UNION (set fs) indets]" by (auto simp: Polys_alt)
qed

end (* pm_powerprod *)

end (* theory *)
