(* Author: Alexander Maletzky *)

section \<open>Degree-Bounds for Computing Gr\"obner Bases via Macaulay Matrices\<close>

theory Groebner_Macaulay_Bounds
  imports Groebner_Macaulay Dube_Bound
begin

subsection \<open>General Case: Dub\'{e}'s Bound\<close>

context pm_powerprod
begin

lemma Dube_is_hom_GB_bound:
  "finite X \<Longrightarrow> finite F \<Longrightarrow> F \<subseteq> P[X] \<Longrightarrow> is_hom_GB_bound F (Dube (card X) (maxdeg F))"
  by (intro is_hom_GB_boundI Dube)

lemma Dube_is_hom_GB_bound_indets:
  "finite F \<Longrightarrow> is_hom_GB_bound F (Dube (card (UNION F indets)) (maxdeg F))"
  by (intro is_hom_GB_boundI Dube_indets)

end

context extended_ord_pm_powerprod
begin

lemma Dube_is_GB_cofactor_bound:
  assumes "finite X" and "finite F" and "F \<subseteq> P[X]"
  shows "is_GB_cofactor_bound F (Dube (Suc (card X)) (maxdeg F))"
  using assms(1, 3)
proof (rule hom_GB_bound_is_GB_cofactor_bound)
  let ?F = "homogenize None ` extend_indets ` F"
  let ?X = "insert None (Some ` X)"
  from assms(1) have "finite ?X" by simp
  moreover from assms(2) have "finite ?F" by (intro finite_imageI)
  moreover have "?F \<subseteq> P[?X]"
  proof
    fix f'
    assume "f' \<in> ?F"
    then obtain f where "f \<in> F" and f': "f' = homogenize None (extend_indets f)" by blast
    from this(1) assms(3) have "f \<in> P[X]" ..
    hence "extend_indets f \<in> P[Some ` X]" by (auto simp: Polys_alt indets_extend_indets)
    thus "f' \<in> P[?X]" unfolding f' by (rule homogenize_in_Polys)
  qed
  ultimately have "extended_ord.is_hom_GB_bound ?F (Dube (card ?X) (maxdeg ?F))"
    by (rule extended_ord.Dube_is_hom_GB_bound)
  moreover have "maxdeg ?F = maxdeg F"
  proof -
    have "maxdeg ?F = maxdeg (extend_indets ` F)"
      by (auto simp: indets_extend_indets intro: maxdeg_homogenize)
    also have "\<dots> = maxdeg F" by (simp add: maxdeg_def image_image)
    finally show "maxdeg ?F = maxdeg F" .
  qed
  moreover from assms(1) have "card ?X = card X + 1" by (simp add: card_image)
  ultimately show "extended_ord.is_hom_GB_bound ?F (Dube (Suc (card X)) (maxdeg F))" by simp
qed

corollary Dube_is_GB_cofactor_bound_indets:
  assumes "finite F"
  shows "is_GB_cofactor_bound F (Dube (Suc (card (UNION F indets))) (maxdeg F))"
  using _ assms _
proof (rule Dube_is_GB_cofactor_bound)
  from assms show "finite (UNION F indets)" by (simp add: finite_indets)
next
  show "F \<subseteq> P[UNION F indets]" by (auto simp: Polys_alt)
qed

theorem thm_2_3_6_Dube:
  assumes "finite X" and "set fs \<subseteq> P[X]"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list
                                        (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs)))"
  using assms Dube_is_GB_cofactor_bound by (rule thm_2_3_6) (simp_all add: assms)

theorem thm_2_3_7_Dube:
  assumes "finite X" and "set fs \<subseteq> P[X]"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow>
          1 \<in> set (punit.Macaulay_list (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs))"
  using assms Dube_is_GB_cofactor_bound by (rule thm_2_3_7) (simp_all add: assms)

theorem thm_2_3_6_indets_Dube:
  fixes fs
  defines "X \<equiv> UNION (set fs) indets"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list
                                        (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs)))"
  unfolding X_def using Dube_is_GB_cofactor_bound_indets by (rule thm_2_3_6_indets) (fact finite_set)

theorem thm_2_3_7_indets_Dube:
  fixes fs
  defines "X \<equiv> UNION (set fs) indets"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow>
          1 \<in> set (punit.Macaulay_list (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs))"
  unfolding X_def using Dube_is_GB_cofactor_bound_indets by (rule thm_2_3_7_indets) (fact finite_set)

end (* extended_ord_pm_powerprod *)

end (* theory *)
