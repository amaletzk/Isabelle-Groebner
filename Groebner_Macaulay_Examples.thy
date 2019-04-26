(* Author: Alexander Maletzky *)

section \<open>Sample Computations of Gr\"obner Bases via Macaulay Matrices\<close>

theory Groebner_Macaulay_Examples
  imports Groebner_Macaulay Dube_Bound
begin

subsection \<open>General Case: Dub\'{e}'s Bound\<close>

context extended_ord_pm_powerprod
begin

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

subsection \<open>Special Case: Wiesinger-Widi's Bounds\<close>

(* TODO *)

end (* theory *)
