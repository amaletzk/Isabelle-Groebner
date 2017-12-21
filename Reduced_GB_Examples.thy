theory Reduced_GB_Examples
  imports Reduced_GB Polynomials.MPoly_Type_Class_FMap
begin

definition "dlex_pm_strict s t \<longleftrightarrow> dlex_pm s t \<and> \<not> dlex_pm t s"

global_interpretation opp_dlex: gd_powerprod dlex_pm dlex_pm_strict
  defines lp_dlex = opp_dlex.lp
  and max_dlex = opp_dlex.ordered_powerprod_lin.max
  and list_max_dlex = opp_dlex.list_max
  and higher_dlex = opp_dlex.higher
  and lower_dlex = opp_dlex.lower
  and lc_dlex = opp_dlex.lc
  and tail_dlex = opp_dlex.tail
  and ord_dlex = opp_dlex.ord_p
  and ord_strict_dlex = opp_dlex.ord_strict_p
  and rd_mult_dlex = opp_dlex.rd_mult
  and rd_dlex = opp_dlex.rd
  and rd_list_dlex = opp_dlex.rd_list
  and trd_dlex = opp_dlex.trd
  and spoly_dlex = opp_dlex.spoly
  and trdsp_dlex = opp_dlex.trdsp
  and gbaux_dlex = opp_dlex.gbaux
  and gb_dlex = opp_dlex.gb
  and comp_min_basis_pre_dlex = opp_dlex.comp_min_basis_pre
  and comp_min_basis_aux_dlex = opp_dlex.comp_min_basis_aux
  and comp_min_basis_dlex = opp_dlex.comp_min_basis
  and comp_red_basis_aux_dlex = opp_dlex.comp_red_basis_aux
  and comp_red_basis_dlex = opp_dlex.comp_red_basis
  and monic_dlex = opp_dlex.monic
  and comp_red_monic_basis_dlex = opp_dlex.comp_red_monic_basis
  and rgb_dlex = opp_dlex.rgb
  apply standard
  subgoal by (simp add: dlex_pm_strict_def)
  subgoal by (rule dlex_pm_refl)
  subgoal by (erule dlex_pm_trans, simp)
  subgoal by (erule dlex_pm_antisym, simp)
  subgoal by (rule dlex_pm_lin)
  subgoal by (rule dlex_pm_zero_min)
  subgoal by (erule dlex_pm_plus_monotone)
  done

abbreviation PP :: "('a \<times> nat) list \<Rightarrow> 'a \<Rightarrow>\<^sub>0 nat" where "PP \<equiv> PM"

lemma
  "rgb_dlex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ] =
    [
     (MP [(PP [(X, 5)], 1), (PP [(X, 1), (Z, 3)], -1)]),
     (MP [(PP [(X, 3), (Y, 1)], 1), (PP [(X, 1), (Z, 1)], -1)]),
     (MP [(PP [(X, 3)], -1), (PP [(X, 1), (Y, 1), (Z, 2)], 1)]),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [], -1)])
    ]"
  by eval

lemma
  "rgb_dlex
    [
     (MP [(PP [(X, 2)], 1), (PP [(Y, 2)], 1), (PP [(Z, 2)], 1::rat), (PP [], -1)]),
     (MP [(PP [(X, 1), (Y, 1)], 1), (PP [(Z, 1)], -1), (PP [], -1)]),
     (MP [(PP [(Y, 2)], 1), (PP [(X, 1)], 1)]),
     (MP [(PP [(Z, 2)], 1), (PP [(X, 1)], 1)])
    ] =
    [
     (MP [(PP [], 1)])
    ]"
  by eval (* Takes a bit longer (~ 1 minute). *)

text \<open>Note: The above computations have been cross-checked with Mathematica 11.1.\<close>

hide_const (open) MPoly_Type_Class_FMap.X MPoly_Type_Class_FMap.Y MPoly_Type_Class_FMap.Z

end (* theory *)
