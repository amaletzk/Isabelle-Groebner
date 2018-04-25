theory Reduced_GB_Examples
  imports Groebner_Bases.Buchberger Reduced_GB Polynomials.MPoly_Type_Class_FMap
begin

definition (in gd_powerprod) rgb :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "rgb bs = comp_red_monic_basis (map fst (gb (map (\<lambda>b. (b, ())) bs) ()))"

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
  and find_adds_dlex = opp_dlex.find_adds
  and trd_aux_dlex = opp_dlex.trd_aux
  and trd_dlex = opp_dlex.trd
  and spoly_dlex = opp_dlex.spoly
  and canon_pair_order_dlex = opp_dlex.canon_pair_order
  and canon_basis_order_dlex = opp_dlex.canon_basis_order
  and product_crit_dlex = opp_dlex.product_crit
  and chain_crit_dlex = opp_dlex.chain_crit
  and comb_crit_dlex = opp_dlex.comb_crit
  and pc_crit_dlex = opp_dlex.pc_crit
  and discard_crit_pairs_aux_dlex = opp_dlex.discard_crit_pairs_aux
  and discard_crit_pairs_dlex = opp_dlex.discard_crit_pairs
  and discard_red_cp_dlex = opp_dlex.discard_red_cp
  and trdsp_dlex = opp_dlex.trdsp
  and gb_sel_dlex = opp_dlex.gb_sel
  and gb_red_aux_dlex = opp_dlex.gb_red_aux
  and gb_red_dlex = opp_dlex.gb_red
  and gb_aux_dlex = opp_dlex.gb_aux
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

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "rgb_dlex
    [
     X ^ 3 - X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1
    ] =
    [
     - (X ^ 3) + X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1,
     X ^ 3 * Y - X * Z,
     - (X * Z ^ 3) + X ^ 5
    ]"
  by eval

lemma
  "rgb_dlex
    [
     X\<^sup>2 + Y\<^sup>2 + Z\<^sup>2 - 1,
     X * Y - Z - 1,
     Y\<^sup>2 + X,
     Z\<^sup>2 + X
    ] =
    [
     1
    ]"
  by eval

text \<open>Note: The above computations have been cross-checked with Mathematica 11.1.\<close>

end

end (* theory *)
