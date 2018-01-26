(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Buchberger's Algorithm\<close>

theory Buchberger_Examples
  imports Buchberger Algorithm_Schema_Impl
begin

subsection \<open>Degree-Reverse-Lexicographic Order\<close>

global_interpretation opp_drlex: gd_powerprod drlex_pm drlex_pm_strict
  defines lp_drlex = opp_drlex.lp
  and max_drlex = opp_drlex.ordered_powerprod_lin.max
  and list_max_drlex = opp_drlex.list_max
  and higher_drlex = opp_drlex.higher
  and lower_drlex = opp_drlex.lower
  and lc_drlex = opp_drlex.lc
  and tail_drlex = opp_drlex.tail
  and ord_drlex = opp_drlex.ord_p
  and ord_strict_drlex = opp_drlex.ord_strict_p
  and rd_mult_drlex = opp_drlex.rd_mult
  and rd_drlex = opp_drlex.rd
  and rd_list_drlex = opp_drlex.rd_list
  and trd_drlex = opp_drlex.trd
  and spoly_drlex = opp_drlex.spoly
  and canon_pair_order_drlex = opp_drlex.canon_pair_order
  and canon_basis_order_drlex = opp_drlex.canon_basis_order
  and product_crit_drlex = opp_drlex.product_crit
  and chain_crit_drlex = opp_drlex.chain_crit
  and comb_crit_drlex = opp_drlex.comb_crit
  and pc_crit_drlex = opp_drlex.pc_crit
  and discard_crit_pairs_aux_drlex = opp_drlex.discard_crit_pairs_aux
  and discard_crit_pairs_drlex = opp_drlex.discard_crit_pairs
  and discard_red_cp_drlex = opp_drlex.discard_red_cp
  and trdsp_drlex = opp_drlex.trdsp
  and gb_sel_drlex = opp_drlex.gb_sel
  and gb_red_aux_drlex = opp_drlex.gb_red_aux
  and gb_red_drlex = opp_drlex.gb_red
  and gb_aux_drlex = opp_drlex.gb_aux
  and gb_drlex = opp_drlex.gb
  apply standard
  subgoal by (simp add: drlex_pm_strict_def)
  subgoal by (rule drlex_pm_refl)
  subgoal by (erule drlex_pm_trans, simp)
  subgoal by (erule drlex_pm_antisym, simp)
  subgoal by (rule drlex_pm_lin)
  subgoal by (rule drlex_pm_zero_min)
  subgoal by (erule drlex_pm_plus_monotone)
  done

subsubsection \<open>Computations\<close>

abbreviation PP :: "('a \<times> nat) list \<Rightarrow> 'a \<Rightarrow>\<^sub>0 nat" where "PP \<equiv> PM"

lemma
  "lp_drlex (MP [(PP [(X, 2::nat), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = PP [(X, 2), (Z, 3)]"
  by eval

lemma
  "lc_drlex (MP [(PP [(X, 2::nat), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) = 1"
  by eval

lemma
  "tail_drlex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) =
    MP [(PP [(X, 2), (Y, 1)], 3::rat)]"
  by eval

lemma
  "higher_drlex (MP [(PP [(X, 2), (Z, 3)], 1::rat), (PP [(X, 2), (Y, 1)], 3)]) (PP [(X, 2)]) =
    MP [(PP [(X, 2), (Z, 3)], 1), (PP [(X, 2), (Y, 1)], 3)]"
  by eval

lemma
  "ord_strict_drlex
    (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
    (MP [(PP [(X, 2), (Z, 7)], 1::rat), (PP [(Y, 3), (Z, 2)], 2)])"
  by eval

lemma
  "rd_mult_drlex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    (1 / 2, PP [(X, 2), (Z, 1)])"
  by eval

lemma
  "rd_drlex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(Y, 3), (Z, 2)], -2), (PP [(X, 2), (Y, 2), (Z, 2)], - 1 / 2)]"
  by eval

lemma
  "rd_list_drlex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(Y, 3), (Z, 2)], - 2), (PP [(X, 2), (Z, 2), (Y, 2)], - 1 / 2)]"
  by eval

lemma
  "trd_drlex
      [MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Y, 1), (Z, 3)], 2)]]
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)]) =
    MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)]"
  by eval

lemma
  "spoly_drlex
      (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)])
      (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)]) =
    MP [(PP [(Z, 2), (Y, 3)], - 2), (PP [(X, 2), (Z, 2), (Y, 2)], - 1 / 2)]"
  by eval

lemma
  "gb_drlex
    [
     (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)], ())
    ] () =
    [
     (MP [(PP [(Z, 2), (Y, 3)], - 2), (PP [(X, 2), (Z, 2), (Y, 2)], - 1 / 2)], ()),
     (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1), (PP [(Z, 3)], 2)], ()),
     (MP [(PP [(X, 2), (Z, 1), (Y, 4)], - 1 / 2), (PP [(Z, 1), (Y, 5)], - 2)], ())
    ]"
  by eval

lemma
  "gb_drlex
    [
     (MP [(PP [(X, 2), (Z, 2)], 1), (PP [(Y, 1)], -1)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (0, -1)], ())
    ] () =
    [
     (MP [(PP [(Y, 3)], - 1), (PP [(X, 2), (Z, 1)], 1)], ()),
     (MP [(PP [(X, 2), (Z, 2)], 1), (PP [(Y, 1)], - 1)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1), (0, - 1)], ())
    ]"
  by eval

lemma
  "gb_drlex
    [
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], -1)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (0, -1)], ())
    ] () =
    [
     (MP [(PP [(X, 3), (Y, 1)], - 1), (PP [(X, 1), (Z, 1)], 1)], ()),
     (MP [(PP [(X, 3)], 1), (PP [(X, 1), (Y, 1), (Z, 2)], - 1)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1), (0, - 1)], ()),
     (MP [(PP [(X, 1), (Z, 3)], - 1), (PP [(X, 5)], 1)], ())
    ]"
  by eval

lemma
  "gb_drlex
    [
     (MP [(PP [(X, 2)], 1), (PP [(Y, 2)], 1), (PP [(Z, 2)], 1::rat), (0, -1)], ()),
     (MP [(PP [(X, 1), (Y, 1)], 1), (PP [(Z, 1)], -1), (0, -1)], ()),
     (MP [(PP [(Y, 2)], 1), (PP [(X, 1)], 1)], ()),
     (MP [(PP [(Z, 2)], 1), (PP [(X, 1)], 1)], ())
    ] () =
    [
     (MP [(0, 1)], ())
    ]"
  by eval

value [code] "gb_drlex (map (\<lambda>p. (p, ())) (cyclic 4)) ()"

end (* theory *)
