(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Buchberger's Algorithm\<close>

theory Buchberger_Examples
  imports "../Groebner_Bases/Buchberger" "Algorithm_Schema_Impl"
begin

lemma greater_eq_of_comp: "greater_eq_of_comp = drlex_pm"
  by (rule, rule, simp add: c.less_eq_of_comparator_def compare_poly_mapping_def drlex_pm_refl)

lemma greater_of_comp: "greater_of_comp = drlex_pm_strict"
  apply (rule, rule, simp add: c.less_of_comparator_def compare_poly_mapping_def drlex_pm_strict_def)
  using drlex_pm_antisym by blast

global_interpretation punit': gd_powerprod drlex_pm "drlex_pm_strict::(('a::{countable,compare,wellorder} \<Rightarrow>\<^sub>0 'b::add_wellorder) \<Rightarrow> _)"
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = id"
  and "punit.component_of_term = (\<lambda>_. ())"
  and "punit.monom_mult = monom_mult_punit"
  and "punit.mult_scalar = mult_scalar_punit"
  and "punit'.punit.min_term = min_term_punit"
  and "punit'.punit.lt = lt_punit"
  and "punit'.punit.lc = lc_punit"
  and "punit'.punit.tail = tail_punit"
  and "punit'.punit.ord_p = ord_p_punit"
  and "punit'.punit.ord_strict_p = ord_strict_p_punit"

  defines rd_mult_punit = punit'.punit.rd_mult
  and rd_punit = punit'.punit.rd
  and rd_list_punit = punit'.punit.rd_list
  and trd_punit = punit'.punit.trd
  and spoly_punit = punit'.punit.spoly
  and count_const_lt_components_punit = punit'.punit.count_const_lt_components
  and count_rem_components_punit = punit'.punit.count_rem_components
  and const_lt_component_punit = punit'.punit.const_lt_component
  and add_pairs_sorted_punit = punit'.punit.add_pairs_sorted
  and full_gb_punit = punit'.punit.full_gb
  and add_pairs_single_sorted_punit = punit'.punit.add_pairs_single_sorted
  and add_pairs_single_sorted_aux_punit = punit'.punit.add_pairs_single_sorted_aux
  and canon_pair_order_punit = punit'.punit.canon_pair_order
  and canon_basis_order_punit = punit'.punit.canon_basis_order
  and product_crit_punit = punit'.punit.product_crit
  and chain_crit_punit = punit'.punit.chain_crit
  and comb_crit_punit = punit'.punit.comb_crit
  and pc_crit_punit = punit'.punit.pc_crit
  and discard_crit_pairs_aux_punit = punit'.punit.discard_crit_pairs_aux
  and discard_crit_pairs_punit = punit'.punit.discard_crit_pairs
  and discard_red_cp_punit = punit'.punit.discard_red_cp
  and trdsp_punit = punit'.punit.trdsp
  and gb_sel_punit = punit'.punit.gb_sel
  and gb_red_aux_punit = punit'.punit.gb_red_aux
  and gb_red_punit = punit'.punit.gb_red
  and gb_aux_punit = punit'.punit.gb_aux
  and gb_punit = punit'.punit.gb
proof -
  show "gd_powerprod drlex_pm drlex_pm_strict"
    apply standard
    subgoal by (simp add: drlex_pm_strict_def)
    subgoal by (rule drlex_pm_refl)
    subgoal by (erule drlex_pm_trans, simp)
    subgoal by (erule drlex_pm_antisym, simp)
    subgoal by (rule drlex_pm_lin)
    subgoal by (rule drlex_pm_zero_min)
    subgoal by (erule drlex_pm_plus_monotone)
    done
  show "punit.adds_term = (adds)" by (fact punit_adds_term)
  show "punit.pp_of_term = id" by (fact punit_pp_of_term)
  show "punit.component_of_term = (\<lambda>_. ())" by (fact punit_component_of_term)
  show "punit.monom_mult = monom_mult_punit" by (simp only: monom_mult_punit_def)
  show "punit.mult_scalar = mult_scalar_punit" by (simp only: mult_scalar_punit_def)
qed (simp_all only: min_term_punit_def lt_punit_def lc_punit_def tail_punit_def ord_p_punit_def
    ord_strict_p_punit_def greater_eq_of_comp greater_of_comp)

lemmas [code_unfold] = id_def

lemma compute_spoly_punit [code]:
  "spoly_punit p q = (let t1 = lt_punit p; t2 = lt_punit q; l = lcs t1 t2 in
         (monom_mult_punit (1 / lc_punit p) (l - t1) p) - (monom_mult_punit (1 / lc_punit q) (l - t2) q))"
  sorry

experiment begin interpretation trivariate\<^sub>0_rat .

subsubsection \<open>Computations\<close>

lemma
  "lt_punit (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, 2), (2, 3)]"
  by eval

lemma
  "lc_punit (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 1"
  by eval

lemma
  "tail_punit (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3 * X\<^sup>2 * Y"
  by eval

lemma
  "ord_strict_p_punit (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "rd_mult_punit (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    Some (1 / 2, sparse\<^sub>0 [(0, 2), (2, 1)])"
  by eval

lemma
  "rd_punit (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    (-2 * Y ^ 3 * Z\<^sup>2 - Const\<^sub>0 (1 / 2) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2, True)"
  by eval

lemma
  "rd_list_punit [Y\<^sup>2 * Z + 2 * Z ^ 3] (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) =
    (-2 * Y ^ 3 * Z\<^sup>2 - Const\<^sub>0 (1 / 2) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2, True)"
  by eval

lemma
  "trd_punit [Y\<^sup>2 * Z + 2 * Y * Z ^ 3] (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) =
    (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "spoly_punit (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    -2 * Y ^ 3 * Z\<^sup>2 - (Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2"
  by eval

lemma
  "gb_punit
    [
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ())
    ] () =
    [
     (-2 * Y ^ 3 * Z\<^sup>2 - (Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2, ()),
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ()),
     (- (Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y ^ 4 * Z - 2 * Y ^ 5 * Z, ())
    ]"
  by eval

lemma
  "gb_punit
    [
     (X\<^sup>2 * Z\<^sup>2 - Y, ()),
     (Y\<^sup>2 * Z - 1, ())
    ] () =
    [
     (- (Y ^ 3) + X\<^sup>2 * Z, ()),
     (X\<^sup>2 * Z\<^sup>2 - Y, ()),
     (Y\<^sup>2 * Z - 1, ())
    ]"
  by eval

lemma
  "gb_punit
    [
     (X ^ 3 - X * Y * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z - 1, ())
    ] () =
    [
     (- (X ^ 3 * Y) + X * Z, ()),
     (X ^ 3 - X * Y * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z - 1, ()),
     (- (X * Z ^ 3) + X ^ 5, ())
    ]"
  by eval

lemma
  "gb_punit
    [
     (X\<^sup>2 + Y\<^sup>2 + Z\<^sup>2 - 1, ()),
     (X * Y - Z - 1, ()),
     (Y\<^sup>2 + X, ()),
     (Z\<^sup>2 + X, ())
    ] () =
    [
     (1, ())
    ]"
  by eval

end

value [code] "gb_punit (map (\<lambda>p. (p, ())) (cyclic 4)) ()"

value [code] "gb_punit (map (\<lambda>p. (p, ())) (Katsura 2)) ()"

end (* theory *)
