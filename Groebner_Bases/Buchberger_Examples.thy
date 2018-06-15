(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Buchberger's Algorithm\<close>

theory Buchberger_Examples
  imports Buchberger Code_Target_Rat Algorithm_Schema_Impl
begin

subsection \<open>Degree-Reverse-Lexicographic Order\<close>

global_interpretation drlex: gd_powerprod drlex_pm drlex_pm_strict
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = (\<lambda>x. x)"
  and "punit.component_of_term = (\<lambda>_. ())"
  and "punit.monom_mult = monom_mult_punit"
  and "punit.mult_scalar = mult_scalar_punit"
  and "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  and "pprod.adds_term = adds_term_pprod"
  and "pprod.splus = splus_pprod"
  and "pprod.monom_mult = monom_mult_pprod"
  and "pprod.mult_scalar = mult_scalar_pprod"

  (* Scalar polynomials *)
  defines min_term_scalar_drlex = drlex.punit.min_term
  and lt_scalar_drlex = drlex.punit.lt
  and max_scalar_drlex = drlex.ordered_powerprod_lin.max
  and list_max_scalar_drlex = drlex.punit.list_max
  and higher_scalar_drlex = drlex.punit.higher
  and lower_scalar_drlex = drlex.punit.lower
  and lc_scalar_drlex = drlex.punit.lc
  and tail_scalar_drlex = drlex.punit.tail
  and ord_p_scalar_drlex = drlex.punit.ord_p
  and ord_strict_p_scalar_drlex = drlex.punit.ord_strict_p
  and find_adds_scalar_drlex = drlex.punit.find_adds
  and trd_aux_scalar_drlex = drlex.punit.trd_aux
  and trd_scalar_drlex = drlex.punit.trd
  and spoly_scalar_drlex = drlex.punit.spoly
  and count_const_lt_components_scalar_drlex = drlex.punit.count_const_lt_components
  and count_rem_components_scalar_drlex = drlex.punit.count_rem_components
  and const_lt_component_scalar_drlex = drlex.punit.const_lt_component
  and full_gb_scalar_drlex = drlex.punit.full_gb
  and add_pairs_single_sorted_scalar_drlex = drlex.punit.add_pairs_single_sorted
  and add_pairs_scalar_drlex = drlex.punit.add_pairs
  and canon_pair_order_aux_scalar_drlex = drlex.punit.canon_pair_order_aux
  and canon_basis_order_scalar_drlex = drlex.punit.canon_basis_order
  and new_pairs_sorted_scalar_drlex = drlex.punit.new_pairs_sorted
  and product_crit_scalar_drlex = drlex.punit.product_crit
  and chain_ncrit_scalar_drlex = drlex.punit.chain_ncrit
  and chain_ocrit_scalar_drlex = drlex.punit.chain_ocrit
  and apply_icrit_scalar_drlex = drlex.punit.apply_icrit
  and apply_ncrit_scalar_drlex = drlex.punit.apply_ncrit
  and apply_ocrit_scalar_drlex = drlex.punit.apply_ocrit
  and trdsp_scalar_drlex = drlex.punit.trdsp
  and gb_sel_scalar_drlex = drlex.punit.gb_sel
  and gb_red_aux_scalar_drlex = drlex.punit.gb_red_aux
  and gb_red_scalar_drlex = drlex.punit.gb_red
  and gb_aux_scalar_drlex = drlex.punit.gb_aux_punit
  and gb_scalar_drlex = drlex.punit.gb_punit \<comment>\<open>Faster, because incorporates product criterion.\<close>

  (* POT *)
  (*and ord_pot_strict_drlex = drlex.ord_pot_strict*)
  and min_term_pot_drlex = drlex.pot.min_term
  and lt_pot_drlex = drlex.pot.lt
  and max_pot_drlex = drlex.pot.ord_term_lin.max
  and list_max_pot_drlex = drlex.pot.list_max
  and higher_pot_drlex = drlex.pot.higher
  and lower_pot_drlex = drlex.pot.lower
  and lc_pot_drlex = drlex.pot.lc
  and tail_pot_drlex = drlex.pot.tail
  and ord_p_pot_drlex = drlex.pot.ord_p
  and ord_strict_p_pot_drlex = drlex.pot.ord_strict_p
  and find_adds_pot_drlex = drlex.pot.find_adds
  and trd_aux_pot_drlex = drlex.pot.trd_aux
  and trd_pot_drlex = drlex.pot.trd
  and spoly_pot_drlex = drlex.pot.spoly
  and insort_key_pot_drlex = drlex.pot.ord_term_lin.insort_key
  and sort_key_pot_drlex = drlex.pot.ord_term_lin.sort_key
  and sorted_list_of_set_pot_drlex = drlex.pot.ord_term_lin.sorted_list_of_set
  and pps_to_list_pot_drlex = drlex.pot.pps_to_list
  and keys_to_list_pot_drlex = drlex.pot.keys_to_list
  and Keys_to_list_pot_drlex = drlex.pot.Keys_to_list
  and count_const_lt_components_pot_drlex = drlex.pot.count_const_lt_components
  and count_rem_components_pot_drlex = drlex.pot.count_rem_components
  and const_lt_component_pot_drlex = drlex.pot.const_lt_component
  and full_gb_pot_drlex = drlex.pot.full_gb
  and add_pairs_single_sorted_pot_drlex = drlex.pot.add_pairs_single_sorted
  and add_pairs_pot_drlex = drlex.pot.add_pairs
  and canon_pair_order_aux_pot_drlex = drlex.pot.canon_pair_order_aux
  and canon_basis_order_pot_drlex = drlex.pot.canon_basis_order
  and new_pairs_sorted_pot_drlex = drlex.pot.new_pairs_sorted
  and component_crit_pot_drlex = drlex.pot.component_crit
  and chain_ncrit_pot_drlex = drlex.pot.chain_ncrit
  and chain_ocrit_pot_drlex = drlex.pot.chain_ocrit
  and apply_icrit_pot_drlex = drlex.pot.apply_icrit
  and apply_ncrit_pot_drlex = drlex.pot.apply_ncrit
  and apply_ocrit_pot_drlex = drlex.pot.apply_ocrit
  and trdsp_pot_drlex = drlex.pot.trdsp
  and gb_sel_pot_drlex = drlex.pot.gb_sel
  and gb_red_aux_pot_drlex = drlex.pot.gb_red_aux
  and gb_red_pot_drlex = drlex.pot.gb_red
  and gb_aux_pot_drlex = drlex.pot.gb_aux
  and gb_pot_drlex = drlex.pot.gb
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
  show "punit.pp_of_term = (\<lambda>x. x)" by (fact punit_pp_of_term)
  show "punit.component_of_term = (\<lambda>_. ())" by (fact punit_component_of_term)
  show "punit.monom_mult = monom_mult_punit" by (simp only: monom_mult_punit_def)
  show "punit.mult_scalar = mult_scalar_punit" by (simp only: mult_scalar_punit_def)
  show "pprod.pp_of_term = fst" by (fact pprod_pp_of_term)
  show "pprod.component_of_term = snd" by (fact pprod_component_of_term)
  show "pprod.adds_term = adds_term_pprod" by (simp only: adds_term_pprod_def)
  show "pprod.splus = splus_pprod" by (simp only: splus_pprod_def)
  show "pprod.monom_mult = monom_mult_pprod" by (simp only: monom_mult_pprod_def)
  show "pprod.mult_scalar = mult_scalar_pprod" by (simp only: mult_scalar_pprod_def)
qed

(* If we define ord_pot_drlex in the global interpretation, no code equations are proved for lp_pot_drlex. *)
definition [code_abbrev]: "ord_pot_drlex = drlex.ord_pot"
definition [code_abbrev]: "ord_pot_strict_drlex = drlex.ord_pot_strict"

lemma compute_ord_pot_drlex [code]: "ord_pot_drlex (s, i) (t, j) = (i < j \<or> (i = j \<and> drlex_pm s t))"
  by (simp add: ord_pot_drlex_def drlex.ord_pot_def)

lemma compute_ord_pot_strict_drlex [code]: "ord_pot_strict_drlex x y = (\<not> ord_pot_drlex y x)"
  by (simp only: ord_pot_strict_drlex_def ord_pot_drlex_def drlex.ord_pot_strict_def)

lemmas [code] = conversep_iff

experiment begin interpretation trivariate\<^sub>0_rat .

subsubsection \<open>Computations with Vector Polynomials (POT)\<close>

lemma
  "lt_pot_drlex (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 1 (3 * X\<^sup>2 * Y)) = (sparse\<^sub>0 [(0, 2), (1, 1)], 1)"
  by eval

lemma
  "lc_pot_drlex (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 1 (3 * X\<^sup>2 * Y)) = 3"
  by eval

lemma
  "tail_pot_drlex (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 1 (3 * X\<^sup>2 * Y)) = Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3)"
  by eval

lemma
  "higher_pot_drlex (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 1 (3 * X\<^sup>2 * Y)) (sparse\<^sub>0 [(0, 2)], 2) = 0"
  by eval

lemma
  "ord_strict_p_pot_drlex (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)) (Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2))"
  by eval

lemma
  "trd_pot_drlex [Vec\<^sub>0 1 (Y\<^sup>2 * Z + 2 * Z ^ 3)] (Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 4) - Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) =
    Vec\<^sub>0 0 (-2 * Y ^ 3 * Z\<^sup>2) - Vec\<^sub>0 1 (Const\<^sub>0 (1 / 2) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2)"
  by eval

lemma
  "spoly_pot_drlex (Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 4) - Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) (Vec\<^sub>0 1 (Y\<^sup>2 * Z + 2 * Z ^ 3)) =
    Vec\<^sub>0 0 (-2 * Y ^ 3 * Z\<^sup>2) - Vec\<^sub>0 1 ((Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2)"
  by eval

lemma
  "gb_pot_drlex
    [
     (Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 4) - Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2), ()),
     (Vec\<^sub>0 1 (Y\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Z ^ 3), ())
    ] () =
  [
    (Vec\<^sub>0 0 (-2 * Y ^ 5 * Z\<^sup>2 - 2 * X\<^sup>2 * Z ^ 6), ()),
    (Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 4) - Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2), ()),
    (Vec\<^sub>0 1 (Y\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Z ^ 3), ())
  ]"
  by eval

subsubsection \<open>Computations with Scalar Polynomials\<close>

lemma
  "lt_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, 2), (2, 3)]"
  by eval

lemma
  "lc_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 1"
  by eval

lemma
  "tail_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3 * X\<^sup>2 * Y"
  by eval

lemma
  "higher_scalar_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) (sparse\<^sub>0 [(0, 2)]) = X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y"
  by eval

lemma
  "ord_strict_p_scalar_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "trd_scalar_drlex [Y\<^sup>2 * Z + 2 * Y * Z ^ 3] (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) =
    (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "spoly_scalar_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    -2 * Y ^ 3 * Z\<^sup>2 - (Const\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2"
  by eval

lemma
  "gb_scalar_drlex
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
  "gb_scalar_drlex
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
  "gb_scalar_drlex
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
  "gb_scalar_drlex
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

value [code] "length (gb_scalar_drlex (map (\<lambda>p. (p, ())) ((cyclic 4)::(_ \<Rightarrow>\<^sub>0 rat) list)) ())"

value [code] "length (gb_scalar_drlex (map (\<lambda>p. (p, ())) (Katsura 2)) ())"

end (* theory *)
