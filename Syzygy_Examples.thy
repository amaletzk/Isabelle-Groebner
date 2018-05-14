(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Buchberger's Algorithm\<close>

theory Syzygy_Examples
  imports "Groebner_Bases/Buchberger" "Groebner_Bases/Algorithm_Schema_Impl" Syzygy
begin

subsection \<open>Degree-Reverse-Lexicographic Order\<close>

global_interpretation drlex: gd_powerprod drlex_pm drlex_pm_strict
  rewrites "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  and "pprod.adds_term = adds_term_pprod"
  and "pprod.splus = splus_pprod"
  and "pprod.monom_mult = monom_mult_pprod"
  and "pprod.mult_scalar = mult_scalar_pprod"

  defines min_term_pot_drlex = drlex.pot.min_term
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
  and add_pairs_single_sorted_scalar_drlex = drlex.pot.add_pairs_single_sorted
  and add_pairs_scalar_drlex = drlex.pot.add_pairs
  and canon_pair_order_aux_scalar_drlex = drlex.pot.canon_pair_order_aux
  and canon_basis_order_scalar_drlex = drlex.pot.canon_basis_order
  and new_pairs_sorted_scalar_drlex = drlex.pot.new_pairs_sorted
  and component_crit_scalar_drlex = drlex.pot.component_crit
  and chain_ncrit_scalar_drlex = drlex.pot.chain_ncrit
  and chain_ocrit_scalar_drlex = drlex.pot.chain_ocrit
  and apply_icrit_scalar_drlex = drlex.pot.apply_icrit
  and apply_ncrit_scalar_drlex = drlex.pot.apply_ncrit
  and apply_ocrit_scalar_drlex = drlex.pot.apply_ocrit
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
  show "pprod.pp_of_term = fst" by (fact pprod_pp_of_term)
  show "pprod.component_of_term = snd" by (fact pprod_component_of_term)
  show "pprod.adds_term = adds_term_pprod" by (simp only: adds_term_pprod_def)
  show "pprod.splus = splus_pprod" by (simp only: splus_pprod_def)
  show "pprod.monom_mult = monom_mult_pprod" by (simp only: monom_mult_pprod_def)
  show "pprod.mult_scalar = mult_scalar_pprod" by (simp only: mult_scalar_pprod_def)
qed

text \<open>If we define ord_pot_drlex in the global interpretation, no code equations are proved for
  lp_pot_drlex and other functions.\<close>
definition [code_abbrev]: "ord_pot_drlex = drlex.ord_pot"
definition [code_abbrev]: "ord_pot_strict_drlex = drlex.ord_pot_strict"

lemma compute_ord_pot_drlex [code]: "ord_pot_drlex (s, i) (t, j) = (i < j \<or> (i = j \<and> drlex_pm s t))"
  by (simp add: ord_pot_drlex_def drlex.ord_pot_def)

lemma compute_ord_pot_strict_drlex [code]: "ord_pot_strict_drlex x y = (\<not> ord_pot_drlex y x)"
  by (simp only: ord_pot_strict_drlex_def ord_pot_drlex_def drlex.ord_pot_strict_def)

definition "syzygy_basis_drlex bs =
    filter_syzygy_basis (length bs) (map fst (gb_pot_drlex (map (\<lambda>p. (p, ())) (init_syzygy_list bs)) ()))"

lemma lookup0_fmupd: "lookup0 (fmupd a b m) a' = (if a = a' then b else lookup0 m a')"
  by (simp add: fmlookup_default_def)

lemma map_of_mapk:
  assumes "inj f"
  shows "map_of (map (case_prod (\<lambda>k. Pair (f k))) t) (f k) = map_of t k"
  using assms by (induct t, auto simp: inj_eq)

lemma compute_lift_poly_syz [code]:
  "lift_poly_syz n (Pm_fmap (fmap_of_list xs)) i =
    Pm_fmap (fmap_of_list (((0, i), 1) # (map (\<lambda>(k, v). ((fst k, snd k + n), v)) xs)))"
proof (rule poly_mapping_eqI, simp add: lookup_lift_poly_syz lookup0_fmupd, intro conjI impI)
  fix v::"'a \<times> nat"
  assume "n \<le> snd v"
  have "map_of (map (\<lambda>(k, y). ((fst k, snd k + n), y)) xs) v =
        map_of (map (\<lambda>(k, y). ((fst k, snd k + n), y)) xs) (fst (fst v, snd v - n), snd (fst v, snd v - n) + n)"
    by (simp add: \<open>n \<le> snd v\<close>)
  also from inj_proj_poly_syz have "... = map_of xs (fst v, snd v - n)" by (rule map_of_mapk)
  finally show "lookup0 (fmap_of_list xs) (fst v, snd v - n) =
         lookup0 (fmap_of_list (map (\<lambda>(k, y). ((fst k, snd k + n), y)) xs)) v"
    by (simp add: fmlookup_default_def fmlookup_of_list)
next
  fix v::"'a \<times> nat"
  assume "\<not> n \<le> snd v"
  have "map_of (map (\<lambda>(k, y). ((fst k, snd k + n), y)) xs) v = None"
  proof (simp add: map_of_eq_None_iff, rule)
    assume "v \<in> fst ` (\<lambda>(k, y). ((fst k, snd k + n), y)) ` set xs"
    then obtain t k where "v = (t, k + n)" by auto
    hence "n \<le> snd v" by simp
    with \<open>\<not> n \<le> snd v\<close> show False ..
  qed
  thus "lookup0 (fmap_of_list (map (\<lambda>(k, y). ((fst k, snd k + n), y)) xs)) v = 0"
    by (simp add: fmlookup_default_def fmlookup_of_list)
qed

lemmas [code] = conversep_iff

experiment begin interpretation trivariate\<^sub>0_rat .

subsubsection \<open>Computations\<close>

lemma
  "syzygy_basis_drlex [Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (X * Y * Z + 2 * Y\<^sup>2)] =
  [Vec\<^sub>0 0 (Const\<^sub>0 (1 / 3) * X * Y * Z + Const\<^sub>0 (2 / 3) * Y\<^sup>2) + Vec\<^sub>0 1 (Const\<^sub>0 (- 1 / 3) * X\<^sup>2 * Z ^ 3 - X\<^sup>2 * Y)]"
  by eval

value [code] "syzygy_basis_drlex [Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (X * Y * Z + 2 * Y\<^sup>2), Vec\<^sub>0 0 (X - Y + 3 * Z)]"

lemma
  "map fst (gb_pot_drlex (map (\<lambda>p. (p, ())) (init_syzygy_list
    [Vec\<^sub>0 0 (X ^ 4 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z), Vec\<^sub>0 0 (Z\<^sup>2 - X - Y)])) ()) =
  [
    Vec\<^sub>0 0 1 + Vec\<^sub>0 3 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 1 1 + Vec\<^sub>0 3 (Y ^ 3 + 2 * X * Z),
    Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z) - Vec\<^sub>0 1 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 2 1 + Vec\<^sub>0 3 (Z\<^sup>2 - X - Y),
    Vec\<^sub>0 1 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (Y ^ 3 + 2 * X * Z),
    Vec\<^sub>0 0 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 0 (- (Y ^ 3 * Z\<^sup>2) + Y ^ 4 + X * Y ^ 3 + 2 * X\<^sup>2 * Z + 2 * X * Y * Z - 2 * X * Z ^ 3) +
      Vec\<^sub>0 1 (X ^ 4 * Z\<^sup>2 - X ^ 5 - X ^ 4 * Y - 3 * X ^ 3 * Y - 3 * X\<^sup>2 * Y\<^sup>2 + 3 * X\<^sup>2 * Y * Z\<^sup>2)
  ]"
  by eval

lemma
  "syzygy_basis_drlex [Vec\<^sub>0 0 (X ^ 4 + 3 * X\<^sup>2 * Y), Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z), Vec\<^sub>0 0 (Z\<^sup>2 - X - Y)] =
  [
    Vec\<^sub>0 0 (Y ^ 3 + 2 * X * Z) - Vec\<^sub>0 1 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 1 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (Y ^ 3 + 2 * X * Z),
    Vec\<^sub>0 0 (Z\<^sup>2 - X - Y) - Vec\<^sub>0 2 (X ^ 4 + 3 * X\<^sup>2 * Y),
    Vec\<^sub>0 0 (- (Y ^ 3 * Z\<^sup>2) + Y ^ 4 + X * Y ^ 3 + 2 * X\<^sup>2 * Z + 2 * X * Y * Z - 2 * X * Z ^ 3) +
      Vec\<^sub>0 1 (X ^ 4 * Z\<^sup>2 - X ^ 5 - X ^ 4 * Y - 3 * X ^ 3 * Y - 3 * X\<^sup>2 * Y\<^sup>2 + 3 * X\<^sup>2 * Y * Z\<^sup>2)
  ]"
  by eval

value [code] "syzygy_basis_drlex [Vec\<^sub>0 0 (X * Y - Z), Vec\<^sub>0 0 (X * Z - Y), Vec\<^sub>0 0 (Y * Z - X)]"

lemma
  "map fst (gb_pot_drlex (map (\<lambda>p. (p, ())) (init_syzygy_list
    [Vec\<^sub>0 0 (X * Y - Z), Vec\<^sub>0 0 (X * Z - Y), Vec\<^sub>0 0 (Y * Z - X)])) ()) =
  [
    Vec\<^sub>0 0 1 + Vec\<^sub>0 3 (X * Y - Z),
    Vec\<^sub>0 1 1 + Vec\<^sub>0 3 (X * Z - Y),
    Vec\<^sub>0 2 1 + Vec\<^sub>0 3 (Y * Z - X),
    Vec\<^sub>0 0 (- X * Z + Y) + Vec\<^sub>0 1 (X * Y - Z),
    Vec\<^sub>0 0 (- Y * Z + X) + Vec\<^sub>0 2 (X * Y - Z),
    Vec\<^sub>0 1 (- Y * Z + X) + Vec\<^sub>0 2 (X * Z - Y),
    Vec\<^sub>0 1 (-Y) + Vec\<^sub>0 2 (X) + Vec\<^sub>0 3 (Y ^ 2 - X ^ 2),
    Vec\<^sub>0 0 (Z) + Vec\<^sub>0 2 (-X) + Vec\<^sub>0 3 (X ^ 2 - Z ^ 2),
    Vec\<^sub>0 0 (Y - Y * Z ^ 2) + Vec\<^sub>0 1 (Y ^ 2 * Z - Z) + Vec\<^sub>0 2 (Y ^ 2 - Z ^ 2),
    Vec\<^sub>0 0 (- Y) + Vec\<^sub>0 1 (- (X * Y)) + Vec\<^sub>0 2 (X ^ 2 - 1) + Vec\<^sub>0 3 (X - X ^ 3)
  ]"
  by eval

lemma
  "syzygy_basis_drlex [Vec\<^sub>0 0 (X * Y - Z), Vec\<^sub>0 0 (X * Z - Y), Vec\<^sub>0 0 (Y * Z - X)] =
  [
    Vec\<^sub>0 0 (- X * Z + Y) + Vec\<^sub>0 1 (X * Y - Z),
    Vec\<^sub>0 0 (- Y * Z + X) + Vec\<^sub>0 2 (X * Y - Z),
    Vec\<^sub>0 1 (- Y * Z + X) + Vec\<^sub>0 2 (X * Z - Y),
    Vec\<^sub>0 0 (Y - Y * Z ^ 2) + Vec\<^sub>0 1 (Y ^ 2 * Z - Z) + Vec\<^sub>0 2 (Y ^ 2 - Z ^ 2)
  ]"
  by eval

end

end (* theory *)
