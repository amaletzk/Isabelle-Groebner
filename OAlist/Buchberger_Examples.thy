(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Buchberger's Algorithm\<close>

theory Buchberger_Examples
  imports "../Groebner_Bases/Buchberger" "Algorithm_Schema_Impl" "../Print" "../Groebner_Bases/Code_Target_Rat"
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

  defines find_adds_punit = punit'.punit.find_adds
  and trd_aux_punit = punit'.punit.trd_aux
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
  and gb_aux_punit = punit'.punit.gb_aux_punit
  and gb_punit = punit'.punit.gb_punit \<comment>\<open>Faster, because incorporates product criterion.\<close>
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

consts pm_to_list :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<times> 'b) list"

lemma compute_pm_to_list [code]: "pm_to_list (Pm_oalist xs) = list_of_oalist xs"
  sorry

lemma compute_spoly_punit [code]:
  "spoly_punit p q = (let t1 = lt_punit p; t2 = lt_punit q; l = lcs t1 t2 in
         (monom_mult_punit (1 / lc_punit p) (l - t1) p) - (monom_mult_punit (1 / lc_punit q) (l - t2) q))"
  sorry

lemma compute_trd_aux_punit [code]:
  "trd_aux_punit fs p r =
    (if is_zero p then
      r
    else
      case find_adds_punit fs (lt_punit p) of
        None   \<Rightarrow> trd_aux_punit fs (tail_punit p) (plus_monomial_less r (lc_punit p) (lt_punit p))
      | Some f \<Rightarrow> trd_aux_punit fs (tail_punit p - monom_mult_punit (lc_punit p / lc_punit f) (lt_punit p - lt_punit f) (tail_punit f)) r
    )"
  apply (simp only: trd_aux_punit_def)
  sorry

function trd_aux_punit_print where
  "trd_aux_punit_print fs p r (i::nat) (j::nat) =
    (if is_zero p then
      print (i, j) r
    else
      case find_adds_punit fs (lt_punit p) of
        None   \<Rightarrow> trd_aux_punit_print fs (tail_punit p) (plus_monomial_less r (lc_punit p) (lt_punit p)) (Suc i) j
      | Some f \<Rightarrow> trd_aux_punit_print fs
                    (timing (tail_punit p - monom_mult_punit (lc_punit p / lc_punit f) (lt_punit p - lt_punit f) (tail_punit f)))
                    (print (lc_punit p / lc_punit f) r)
                    i (Suc j)
    )"
  by auto
termination sorry

definition "product_crit_punit_print =
  (\<lambda>gs bs ps data p q. if product_crit_punit gs bs ps data p q then (print ''prod'' True) else False)"

definition "chain_crit_punit_print =
  (\<lambda>gs bs ps data p q. if chain_crit_punit gs bs ps data p q then (print ''chain'' True) else False)"

definition "pc_crit_punit_print = comb_crit_punit product_crit_punit_print chain_crit_punit_print"

definition "pc_crit_punit_timing =
  (\<lambda>gs bs ps data p q. timing_lbl ''pc'' (comb_crit_punit product_crit_punit chain_crit_punit gs bs ps data p q))"

definition "trdsp_punit_timing = (\<lambda>bs p. timing_lbl ''trdsp'' (trd_punit bs (spoly_punit (fst (fst p)) (fst (snd p)))))"

definition "discard_red_cp_punit_timing =
  (\<lambda>crit rcp gs bs ps sps data. timing_lbl ''rd'' (rcp gs bs (discard_crit_pairs_punit crit gs bs ps sps data) data))"

definition "add_pairs_sorted_punit_timing =
  (\<lambda>rel gs bs ps hs data.
      timing_lbl ''ap'' (fold (add_pairs_single_sorted_punit (rel data) gs bs) hs
                (merge_wrt (rel data) ps (Algorithm_Schema.pairs (add_pairs_single_sorted_punit (rel data)) hs))))"

definition "add_basis_sorted_print =
  (\<lambda>rel gs bs ns data. (if length ns = 0 then (\<lambda>_ x. x) else print) (length bs + length ns, map (card_keys \<circ> fst) ns) (merge_wrt (rel data) bs ns))"

definition "add_basis_sorted_print2 =
  (\<lambda>rel gs bs ns data. print (length (filter (\<lambda>b. let v = lt_punit (fst b) in \<exists>h\<in>set ns. adds_pm_add_linorder (lt_punit (fst h)) v) bs)) (merge_wrt (rel data) bs ns))"

definition "add_basis_sorted_timing =
  (\<lambda>rel gs bs ns data. timing_lbl ''ab'' (merge_wrt (rel data) bs ns))"

definition "gb_sel_punit_print =
  (\<lambda>_ _ ps _. print (length ps) (if List.null ps then [] else [hd ps]))"

lemma product_crit_punit_print [simp]: "product_crit_punit_print = product_crit_punit"
  by (simp add: product_crit_punit_print_def)

lemma chain_crit_punit_print [simp]: "chain_crit_punit_print = chain_crit_punit"
  by (simp add: chain_crit_punit_print_def)

(*
lemma pc_crit_punit_print [code_abbrev]: "pc_crit_punit_print = pc_crit_punit"
  by (simp add: pc_crit_punit_print_def punit'.punit.pc_crit_def)
*)

(*
lemma gb_sel_punit_print [code_abbrev]: "gb_sel_punit_print = gb_sel_punit"
  apply (simp add: gb_sel_punit_print_def Let_def) sorry
*)

(*
lemma pc_crit_punit_timing [code_abbrev]: "pc_crit_punit_timing = pc_crit_punit"
  sorry
*)

(*
lemma discard_red_cp_punit_timing [code_abbrev]: "discard_red_cp_punit_timing = discard_red_cp_punit"
  sorry

lemma add_pairs_sorted_punit_timing [code_abbrev]: "add_pairs_sorted_punit_timing = add_pairs_sorted_punit"
  sorry

lemma add_basis_sorted_timing [code_abbrev]: "add_basis_sorted_timing = add_basis_sorted"
  sorry
*)

lemma add_basis_sorted_print [code_abbrev]: "add_basis_sorted_print = add_basis_sorted"
  sorry

(*
lemma trd_punit_print [code_abbrev]: "trd_punit_print = trd_punit"
  sorry
*)

(*
lemma compute_trd_punit [code]: "trd_punit fs p = trd_aux_punit_print fs p 0 0 0"
  sorry
*)

(*
lemma trdsp_punit_timing [code_abbrev]: "trdsp_punit_timing = trdsp_punit"
  sorry
*)

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
  "trd_punit [Y\<^sup>2 * Z + 2 * Y * Z ^ 3] (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z ^ 3) =
    X\<^sup>2 * Z ^ 4 + Y ^ 4 * Z"
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

definition "gb_cyclic n = (gb_punit (map (\<lambda>p. (p, ())) (rev ((cyclic n)::(_ \<Rightarrow>\<^sub>0 rat) list))) ())"

value [code] "timing (length (gb_punit (map (\<lambda>p. (p, ())) (Katsura 2)) ()))"

value [code] "timing (length (gb_cyclic 5))"

function repeat :: "(natural \<Rightarrow> 'c) \<Rightarrow> natural \<Rightarrow> 'c" where
  "repeat f n = (if n = 0 then f 0 else (let _ = f n in repeat f (n - 1)))"
  by auto
termination sorry

value [code] "(215/587)::rat"

value [code] "let r1 = (1587403220023648961010354787510025/754422498806579781314598530046874)::rat;
                  r2 = (1587410325684552047810144874/8455657518197317514479580621624761948498527639189070213488573493541897381325890539198611871410797366962398562593692460878056090389366922786523226701592701116126522722087517900268748285083392130388459943058915232146768)::rat in
                timing (repeat (\<lambda>i. r1 + r2) (natural_of_nat 1000))"

(* The same computation takes 0.004 seconds with Ratio.ratio in OCaml!
  The denominator of r2 with 200+ digits actually appears in the computation of cyclic-6. *)

end (* theory *)
