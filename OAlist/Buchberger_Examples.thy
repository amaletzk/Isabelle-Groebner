(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Buchberger's Algorithm\<close>

theory Buchberger_Examples
  imports Groebner_Bases.Buchberger Groebner_Bases.Algorithm_Schema_Impl Groebner_Bases.Code_Target_Rat "../Print"
begin

subsection \<open>Scalar Polynomials\<close>

global_interpretation punit': gd_powerprod "ord_pp_punit cmp_term" "ord_pp_strict_punit cmp_term"
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = (\<lambda>x. x)"
  and "punit.component_of_term = (\<lambda>_. ())"
  and "punit.monom_mult = monom_mult_punit"
  and "punit.mult_scalar = mult_scalar_punit"
  and "punit'.punit.min_term = min_term_punit"
  and "punit'.punit.lt = lt_punit cmp_term"
  and "punit'.punit.lc = lc_punit cmp_term"
  and "punit'.punit.tail = tail_punit cmp_term"
  and "punit'.punit.ord_p = ord_p_punit cmp_term"
  and "punit'.punit.ord_strict_p = ord_strict_p_punit cmp_term"
  for cmp_term :: "('a::nat, 'b::{nat,add_wellorder}) pp nat_term_order"

  defines find_adds_punit = punit'.punit.find_adds
  and trd_aux_punit = punit'.punit.trd_aux
  and trd_punit = punit'.punit.trd
  and spoly_punit = punit'.punit.spoly
  and count_const_lt_components_punit = punit'.punit.count_const_lt_components
  and count_rem_components_punit = punit'.punit.count_rem_components
  and const_lt_component_punit = punit'.punit.const_lt_component
  and full_gb_punit = punit'.punit.full_gb
  and add_pairs_single_sorted_punit = punit'.punit.add_pairs_single_sorted
  and add_pairs_punit = punit'.punit.add_pairs
  and canon_pair_order_aux_punit = punit'.punit.canon_pair_order_aux
  and canon_basis_order_punit = punit'.punit.canon_basis_order
  and new_pairs_sorted_punit = punit'.punit.new_pairs_sorted
  and product_crit_punit = punit'.punit.product_crit
  and chain_ncrit_punit = punit'.punit.chain_ncrit
  and chain_ocrit_punit = punit'.punit.chain_ocrit
  and apply_icrit_punit = punit'.punit.apply_icrit
  and apply_ncrit_punit = punit'.punit.apply_ncrit
  and apply_ocrit_punit = punit'.punit.apply_ocrit
  and trdsp_punit = punit'.punit.trdsp
  and gb_sel_punit = punit'.punit.gb_sel
  and gb_red_aux_punit = punit'.punit.gb_red_aux
  and gb_red_punit = punit'.punit.gb_red
  and gb_aux_punit = punit'.punit.gb_aux_punit
  and gb_punit = punit'.punit.gb_punit \<comment>\<open>Faster, because incorporates product criterion.\<close>
  subgoal by (fact gd_powerprod_ord_pp_punit)
  subgoal by (fact punit_adds_term)
  subgoal by (simp add: id_def)
  subgoal by (fact punit_component_of_term)
  subgoal by (simp only: monom_mult_punit_def)
  subgoal by (simp only: mult_scalar_punit_def)
  subgoal using min_term_punit_def by fastforce
  subgoal by (simp only: lt_punit_def ord_pp_punit_alt)
  subgoal by (simp only: lc_punit_def ord_pp_punit_alt)
  subgoal by (simp only: tail_punit_def ord_pp_punit_alt)
  subgoal by (simp only: ord_p_punit_def ord_pp_strict_punit_alt)
  subgoal by (simp only: ord_strict_p_punit_def ord_pp_strict_punit_alt)
  done

lemma compute_spoly_punit [code]:
  "spoly_punit to p q = (let t1 = lt_punit to p; t2 = lt_punit to q; l = lcs t1 t2 in
         (monom_mult_punit (1 / lc_punit to p) (l - t1) p) - (monom_mult_punit (1 / lc_punit to q) (l - t2) q))"
  by (simp add: punit'.punit.spoly_def Let_def punit'.punit.lc_def)

lemma compute_trd_aux_punit [code]:
  "trd_aux_punit to fs p r =
    (if is_zero p then
      r
    else
      case find_adds_punit to fs (lt_punit to p) of
        None   \<Rightarrow> trd_aux_punit to fs (tail_punit to p) (plus_monomial_less r (lc_punit to p) (lt_punit to p))
      | Some f \<Rightarrow> trd_aux_punit to fs (tail_punit to p - monom_mult_punit (lc_punit to p / lc_punit to f) (lt_punit to p - lt_punit to f) (tail_punit to f)) r
    )"
  by (simp only: punit'.punit.trd_aux.simps[of to fs p r] plus_monomial_less_def is_zero_def)

function trd_aux_punit_print where
  "trd_aux_punit_print to fs p r (i::nat) (j::nat) =
    (if is_zero p then
      print (i, j) r
    else
      case find_adds_punit to fs (lt_punit to p) of
        None   \<Rightarrow> trd_aux_punit_print to fs (tail_punit to p) (plus_monomial_less r (lc_punit to p) (lt_punit to p)) (Suc i) j
      | Some f \<Rightarrow> trd_aux_punit_print to fs
                    (timing (tail_punit to p - monom_mult_punit (lc_punit to p / lc_punit to f) (lt_punit to p - lt_punit to f) (tail_punit to f)))
                    (print (lc_punit to p / lc_punit to f) r)
                    i (Suc j)
    )"
  by auto
termination sorry

lemma compute_trd_punit [code]: "trd_punit to fs p = trd_aux_punit to fs p (change_ord to 0)"
  by (simp add: punit'.punit.trd_def change_ord_def)

definition "product_crit_punit_print to =
  (\<lambda>gs bs ps data p q. if product_crit_punit to gs bs ps data p q then (print ''prod'' True) else False)"

definition "chain_ncrit_punit_print to =
  (\<lambda>data gs bs hs ps q_in_bs p q. if chain_ncrit_punit to data gs bs hs ps q_in_bs p q then (print ''nchain'' True) else False)"

definition "chain_ocrit_punit_print to =
  (\<lambda>data hs ps p q. if chain_ocrit_punit to data hs ps p q then (print ''ochain'' True) else False)"

definition "trdsp_punit_timing to = (\<lambda>bs p. timing_lbl ''trdsp'' (trd_punit to bs (spoly_punit to (fst (fst p)) (fst (snd p)))))"

definition "add_pairs_punit_timing =
  (\<lambda>np icrit ncrit ocrit comb gs bs ps hs data.
      timing_lbl ''ap''
        (let ps1 = apply_ncrit_punit ncrit data gs bs hs (apply_icrit_punit icrit data gs bs hs (np gs bs hs data));
             ps2 = apply_ocrit_punit ocrit data hs ps1 ps in comb (map snd [x\<leftarrow>ps1 . \<not> fst x]) ps2))"

definition "add_pairs_punit_print =
  (\<lambda>np icrit ncrit ocrit comb gs bs ps hs data.
      (let ps1 = apply_ncrit_punit ncrit data gs bs hs (apply_icrit_punit icrit data gs bs hs (np gs bs hs data));
           ps2 = apply_ocrit_punit ocrit data hs ps1 ps;
           ps3 = [x\<leftarrow>ps1 . \<not> fst x] in print (length ps2 + length ps3) (comb (map snd ps3) ps2)))"

definition "add_basis_sorted_print =
  (\<lambda>rel gs bs ns data. (if length ns = 0 then (\<lambda>_ x. x) else print) (length bs + length ns, map (card_keys \<circ> fst) ns) (merge_wrt (rel data) bs ns))"

definition "add_basis_sorted_timing =
  (\<lambda>rel gs bs ns data. timing_lbl ''ab'' (merge_wrt (rel data) bs ns))"

definition "gb_sel_punit_print =
  (\<lambda>_ _ ps _. print (length ps) (if List.null ps then [] else [hd ps]))"

lemma product_crit_punit_print [simp]: "product_crit_punit_print = product_crit_punit"
  by (rule ext, simp add: product_crit_punit_print_def)

lemma chain_ncrit_punit_print [simp]: "chain_ncrit_punit_print = chain_ncrit_punit"
  by (rule ext, simp add: chain_ncrit_punit_print_def)

lemma chain_ocrit_punit_print [simp]: "chain_ocrit_punit_print = chain_ocrit_punit"
  by (rule ext, simp add: chain_ocrit_punit_print_def)

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

(*
lemma add_pairs_punit_canon_print [code_abbrev]: "add_pairs_punit_print = add_pairs_punit"
  sorry
*)

(*
lemma add_basis_sorted_print [code_abbrev]: "add_basis_sorted_print = add_basis_sorted"
  sorry
*)

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
  "lt_punit DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, 2), (2, 3)]"
  by eval

lemma
  "lc_punit DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 1"
  by eval

lemma
  "tail_punit DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3 * X\<^sup>2 * Y"
  by eval

lemma
  "ord_strict_p_punit DRLEX (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

value [code] "(sparse\<^sub>0 [(0::nat, 2::nat), (2, 1)]) adds (sparse\<^sub>0 [(0, 3), (1, 2), (2, 1)])"

lemma
  "trd_punit DRLEX [Y\<^sup>2 * Z + 2 * Y * Z ^ 3] (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z ^ 3) =
    X\<^sup>2 * Z ^ 4 + Y ^ 4 * Z"
  by eval

lemma
  "spoly_punit DRLEX (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (Y\<^sup>2 * Z + 2 * Z ^ 3) =
    -2 * Y ^ 3 * Z\<^sup>2 - (C\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2"
  by eval

lemma
  "gb_punit DRLEX
    [
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ())
    ] () =
    [
     (-2 * Y ^ 3 * Z\<^sup>2 - (C\<^sub>0 (1 / 2)) * X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2, ()),
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ()),
     (- (C\<^sub>0 (1 / 2)) * X\<^sup>2 * Y ^ 4 * Z - 2 * Y ^ 5 * Z, ())
    ]"
  by eval

lemma
  "gb_punit DRLEX
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
  "gb_punit DRLEX
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
  "gb_punit DRLEX
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

definition "gb_cyclic to n = (gb_punit to (map (\<lambda>p. (p, ())) (rev ((cyclic to n)::(_ \<Rightarrow>\<^sub>0 rat) list))) ())"

value [code] "timing (length (gb_punit DRLEX (map (\<lambda>p. (p, ())) (Katsura DRLEX 2)) ()))"

value [code] "timing (length (gb_cyclic DRLEX 5))"

function repeat :: "(natural \<Rightarrow> 'c) \<Rightarrow> natural \<Rightarrow> 'c" where
  "repeat f n = (if n = 0 then f 0 else (let _ = f n in repeat f (n - 1)))"
  by auto
termination sorry

value [code] "let r1 = (1587403220023648961010354787510025/754422498806579781314598530046874)::rat;
                  r2 = (1587410325684552047810144874/8455657518197317514479580621624761948498527639189070213488573493541897381325890539198611871410797366962398562593692460878056090389366922786523226701592701116126522722087517900268748285083392130388459943058915232146768)::rat in
                timing_nores (repeat (\<lambda>i. r1 + r2) (natural_of_nat 1000))"

(* The same computation takes 0.004 seconds with Ratio.ratio in OCaml!
  The denominator of r2 with 200+ digits actually appears in the computation of cyclic-6. *)

subsection \<open>Vector Polynomials\<close>

text \<open>We must define the following four constants outside the global interpretation, since otherwise
  their types are too general.\<close>

definition splus_pprod :: "('a::nat, 'b::nat) pp \<Rightarrow> _"
  where "splus_pprod = pprod.splus"

definition monom_mult_pprod :: "'c::semiring_0 \<Rightarrow> ('a::nat, 'b::nat) pp \<Rightarrow> _"
  where "monom_mult_pprod = pprod.monom_mult"

definition mult_scalar_pprod :: "(('a::nat, 'b::nat) pp \<Rightarrow>\<^sub>0 'c::semiring_0) \<Rightarrow> _"
  where "mult_scalar_pprod = pprod.mult_scalar"

definition adds_term_pprod :: "(('a::nat, 'b::nat) pp \<times> _) \<Rightarrow> _"
  where "adds_term_pprod = pprod.adds_term"

global_interpretation pprod': gd_nat_term "\<lambda>x::('a, 'b) pp \<times> 'c. x" "\<lambda>x. x" cmp_term
  rewrites "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  and "pprod.splus = splus_pprod"
  and "pprod.monom_mult = monom_mult_pprod"
  and "pprod.mult_scalar = mult_scalar_pprod"
  and "pprod.adds_term = adds_term_pprod"
  for cmp_term :: "(('a::nat, 'b::nat) pp \<times> 'c::{nat,the_min}) nat_term_order"
  defines shift_map_keys_pprod = pprod'.shift_map_keys
  and min_term_pprod = pprod'.min_term
  and lt_pprod = pprod'.lt
  and lc_pprod = pprod'.lc
  and tail_pprod = pprod'.tail
  and comp_opt_p_pprod = pprod'.comp_opt_p
  and ord_p_pprod = pprod'.ord_p
  and ord_strict_p_pprod = pprod'.ord_strict_p
  and find_adds_pprod = pprod'.find_adds
  and trd_aux_pprod= pprod'.trd_aux
  and trd_pprod = pprod'.trd
  and spoly_pprod = pprod'.spoly
  and count_const_lt_components_pprod = pprod'.count_const_lt_components
  and count_rem_components_pprod = pprod'.count_rem_components
  and const_lt_component_pprod = pprod'.const_lt_component
  and full_gb_pprod = pprod'.full_gb
  and keys_to_list_pprod = pprod'.keys_to_list
  and Keys_to_list_pprod = pprod'.Keys_to_list
  and add_pairs_single_sorted_pprod = pprod'.add_pairs_single_sorted
  and add_pairs_pprod = pprod'.add_pairs
  and canon_pair_order_aux_pprod = pprod'.canon_pair_order_aux
  and canon_basis_order_pprod = pprod'.canon_basis_order
  and new_pairs_sorted_pprod = pprod'.new_pairs_sorted
  and component_crit_pprod = pprod'.component_crit
  and chain_ncrit_pprod = pprod'.chain_ncrit
  and chain_ocrit_pprod = pprod'.chain_ocrit
  and apply_icrit_pprod = pprod'.apply_icrit
  and apply_ncrit_pprod = pprod'.apply_ncrit
  and apply_ocrit_pprod = pprod'.apply_ocrit
  and trdsp_pprod = pprod'.trdsp
  and gb_sel_pprod = pprod'.gb_sel
  and gb_red_aux_pprod = pprod'.gb_red_aux
  and gb_red_pprod = pprod'.gb_red
  and gb_aux_pprod = pprod'.gb_aux
  and gb_pprod = pprod'.gb
  subgoal by (fact gd_nat_term_id)
  subgoal by (fact pprod_pp_of_term)
  subgoal by (fact pprod_component_of_term)
  subgoal by (simp only: splus_pprod_def)
  subgoal by (simp only: monom_mult_pprod_def)
  subgoal by (simp only: mult_scalar_pprod_def)
  subgoal by (simp only: adds_term_pprod_def)
  done

lemma compute_adds_term_pprod [code]:
  "adds_term_pprod u v = (snd u = snd v \<and> adds_pp_add_linorder (fst u) (fst v))"
  by (simp add: adds_term_pprod_def pprod.adds_term_def adds_pp_add_linorder_def)

lemma compute_splus_pprod [code]: "splus_pprod t (s, i) = (t + s, i)"
  by (simp add: splus_pprod_def pprod.splus_def)

lemma compute_shift_map_keys_pprod [code abstract]:
  "list_of_oalist_ntm (shift_map_keys_pprod t f xs) = map_raw (\<lambda>(k, v). (splus_pprod t k, f v)) (list_of_oalist_ntm xs)"
  by (simp add: pprod'.list_of_oalist_shift_keys case_prod_beta')

lemma compute_trd_pprod [code]: "trd_pprod to fs p = trd_aux_pprod to fs p (change_ord to 0)"
  by (simp add: pprod'.trd_def change_ord_def)

lemmas [code] = conversep_iff

definition Vec\<^sub>0 :: "nat \<Rightarrow> (('a, nat) pp \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a::nat, nat) pp \<times> nat) \<Rightarrow>\<^sub>0 'b::semiring_1" where
  "Vec\<^sub>0 i p = mult_scalar_pprod p (Poly_Mapping.single (0, i) 1)"

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "ord_p_pprod (POT DRLEX) (Vec\<^sub>0 1 (X\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) (Vec\<^sub>0 1 (X\<^sup>2 * Z\<^sup>2 + 2 * Y ^ 3 * Z\<^sup>2))"
  by eval

lemma
  "tail_pprod (POT DRLEX) (Vec\<^sub>0 1 (X\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) = Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "lt_pprod (POT DRLEX) (Vec\<^sub>0 1 (X\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) = (sparse\<^sub>0 [(0, 2), (2, 1)], 1)"
  by eval

lemma
  "keys (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2)) =
    {(sparse\<^sub>0 [(0, 2), (2, 3)], 0), (sparse\<^sub>0 [(1, 3), (2, 2)], 1)}"
  by eval

lemma
  "keys (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 2 (2 * Y ^ 3 * Z\<^sup>2)) =
    {(sparse\<^sub>0 [(0, 2), (2, 3)], 0), (sparse\<^sub>0 [(1, 3), (2, 2)], 2)}"
  by eval

lemma
  "Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2) + Vec\<^sub>0 3 (X\<^sup>2 * Z ^ 4) + Vec\<^sub>0 1 (- 2 * Y ^ 3 * Z\<^sup>2) =
    Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 7) + Vec\<^sub>0 3 (X\<^sup>2 * Z ^ 4)"
  by eval

lemma
  "lookup (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 7) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2 + 2)) (sparse\<^sub>0 [(0, 2), (2, 7)], 0) = 1"
  by eval

lemma
  "lookup (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 7) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2 + 2)) (sparse\<^sub>0 [(0, 2), (2, 7)], 1) = 0"
  by eval

lemma
  "Vec\<^sub>0 0 (0 * X^2 * Z^7) + Vec\<^sub>0 1 (0 * Y^3*Z\<^sup>2) = 0"
  by eval

lemma
  "monom_mult_pprod 3 (sparse\<^sub>0 [(1, 2::nat)]) (Vec\<^sub>0 0 (X\<^sup>2 * Z) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2)) =
    Vec\<^sub>0 0 (3 * Y\<^sup>2 * Z * X\<^sup>2) + Vec\<^sub>0 1 (6 * Y ^ 5 * Z\<^sup>2)"
  by eval

lemma
  "trd_pprod DRLEX [Vec\<^sub>0 0 (Y\<^sup>2 * Z + 2 * Y * Z ^ 3)] (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z ^ 3)) =
    Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 4 + Y ^ 4 * Z)"
  by eval

lemma
  "length (gb_pprod (POT DRLEX)
    [
     (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2), ()),
     (Vec\<^sub>0 0 (Y\<^sup>2 * Z + 2 * Z ^ 3), ())
    ] ()) = 4"
  by eval

end

end (* theory *)
