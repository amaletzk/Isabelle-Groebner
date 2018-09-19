theory Buchberger_Timings
  imports Groebner_Bases.Buchberger_Examples Print "Signature_Groebner/Benchmarks"
begin

subsection \<open>Scalar Polynomials\<close>

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

definition "trdsp_punit_print to = (\<lambda>bs p. (let res = trd_punit to bs (spoly_punit to (fst (fst p)) (fst (snd p))) in if res = 0 then print ''0'' res else res))"

definition "add_pairs_punit_timing =
  (\<lambda>np icrit ncrit ocrit comb gs bs ps hs data.
      timing_lbl ''ap''
        (let ps1 = apply_ncrit_punit ncrit data gs bs hs (apply_icrit_punit icrit data gs bs hs (np gs bs hs data));
             ps2 = apply_ocrit_punit ocrit data hs ps1 ps in comb (map snd [x\<leftarrow>ps1 . \<not> fst x]) ps2))"

definition "add_pairs_punit_print =
  (\<lambda>np icrit ncrit ocrit comb gs bs ps hs data.
      (let ps0 = np gs bs hs data;
           ps1 = apply_ncrit_punit ncrit data gs bs hs (apply_icrit_punit icrit data gs bs hs ps0);
           ps2 = apply_ocrit_punit ocrit data hs ps1 ps;
           ps3 = [x\<leftarrow>ps1 . \<not> fst x] in print ((length ps + length ps0) - (length ps2 + length ps3)) (comb (map snd ps3) ps2)))"

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
lemma gb_sel_punit_print [code_abbrev]: "gb_sel_punit_print = gb_sel_punit"
  apply (simp add: gb_sel_punit_print_def Let_def) sorry
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

(*
lemma trdsp_punit_print [code_abbrev]: "trdsp_punit_print = trdsp_punit"
  sorry
*)

value [code] "timing (length (gb_punit DRLEX (map (\<lambda>p. (p, ())) ((eco DRLEX 8)::(_ \<Rightarrow>\<^sub>0 rat) list)) ()))"

end (* theory *)
