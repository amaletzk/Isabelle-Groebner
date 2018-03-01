(* Author: Alexander Maletzky *)

section \<open>Sample Computations with the F4 Algorithm\<close>

theory F4_Examples
  imports F4 Algorithm_Schema_Impl Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
begin

lemma compute_list_to_poly [code]: "list_to_poly ts cs = sparse\<^sub>0 (zip ts cs)"
  by (rule poly_mapping_eqI, simp add: lookup_list_to_poly sparse\<^sub>0_def list_to_fun_def
      fmlookup_default_def fmlookup_of_list)

lemma (in ordered_powerprod) compute_Macaulay_list [code]:
  "Macaulay_list ps =
     (let ts = Keys_to_list ps in
      filter (\<lambda>p. p \<noteq> 0) (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))
     )"
  by (simp add: Macaulay_list_def Macaulay_mat_def Let_def)

declare conversep_iff [code]

derive (eq) ceq poly_mapping
derive (no) ccompare poly_mapping
derive (dlist) set_impl poly_mapping
derive (no) cenum poly_mapping

derive (eq) ceq rat
derive (no) ccompare rat
derive (dlist) set_impl rat
derive (no) cenum rat

subsection \<open>Degree-Reverse-Lexicographic Order\<close>

thm RBT_ext.linorder_class.is_rbt_fold_rbt_insert_impl
thm RBT_Set2.linorder_class.is_rbt_fold_rbt_insert
thm linorder_class.set_less_eq_aux''_refl
thm ord_class.set_less_eq_aux'_refl
thm RBT_Set2.linorder_class.rbt_lookup_fold_rbt_insert
thm RBT_ext.linorder_class.rbt_lookup_fold_rbt_insert_impl

global_interpretation f4_drlex: gd_powerprod drlex_pm drlex_pm_strict
  defines lp_drlex = f4_drlex.lp
  and max_drlex = f4_drlex.ordered_powerprod_lin.max
  and max_list_drlex = f4_drlex.ordered_powerprod_lin.max_list
  and list_max_drlex = f4_drlex.list_max
  and higher_drlex = f4_drlex.higher
  and lower_drlex = f4_drlex.lower
  and lc_drlex = f4_drlex.lc
  and tail_drlex = f4_drlex.tail
  and ord_drlex = f4_drlex.ord_p
  and ord_strict_drlex = f4_drlex.ord_strict_p
  and rd_mult_drlex = f4_drlex.rd_mult
  and rd_drlex = f4_drlex.rd
  and rd_list_drlex = f4_drlex.rd_list
  and trd_drlex = f4_drlex.trd
  and spoly_drlex = f4_drlex.spoly
  and canon_pair_order_drlex = f4_drlex.canon_pair_order
  and canon_basis_order_drlex = f4_drlex.canon_basis_order
  and product_crit_drlex = f4_drlex.product_crit
  and chain_crit_drlex = f4_drlex.chain_crit
  and comb_crit_drlex = f4_drlex.comb_crit
  and pc_crit_drlex = f4_drlex.pc_crit
  and discard_crit_pairs_aux_drlex = f4_drlex.discard_crit_pairs_aux
  and discard_crit_pairs_drlex = f4_drlex.discard_crit_pairs
  and discard_red_cp_drlex = f4_drlex.discard_red_cp
  and part_key_drlex = f4_drlex.ordered_powerprod_lin.part
  and sort_key_drlex = f4_drlex.ordered_powerprod_lin.sort_key
  and pps_to_list_drlex = f4_drlex.pps_to_list
  and keys_to_list_drlex = f4_drlex.keys_to_list
  and Keys_to_list_drlex = f4_drlex.Keys_to_list
  and sym_preproc_addnew_drlex = f4_drlex.sym_preproc_addnew
  and sym_preproc_aux_drlex = f4_drlex.sym_preproc_aux
  and sym_preproc_drlex = f4_drlex.sym_preproc
  and Macaulay_mat_drlex = f4_drlex.Macaulay_mat
  and Macaulay_list_drlex = f4_drlex.Macaulay_list
  and pdata_pairs_to_list_drlex = f4_drlex.pdata_pairs_to_list
  and Macaulay_red_drlex = f4_drlex.Macaulay_red
  and f4_sel_aux_drlex = f4_drlex.f4_sel_aux
  and f4_sel_drlex = f4_drlex.f4_sel
  and f4_red_aux_drlex = f4_drlex.f4_red_aux
  and f4_red_drlex = f4_drlex.f4_red
  and f4_aux_drlex = f4_drlex.f4_aux
  and f4_drlex = f4_drlex.f4
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

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "lp_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, 2), (2, 3)]"
  by eval

lemma
  "lc_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 1"
  by eval

lemma
  "tail_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3 * X\<^sup>2 * Y"
  by eval

lemma
  "higher_drlex (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) (sparse\<^sub>0 [(0, 2)]) = X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y"
  by eval

lemma
  "ord_strict_drlex (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "f4_drlex
    [
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ())
    ] () =
    [
     (X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2 + 4 * Y ^ 3 * Z\<^sup>2, ()),
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ()),
     (X\<^sup>2 * Y ^ 4 * Z + 4 * Y ^ 5 * Z, ())
    ]"
  by eval

lemma
  "f4_drlex
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

value [code] "f4_drlex (map (\<lambda>p. (p, ())) (cyclic 4)) ()"

value [code] "f4_drlex (map (\<lambda>p. (p, ())) (Katsura 2)) ()"

end (* theory *)
