(* Author: Alexander Maletzky *)

section \<open>Sample Computations with the F4 Algorithm\<close>

theory F4_Examples
  imports F4 Polynomials.MPoly_Type_Class_FMap Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
begin

definition keys_list :: "('a \<times> 'b::zero) list \<Rightarrow> 'a list"
  where "keys_list xs = map fst [x\<leftarrow>AList.clearjunk xs. snd x \<noteq> 0]"

lemma distinct_keys_list: "distinct (keys_list xs)"
  unfolding keys_list_def using distinct_clearjunk by (rule distinct_map_filter)

lemma compute_keys_alt [code]: "keys (Pm_fmap (fmap_of_list xs)) = set (keys_list xs)"
proof (simp add: compute_keys_pp clearjunk0_def fmlookup_of_list fmdom'_alt_def fset_of_list.rep_eq
      keys_list_def)
  show "{x. map_of xs x \<noteq> Some 0} \<inter> fst ` set xs = fst ` {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}"
      (is "?l = ?r")
  proof
    show "?l \<subseteq> ?r"
    proof (rule, simp, elim conjE)
      fix t
      assume "map_of xs t \<noteq> Some 0" and "t \<in> fst ` set xs"
      hence "map_of (AList.clearjunk xs) t \<noteq> Some 0" and "t \<in> fst ` set (AList.clearjunk xs)"
        by (simp_all add: map_of_clearjunk dom_clearjunk)
      then obtain c where "(t, c) \<in> set (AList.clearjunk xs)" and "c \<noteq> 0"
        by (metis domD dom_map_of_conv_image_fst map_of_SomeD)
      hence "(t, c) \<in> {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}" by simp
      thus "t \<in> fst ` {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}" by force
    qed
  next
    show "?r \<subseteq> ?l"
    proof (rule, simp)
      fix t
      assume "t \<in> fst ` {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}"
      then obtain c where "(t, c) \<in> {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}" by fastforce
      hence 1: "(t, c) \<in> set (AList.clearjunk xs)" and "c \<noteq> 0" by simp_all
      from 1 have "map_of (AList.clearjunk xs) t = Some c" by simp
      hence "map_of xs t = Some c" by (simp only: map_of_clearjunk)
      with \<open>c \<noteq> 0\<close> have "map_of xs t \<noteq> Some 0" by simp
      moreover from 1 have "t \<in> fst ` set xs"
      proof -
        from 1 have "t \<in> fst ` set (AList.clearjunk xs)" by force
        thus ?thesis by (simp only: dom_clearjunk)
      qed
      ultimately show "map_of xs t \<noteq> Some 0 \<and> t \<in> fst ` set xs" ..
    qed
  qed
qed

lemma compute_card_keys [code]:
  "card_keys (Pm_fmap (fmap_of_list xs)) = length [x\<leftarrow>AList.clearjunk xs . snd x \<noteq> 0]"
proof -
  from distinct_keys_list have "card (set (keys_list xs)) = length (keys_list xs)"
    by (rule distinct_card)
  also have "... = length [x\<leftarrow>AList.clearjunk xs . snd x \<noteq> 0]" by (simp add: keys_list_def)
  finally show ?thesis by (simp only: card_keys_def o_def compute_keys_alt)
qed

lemma (in ordered_powerprod) compute_keys_to_list [code]:
  "keys_to_list (Pm_fmap (fmap_of_list xs)) = rev (ordered_powerprod_lin.sort (keys_list xs))"
  by (simp add: keys_to_list_def compute_keys_alt pps_to_list_def distinct_keys_list
        distinct_remdups_id ordered_powerprod_lin.sorted_list_of_set_sort_remdups)

lemma compute_list_to_poly [code]: "list_to_poly ts cs = MP (zip ts cs)"
  by (rule poly_mapping_eqI, simp add: lookup_list_to_poly PM_def list_to_fun_def
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
  "f4_drlex
    [
     (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], -2)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1::rat), (PP [(Z, 3)], 2)], ())
    ] () =
    [
     (MP [(PP [(X, 2), (Z, 2), (Y, 2)], 1), (PP [(Z, 2), (Y, 3)], 4)], ()),
     (MP [(PP [(X, 2), (Z, 4)], 1), (PP [(Y, 3), (Z, 2)], - 2)], ()),
     (MP [(PP [(Y, 2), (Z, 1)], 1), (PP [(Z, 3)], 2)], ()),
     (MP [(PP [(X, 2), (Z, 1), (Y, 4)], 1), (PP [(Z, 1), (Y, 5)], 4)], ())
    ]"
  by eval

lemma
  "f4_drlex
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

end (* theory *)