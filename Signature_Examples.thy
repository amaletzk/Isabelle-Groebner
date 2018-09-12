(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Signature-Based Algorithms\<close>

theory Signature_Examples
  imports Signature_Based Benchmarks Polynomials.MPoly_Type_Class_OAlist Groebner_Bases.Code_Target_Rat Print
begin

subsection \<open>Setup\<close>

lift_definition truncate_pp :: "'a set \<Rightarrow> ('a, 'b) pp \<Rightarrow> ('a, 'b::zero) pp" is truncate_poly_mapping .

lemma hom_grading_varnum_pp: "hom_grading (varnum_pp::('a::countable, 'b::add_wellorder) pp \<Rightarrow> nat)"
proof -
  define f where "f = (\<lambda>n. (truncate_pp {x. elem_index x < n})::_ \<Rightarrow> ('a, 'b) pp)"
  show ?thesis unfolding hom_grading_def hom_grading_fun_def
  proof (intro exI allI conjI impI)
    fix n s t
    show "f n (s + t) = f n s + f n t" unfolding f_def by (transfer, rule truncate_poly_mapping_plus)
  next
    fix n t
    show "varnum_pp (f n t) \<le> n" unfolding f_def
      by (transfer, simp add: varnum_le_iff sub_keys_def[symmetric] sub_keys_truncate)
  next
    fix n t
    show "varnum_pp t \<le> n \<Longrightarrow> f n t = t" unfolding f_def
      by (transfer, simp add: truncate_poly_mapping_id_iff varnum_le_iff)
  qed
qed

instance pp :: (countable, add_wellorder) quasi_pm_powerprod
  by (standard, intro exI conjI, fact dickson_grading_varnum_pp, fact hom_grading_varnum_pp)

subsubsection \<open>Projections of Term Orders to Orders on Power-Products\<close>

definition proj_comp :: "(('a::nat, 'b::nat) pp \<times> nat) nat_term_order \<Rightarrow> ('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> order"
  where "proj_comp cmp = (\<lambda>x y. nat_term_compare cmp (x, 0) (y, 0))"

definition proj_ord :: "(('a::nat, 'b::nat) pp \<times> nat) nat_term_order \<Rightarrow> ('a, 'b) pp nat_term_order"
  where "proj_ord cmp = Abs_nat_term_order (proj_comp cmp)"

text \<open>In principle, @{const proj_comp} and @{const proj_ord} could be defined more generally on type
  @{typ "'a \<times> nat"}, but then @{typ 'a} would have to belong to some new type-class which is the
  intersection of @{class nat_pp_term} and @{class nat_pp_compare} and additionally requires
  @{prop "rep_nat_term x = (rep_nat_pp x, 0)"}.\<close>

lemma comparator_proj_comp: "comparator (proj_comp cmp)"
proof -
  interpret cmp: comparator "nat_term_compare cmp" by (rule comparator_nat_term_compare)
  show ?thesis unfolding proj_comp_def
  proof
    fix x y :: "('a, 'b) pp"
    show "invert_order (nat_term_compare cmp (x, 0) (y, 0)) = nat_term_compare cmp (y, 0) (x, 0)"
      by (simp only: cmp.sym)
  next
    fix x y :: "('a, 'b) pp"
    assume "nat_term_compare cmp (x, 0) (y, 0) = Eq"
    hence "(x, 0) = (y, 0::nat)" by (rule cmp.weak_eq)
    thus "x = y" by simp
  next
    fix x y z :: "('a, 'b) pp"
    assume "nat_term_compare cmp (x, 0) (y, 0) = Lt" and "nat_term_compare cmp (y, 0) (z, 0) = Lt"
    thus "nat_term_compare cmp (x, 0) (z, 0) = Lt" by (rule cmp.trans)
  qed
qed

lemma nat_term_comp_proj_comp: "nat_term_comp (proj_comp cmp)"
proof -
  have 1: "fst (rep_nat_term (u, i)) = rep_nat_pp u" for u::"('a, 'b) pp" and i::nat
    by (simp add: rep_nat_term_prod_def)
  have 2: "snd (rep_nat_term (u, i)) = i" for u::"('a, 'b) pp" and i::nat
    by (simp add: rep_nat_term_prod_def rep_nat_nat_def)
  show ?thesis
  proof (rule nat_term_compI)
    fix u v :: "('a, 'b) pp"
    assume a: "fst (rep_nat_term u) = 0"
    note nat_term_comp_nat_term_compare
    moreover have "snd (rep_nat_term (u, 0::nat)) = snd (rep_nat_term (v, 0::nat))" by (simp only: 2)
    moreover from a have "fst (rep_nat_term (u, 0::nat)) = 0" by (simp add: 1 rep_nat_term_pp_def)
    ultimately have "nat_term_compare cmp (u, 0) (v, 0) \<noteq> Gt" by (rule nat_term_compD1)
    thus "proj_comp cmp u v \<noteq> Gt" by (simp add: proj_comp_def)
  next
    fix u v :: "('a, 'b) pp"
    assume "snd (rep_nat_term u) < snd (rep_nat_term v)"
    thus "proj_comp cmp u v = Lt" by (simp add: rep_nat_term_pp_def)
  next
    fix t u v :: "('a, 'b) pp"
    assume "proj_comp cmp u v = Lt"
    hence "nat_term_compare cmp (u, 0) (v, 0) = Lt" by (simp add: proj_comp_def)
    with nat_term_comp_nat_term_compare have "nat_term_compare cmp (splus (t, 0) (u, 0)) (splus (t, 0) (v, 0)) = Lt"
      by (rule nat_term_compD3)
    thus "proj_comp cmp (splus t u) (splus t v) = Lt"
      by (simp add: proj_comp_def splus_prod_def pprod.splus_def splus_pp_term)
  next
    fix u v a b :: "('a, 'b) pp"
    assume u: "fst (rep_nat_term u) = fst (rep_nat_term a)" and v: "fst (rep_nat_term v) = fst (rep_nat_term b)"
      and a: "proj_comp cmp a b = Lt"
    note nat_term_comp_nat_term_compare
    moreover from u have "fst (rep_nat_term (u, 0::nat)) = fst (rep_nat_term (a, 0::nat))"
      by (simp add: 1 rep_nat_term_pp_def)
    moreover from v have "fst (rep_nat_term (v, 0::nat)) = fst (rep_nat_term (b, 0::nat))"
      by (simp add: 1 rep_nat_term_pp_def)
    moreover have "snd (rep_nat_term (u, 0::nat)) = snd (rep_nat_term (v, 0::nat))"
      and "snd (rep_nat_term (a, 0::nat)) = snd (rep_nat_term (b, 0::nat))" by (simp_all only: 2)
    moreover from a have "nat_term_compare cmp (a, 0) (b, 0) = Lt" by (simp add: proj_comp_def)
    ultimately have "nat_term_compare cmp (u, 0) (v, 0) = Lt" by (rule nat_term_compD4)
    thus "proj_comp cmp u v = Lt" by (simp add: proj_comp_def)
  qed
qed

corollary nat_term_compare_proj_ord: "nat_term_compare (proj_ord cmp) = proj_comp cmp"
  unfolding proj_ord_def using comparator_proj_comp nat_term_comp_proj_comp
  by (rule nat_term_compare_Abs_nat_term_order_id)

lemma proj_ord_LEX [code]: "proj_ord LEX = LEX"
proof -
  have "nat_term_compare (proj_ord LEX) = nat_term_compare LEX"
    by (auto simp: nat_term_compare_proj_ord nat_term_compare_LEX proj_comp_def lex_comp
        lex_comp_aux_def rep_nat_term_prod_def rep_nat_term_pp_def intro!: ext split: order.split)
  thus ?thesis by (simp only: nat_term_compare_inject)
qed

lemma proj_ord_DRLEX [code]: "proj_ord DRLEX = DRLEX"
proof -
  have "nat_term_compare (proj_ord DRLEX) = nat_term_compare DRLEX"
    by (auto simp: nat_term_compare_proj_ord nat_term_compare_DRLEX proj_comp_def deg_comp pot_comp
        lex_comp lex_comp_aux_def rep_nat_term_prod_def rep_nat_term_pp_def intro!: ext split: order.split)
  thus ?thesis by (simp only: nat_term_compare_inject)
qed

lemma proj_ord_DEG [code]: "proj_ord (DEG to) = DEG (proj_ord to)"
proof -
  have "nat_term_compare (proj_ord (DEG to)) = nat_term_compare (DEG (proj_ord to))"
    by (simp add: nat_term_compare_proj_ord nat_term_compare_DEG proj_comp_def deg_comp
        rep_nat_term_prod_def rep_nat_term_pp_def)
  thus ?thesis by (simp only: nat_term_compare_inject)
qed

lemma proj_ord_POT [code]: "proj_ord (POT to) = proj_ord to"
proof -
  have "nat_term_compare (proj_ord (POT to)) = nat_term_compare (proj_ord to)"
    by (simp add: nat_term_compare_proj_ord nat_term_compare_POT proj_comp_def pot_comp
        rep_nat_term_prod_def rep_nat_term_pp_def)
  thus ?thesis by (simp only: nat_term_compare_inject)
qed

subsubsection \<open>Locale Interpretation\<close>

locale qpm_nat_inf_term = gd_nat_term "\<lambda>x. x" "\<lambda>x. x" to
  for to::"(('a::nat, 'b::nat) pp \<times> nat) nat_term_order"
begin

sublocale aux: qpm_inf_term "\<lambda>x. x" "\<lambda>x. x"
        "le_of_nat_term_order (proj_ord to)"
        "lt_of_nat_term_order (proj_ord to)"
        "le_of_nat_term_order to"
        "lt_of_nat_term_order to"
proof intro_locales
(*
  show "class.preorder (le_of_nat_term_order (proj_ord to)) (lt_of_nat_term_order (proj_ord to))"
    and "class.order_axioms (le_of_nat_term_order (proj_ord to))"
    and "class.linorder_axioms (le_of_nat_term_order (proj_ord to))"
    using linorder_le_of_nat_term_order[of "proj_ord to"] by (simp_all add: class.linorder_def class.order_def)
next*)
  show "ordered_powerprod_axioms (le_of_nat_term_order (proj_ord to))"
    by (unfold_locales, fact le_of_nat_term_order_zero_min, auto dest: le_of_nat_term_order_plus_monotone simp: ac_simps)
next
  show "ordered_term_axioms (\<lambda>x. x) (\<lambda>x. x) (le_of_nat_term_order (proj_ord to)) (le_of_nat_term_order to)"
  proof
    fix v w t
    assume "le_of_nat_term_order to v w"
    thus "le_of_nat_term_order to (local.splus t v) (local.splus t w)"
      by (simp add: le_of_nat_term_order nat_term_compare_splus splus_eq_splus)
  next
    fix v w
    assume "le_of_nat_term_order (proj_ord to) (pp_of_term v) (pp_of_term w)"
      and "component_of_term v \<le> component_of_term w"
    hence "nat_term_compare to (fst v, 0) (fst w, 0) \<noteq> Gt" and "snd v \<le> snd w"
      by (simp_all add: le_of_nat_term_order nat_term_compare_proj_ord proj_comp_def)
    from comparator_nat_term_compare nat_term_comp_nat_term_compare _ _ _ _ this(1)
    have "nat_term_compare to v w \<noteq> Gt"
      by (rule nat_term_compD4'') (simp_all add: rep_nat_term_prod_def ord_iff[symmetric] \<open>snd v \<le> snd w\<close>)
    thus "le_of_nat_term_order to v w" by (simp add: le_of_nat_term_order)
  qed
qed

end

text \<open>We must define the following two constants outside the global interpretation, since otherwise
  their types are too general.\<close>

definition splus_pprod :: "('a::nat, 'b::nat) pp \<Rightarrow> _"
  where "splus_pprod = pprod.splus"

definition adds_term_pprod :: "(('a::nat, 'b::nat) pp \<times> _) \<Rightarrow> _"
  where "adds_term_pprod = pprod.adds_term"

global_interpretation pprod': qpm_nat_inf_term to
  rewrites "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  and "pprod.splus = splus_pprod"
  and "pprod.adds_term = adds_term_pprod"
  and "punit.monom_mult = monom_mult_punit"
  and "pprod'.aux.punit.lt = lt_punit (proj_ord to)"
  and "pprod'.aux.punit.lc = lc_punit (proj_ord to)"
  and "pprod'.aux.punit.tail = tail_punit (proj_ord to)"
  for to :: "(('a::nat, 'b::nat) pp \<times> nat) nat_term_order"
  defines max_pprod = pprod'.ord_term_lin.max
  and Koszul_syz_sigs_aux_pprod = pprod'.aux.Koszul_syz_sigs_aux
  and Koszul_syz_sigs_pprod = pprod'.aux.Koszul_syz_sigs
  and find_sig_reducer_pprod = pprod'.aux.find_sig_reducer
  and sig_trd_spp_body_pprod = pprod'.aux.sig_trd_spp_body
  and sig_trd_spp_aux_pprod = pprod'.aux.sig_trd_spp_aux
  and sig_trd_spp_pprod = pprod'.aux.sig_trd_spp
  and spair_sigs_spp_pprod = pprod'.aux.spair_sigs_spp
  and is_pred_syz_pprod = pprod'.aux.is_pred_syz
  and is_rewritable_spp_pprod = pprod'.aux.is_rewritable_spp
  and sig_crit_spp_pprod = pprod'.aux.sig_crit_spp
  and spair_spp_pprod = pprod'.aux.spair_spp
  and spp_of_pair_pprod = pprod'.aux.spp_of_pair
  and pair_ord_spp_pprod = pprod'.aux.pair_ord_spp
  and sig_of_pair_spp_pprod = pprod'.aux.sig_of_pair_spp
  and new_spairs_spp_pprod = pprod'.aux.new_spairs_spp
  and is_regular_spair_spp_pprod = pprod'.aux.is_regular_spair_spp
  and add_spairs_spp_pprod = pprod'.aux.add_spairs_spp
  and is_pot_ord_pprod = pprod'.is_pot_ord
  and new_syz_sigs_spp_pprod = pprod'.aux.new_syz_sigs_spp
  and rb_spp_body_pprod = pprod'.aux.rb_spp_body
  and rb_spp_aux_pprod = pprod'.aux.rb_spp_aux
  and sig_gb_z_pprod' = pprod'.aux.sig_gb_z
  and sig_gb_pprod' = pprod'.aux.sig_gb
  and rw_rat_strict_pprod = pprod'.aux.rw_rat_strict
  and rw_add_strict_pprod = pprod'.aux.rw_add_strict
  subgoal by (rule qpm_nat_inf_term.intro, fact gd_nat_term_id)
  subgoal by (fact pprod_pp_of_term)
  subgoal by (fact pprod_component_of_term)
  subgoal by (simp only: splus_pprod_def)
  subgoal by (simp only: adds_term_pprod_def)
  subgoal by (simp only: monom_mult_punit_def)
  subgoal by (simp only: lt_punit_def)
  subgoal by (simp only: lc_punit_def)
  subgoal by (simp only: tail_punit_def)
  done

subsubsection \<open>More Lemmas and Definitions\<close>

lemma compute_adds_term_pprod [code]:
  "adds_term_pprod u v = (snd u = snd v \<and> adds_pp_add_linorder (fst u) (fst v))"
  by (simp add: adds_term_pprod_def pprod.adds_term_def adds_pp_add_linorder_def)

lemma compute_splus_pprod [code]: "splus_pprod t (s, i) = (t + s, i)"
  by (simp add: splus_pprod_def pprod.splus_def)

lemma compute_sig_trd_spp_body_pprod [code]:
  "sig_trd_spp_body_pprod to bs v (p, r) =
    (case find_sig_reducer_pprod to bs v (lt_punit (proj_ord to) p) 0 of
        None   \<Rightarrow> (tail_punit (proj_ord to) p, plus_monomial_less r (lc_punit (proj_ord to) p) (lt_punit (proj_ord to) p))
      | Some i \<Rightarrow> let b = snd (bs ! i) in
          (tail_punit (proj_ord to) p - monom_mult_punit (lc_punit (proj_ord to) p / lc_punit (proj_ord to) b)
              (lt_punit (proj_ord to) p - lt_punit (proj_ord to) b) (tail_punit (proj_ord to) b), r))"
  by (simp add: plus_monomial_less_def split: option.split)

lemma compute_sig_trd_spp_pprod [code]:
  "sig_trd_spp_pprod to bs (v, p) \<equiv> (v, sig_trd_spp_aux_pprod to bs v (p, change_ord (proj_ord to) 0))"
  by (simp add: change_ord_def)

lemmas [code] = conversep_iff

lemma compute_is_pot_ord [code]:
  "is_pot_ord_pprod (LEX::(('a::nat, 'b::nat) pp \<times> nat) nat_term_order) = False"
    (is "is_pot_ord_pprod ?lex = _")
  "is_pot_ord_pprod (DRLEX::(('a::nat, 'b::nat) pp \<times> nat) nat_term_order) = False"
    (is "is_pot_ord_pprod ?drlex = _")
  "is_pot_ord_pprod (DEG (to::(('a::nat, 'b::nat) pp \<times> nat) nat_term_order)) = False"
  "is_pot_ord_pprod (POT (to::(('a::nat, 'b::nat) pp \<times> nat) nat_term_order)) = True"
proof -
  have eq1: "snd ((Term_Order.of_exps a b i)::('a, 'b) pp \<times> nat) = i" for a b and i::nat
  proof -
    have "snd ((Term_Order.of_exps a b i)::('a, 'b) pp \<times> nat) =
          snd (rep_nat_term ((Term_Order.of_exps a b i)::('a, 'b) pp \<times> nat))"
      by (simp add: rep_nat_term_prod_def rep_nat_nat_def)
    also have "... = i"
    proof (rule snd_of_exps)
      show "snd (rep_nat_term (undefined, i)) = i" by (simp add: rep_nat_term_prod_def rep_nat_nat_def)
    qed
    finally show ?thesis .
  qed

  let ?u = "(Term_Order.of_exps 1 0 0)::('a, 'b) pp \<times> nat"
  let ?v = "(Term_Order.of_exps 0 0 1)::('a, 'b) pp \<times> nat"
  have "\<not> is_pot_ord_pprod ?lex"
  proof
    assume "is_pot_ord_pprod ?lex"
    moreover have "le_of_nat_term_order ?lex ?v ?u"
      by (simp add: le_of_nat_term_order nat_term_compare_LEX lex_comp lex_comp_aux_def
            comp_of_ord_def lex_pp_of_exps eq_of_exps)
    ultimately have "snd ?v \<le> snd ?u" by (rule pprod'.is_pot_ordD2)
    thus False by (simp add: eq1)
  qed
  thus "is_pot_ord_pprod ?lex = False" by simp

  have "\<not> is_pot_ord_pprod ?drlex"
  proof
    assume "is_pot_ord_pprod ?drlex"
    moreover have "le_of_nat_term_order ?drlex ?v ?u"
      by (simp add: le_of_nat_term_order nat_term_compare_DRLEX deg_comp comparator_of_def)
    ultimately have "snd ?v \<le> snd ?u" by (rule pprod'.is_pot_ordD2)
    thus False by (simp add: eq1)
  qed
  thus "is_pot_ord_pprod ?drlex = False" by simp

  have "\<not> is_pot_ord_pprod (DEG to)"
  proof
    assume "is_pot_ord_pprod (DEG to)"
    moreover have "le_of_nat_term_order (DEG to) ?v ?u"
      by (simp add: le_of_nat_term_order nat_term_compare_DEG deg_comp comparator_of_def)
    ultimately have "snd ?v \<le> snd ?u" by (rule pprod'.is_pot_ordD2)
    thus False by (simp add: eq1)
  qed
  thus "is_pot_ord_pprod (DEG to) = False" by simp

  have "is_pot_ord_pprod (POT to)"
    by (rule pprod'.is_pot_ordI, simp add: lt_of_nat_term_order nat_term_compare_POT pot_comp rep_nat_term_prod_def,
        simp add: comparator_of_def)
  thus "is_pot_ord_pprod (POT to) = True" by simp
qed

corollary is_pot_ord_POT: "is_pot_ord_pprod (POT to)"
  by (simp only: compute_is_pot_ord)

definition "sig_gb_z_pprod to rword_strict fs \<equiv>
                  (let res = sig_gb_z_pprod' to (rword_strict to) (map (change_ord (proj_ord to)) fs) in
                    (length (fst res), snd res))"

definition "sig_gb_pprod to rword_strict fs \<equiv> sig_gb_pprod' to (rword_strict to) (map (change_ord (proj_ord to)) fs)"

lemma snd_sig_gb_z_pprod'_eq_sig_gb_z_pprod:
  "snd (sig_gb_z_pprod' to (rword_strict to) fs) = snd (sig_gb_z_pprod to rword_strict fs)"
  by (simp add: sig_gb_z_pprod_def change_ord_def Let_def)

lemma sig_gb_pprod'_eq_sig_gb_pprod:
  "sig_gb_pprod' to (rword_strict to) fs = sig_gb_pprod to rword_strict fs"
  by (simp add: sig_gb_pprod_def change_ord_def)

thm pprod'.aux.sig_gb_isGB[OF pprod'.aux.rw_rat_strict_is_strict_rewrite_ord, simplified sig_gb_pprod'_eq_sig_gb_pprod]
thm pprod'.aux.sig_gb_no_zero_red[OF pprod'.aux.rw_rat_strict_is_strict_rewrite_ord is_pot_ord_POT, simplified snd_sig_gb_z_pprod'_eq_sig_gb_z_pprod]

(*
lemma sig_gb_spp_body_pprod_code_print [code]:
  "sig_gb_spp_body_pprod to fs rword_strict ((bs, ss, p # ps), z) =
  (let ss' = new_syz_sigs_spp_pprod to fs ss bs p
  in if sig_crit_spp_pprod to rword_strict bs ss' p then ((bs, ss', ps), z)
     else let p' = sig_trd_spp_pprod to bs (spp_of_pair_pprod to fs p)
          in if snd p' = 0 then print ''0'' ((bs, fst p' # ss', ps), Suc z)
              else ((p' # bs, ss', add_spairs_spp_pprod to ps bs p'), z))"
  "sig_gb_spp_body_pprod to fs rword_strict ((bs, ss, []), z) = ((bs, ss, []), z)"
  by (simp_all add: Let_def)
*)

subsection \<open>Computations\<close>

experiment begin interpretation trivariate\<^sub>0_rat .

abbreviation "poly1 \<equiv> change_ord DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y)"
abbreviation "poly2 \<equiv> change_ord DRLEX (X * Y * Z + 2 * Y\<^sup>2)"
abbreviation "poly3 \<equiv> change_ord DRLEX (X\<^sup>2 * Z ^ 3)"

value [code] "is_pot_ord_pprod (POT (DRLEX::((nat, nat) pp \<times> nat) nat_term_order))"

value [code] "Koszul_syz_sigs_pprod DRLEX [poly1, poly2]"

value [code] "find_sig_reducer_pprod DRLEX [((0, 0), poly1), ((0, 0), poly2)] (0, 1) (sparse\<^sub>0 [(0, 2), (1, 1), (2, 3)]) 0"

value [code] "sig_trd_spp_body_pprod DRLEX [((0, 0), poly1), ((0, 0), poly2)] (0, 1) (poly3, 0)"

value [code] "sig_trd_spp_pprod DRLEX [((0, 0), poly1), ((0, 0), poly2)] ((0, 1), poly3)"

value [code] "rw_rat_strict_pprod DRLEX ((0, 0), poly1) ((0, 0), poly2)"

value [code] "rw_add_strict_pprod DRLEX ((0, 0), poly1) ((0, 0), poly2)"

value [code] "sig_gb_spp_body_pprod DRLEX ((cyclic DRLEX 2)::(_ \<Rightarrow>\<^sub>0 rat) list) (rw_rat_strict_pprod DRLEX) (([], [], [Inr 0, Inr 1]), 0)"

text \<open>We restrict computations of (signature) Gr\"obner bases to @{const rw_rat_strict_pprod}, because
  according to @{thm pprod'.aux.sig_gb_aux_is_min_sig_GB} this rewrite-order is optimal.\<close>

value [code] "sig_gb_pprod DRLEX rw_rat_strict_pprod [poly1, poly2]"

value [code] "timing ((sig_gb_z_pprod (POT DRLEX) rw_rat_strict_pprod ((cyclic DRLEX 1)::(_ \<Rightarrow>\<^sub>0 rat) list)))"

(*
Timings on benchmark problems
=============================
ATTENTION! The "katsura n" here corresponds to "Katsura (n-1)" in "Buchberger_Examples" etc.!

All tests have been performed with "POT DRLEX" and "rw_rat_strict_pprod".

New implementation, rational coefficients, on qftquad4:

Problem       Time (s)      #Basis      #0-Reductions
-----------------------------------------------------
Cyclic-4          0.0           7           1
Cyclic-5          0.1          39           0
Cyclic-6          2.0         155           8
Cyclic-7        500.0         749          36
Katsura-5         0.0          16           0
Katsura-6         0.5          32           0
Katsura-7        10.0          64           0
Eco-8             0.5          76           0
Eco-9             3.0         143           0
Eco-10           32.0         282           0
Eco-11          297.2         559           0
Noon-5            0.9          83           0
Noon-6            8.8         206           0
Noon-7          213.5         524           0


Old implementation (initial Koszul syzygies only), rational coefficients, on qftquad2:

Problem       Time (s)      #Basis      #0-Reductions
-----------------------------------------------------
Cyclic-4        0.0            7           3
Cyclic-5        0.1           39          14
Cyclic-6        2.5          155          47
Cyclic-7      996.6            ?         177            (on qftquad4)
Katsura-4       0.0           16          11
Katsura-5       1.0           32          26
Katsura-6      28.1           64          57
*)

end (* theory *)
