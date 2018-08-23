(* Author: Alexander Maletzky *)

section \<open>Sample Computations with Signature-Based Algorithms\<close>

theory Signature_Examples
  imports Signature_Based Polynomials.MPoly_Type_Class_OAlist Groebner_Bases.Code_Target_Rat Print
begin

subsection \<open>Benchmarks\<close>

(* TODO: Move to separate "Benchmarks" theory. *)

subsubsection \<open>Cyclic\<close>

definition cycl_pp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) pp"
  where "cycl_pp n d i = sparse\<^sub>0 (map (\<lambda>k. (modulo (k + i) n, 1)) [0..<d])"

definition cyclic :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::{zero,one,uminus}) list"
  where "cyclic to n =
            (let xs = [0..<n] in
              (map (\<lambda>d. distr\<^sub>0 to (map (\<lambda>i. (cycl_pp n d i, 1)) xs)) [1..<n]) @ [distr\<^sub>0 to [(cycl_pp n n 0, 1), (0, -1)]]
            )"

text \<open>@{term "cyclic n"} is a system of \<open>n\<close> polynomials in \<open>n\<close> indeterminates, with maximum degree \<open>n\<close>.\<close>

subsubsection \<open>Katsura\<close>

definition Katsura_poly :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 rat)"
  where "Katsura_poly to n i =
            change_ord to ((\<Sum>j=-(int n)..<(int n) + 1 - i. V\<^sub>0 (nat (abs j)) * V\<^sub>0 (nat (abs j + i))) - V\<^sub>0 i)"

definition Katsura :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 rat) list"
  where "Katsura to n =
          (let xs = [0..<n] in
            (distr\<^sub>0 to ((sparse\<^sub>0 [(0, 1)], 1) # (map (\<lambda>i. (sparse\<^sub>0 [(Suc i, 1)], 2)) xs) @ [(0, -1)])) # (map (Katsura_poly to n) xs)
          )"

text \<open>@{term "Katsura n"} is a system of \<open>n + 1\<close> polynomials in \<open>n + 1\<close> indeterminates, with maximum degree \<open>2\<close>.\<close>

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

(* TODO: Replace class "nat_pp_term" by this. *)
class nat_pp_term2 = nat_pp_term +
  assumes snd_rep_nat_term: "snd (rep_nat_term x) = 0"

instance pp :: (nat, nat) nat_pp_term2
  by (intro_classes, simp add: rep_nat_term_pp_def)

definition pot_comp' :: "'a::nat_pp_term2 nat_term_order \<Rightarrow> ('a \<times> nat) \<Rightarrow> ('a \<times> nat) \<Rightarrow> order"
  where "pot_comp' cmp = (\<lambda>x y. case comparator_of (snd x) (snd y) of Eq \<Rightarrow> nat_term_compare cmp (fst x) (fst y) | val \<Rightarrow> val)"

definition pot :: "'a::{comm_powerprod,nat_pp_term2,nat_pp_compare} nat_term_order \<Rightarrow> ('a \<times> nat) nat_term_order"
  where "pot cmp = Abs_nat_term_order (pot_comp' cmp)"

lemma nat_term_compare_pot: "nat_term_compare (pot cmp) = pot_comp' cmp"
  unfolding pot_def
proof (rule nat_term_compare_Abs_nat_term_order_id)
  show "comparator (pot_comp' cmp)" unfolding pot_comp'_def using comparator_of comparator_nat_term_compare
    by (rule comparator_lexicographic) (simp add: prod_eqI)
next
  have 1: "fst u = fst v" if "fst (rep_nat_term u) = fst (rep_nat_term v)" for u v :: "'a \<times> nat"
  proof (rule rep_nat_pp_inj)
    from that show "rep_nat_pp (fst u) = rep_nat_pp (fst v)" by (simp add: rep_nat_term_prod_def)
  qed
  have 2: "snd u = snd v" if "snd (rep_nat_term u) = snd (rep_nat_term v)" for u v :: "'a \<times> nat"
  proof (rule rep_inj)
    from that show "rep_nat (snd u) = rep_nat (snd v)" by (simp add: rep_nat_term_prod_def)
  qed
  show "nat_term_comp (pot_comp' cmp)"
  proof (rule nat_term_compI)
    fix u v :: "'a \<times> nat"
    assume "snd (rep_nat_term u) = snd (rep_nat_term v)"
    hence a: "snd u = snd v" by (rule 2)
    assume "fst (rep_nat_term u) = 0"
    hence "rep_nat_pp (fst u) = rep_nat_pp 0" by (simp add: rep_nat_term_prod_def zero_pp)
    hence "fst u = 0" by (rule rep_nat_pp_inj)
    note nat_term_comp_nat_term_compare
    moreover have "snd (rep_nat_term (fst u)) = snd (rep_nat_term (fst v))" by (simp only: snd_rep_nat_term)
    moreover have "fst (rep_nat_term (fst u)) = 0" by (simp add: \<open>fst u = 0\<close> rep_nat_term_zero)
    ultimately have "nat_term_compare cmp (fst u) (fst v) \<noteq> Gt" by (rule nat_term_compD1)
    thus "pot_comp' cmp u v \<noteq> Gt" using a by (simp add: pot_comp'_def)
  next
    fix u v :: "'a \<times> nat"
    assume "snd (rep_nat_term u) < snd (rep_nat_term v)"
    hence "rep_nat (snd u) < rep_nat (snd v)" by (simp add: rep_nat_term_prod_def)
    hence "snd u < snd v" by (simp only: ord_iff[symmetric])
    thus "pot_comp' cmp u v = Lt" by (simp add: pot_comp'_def comparator_of_def)
  next
    fix t u v :: "'a \<times> nat"
    have "nat_term_compare cmp (fst u) (fst v) = Lt \<Longrightarrow>
            nat_term_compare cmp (splus (fst t) (fst u)) (splus (fst t) (fst v)) = Lt"
      using nat_term_comp_nat_term_compare by (rule nat_term_compD3)
    moreover assume "pot_comp' cmp u v = Lt"
    ultimately show "pot_comp' cmp (splus t u) (splus t v) = Lt"
      by (simp add: pot_comp'_def splus_prod_def pprod.splus_def splus_pp_term split: order.splits)
  next
    fix u v a b :: "'a \<times> nat"
    assume "fst (rep_nat_term u) = fst (rep_nat_term a)" and "fst (rep_nat_term v) = fst (rep_nat_term b)"
      and "snd (rep_nat_term u) = snd (rep_nat_term v)" and "snd (rep_nat_term a) = snd (rep_nat_term b)"
    hence 3: "fst u = fst a" and 4: "fst v = fst b" and 5: "snd u = snd v" and 6: "snd a = snd b"
      by (auto dest!: 1 2)
    note comparator_nat_term_compare nat_term_comp_nat_term_compare
    moreover have "fst (rep_nat_term (fst u)) = fst (rep_nat_term (fst a))" by (simp only: 3)
    moreover have "fst (rep_nat_term (fst v)) = fst (rep_nat_term (fst b))" by (simp only: 4)
    moreover have "snd (rep_nat_term (fst u)) = snd (rep_nat_term (fst v))" by (simp only: snd_rep_nat_term)
    moreover have "snd (rep_nat_term (fst a)) = snd (rep_nat_term (fst b))" by (simp only: snd_rep_nat_term)
    ultimately have "nat_term_compare cmp (fst u) (fst v) = nat_term_compare cmp (fst a) (fst b)"
      by (rule nat_term_compD4')
    moreover assume "pot_comp' cmp a b = Lt"
    ultimately show "pot_comp' cmp u v = Lt"
      by (simp add: pot_comp'_def 5 6 split: order.splits)
  qed
qed

lemma le_of_nat_term_order_pot [code_unfold]:
  "le_of_nat_term_order (pot cmp_pp) = le_of_comp (pot_comp' cmp_pp)"
  by (intro ext, simp add: le_of_nat_term_order nat_term_compare_pot le_of_comp_def split: order.split)

lemma lt_of_nat_term_order_pot [code_unfold]:
  "lt_of_nat_term_order (pot cmp_pp) = lt_of_comp (pot_comp' cmp_pp)"
  by (intro ext, simp add: lt_of_nat_term_order nat_term_compare_pot lt_of_comp_def split: order.split)

locale qpm_nat_inf_term = gd_nat_term "\<lambda>x. x" "\<lambda>x. x" "pot cmp_pp"
  for cmp_pp::"'a::{nat_pp_term2,quasi_pm_powerprod,nat_pp_compare} nat_term_order"
begin

sublocale aux: qpm_inf_term "\<lambda>x. x" "\<lambda>x. x"
        "le_of_nat_term_order cmp_pp"
        "lt_of_nat_term_order cmp_pp"
        "le_of_nat_term_order (pot cmp_pp)"
        "lt_of_nat_term_order (pot cmp_pp)"
  apply intro_locales
  subgoal using linorder_le_of_nat_term_order[of cmp_pp] by (simp add: class.linorder_def class.order_def)
  subgoal using linorder_le_of_nat_term_order[of cmp_pp] by (simp add: class.linorder_def class.order_def)
  subgoal using linorder_le_of_nat_term_order[of cmp_pp] by (simp add: class.linorder_def class.order_def)
  subgoal by (unfold_locales, fact le_of_nat_term_order_zero_min, auto dest: le_of_nat_term_order_plus_monotone simp: ac_simps)
  subgoal apply unfold_locales
    subgoal by (simp add: le_of_nat_term_order nat_term_compare_splus splus_eq_splus)
    subgoal by (simp add: le_of_nat_term_order nat_term_compare_pot pot_comp'_def comparator_of_def split: order.split)
    done
  done

end

text \<open>We must define the following four constants outside the global interpretation, since otherwise
  their types are too general.\<close>

definition splus_pprod :: "('a::nat, 'b::nat) pp \<Rightarrow> _"
  where "splus_pprod = pprod.splus"

definition adds_term_pprod :: "(('a::nat, 'b::nat) pp \<times> _) \<Rightarrow> _"
  where "adds_term_pprod = pprod.adds_term"

global_interpretation pprod': qpm_nat_inf_term cmp_pp
  rewrites "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  and "pprod.splus = splus_pprod"
  and "pprod.adds_term = adds_term_pprod"
  and "punit.monom_mult = monom_mult_punit"
  and "pprod'.aux.punit.lt = lt_punit cmp_pp"
  and "pprod'.aux.punit.lc = lc_punit cmp_pp"
  and "pprod'.aux.punit.tail = tail_punit cmp_pp"
  for cmp_pp :: "('a::nat, 'b::nat) pp nat_term_order"
  defines max_pprod = pprod'.ord_term_lin.max
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
  and sig_gb_spp_body_pprod = pprod'.aux.sig_gb_spp_body
  and sig_gb_spp_aux_pprod = pprod'.aux.sig_gb_spp_aux
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

lemma compute_adds_term_pprod [code]:
  "adds_term_pprod u v = (snd u = snd v \<and> adds_pp_add_linorder (fst u) (fst v))"
  by (simp add: adds_term_pprod_def pprod.adds_term_def adds_pp_add_linorder_def)

lemma compute_splus_pprod [code]: "splus_pprod t (s, i) = (t + s, i)"
  by (simp add: splus_pprod_def pprod.splus_def)

lemma compute_sig_trd_spp_body_pprod [code]:
  "sig_trd_spp_body_pprod cmp_pp bs v (p, r) =
    (case find_sig_reducer_pprod cmp_pp bs v (lt_punit cmp_pp p) 0 of
        None   \<Rightarrow> (tail_punit cmp_pp p, plus_monomial_less r (lc_punit cmp_pp p) (lt_punit cmp_pp p))
      | Some i \<Rightarrow> let b = snd (bs ! i) in
          (tail_punit cmp_pp p - monom_mult_punit (lc_punit cmp_pp p / lc_punit cmp_pp b)
              (lt_punit cmp_pp p - lt_punit cmp_pp b) (tail_punit cmp_pp b), r))"
  by (simp add: plus_monomial_less_def split: option.split)

lemma compute_sig_trd_spp_pprod [code]:
  "sig_trd_spp_pprod cmp_pp bs (v, p) \<equiv> (v, sig_trd_spp_aux_pprod cmp_pp bs v (p, change_ord cmp_pp 0))"
  by (simp add: change_ord_def)

lemmas [code] = conversep_iff

definition "sig_gb_pprod cmp_pp rword_strict fs \<equiv> sig_gb_pprod' cmp_pp (rword_strict cmp_pp) (map (change_ord cmp_pp) fs)"

definition "zero_reds_pprod cmp_pp rword_strict fs0 =
              (let fs = remdups (filter (\<lambda>f. f \<noteq> 0) fs0); Ksyz = Koszul_syz_sigs_pprod cmp_pp fs 0 in
                  length (fst (snd (sig_gb_spp_aux_pprod cmp_pp fs (rword_strict cmp_pp) ([], Ksyz, map Inr [0..<length fs])))) - length Ksyz)"

lemma sig_gb_pprod'_eq_sig_gb_pprod:
  "sig_gb_pprod' cmp_pp (rword_strict cmp_pp) fs = sig_gb_pprod cmp_pp rword_strict fs"
  by (simp add: sig_gb_pprod_def change_ord_def)

thm pprod'.aux.sig_gb[OF pprod'.aux.rw_rat_strict_is_strict_rewrite_ord, simplified sig_gb_pprod'_eq_sig_gb_pprod]

experiment begin interpretation trivariate\<^sub>0_rat .

subsection \<open>Computations\<close>

abbreviation "poly1 \<equiv> change_ord DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y)"
abbreviation "poly2 \<equiv> change_ord DRLEX (X * Y * Z + 2 * Y\<^sup>2)"
abbreviation "poly3 \<equiv> change_ord DRLEX (X\<^sup>2 * Z ^ 3)"

value [code] "Koszul_syz_sigs_pprod DRLEX [poly1, poly2] 0"

value [code] "find_sig_reducer_pprod DRLEX [((0, 0), poly1), ((0, 0), poly2)] (0, 1) (sparse\<^sub>0 [(0, 2), (1, 1), (2, 3)]) 0"

value [code] "sig_trd_spp_body_pprod DRLEX [((0, 0), poly1), ((0, 0), poly2)] (0, 1) (poly3, 0)"

value [code] "sig_trd_spp_pprod DRLEX [((0, 0), poly1), ((0, 0), poly2)] ((0, 1), poly3)"

value [code] "rw_rat_strict_pprod DRLEX ((0, 0), poly1) ((0, 0), poly2)"

value [code] "rw_add_strict_pprod DRLEX ((0, 0), poly1) ((0, 0), poly2)"

value [code] "sig_gb_spp_body_pprod DRLEX ((cyclic DRLEX 2)::(_ \<Rightarrow>\<^sub>0 rat) list) (rw_rat_strict_pprod DRLEX) ([], [], [Inr 0, Inr 1])"

value [code] "sig_gb_pprod DRLEX rw_rat_strict_pprod [poly1, poly2]"

value [code] "timing (length (sig_gb_pprod DRLEX rw_rat_strict_pprod ((Katsura DRLEX 1)::(_ \<Rightarrow>\<^sub>0 rat) list)))"

value [code] "timing (zero_reds_pprod DRLEX rw_rat_strict_pprod ((Katsura DRLEX 1)::(_ \<Rightarrow>\<^sub>0 rat) list))"

(* Timings on benchmark problems (on qftquad2)

Problem       Time (s)      #Basis      #0-Reductions
-----------------------------------------------------
Cyclic-4        0.0            7           3
Cyclic-5        0.1           39          14
Cyclic-6        2.5          155          47
Katsura-4       0.0           16          11
Katsura-5       1.0           32          26
Katsura-6      28.1           64          57

*)

end (* theory *)
