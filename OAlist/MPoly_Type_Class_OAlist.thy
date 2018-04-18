(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Executable Representation of Polynomial Mappings as Association Lists\<close>

theory MPoly_Type_Class_OAlist
  imports
    "../Polynomials/MPoly_Type_Class_Ordered"
    OAlist
begin

instantiation poly_mapping :: (type, "{equal, zero}") equal
begin
definition equal_poly_mapping::"('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool" where
  "equal_poly_mapping p q \<equiv> (\<forall>t. lookup p t = lookup q t)"

instance by standard (auto simp: equal_poly_mapping_def poly_mapping_eq_iff)

end

lift_definition Pm_oalist :: "('a::compare, 'b::zero) oalist \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  is OAlist.lookup
  sorry

lemmas [simp, code] = Pm_oalist.rep_eq

code_datatype Pm_oalist

lemma compute_keys_pm [code]: "keys (Pm_oalist xs) = set (map fst (list_of_oalist xs))"
  sorry

lemma compute_zero_pm [code]: "0 = Pm_oalist OAlist.empty"
  sorry

definition is_zero :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where [code_abbrev]: "is_zero p \<longleftrightarrow> (p = 0)"

lemma compute_is_zero_pm [code]:
  "is_zero (Pm_oalist xs) = List.null (list_of_oalist xs)"
  sorry

lemma compute_plus_pm [code]:
  "Pm_oalist xs + Pm_oalist ys = Pm_oalist (OAlist.map2_val (\<lambda>_. (+)) xs ys)"
  sorry

lemma compute_minus_pm [code]:
  "Pm_oalist xs - Pm_oalist ys = Pm_oalist (OAlist.map2_val (\<lambda>_. (-)) xs ys)"
  sorry

lemma compute_uminus_pm [code]:
  "- Pm_oalist xs = Pm_oalist (OAlist.map_val (\<lambda>_. uminus) xs)"
  sorry

lemma compute_equal_pm [code]:
  "equal_class.equal (Pm_oalist xs) (Pm_oalist ys) = (equal_class.equal xs ys)"
  sorry

lemma compute_map_pm [code]:
  "Poly_Mapping.map f (Pm_oalist xs) = Pm_oalist (OAlist.map_val (\<lambda>_. f) xs)"
  sorry

lemma compute_range_pm [code]:
  "Poly_Mapping.range (Pm_oalist xs) = set (map snd (list_of_oalist xs))"
  sorry

subsubsection \<open>Constructors\<close>

definition "sparse\<^sub>0 xs = Pm_oalist (oalist_of_list xs)" \<comment>\<open>sparse representation\<close>

lemma compute_single [code]: "Poly_Mapping.single k v = sparse\<^sub>0 [(k, v)]"
  sorry

subsection \<open>Power Products\<close>

lemma compute_lcs_pm [code]:
  "lcs (Pm_oalist xs) (Pm_oalist ys) = Pm_oalist (OAlist.map2_val (\<lambda>_. max) xs ys)"
  sorry

lemma compute_deg_pm [code]: "deg_pm (Pm_oalist xs) = sum_list (map snd (list_of_oalist xs))"
  sorry

definition adds_pm_add_linorder :: "('b \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow> _ \<Rightarrow> bool"
  where [code_abbrev]: "adds_pm_add_linorder = (adds)"

lemma compute_adds_pm [code]:
  "adds_pm_add_linorder (Pm_oalist xs) (Pm_oalist ys) = OAlist.prod_ord (\<lambda>_. less_eq) xs ys"
  for xs ys::"('a::compare, 'b::add_linorder_min) oalist"
  sorry

lemma compute_lex_pm [code]:
  "(lex_pm (Pm_oalist xs) (Pm_oalist (ys))) =
    (OAlist.lex_ord (\<lambda>_ x y. Some (compare x y)) xs ys \<noteq> Some GREATER)"
  for xs ys::"('a::{wellorder,compare}, 'b::{compare,ordered_comm_monoid_add}) oalist"
  sorry

lemma compute_dord_pm [code]:
  "dord_pm ord p q =
    (let dx = deg_pm p in let dy = deg_pm q in
      dx < dy \<or> (dx = dy \<and> ord p q)
    )"
  by (simp add: Let_def deg_pm.rep_eq dord_fun_def dord_pm.rep_eq lookup_inverse)

subsubsection \<open>Computations\<close>

experiment begin

abbreviation "X \<equiv> 0::nat"
abbreviation "Y \<equiv> 1::nat"
abbreviation "Z \<equiv> 2::nat"

lemma
  "sparse\<^sub>0 [(X, 2::nat), (Z, 7)] - sparse\<^sub>0 [(X, 2), (Z, 2)] = sparse\<^sub>0 [(Z, 5)]"
  by eval

lemma
  "lcs (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 7)]) (sparse\<^sub>0 [(Y, 3), (Z, 2)]) = sparse\<^sub>0 [(X, 2), (Y, 3), (Z, 7)]"
  by eval

lemma
  "(sparse\<^sub>0 [(X, 2::nat), (Z, 1)]) adds (sparse\<^sub>0 [(X, 3), (Y, 2), (Z, 1)])"
  by eval

lemma
  "lookup (sparse\<^sub>0 [(X, 2::nat), (Z, 3)]) X = 2"
  by eval

lemma
  "deg_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3), (X, 1)]) = 6"
  by eval

lemma
  "lex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)])"
  by eval

lemma
  "lex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)])"
  by eval

lemma
  "\<not> (dlex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)]))"
  by eval

lemma
  "dlex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 2)]) (sparse\<^sub>0 [(X, 5)])"
  by eval

lemma
  "\<not> (drlex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 2)]) (sparse\<^sub>0 [(X, 5)]))"
  by eval

end


subsection \<open>Implementation of Multivariate Polynomials as Association Lists\<close>

subsubsection \<open>Unordered Power-Products\<close>

lemma compute_one_poly_mapping [code]: "1 = sparse\<^sub>0 [(0, 1)]"
  by (metis compute_single single_one)

lemma compute_except_poly_mapping [code]:
  "except (Pm_oalist xs) S = Pm_oalist (OAlist.filter (\<lambda>kv. fst kv \<notin> S) xs)"
  sorry

lemma if_poly_mapping_eq_iff:
  "(if x = y then a else b) =
    (if (\<forall>i\<in>keys x \<union> keys y. lookup x i = lookup y i) then a else b)"
  by (auto simp: poly_mapping_eq_iff intro!: ext)

lemma keys_add_eq: "keys (a + b) = keys a \<union> keys b - {x \<in> keys a \<inter> keys b. lookup a x + lookup b x = 0}"
  by (auto simp: in_keys_iff lookup_add add_eq_0_iff
      simp del: lookup_not_eq_zero_eq_in_keys)

locale gd_term_compare =
    gd_term pair_of_term term_of_pair "greater_eq_of_comp" "greater_of_comp" "greater_eq_of_comp" "greater_of_comp"
      for pair_of_term::"'t::compare \<Rightarrow> ('a::{compare,graded_dickson_powerprod} \<times> 'k::{the_min,wellorder})"
      and term_of_pair::"('a \<times> 'k) \<Rightarrow> 't"
begin

context includes oalist.lifting begin

definition shift_keys :: "'a \<Rightarrow> ('t, 'b) oalist \<Rightarrow> ('t, 'b::zero) oalist"
  where "shift_keys t xs = OAlist.map (\<lambda>kv. (t \<oplus> fst kv, snd kv)) xs"

definition "shift_map_keys t f m = OAlist.map_val (\<lambda>_. f) (shift_keys t m)"

lemma list_of_oalist_shift_keys [code abstract]:
  "list_of_oalist (shift_map_keys t f xs) = (List.map (\<lambda>kv. (t \<oplus> fst kv, f (snd kv))) (list_of_oalist xs))"
  sorry

end

lemmas [simp] = compute_zero_pm [symmetric]

lemma compute_monom_mult_poly_mapping [code]:
  "monom_mult c t (Pm_oalist xs) = Pm_oalist (if c = 0 then OAlist.empty else shift_map_keys t (( * ) c) xs)"
proof (cases "c = 0")
  case True
  hence "monom_mult c t (Pm_oalist xs) = 0" using monom_mult_zero_left by simp
  thus ?thesis using True
    by simp
next
  case False
  thus ?thesis sorry
qed

lemma compute_mult_scalar_poly_mapping [code]:
  "(Pm_oalist xs) \<odot> q = (case (list_of_oalist xs) of ((t, c) # ys) \<Rightarrow>
    (monom_mult c t q + (Pm_oalist (oalist_of_list ys)) \<odot> q) | _ \<Rightarrow>
    Pm_oalist OAlist.empty)"
  sorry

end (* term_powerprod *)

subsubsection \<open>restore constructor view\<close>

named_theorems mpoly_simps

definition "monomial1 pp = monomial 1 pp"

lemma monomial1_Nil[mpoly_simps]: "monomial1 0 = 1"
  by (simp add: monomial1_def)

lemma monomial_mp: "monomial c (pp::'a \<Rightarrow>\<^sub>0 nat) = Const\<^sub>0 c * monomial1 pp"
  for c::"'b::comm_semiring_1"
  by (auto intro!: poly_mapping_eqI simp: monomial1_def Const\<^sub>0_def mult_single)

lemma monomial1_add: "(monomial1 (a + b)::('a::monoid_add\<Rightarrow>\<^sub>0'b::comm_semiring_1)) = monomial1 a * monomial1 b"
  by (auto simp: monomial1_def mult_single)

lemma monomial1_monomial: "monomial1 (monomial n v) = (Var\<^sub>0 v::_\<Rightarrow>\<^sub>0('b::comm_semiring_1))^n"
  by (auto intro!: poly_mapping_eqI simp: monomial1_def Var\<^sub>0_power lookup_single when_def)

lemma MPoly_numeral: "MPoly (numeral x) = numeral x"
  by (metis monom.abs_eq monom_numeral single_numeral)

lemma MPoly_power: "MPoly (x ^ n) = MPoly x ^ n"
  by (induction n) (auto simp: one_mpoly_def times_mpoly.abs_eq[symmetric])

subsubsection \<open>Ordered Power-Products\<close>

lemma foldl_assoc:
  assumes "\<And>x y z. f (f x y) z = f x (f y z)"
  shows "foldl f (f a b) xs = f a (foldl f b xs)"
proof (induct xs arbitrary: a b)
  fix a b
  show "foldl f (f a b) [] = f a (foldl f b [])" by simp
next
  fix a b x xs
  assume "\<And>a b. foldl f (f a b) xs = f a (foldl f b xs)"
  from assms[of a b x] this[of a "f b x"]
    show "foldl f (f a b) (x # xs) = f a (foldl f b (x # xs))" unfolding foldl_Cons by simp
qed

context gd_term_compare
begin

lemma compute_lt_poly_mapping [code]:
  "lt (Pm_oalist xs) = (let aux = list_of_oalist xs in if aux = [] then min_term else fst (hd aux))"
  sorry

lemma compute_lc_poly_mapping [code]:
  "lc (Pm_oalist xs) = (let aux = list_of_oalist xs in if aux = [] then 0 else snd (hd aux))"
  sorry

lemma compute_tail_poly_mapping [code]:
  "tail (Pm_oalist xs) = Pm_oalist (OAlist.except_min xs)"
  sorry

definition comp_opt_p :: "('t \<Rightarrow>\<^sub>0 'b::zero) comp_opt"
  where "comp_opt_p p q =
              (if p = q then Some EQUAL else if ord_strict_p p q then Some LESS else if ord_strict_p q p then Some GREATER else None)"

lemma compute_comp_opt_p_poly_mapping [code]:
  "comp_opt_p (Pm_oalist xs) (Pm_oalist ys) =
    OAlist.lex_ord (\<lambda>_ x y. if x = y then Some EQUAL else if x = 0 then Some LESS else if y = 0 then Some GREATER else None) xs ys"
  sorry

lemma compute_ord_p [code]:
  "(ord_p p q) = (let aux = comp_opt_p p q in aux \<noteq> None \<and> aux \<noteq> Some GREATER)"
  sorry

lemma compute_ord_p_strict [code]: "(ord_strict_p p q) = (comp_opt_p p q = Some LESS)"
  sorry

lemma compute_keys_to_list_pm [code]: "keys_to_list (Pm_oalist xs) = map fst (list_of_oalist xs)"
  sorry

end (* gd_term_compare *)

lifting_update poly_mapping.lifting
lifting_forget poly_mapping.lifting

subsection \<open>Type Class Instantiations\<close>

text \<open>Degree-Reverse-Lexicographic Ordering\<close>

instantiation poly_mapping :: ("{compare,wellorder}", ordered_comm_monoid_add) compare
begin

definition compare_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) comparator"
  where "compare_poly_mapping s t = (if s = t then EQUAL else if drlex_pm s t then GREATER else LESS)"

text \<open>This must be the converse of @{const drlex_pm}, to ensure that terms are sorted descending in
  the representation of polynomials by ordered associative lists.\<close>

instance sorry

end

text \<open>POT Ordering\<close>

instantiation prod:: (compare, compare) compare
begin

definition compare_prod :: "('a \<times> 'b) comparator" where
  "compare_prod x y = (let aux = compare (snd x) (snd y) in (if aux = EQUAL then compare (fst x) (fst y) else -aux))"

instance sorry

end

subsection \<open>Computations\<close>

subsubsection \<open>Scalar Polynomials\<close>

type_synonym 'a mpoly_tc = "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"

global_interpretation punit: gd_term_compare to_pair_unit fst
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = id"
  and "punit.component_of_term = (\<lambda>_. ())"
  defines monom_mult_punit = punit.monom_mult
  and mult_scalar_punit = punit.mult_scalar
  and shift_map_keys_punit = punit.shift_map_keys
  and min_term_punit = punit.min_term
  and lt_punit = punit.lt
  and lc_punit = punit.lc
  and tail_punit = punit.tail
  and comp_opt_p_punit = punit.comp_opt_p
  and ord_p_punit = punit.ord_p
  and ord_strict_p_punit = punit.ord_strict_p
  subgoal apply (standard) sorry
  apply (fact MPoly_Type_Class.punit_adds_term)
  apply (fact MPoly_Type_Class.punit_pp_of_term)
  apply (fact MPoly_Type_Class.punit_component_of_term)
  done

lemma compute_shift_map_keys_punit [code abstract]:
  "list_of_oalist (shift_map_keys_punit t f xs) = map (\<lambda>(k, v). (t + k, f v)) (list_of_oalist xs)"
  sorry

lemma compute_mult_scalar_punit [code]:
  "Pm_oalist xs * q = (case list_of_oalist xs of ((t, c) # ys) \<Rightarrow>
    (monom_mult_punit c t q + (Pm_oalist (oalist_of_list ys)) * q) | _ \<Rightarrow>
    Pm_oalist OAlist.empty)"
  sorry

locale trivariate\<^sub>0_rat
begin

abbreviation X::"rat mpoly_tc" where "X \<equiv> Var\<^sub>0 (0::nat)"
abbreviation Y::"rat mpoly_tc" where "Y \<equiv> Var\<^sub>0 (1::nat)"
abbreviation Z::"rat mpoly_tc" where "Z \<equiv> Var\<^sub>0 (2::nat)"

end

locale trivariate
begin

abbreviation "X \<equiv> Var 0"
abbreviation "Y \<equiv> Var 1"
abbreviation "Z \<equiv> Var 2"

end

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "ord_p_punit (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z\<^sup>2 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "tail_punit (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) = X\<^sup>2 * Z"
  by eval

lemma
  "lt_punit (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) = sparse\<^sub>0 [(1, 3), (2, 2)]"
  by eval

lemma
  "lt_punit (X + Y + Z) = sparse\<^sub>0 [(2, 1)]"
  by eval

lemma
  "keys (X\<^sup>2 * Z ^ 3 + 2 * Y ^ 3 * Z\<^sup>2) =
    {monomial 2 0 + monomial 3 2, monomial 3 1 + monomial 2 2}"
  by eval

lemma
  "keys (X\<^sup>2 * Z ^ 3 + 2 * Y ^ 3 * Z\<^sup>2) =
    {monomial 2 0 + monomial 3 2, monomial 3 1 + monomial 2 2}"
  by eval

lemma
  "- 1 * X\<^sup>2 * Z ^ 7 + - 2 * Y ^ 3 * Z\<^sup>2 = - X\<^sup>2 * Z ^ 7 + - 2 * Y ^ 3 * Z\<^sup>2"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 + X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2 = X\<^sup>2 * Z ^ 7 + X\<^sup>2 * Z ^ 4"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 - X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2 =
    X\<^sup>2 * Z ^ 7 - X\<^sup>2 * Z ^ 4"
  by eval

lemma
  "lookup (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 + 2) (sparse\<^sub>0 [(0, 2), (2, 7)]) = 1"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 \<noteq>
   X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2"
  by eval

lemma
  "0 * X^2 * Z^7 + 0 * Y^3*Z\<^sup>2 = 0"
  by eval

lemma
  "monom_mult_punit 3 (sparse\<^sub>0 [(1, 2::nat)]) (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) =
    3 * Y\<^sup>2 * Z * X\<^sup>2 + 6 * Y ^ 5 * Z\<^sup>2"
  by eval

lemma
  "monomial (-4) (sparse\<^sub>0 [(0, 2::nat)]) = - 4 * X\<^sup>2"
  by eval

lemma "monomial (0::rat) (sparse\<^sub>0 [(0::nat, 2::nat)]) = 0"
  by eval

lemma
  "(X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) * (X\<^sup>2 * Z ^ 3 + - 2 * Y ^ 3 * Z\<^sup>2) =
    X ^ 4 * Z ^ 4 + - 2 * X\<^sup>2 * Z ^ 3 * Y ^ 3 +
 - 4 * Y ^ 6 * Z ^ 4 + 2 * Y ^ 3 * Z ^ 5 * X\<^sup>2"
  by eval

end

subsubsection \<open>Vector-Polynomials\<close>

type_synonym 'a vmpoly_tc = "((nat \<Rightarrow>\<^sub>0 nat) \<times> nat) \<Rightarrow>\<^sub>0 'a"

global_interpretation pprod: gd_term_compare id id
  rewrites "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  defines splus_pprod = pprod.splus
  and monom_mult_pprod = pprod.monom_mult
  and mult_scalar_pprod = pprod.mult_scalar
  and adds_term_pprod = pprod.adds_term
  and shift_map_keys_pprod = pprod.shift_map_keys
  and min_term_pprod = pprod.min_term
  and lt_pprod = pprod.lt
  and lc_pprod = pprod.lc
  and tail_pprod = pprod.tail
  and comp_opt_p_pprod = pprod.comp_opt_p
  and ord_p_pprod = pprod.ord_p
  and ord_strict_p_pprod = pprod.ord_strict_p
  subgoal apply (standard) sorry
  apply (fact MPoly_Type_Class.pprod_pp_of_term)
  apply (fact MPoly_Type_Class.pprod_component_of_term)
  done

lemma compute_adds_term_pprod [code_unfold]:
  "adds_term_pprod u v = (snd u = snd v \<and> adds_pm_add_linorder (fst u) (fst v))"
  by (simp add: adds_term_pprod_def pprod.adds_term_def adds_pm_add_linorder_def)

lemma compute_splus_pprod [code]: "splus_pprod t (s, i) = (t + s, i)"
  by (simp add: splus_pprod_def pprod.splus_def)

lemma compute_shift_map_keys_pprod [code abstract]:
  "list_of_oalist (shift_map_keys_pprod t f xs) = map (\<lambda>(k, v). (splus_pprod t k, f v)) (list_of_oalist xs)"
  sorry

definition Vec\<^sub>0 :: "nat \<Rightarrow> (('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 nat) \<times> nat) \<Rightarrow>\<^sub>0 'b::semiring_1" where
  "Vec\<^sub>0 i p = mult_scalar_pprod p (Poly_Mapping.single (0, i) 1)"

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "ord_p_pprod (Vec\<^sub>0 1 (X\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) (Vec\<^sub>0 1 (X\<^sup>2 * Z\<^sup>2 + 2 * Y ^ 3 * Z\<^sup>2))"
  by eval

lemma
  "tail_pprod (Vec\<^sub>0 1 (X\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) = Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "lt_pprod (Vec\<^sub>0 1 (X\<^sup>2 * Z) + Vec\<^sub>0 0 (2 * Y ^ 3 * Z\<^sup>2)) = (sparse\<^sub>0 [(0, 2), (2, 1)], 1)"
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

end

subsection \<open>Code setup for type MPoly\<close>

text \<open>postprocessing from \<open>Var\<^sub>0, Const\<^sub>0\<close> to \<open>Var, Const\<close>.\<close>

lemmas [code_post] =
  plus_mpoly.abs_eq[symmetric]
  times_mpoly.abs_eq[symmetric]
  MPoly_numeral
  MPoly_power
  one_mpoly_def[symmetric]
  Var.abs_eq[symmetric]
  Const.abs_eq[symmetric]

instantiation mpoly::("{equal, zero}")equal begin

lift_definition equal_mpoly:: "'a mpoly \<Rightarrow> 'a mpoly \<Rightarrow> bool" is HOL.equal .

instance proof standard qed (transfer, rule equal_eq)

end

experiment begin interpretation trivariate .

lemmas [mpoly_simps] = plus_mpoly.abs_eq

lemma "content_primitive (4 * X * Y^2 * Z^3 + 6 * X\<^sup>2 * Y^4 + 8 * X\<^sup>2 * Y^5) =
    (2::int, 2 * X * Y\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y ^ 4 + 4 * X\<^sup>2 * Y ^ 5)"
  by eval

end

end (* theory *)
