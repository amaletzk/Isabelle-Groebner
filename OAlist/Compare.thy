(* Author: Andreas Lochbihler, ETH Zurich *)

theory Compare
  imports Auxiliary
begin

datatype comparison = LESS | EQUAL | GREATER

code_printing type_constructor comparison \<rightharpoonup>
  (SML) "General.order" and
  (Haskell) "Prelude.Ordering"
| constant LESS \<rightharpoonup>
  (SML) "General.LESS" and
  (Haskell) "Prelude.LT"
| constant EQUAL \<rightharpoonup>
  (SML) "General.EQUAL" and
  (Haskell) "Prelude.EQ"
| constant GREATER \<rightharpoonup>
  (SML) "General.GREATER" and
  (Haskell) "Prelude.GT"

instantiation comparison :: uminus begin

primrec uminus_comparison :: "comparison \<Rightarrow> comparison"
where "- LESS = GREATER" | "- EQUAL = EQUAL" | "- GREATER = LESS"

instance ..
end

lemma uminus_uminus_comparision [simp]: "- (- x) = (x :: comparison)"
by(cases x) simp_all

lemma uminus_eq_LESS_iff [simp]: "- x = LESS \<longleftrightarrow> x = GREATER"
by(cases x) simp_all

lemma uminus_eq_EQUAL_iff [simp]: "- x = EQUAL \<longleftrightarrow> x = EQUAL"
by(cases x) simp_all

lemma uminus_eq_GREATER_iff [simp]: "- x = GREATER \<longleftrightarrow> x = LESS"
by(cases x) simp_all

lemma LESS_eq_uminus_iff [simp]: "LESS = - x \<longleftrightarrow> x = GREATER"
by(cases x) simp_all

lemma EQUAL_eq_uminus_iff [simp]: "EQUAL = - x \<longleftrightarrow> x = EQUAL"
by(cases x) simp_all

lemma GREATER_eq_uminus_iff [simp]: "GREATER = - x \<longleftrightarrow> x = LESS"
by(cases x) simp_all


type_synonym 'a comparator = "'a \<Rightarrow> 'a \<Rightarrow> comparison"

locale comparator_on_base =
  fixes compare :: "'a comparator"
begin

definition less_of_comparator :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
where "less_of_comparator x y \<longleftrightarrow> compare x y = LESS"

definition less_eq_of_comparator :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
where "less_eq_of_comparator x y \<longleftrightarrow> compare x y \<noteq> GREATER"

end

interpretation c: comparator_on_base compare for compare .

definition compare_vimage :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a comparator \<Rightarrow> 'b comparator"
where "compare_vimage f compare x y = compare (f x) (f y)"

lemma compare_vimage_compose [simp]:
  "compare_vimage f (compare_vimage g cmp) = compare_vimage (g \<circ> f) cmp"
by(simp add: fun_eq_iff compare_vimage_def)

lemma compare_vimage_id [simp]: "compare_vimage (\<lambda>x. x) cmp = cmp"
by(simp add: compare_vimage_def fun_eq_iff)

locale comparator_on = comparator_on_base +
  fixes D :: "'a set"
  assumes uminus_compare: "\<lbrakk> x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> - compare x y = compare y x"
  and compare_refl: "x \<in> D \<Longrightarrow> compare x x = EQUAL"
  and compare_trans':
  "\<lbrakk> compare x y = LESS;  compare y z = LESS;  x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare x z = LESS"
  "\<lbrakk> compare x y = LESS;  compare y z = EQUAL; x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare x z = LESS"
  "\<lbrakk> compare x y = EQUAL; compare y z = LESS;  x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare x z = LESS"
  "\<lbrakk> compare x y = EQUAL; compare y z = EQUAL; x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare x z = EQUAL"
begin

lemma comparator_on: "comparator_on compare D" ..

lemma compare_sym: 
  "\<lbrakk> compare y x = EQUAL; x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> compare x y = EQUAL"
by(drule (1) uminus_compare[rotated]) simp

lemma compare_eq_GREATER:
  "\<lbrakk> x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> compare x y = GREATER \<longleftrightarrow> compare y x = LESS"
by(auto dest: uminus_compare)

lemma compare_eq_EQUAL:
  "\<lbrakk> x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> compare x y = EQUAL \<longleftrightarrow> compare y x = EQUAL"
by(auto dest: uminus_compare)

lemma compare_trans'':
  "\<lbrakk> compare x y = GREATER; compare y z = GREATER; x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare x z = GREATER"
  "\<lbrakk> compare x y = GREATER; compare y z = EQUAL;   x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare x z = GREATER"
  "\<lbrakk> compare x y = EQUAL;   compare y z = GREATER; x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare x z = GREATER"
by(metis compare_trans' uminus_compare uminus_comparison.simps)+

lemmas compare_trans = compare_trans' compare_trans''

lemma less_of_comparator_conv_less_eq_of_comparator:
  "\<lbrakk> x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x"
by(auto simp add: less_of_comparator_def less_eq_of_comparator_def dest: uminus_compare[rotated])

lemma less_eq_of_comparator_refl: "x \<in> D \<Longrightarrow> x \<sqsubseteq> x"
by(simp add: less_eq_of_comparator_def compare_refl)

lemma less_eq_of_comparator_trans: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
by(cases "compare x y" "compare y z" rule: comparison.exhaust[case_product comparison.exhaust])
  (auto simp add: less_eq_of_comparator_def dest: compare_trans)

lemma less_eq_of_comparator_linear: "\<lbrakk> x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
by(cases "compare x y")(auto simp add: less_eq_of_comparator_def dest: uminus_compare)

lemma subset_comparator_on: "D' \<subseteq> D \<Longrightarrow> comparator_on compare D'"
by(unfold_locales)(auto intro: uminus_compare compare_refl compare_trans)

lemma comparator_on_dual: "comparator_on (- compare) D"
by(unfold_locales)(auto dest: uminus_compare compare_refl compare_trans)

lemma comparator_on_vimage: "comparator_on (compare_vimage f compare) (f -` D)"
by(unfold_locales)(auto simp add: compare_vimage_def dest: uminus_compare intro: compare_refl compare_trans)

end

locale comparator_eq_on = comparator_on +
  assumes compare_eq_EQUALD: "\<lbrakk> compare x y = EQUAL; x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> x = y"
begin

lemma comparator_eq_on: "comparator_eq_on compare D" ..

lemma less_eq_of_comparator_antisym: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> x = y"
by(cases "compare x y")(auto simp add: less_eq_of_comparator_def intro: compare_eq_EQUALD dest: uminus_compare[rotated])

lemma subset_comparator_eq_on:
  assumes "D' \<subseteq> D"
  shows "comparator_eq_on compare D'"
proof -
  interpret D': comparator_on compare D' using assms by(rule subset_comparator_on)
  show ?thesis using assms by unfold_locales(blast intro: compare_eq_EQUALD)
qed

lemma comparator_eq_on_dual: "comparator_eq_on (- compare) D"
proof -
  interpret dual: comparator_on "- compare" D by(rule comparator_on_dual)
  show ?thesis by unfold_locales(auto dest: compare_eq_EQUALD)
qed

lemma comparator_eq_on_vimage: 
  assumes "inj_on f (f -` D)"
  shows "comparator_eq_on (compare_vimage f compare) (f -` D)"
proof -
  interpret image: comparator_on "compare_vimage f compare" "f -` D" by(rule comparator_on_vimage)
  show ?thesis
    by unfold_locales(auto dest: compare_eq_EQUALD inj_onD[OF assms] simp add: compare_vimage_def)
qed

end

abbreviation comparator :: "'a comparator \<Rightarrow> bool"
where "comparator cmp \<equiv> comparator_on cmp UNIV"

abbreviation comparator_eq :: "'a comparator \<Rightarrow> bool"
where "comparator_eq cmp \<equiv> comparator_eq_on cmp UNIV"

lemma comparator_eq_on_empty [iff]:
  "comparator_eq_on cmp {}"
  by standard simp_all

lemma comparator_vimageI [simp]: "comparator cmp \<Longrightarrow> comparator (compare_vimage f cmp)"
by(drule comparator_on.comparator_on_vimage[where f=f]) simp

lemma comparator_eq_vimageI [simp]:
  "\<lbrakk> comparator_eq cmp; inj f \<rbrakk> \<Longrightarrow> comparator_eq (compare_vimage f cmp)"
by(drule comparator_eq_on.comparator_eq_on_vimage[where f=f])(auto intro: comparator_eq_on.subset_comparator_eq_on)



lemma linorder_of_comparator_eq:
  assumes "comparator_eq_on cmp UNIV"
  shows "class.linorder (c.less_eq_of_comparator cmp) (c.less_of_comparator cmp)"
proof -
  interpret comparator_eq_on cmp UNIV by(rule assms)
  show ?thesis
    by unfold_locales(auto simp add: less_of_comparator_conv_less_eq_of_comparator less_eq_of_comparator_refl intro: less_eq_of_comparator_trans less_eq_of_comparator_antisym less_eq_of_comparator_linear del: disjCI)
qed


definition (in ord) comparator_of_le :: "'a comparator"
where "comparator_of_le x y = (if x \<le> y then if y \<le> x then EQUAL else LESS else GREATER)"

declare ord.comparator_of_le_def[code]

lemma (in linorder) [simp]:
  shows comparator_on_comparator_of_le: "comparator_on comparator_of_le D" (is ?thesis1)
  and comparator_eq_on_comparator_of_le: "comparator_eq_on comparator_of_le D" (is ?thesis2)
proof -
  show ?thesis1
  proof(unfold_locales)
    fix x y
    show "- comparator_of_le x y = comparator_of_le y x"
      using linear[of x y] by(auto simp add: comparator_of_le_def)
  qed(auto simp add: comparator_of_le_def split: if_split_asm)
  then interpret comparator_on comparator_of_le D .
  show ?thesis2
    by unfold_locales(simp add: comparator_of_le_def split: if_split_asm)
qed

context comparator_on_base begin

fun lex_compare :: "'a list comparator"
where
  "lex_compare []       []       = EQUAL"
| "lex_compare []       (y # ys) = LESS"
| "lex_compare (x # xs) []       = GREATER"
| "lex_compare (x # xs) (y # ys) =
  (case compare x y of LESS    \<Rightarrow> LESS
                     | EQUAL   \<Rightarrow> lex_compare xs ys
                     | GREATER \<Rightarrow> GREATER)"

lemma lex_compare_Cons1:
  "lex_compare (x # xs) ys =
  (case ys of [] \<Rightarrow> GREATER 
   | y # ys \<Rightarrow> case compare x y of LESS \<Rightarrow> LESS | EQUAL \<Rightarrow> lex_compare xs ys | GREATER \<Rightarrow> GREATER)"
by(simp split: list.split)

end

context comparator_on begin

lemma uminus_lex_compare: "\<lbrakk> xs \<in> lists D; ys \<in> lists D \<rbrakk> \<Longrightarrow> - lex_compare xs ys = lex_compare ys xs"
by(induction xs ys rule: lex_compare.induct)(auto split: comparison.split dest: uminus_compare[rotated])

lemma lex_compare_same [simp]: "xs \<in> lists D \<Longrightarrow> lex_compare xs xs = EQUAL"
by(induction xs)(auto split: comparison.split dest: compare_refl)

lemma lex_compare_trans_lt_lt:
  "\<lbrakk> lex_compare xs ys = LESS; lex_compare ys zs = LESS; xs \<in> lists D; ys \<in> lists D; zs \<in> lists D \<rbrakk>
  \<Longrightarrow> lex_compare xs zs = LESS"
by(induction xs ys arbitrary: zs rule: lex_compare.induct)(auto simp add: lex_compare_Cons1 split: list.split_asm comparison.splits dest: compare_trans)

lemma lex_compare_trans_lt_eq:
  "\<lbrakk> lex_compare xs ys = LESS; lex_compare ys zs = EQUAL; xs \<in> lists D; ys \<in> lists D; zs \<in> lists D \<rbrakk>
  \<Longrightarrow> lex_compare xs zs = LESS"
by(induction xs ys arbitrary: zs rule: lex_compare.induct)(auto simp add: lex_compare_Cons1 split: list.split_asm comparison.splits dest: compare_trans)

lemma lex_compare_trans_eq_lt:
  "\<lbrakk> lex_compare xs ys = EQUAL; lex_compare ys zs = LESS; xs \<in> lists D; ys \<in> lists D; zs \<in> lists D \<rbrakk>
  \<Longrightarrow> lex_compare xs zs = LESS"
by(induction xs ys arbitrary: zs rule: lex_compare.induct)(auto simp add: lex_compare_Cons1 split: list.split_asm comparison.splits dest: compare_trans)

lemma lex_compare_trans_eq_eq:
  "\<lbrakk> lex_compare xs ys = EQUAL; lex_compare ys zs = EQUAL; xs \<in> lists D; ys \<in> lists D; zs \<in> lists D \<rbrakk>
  \<Longrightarrow> lex_compare xs zs = EQUAL"
by(induction xs ys arbitrary: zs rule: lex_compare.induct)(auto simp add: lex_compare_Cons1 split: list.split_asm comparison.splits dest: compare_trans)

lemmas lex_compare_trans =
  lex_compare_trans_lt_lt
  lex_compare_trans_lt_eq
  lex_compare_trans_eq_lt
  lex_compare_trans_eq_eq

lemma comparator_on_lex_compare: "comparator_on lex_compare (lists D)"
by unfold_locales(auto simp add: uminus_lex_compare intro: lex_compare_trans)

end

context comparator_eq_on begin

lemma lex_compare_eq_EQUALD: "\<lbrakk> lex_compare xs ys = EQUAL; xs \<in> lists D; ys \<in> lists D \<rbrakk> \<Longrightarrow> xs = ys"
by(induction xs ys rule: lex_compare.induct)(auto split: comparison.split_asm dest: compare_eq_EQUALD)

lemma comparator_eq_on_lex_compare: "comparator_eq_on lex_compare (lists D)"
proof -
  interpret l: comparator_on lex_compare "lists D" by(fact comparator_on_lex_compare)
  show ?thesis by unfold_locales(rule lex_compare_eq_EQUALD)
qed

end

context
  fixes cmp_a :: "'a comparator"
  and cmp_b :: "'b comparator"
begin

fun compare_prod :: "('a \<times> 'b) comparator"
where
  "compare_prod (x, y) (x', y') =
  (case cmp_a x x' of LESS \<Rightarrow> LESS 
   | EQUAL \<Rightarrow> cmp_b y y'
   | GREATER \<Rightarrow> GREATER)"

fun compare_sum :: "('a + 'b) comparator"
where
  "compare_sum (Inl x) (Inl y) = cmp_a x y"
| "compare_sum (Inl x) (Inr y) = LESS"
| "compare_sum (Inr x) (Inl y) = GREATER"
| "compare_sum (Inr x) (Inr y) = cmp_b x y"

context
  fixes A :: "'a set" and B :: "'b set"
  assumes A: "comparator_on cmp_a A"
  and B: "comparator_on cmp_b B"
begin

interpretation a: comparator_on cmp_a A by(fact A)
interpretation b: comparator_on cmp_b B by(fact B)

lemma uminus_compare_prod [simp]:
  "\<lbrakk> xy \<in> A \<times> B; xy' \<in> A \<times> B \<rbrakk> \<Longrightarrow> - compare_prod xy xy' = compare_prod xy' xy"
by(cases xy xy' rule: prod.exhaust[case_product prod.exhaust])(auto split: comparison.split dest: a.uminus_compare b.uminus_compare)

lemma uminus_compare_sum [simp]:
  "\<lbrakk> xy \<in> A <+> B; xy' \<in> A <+> B \<rbrakk> \<Longrightarrow> - compare_sum xy xy' = compare_sum xy' xy"
by(cases xy xy' rule: sum.exhaust[case_product sum.exhaust])(auto split: comparison.split dest: a.uminus_compare b.uminus_compare)

lemma compare_prod_same [simp]:
  "xy \<in> A \<times> B \<Longrightarrow> compare_prod xy xy = EQUAL"
by(cases xy)(simp add: a.compare_refl b.compare_refl)
lemma compare_sum_same [simp]:
  "xy \<in> A <+> B \<Longrightarrow> compare_sum xy xy = EQUAL"
by(cases xy)(auto simp add: a.compare_refl b.compare_refl)

lemma comparator_on_compare_prod: "comparator_on compare_prod (A \<times> B)"
apply(unfold_locales)
apply(auto split: comparison.splits)
apply(drule (4) a.compare_trans b.compare_trans, simp)+
done

lemma comparator_on_compare_sum: "comparator_on compare_sum (A <+> B)"
apply(unfold_locales)
apply(auto split: comparison.splits)
apply(drule (4) a.compare_trans b.compare_trans, simp)+
done

end

context
  fixes A :: "'a set" and B :: "'b set"
  assumes A: "comparator_eq_on cmp_a A"
  and B: "comparator_eq_on cmp_b B"
begin

interpretation a: comparator_eq_on cmp_a A by(fact A)
interpretation b: comparator_eq_on cmp_b B by(fact B)

interpretation prod: comparator_on compare_prod "A \<times> B"
  by(rule comparator_on_compare_prod) unfold_locales

lemma comparator_eq_on_compare_prod: "comparator_eq_on compare_prod (A \<times> B)"
by unfold_locales(auto split: comparison.split_asm dest: a.compare_eq_EQUALD b.compare_eq_EQUALD)

interpretation sum: comparator_on compare_sum "A <+> B"
  by(rule comparator_on_compare_sum) unfold_locales

lemma comparator_eq_on_compare_sum: "comparator_eq_on compare_sum (A <+> B)"
by unfold_locales(auto split: comparison.split_asm dest: a.compare_eq_EQUALD b.compare_eq_EQUALD)

end

end

subsection \<open>Type classes for @{text compare}\<close>

class linpreorder = preorder +
  assumes linear': "x \<le> y \<or> y \<le> x"

subclass (in linorder) linpreorder
by(unfold_locales)(rule linear)

class linpreorder_compare = linpreorder +
  fixes compare :: "'a comparator"
  assumes compare_compatible':
  "x < y \<Longrightarrow> compare x y = LESS"
  "\<lbrakk> x \<le> y; y \<le> x \<rbrakk> \<Longrightarrow> compare x y = EQUAL"
  "x > y \<Longrightarrow> compare x y = GREATER"
begin

lemma compare_same [simp]: "compare x x = EQUAL"
by(rule compare_compatible') simp_all

lemmas compare_compatible = compare_compatible' compare_compatible'[symmetric]

lemma compare_conv_le:
  "compare x y = LESS    \<longleftrightarrow> x < y"         (is ?less)
  "compare x y = EQUAL   \<longleftrightarrow> x \<le> y \<and> y \<le> x" (is ?equal)
  "compare x y = GREATER \<longleftrightarrow> y < x"         (is ?greater)
proof -
  have "x < y \<or> x \<le> y \<and> y \<le> x \<or> y < x" by (metis less_le_not_le linear')
  thus ?less ?equal ?greater by(auto dest: compare_compatible)
qed

lemma uminus_compare [simp]: "- compare x y = compare y x"
by(cases "compare x y")(simp_all, auto simp add: compare_conv_le intro: compare_compatible)

lemma comparator_on_compare [simp]: "comparator_on compare D"
by(unfold_locales)(auto simp add: compare_conv_le intro: less_trans less_le_trans le_less_trans order_trans)

end

class linorder_compare = order + linpreorder_compare
begin

subclass linorder by(unfold_locales)(rule linear')

lemma comparator_eq_on_compare [simp]: "comparator_eq_on compare D"
proof -
  interpret comparator_on compare D by(rule comparator_on_compare)
  show ?thesis by(unfold_locales)(auto simp add: compare_conv_le)
qed

end

setup \<open>Sign.add_const_constraint (@{const_name compare}, SOME @{typ "'a :: linpreorder comparator"})\<close>

lemma linpreorder_compare_classI:
  assumes "compare = (comparator_of_le :: 'a :: linpreorder comparator)"
  shows "OFCLASS('a, linpreorder_compare_class)"
apply(rule linpreorder_compare_class.intro)
apply(intro_classes)[1]
apply(unfold_locales)
apply(simp_all add: assms comparator_of_le_def less_le_not_le)
done

lemma linorder_compare_classI:
  assumes "compare = (comparator_of_le :: 'a :: linorder comparator)"
  shows "OFCLASS('a, linorder_compare_class)"
apply(rule linorder_compare_class.intro)
apply(rule linpreorder_compare_classI[OF assms])
apply intro_classes
done

setup \<open>Sign.add_const_constraint (@{const_name compare}, SOME @{typ "'a :: linpreorder_compare comparator"})\<close>

instantiation nat :: linorder_compare begin
definition compare_nat :: "nat comparator" where "compare_nat = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_nat_def)
end

lemma compare_nat_code [code]:
  "compare (0 :: nat) 0       = EQUAL"
  "compare 0          (Suc m) = LESS"
  "compare (Suc n)    0       = GREATER"
  "compare (Suc n)    (Suc m) = compare n m"
by(simp_all add: compare_nat_def comparator_of_le_def)

instantiation int :: linorder_compare begin
definition compare_int :: "int comparator" where "compare_int = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_int_def)
end

instantiation num :: linorder_compare begin
definition compare_num :: "num comparator" where "compare_num = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_num_def)
end

lemma compare_num_code [simp, code]:
  "compare num.One      num.One      = EQUAL"
  "compare num.One      (num.Bit0 m) = LESS"
  "compare num.One      (num.Bit1 m) = LESS"
  "compare (num.Bit0 n) num.One      = GREATER"
  "compare (num.Bit0 n) (num.Bit0 m) = compare n m"
  "compare (num.Bit0 n) (num.Bit1 m) = (case compare n m of LESS \<Rightarrow> LESS | EQUAL \<Rightarrow> LESS | GREATER \<Rightarrow> GREATER)"
  "compare (num.Bit1 n) num.One      = GREATER"
  "compare (num.Bit1 n) (num.Bit0 m) = (case compare n m of LESS \<Rightarrow> LESS | EQUAL \<Rightarrow> GREATER | GREATER \<Rightarrow> GREATER)"
  "compare (num.Bit1 n) (num.Bit1 m) = compare n m"
by(auto simp add: compare_num_def comparator_of_le_def)

instantiation integer :: linorder_compare begin
definition compare_integer :: "integer comparator" where "compare_integer = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_integer_def)
end

code_printing constant "compare :: integer comparator" \<rightharpoonup>
  (SML) "IntInf.compare ((_), (_))" and
  (Haskell) "Prelude.compare"

lemma compare_integer_code [simp, code]:
  "compare (0 :: integer)       0                    = EQUAL"
  "compare 0                    (Code_Numeral.Pos m) = LESS"
  "compare 0                    (Code_Numeral.Neg m) = GREATER"
  "compare (Code_Numeral.Pos n) 0                    = GREATER"
  "compare (Code_Numeral.Pos n) (Code_Numeral.Pos m) = compare n m"
  "compare (Code_Numeral.Pos n) (Code_Numeral.Neg m) = GREATER"
  "compare (Code_Numeral.Neg n) 0                    = LESS"
  "compare (Code_Numeral.Neg n) (Code_Numeral.Pos m) = LESS"
  "compare (Code_Numeral.Neg n) (Code_Numeral.Neg m) = - compare n m"
by(auto simp add: compare_integer_def comparator_of_le_def intro: compare_compatible)

instantiation natural :: linorder_compare begin
definition compare_natural :: "natural comparator" where "compare_natural = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_natural_def)
end

lemma compare_natural_code [code]:
  "compare x y = compare (integer_of_natural x) (integer_of_natural y)"
unfolding compare_integer_def compare_natural_def comparator_of_le_def
including integer.lifting natural.lifting
by transfer simp

instantiation bool :: linorder_compare begin
definition compare_bool :: "bool comparator" where "compare_bool = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_bool_def)
end

lemma compare_bool_code [code, simp]:
  "compare False False = EQUAL"
  "compare False True  = LESS"
  "compare True  False = GREATER"
  "compare True  True  = EQUAL"
by(simp_all add: compare_bool_def comparator_of_le_def)

instantiation Enum.finite_1 :: linorder_compare begin
definition compare_finite_1 :: "Enum.finite_1 comparator" where "compare_finite_1 = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_finite_1_def)
end

lemma compare_finite_1_code [code]:
  "compare x (y :: Enum.finite_1) = EQUAL"
by(cases x y rule: finite_1.exhaust[case_product finite_1.exhaust])(simp add: compare_finite_1_def comparator_of_le_def)

instantiation Enum.finite_2 :: linorder_compare begin
definition compare_finite_2 :: "Enum.finite_2 comparator" where "compare_finite_2 = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_finite_2_def)
end

lemma compare_finite_2_code [code]:
  "compare finite_2.a\<^sub>1 finite_2.a\<^sub>1 = EQUAL"
  "compare finite_2.a\<^sub>1 finite_2.a\<^sub>2 = LESS"
  "compare finite_2.a\<^sub>2 finite_2.a\<^sub>1 = GREATER"
  "compare finite_2.a\<^sub>2 finite_2.a\<^sub>2 = EQUAL"
by(simp_all add: compare_finite_2_def comparator_of_le_def less_eq_finite_2_def less_finite_2_def)

instantiation Enum.finite_3 :: linorder_compare begin
definition compare_finite_3 :: "Enum.finite_3 comparator" where "compare_finite_3 = comparator_of_le"
instance by(rule linorder_compare_classI)(simp add: compare_finite_3_def)
end

lemma compare_finite_3_code [code]:
  "compare finite_3.a\<^sub>1 finite_3.a\<^sub>1 = EQUAL"
  "compare finite_3.a\<^sub>1 finite_3.a\<^sub>2 = LESS"
  "compare finite_3.a\<^sub>1 finite_3.a\<^sub>3 = LESS"
  "compare finite_3.a\<^sub>2 finite_3.a\<^sub>1 = GREATER"
  "compare finite_3.a\<^sub>2 finite_3.a\<^sub>2 = EQUAL"
  "compare finite_3.a\<^sub>2 finite_3.a\<^sub>3 = LESS"
  "compare finite_3.a\<^sub>3 finite_3.a\<^sub>1 = GREATER"
  "compare finite_3.a\<^sub>3 finite_3.a\<^sub>2 = GREATER"
  "compare finite_3.a\<^sub>3 finite_3.a\<^sub>3 = EQUAL"
by(simp_all add: compare_finite_3_def comparator_of_le_def less_eq_finite_3_def less_finite_3_def)

(* FIXME: add instantiation for unit type *)


subsection \<open>Operations that use comparators\<close>

context comparator_on_base begin

inductive dsorted_above :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  Nil: "dsorted_above y []"
| Cons: "\<lbrakk> compare y x = LESS; dsorted_above x xs \<rbrakk> \<Longrightarrow> dsorted_above y (x#xs)"

inductive_simps dsorted_above_simps [simp]:
  "dsorted_above y []"
  "dsorted_above y (x#xs)"

inductive dsorted_by :: "'a list \<Rightarrow> bool"
where
  Nil: "dsorted_by []"
| Cons: "dsorted_above x xs \<Longrightarrow> dsorted_by (x#xs)"

inductive_simps dsorted_by_simps [simp]:
  "dsorted_by []"
  "dsorted_by (x#xs)"

lemma dsorted_above_imp_dsorted_by:
  "dsorted_above y xs \<Longrightarrow> dsorted_by xs"
by(cases xs) simp_all

lemma dsorted_above_dsorted_byI:
  "\<lbrakk> dsorted_by xs; \<forall>x\<in>set xs. compare y x = LESS \<rbrakk> \<Longrightarrow> dsorted_above y xs"
by(cases xs) simp_all

context fixes x :: 'a begin

fun insort_by :: "'a list \<Rightarrow> 'a list"
where
  "insort_by [] = [x]"
| "insort_by (y # ys) =
  (case compare x y of LESS \<Rightarrow> x # y # ys
   | EQUAL \<Rightarrow> y # ys
   | GREATER \<Rightarrow> y # insort_by ys)"

lemma set_insort_by: "set (insort_by xs) \<subseteq> insert x (set xs)"
by(induction xs)(auto split: comparison.split)

lemma insort_by_in_lists: "\<lbrakk> x \<in> D; xs \<in> lists D \<rbrakk> \<Longrightarrow> insort_by xs \<in> lists D"
by(induction xs)(auto split: comparison.split)

end

(* TODO: insertion sort is used here, may want to consider faster implementations *)

definition sort_by :: "'a list \<Rightarrow> 'a list"
where "sort_by xs = foldr insort_by xs []"

lemma sort_by_simps [simp]:
  "sort_by [] = []"
  "sort_by (x#xs) = insort_by x (sort_by xs)"
by(simp_all add: sort_by_def)

lemma sort_by_in_lists: "xs \<in> lists D \<Longrightarrow> sort_by xs \<in> lists D"
by(induction xs)(simp_all add: insort_by_in_lists)

lemma set_sort_by_subset: "set (sort_by xs) \<subseteq> set xs"
by(induction xs)(auto dest: subsetD[OF set_insort_by])

end

lemma dsorted_above_vimage:
  "comparator_on_base.dsorted_above (compare_vimage f cmp) x xs \<longleftrightarrow> comparator_on_base.dsorted_above cmp (f x) (map f xs)"
by(induction xs arbitrary: x)(auto simp add: compare_vimage_def)

lemma dsorted_by_vimage: 
  "comparator_on_base.dsorted_by (compare_vimage f cmp) xs \<longleftrightarrow> comparator_on_base.dsorted_by cmp (map f xs)"
by(cases xs)(simp_all add: dsorted_above_vimage)

lemma insort_by_map:
  "c.insort_by cmp (f x) (map f xs) = map f (c.insort_by (compare_vimage f cmp) x xs)"
by(induction xs)(simp_all split: comparison.split add: compare_vimage_def)

lemma sort_by_map: "c.sort_by cmp (map f xs) = map f (c.sort_by (compare_vimage f cmp) xs)"
by(induction xs)(simp_all add: insort_by_map)

context comparator_on begin

lemma dsorted_above_aboveD:
  "\<lbrakk> dsorted_above x ys; y \<in> set ys; x \<in> D; ys \<in> lists D \<rbrakk> \<Longrightarrow> compare x y = LESS"
by(induction rule: dsorted_above.induct)(auto intro: compare_trans)

lemma dsorted_above_conv_dsorted_by:
  "\<lbrakk> x \<in> D; ys \<in> lists D \<rbrakk> \<Longrightarrow> dsorted_above x ys \<longleftrightarrow> dsorted_by ys \<and> (\<forall>y\<in>set ys. compare x y = LESS)"
by(auto dest: dsorted_above_aboveD dsorted_above_imp_dsorted_by intro: dsorted_above_dsorted_byI)

lemma dsorted_above_distinct: "\<lbrakk> dsorted_above x xs; x \<in> D; xs \<in> lists D \<rbrakk> \<Longrightarrow> distinct xs"
by(induction x xs rule: dsorted_above.induct)(auto dest: dsorted_above_aboveD simp add: compare_refl)

lemma dsorted_by_distinct: "\<lbrakk> dsorted_by xs; xs \<in> lists D \<rbrakk> \<Longrightarrow> distinct xs"
by(cases xs)(auto dest: dsorted_above_distinct dsorted_above_aboveD simp add: compare_refl)

lemma dsorted_by_insort_by:
  "\<lbrakk> dsorted_by xs; xs \<in> lists D; x \<in> D \<rbrakk> \<Longrightarrow> dsorted_by (insort_by x xs)"
by(induction xs)(auto 4 3 split: comparison.split simp add: dsorted_above_conv_dsorted_by insort_by_in_lists intro: compare_trans dest: set_insort_by[THEN subsetD] dest: uminus_compare)

lemma dsorted_by_sort_by [simp]: "xs \<in> lists D \<Longrightarrow> dsorted_by (sort_by xs)"
by(induction xs)(simp_all add: dsorted_by_insort_by sort_by_in_lists in_listsI)

lemma dsorted_above_subst:
  "\<lbrakk> dsorted_above x xs; compare y x = EQUAL; x \<in> D; y \<in> D; xs \<in> lists D \<rbrakk>
  \<Longrightarrow> dsorted_above y xs"
by(cases xs)(auto dest: compare_trans')

lemma dsorted_above_subst_EQUAL:
  "\<lbrakk> compare x y = EQUAL; x \<in> D; y \<in> D; xs \<in> lists D \<rbrakk>
  \<Longrightarrow> dsorted_above x xs \<longleftrightarrow> dsorted_above y xs"
by(auto intro: dsorted_above_subst simp add: compare_eq_EQUAL)

lemma dsorted_above_mono:
  "\<lbrakk> dsorted_above x xs; compare x y = GREATER; x \<in> D; y \<in> D; xs \<in> lists D \<rbrakk>
  \<Longrightarrow> dsorted_above y xs"
by(cases xs)(auto dest: compare_trans' simp add: compare_eq_GREATER)

end

lemma dsorted_by_sorted: "c.dsorted_by comparator_of_le xs \<Longrightarrow> sorted xs"
by(induct xs)(auto simp add: comparator_on.dsorted_above_conv_dsorted_by[where D=UNIV] comparator_of_le_def split: if_split_asm)

lemma sorted_distinct_dsorted_by: "\<lbrakk> sorted xs; distinct xs \<rbrakk> \<Longrightarrow> c.dsorted_by comparator_of_le xs"
by(induct xs)(auto simp add: comparator_on.dsorted_above_conv_dsorted_by[where D=UNIV] comparator_of_le_def)

lemma dsorted_by_conv_sorted_distinct:
  "c.dsorted_by comparator_of_le xs \<longleftrightarrow> sorted xs \<and> distinct xs"
by(blast intro: dsorted_by_sorted sorted_distinct_dsorted_by comparator_on.dsorted_by_distinct[OF comparator_on_comparator_of_le])

context comparator_eq_on begin

lemma set_insort_by:
  "\<lbrakk> xs \<in> lists D; x \<in> D \<rbrakk> \<Longrightarrow> set (insort_by x xs) = insert x (set xs)"
by(induct xs)(auto split: comparison.split dest: compare_eq_EQUALD)

lemma set_sort_by: "xs \<in> lists D \<Longrightarrow> set (sort_by xs) = set xs"
by(induct xs)(simp_all add: set_insort_by sort_by_in_lists)

end

context comparator_on_base begin

definition sorted_list_of_set_by :: "'a set \<Rightarrow> 'a list"
where "sorted_list_of_set_by A = (THE xs. dsorted_by xs \<and> set xs = A)"

lemma sorted_list_of_set_by_empty [simp]:
  "sorted_list_of_set_by {} = []"
by(auto simp add: sorted_list_of_set_by_def)

end

context comparator_eq_on begin

lemma finite_ex_dsorted_by:
  "\<lbrakk> finite A; A \<subseteq> D \<rbrakk> \<Longrightarrow> \<exists>xs. dsorted_by xs \<and> set xs = A"
proof(induction rule: finite_induct)
  case (insert x A)
  then obtain xs where "dsorted_by xs" "A = set xs" by auto
  with \<open>insert x A \<subseteq> D\<close> have "xs \<in> lists D" "x \<in> D" by(auto)
  with \<open>dsorted_by xs\<close> have "dsorted_by (insort_by x xs)"
    by(rule dsorted_by_insort_by)
  moreover
  have "set (insort_by x xs) = insert x (set xs)"
    using \<open>xs \<in> lists D\<close> \<open>x \<in> D\<close> by(rule set_insort_by)
  ultimately show ?case using \<open>A = set xs\<close> by auto
qed simp

lemma dsorted_by_unique:
  "\<lbrakk> dsorted_by xs; dsorted_by ys; set xs = set ys; ys \<in> lists D \<rbrakk> \<Longrightarrow> xs = ys"
proof(induction xs arbitrary: ys)
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'" by(cases ys) auto
  with Cons.prems have xxs: "x \<in> D" "xs \<in> lists D" by auto
  have [simp]: "x = y"
  proof(cases "compare x y = LESS \<or> compare x y = GREATER")
    case True
    with \<open>set (x # xs) = set ys\<close> ys xxs 
    have "x \<in> set ys" "y \<in> set xs"
      by(auto 4 3 simp add: compare_refl dest: subsetD[where c=y] elim: equalityE)
    with \<open>dsorted_by ys\<close> ys xxs \<open>ys \<in> lists D\<close> True \<open>dsorted_by (x # xs)\<close>
    have False by(auto 4 3 simp add: dsorted_above_conv_dsorted_by compare_refl compare_eq_GREATER dest: compare_trans')
    thus ?thesis ..
  next
    case False
    hence "compare x y = EQUAL" by(cases "compare x y") simp_all
    thus "x = y" using xxs \<open>ys \<in> lists D\<close> ys by(auto dest: compare_eq_EQUALD)
  qed
  from xxs \<open>dsorted_by (x # xs)\<close> have "x \<notin> set xs"
    by(auto simp add: dsorted_above_conv_dsorted_by compare_refl)
  moreover from \<open>ys \<in> lists D\<close> ys \<open>dsorted_by ys\<close>
  have "y \<notin> set ys'" by(auto simp add: dsorted_above_conv_dsorted_by compare_refl)
  ultimately have "set xs = set ys'" using \<open>set (x # xs) = set ys\<close> ys by auto
  thus ?case using ys Cons.IH[of ys'] Cons.prems \<open>ys = y # ys'\<close> xxs
    by(simp add: dsorted_above_conv_dsorted_by)
qed simp


lemma assumes "finite A" "A \<subseteq> D"
  shows dsorted_by_sorted_list_of_set_by: "dsorted_by (sorted_list_of_set_by A)" (is ?thesis1)
  and set_sorted_list_of_set_by: "set (sorted_list_of_set_by A) = A" (is ?thesis2)
proof -
  from assms obtain xs where xs: "dsorted_by xs \<and> set xs = A"
    by(blast dest: finite_ex_dsorted_by)
  hence "?thesis1 \<and> ?thesis2"
    unfolding sorted_list_of_set_by_def
    by(rule theI)(insert assms xs, rule dsorted_by_unique, auto)
  thus ?thesis1 ?thesis2 by simp_all
qed

lemma sorted_list_of_set_by_in_lists:
  "\<lbrakk> finite A; A \<subseteq> D \<rbrakk> \<Longrightarrow> sorted_list_of_set_by A \<in> lists D"
by(auto simp add: in_lists_conv_set set_sorted_list_of_set_by)

lemma sorted_list_of_set_by_insert:
  "\<lbrakk> finite A; A \<subseteq> D; x \<in> D \<rbrakk>
  \<Longrightarrow> sorted_list_of_set_by (insert x A) = insort_by x (sorted_list_of_set_by A)"
by(rule dsorted_by_unique)(simp_all add: dsorted_by_insort_by dsorted_by_sorted_list_of_set_by set_insort_by sorted_list_of_set_by_in_lists set_sorted_list_of_set_by insort_by_in_lists)

lemma sorted_list_of_set_by_eq_Nil_iff [simp]:
  "\<lbrakk> finite A; A \<subseteq> D \<rbrakk> \<Longrightarrow> sorted_list_of_set_by A = [] \<longleftrightarrow> A = {}"
by(auto dest: arg_cong[where f=set] simp add: set_sorted_list_of_set_by)

end

end