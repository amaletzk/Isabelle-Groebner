(* Author: Florian Haftmann, TU Muenchen *)
(* Author: Andreas Lochbihler, ETH Zurich *)
(* Author: Alexander Maletzky, RISC Linz *)

section \<open>Associative Lists with Sorted Keys\<close>

theory OAlist
  imports Deriving.Comparator
begin

text \<open>We define the type of @{emph \<open>ordered associative lists\<close>} (oalist). An oalist is an associative
  list (i.\,e. a list of pairs) such that the keys are distinct and sorted wrt. some linear
  order relation, and no key is mapped to @{term 0}. The latter invariant allows to implement various
  functions operating on oalists more efficiently.

  The ordering of the keys in an oalist \<open>xs\<close> is encoded as an additional parameter of \<open>xs\<close>.
  This means that oalists may be ordered wrt. different orderings, even if they are of the same type.
  Operations operating on more than one oalists, like \<open>map2_val\<close>, typically ensure that the orderings
  of their arguments are identical by re-ordering one argument wrt. the order relation of the other.
  This, however, implies that equality of order relations must be effectively decidable if executable
  code is to be generated.\<close>

subsection \<open>Preliminaries\<close>

fun min_list_param :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "min_list_param rel (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> (let m = min_list_param rel xs in if rel x m then x else m))"

lemma min_list_param_in:
  assumes "xs \<noteq> []"
  shows "min_list_param rel xs \<in> set xs"
  using assms
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp add: min_list_param.simps[of rel x xs] Let_def del: min_list_param.simps set_simps(2) split: list.split,
        intro conjI impI allI, simp, simp)
    fix y ys
    assume xs: "xs = y # ys"
    have "min_list_param rel (y # ys) = min_list_param rel xs" by (simp only: xs)
    also have "... \<in> set xs" by (rule Cons(1), simp add: xs)
    also have "... \<subseteq> set (x # y # ys)" by (auto simp: xs)
    finally show "min_list_param rel (y # ys) \<in> set (x # y # ys)" .
  qed
qed

lemma min_list_param_minimal:
  assumes "transp rel" and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> rel x y \<or> rel y x"
    and "z \<in> set xs"
  shows "rel (min_list_param rel xs) z"
  using assms(2, 3)
proof (induct xs)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons x xs)
  from Cons(3) have disj1: "z = x \<or> z \<in> set xs" by simp
  have "x \<in> set (x # xs)" by simp
  hence disj2: "rel x z \<or> rel z x" using Cons(3) by (rule Cons(2))
  have *: "rel (min_list_param rel xs) z" if "z \<in> set xs" using _ that
  proof (rule Cons(1))
    fix a b
    assume "a \<in> set xs" and "b \<in> set xs"
    hence "a \<in> set (x # xs)" and "b \<in> set (x # xs)" by simp_all
    thus "rel a b \<or> rel b a" by (rule Cons(2))
  qed
  show ?case
  proof (simp add: min_list_param.simps[of rel x xs] Let_def del: min_list_param.simps set_simps(2) split: list.split,
        intro conjI impI allI)
    assume "xs = []"
    with disj1 disj2 show "rel x z" by simp
  next
    fix y ys
    assume "xs = y # ys" and "rel x (min_list_param rel (y # ys))"
    hence "rel x (min_list_param rel xs)" by simp
    from disj1 show "rel x z"
    proof
      assume "z = x"
      thus ?thesis using disj2 by simp
    next
      assume "z \<in> set xs"
      hence "rel (min_list_param rel xs) z" by (rule *)
      with assms(1) \<open>rel x (min_list_param rel xs)\<close> show ?thesis by (rule transpD)
    qed
  next
    fix y ys
    assume xs: "xs = y # ys" and "\<not> rel x (min_list_param rel (y # ys))"
    from disj1 show "rel (min_list_param rel (y # ys)) z"
    proof
      assume "z = x"
      have "min_list_param rel (y # ys) \<in> set (y # ys)" by (rule min_list_param_in, simp)
      hence "min_list_param rel (y # ys) \<in> set (x # xs)" by (simp add: xs)
      with \<open>x \<in> set (x # xs)\<close> have "rel x (min_list_param rel (y # ys)) \<or> rel (min_list_param rel (y # ys)) x"
        by (rule Cons(2))
      with \<open>\<not> rel x (min_list_param rel (y # ys))\<close> have "rel (min_list_param rel (y # ys)) x" by simp
      thus ?thesis by (simp only: \<open>z = x\<close>)
    next
      assume "z \<in> set xs"
      hence "rel (min_list_param rel xs) z" by (rule *)
      thus ?thesis by (simp only: xs)
    qed
  qed
qed

(*
subsection \<open>Syntactic Type Class for Default Elements\<close>

text \<open>We do not want to use the existing type-class @{class default}, but instead introduce a new one:\<close>

class oalist_dflt = fixes dflt::'a

simproc_setup reorient_dflt ("dflt = x") = Reorient_Proc.proc
*)

subsection \<open>Type \<open>key_order\<close>\<close>

typedef 'a key_order = "{compare :: 'a comparator. comparator compare}"
  morphisms key_compare Abs_key_order
proof -
  from well_order_on obtain r where "well_order_on (UNIV::'a set) r" ..
  hence "linear_order r" by (simp only: well_order_on_def)
  hence lin: "(x, y) \<in> r \<or> (y, x) \<in> r" for x y
    by (metis Diff_iff Linear_order_in_diff_Id UNIV_I \<open>well_order r\<close> well_order_on_Field)
  have antisym: "(x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> x = y" for x y
    by (meson \<open>linear_order r\<close> antisymD linear_order_on_def partial_order_on_def)
  have trans: "(x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r" for x y z
    by (meson \<open>linear_order r\<close> linear_order_on_def order_on_defs(1) partial_order_on_def trans_def)
  define comp where "comp = (\<lambda>x y. if (x, y) \<in> r then if (y, x) \<in> r then Eq else Lt else Gt)"
  show ?thesis
  proof (rule, simp)
    show "comparator comp"
    proof (standard, simp_all add: comp_def split: if_splits, intro impI)
      fix x y
      assume "(x, y) \<in> r" and "(y, x) \<in> r"
      thus "x = y" by (rule antisym)
    next
      fix x y
      assume "(x, y) \<notin> r"
      with lin show "(y, x) \<in> r" by blast
    next
      fix x y z
      assume "(y, x) \<notin> r" and "(z, y) \<notin> r"
      assume "(x, y) \<in> r" and "(y, z) \<in> r"
      hence "(x, z) \<in> r" by (rule trans)
      moreover have "(z, x) \<notin> r"
      proof
        assume "(z, x) \<in> r"
        with \<open>(x, z) \<in> r\<close> have "x = z" by (rule antisym)
        from \<open>(z, y) \<notin> r\<close> \<open>(x, y) \<in> r\<close> show False unfolding \<open>x = z\<close> ..
      qed
      ultimately show "(z, x) \<notin> r \<and> ((z, x) \<notin> r \<longrightarrow> (x, z) \<in> r)" by simp
    qed
  qed
qed

lemma comparator_key_compare [simp, intro!]: "comparator (key_compare ko)"
  using key_compare[of ko] by simp

instantiation key_order :: (type) equal
begin
  definition equal_key_order :: "'a key_order \<Rightarrow> 'a key_order \<Rightarrow> bool" where "equal_key_order = (=)"
  instance by (standard, simp add: equal_key_order_def)
end

setup_lifting type_definition_key_order

instantiation key_order :: (type) uminus
begin

lift_definition uminus_key_order :: "'a key_order \<Rightarrow> 'a key_order" is "\<lambda>c x y. invert_order (c x y)"
proof -
  fix comp::"'a comparator"
  assume "comparator comp"
  then interpret comp: comparator comp .
  show "comparator (\<lambda>x y. invert_order (comp x y))"
  proof
    fix x y
    assume "invert_order (comp x y) = Eq"
    thus "x = y" using comp.sym comp.weak_eq by auto
  next
    fix x y
    show "invert_order (invert_order (comp x y)) = invert_order (comp y x)" by (simp add: comp.sym)
  next
    fix x y z
    assume "invert_order (comp x y) = Lt" and "invert_order (comp y z) = Lt"
    hence "comp z y = Lt" and "comp y x = Lt" by (simp_all add: comp.sym)
    hence "comp z x = Lt" by (rule comp.trans)
    thus "invert_order (comp x z) = Lt" by (simp only: comp.sym)
  qed
qed

instance ..

end

lift_definition le_of_key_order :: "'a key_order \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" is "\<lambda>cmp. le_of_comp cmp" .

lift_definition lt_of_key_order :: "'a key_order \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" is "\<lambda>cmp. lt_of_comp cmp" .

definition key_order_of_ord :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a key_order"
  where "key_order_of_ord ord = Abs_key_order (comp_of_ords ord (\<lambda>x y. ord x y \<and> \<not> ord y x))"

lift_definition key_order_of_le :: "'a::linorder key_order" is comparator_of
  by (fact comparator_of)

interpretation key_order_lin: linorder "le_of_key_order ko" "lt_of_key_order ko"
proof transfer
  fix comp::"'a comparator"
  assume "comparator comp"
  then interpret comp: comparator comp .
  show "class.linorder comp.le comp.lt" by (fact comp.linorder)
qed

lemma le_of_key_order_alt: "le_of_key_order ko x y = (key_compare ko x y \<noteq> Gt)"
  by (transfer, simp add: comparator.nGt_le_conv)

lemma lt_of_key_order_alt: "lt_of_key_order ko x y = (key_compare ko x y = Lt)"
  by (transfer, meson comparator.Lt_lt_conv)

lemma key_compare_Gt: "key_compare ko x y = Gt \<longleftrightarrow> key_compare ko y x = Lt"
  by (transfer, meson comparator.nGt_le_conv comparator.nLt_le_conv)

lemma key_compare_Eq: "key_compare ko x y = Eq \<longleftrightarrow> x = y"
  by (transfer, simp add: comparator.eq)

lemma key_compare_same [simp]: "key_compare ko x x = Eq"
  by (simp add: key_compare_Eq)

lemma uminus_key_compare [simp]: "invert_order (key_compare ko x y) = key_compare ko y x"
  by (transfer, simp add: comparator.sym)

lemma key_compare_uminus [simp]: "key_compare (- ko) x y = key_compare ko y x"
proof -
  have "key_compare (- ko) x y = invert_order (key_compare ko x y)" by (transfer, rule refl)
  also have "... = key_compare ko y x" by simp
  finally show ?thesis .
qed

lemma uminus_key_order_sameD:
  assumes "- ko = (ko::'a key_order)"
  shows "x = (y::'a)"
proof (rule ccontr)
  assume "x \<noteq> y"
  hence "key_compare ko x y \<noteq> Eq" by (simp add: key_compare_Eq)
  hence "key_compare ko x y \<noteq> invert_order (key_compare ko x y)"
    by (metis invert_order.elims order.distinct(5))
  also have "invert_order (key_compare ko x y) = key_compare (- ko) x y" by simp
  finally have "- ko \<noteq> ko" by (auto simp del: key_compare_uminus)
  thus False using assms ..
qed

lemma key_compare_key_order_of_ord:
  assumes "antisymp ord" and "transp ord" and "\<And>x y. ord x y \<or> ord y x"
  shows "key_compare (key_order_of_ord ord) = (\<lambda>x y. if ord x y then if x = y then Eq else Lt else Gt)"
proof -
  have eq: "key_compare (key_order_of_ord ord) = comp_of_ords ord (\<lambda>x y. ord x y \<and> \<not> ord y x)"
    unfolding key_order_of_ord_def
  proof (rule Abs_key_order_inverse, simp, rule comp_of_ords, unfold_locales)
    fix x
    from assms(3) show "ord x x" by blast
  next
    fix x y z
    assume "ord x y" and "ord y z"
    with assms(2) show "ord x z" by (rule transpD)
  next
    fix x y
    assume "ord x y" and "ord y x"
    with assms(1) show "x = y" by (rule antisympD)
  qed (rule refl, rule assms(3))
  have *: "x = y" if "ord x y" and "ord y x" for x y using assms(1) that by (rule antisympD)
  show ?thesis by (rule, rule, auto simp: eq comp_of_ords_def intro: *)
qed

lemma key_compare_key_order_of_le:
  "key_compare key_order_of_le = (\<lambda>x y. if x < y then Lt else if x = y then Eq else Gt)"
  by (transfer, intro ext, fact comparator_of_def)

subsection \<open>Invariant\<close>

definition oalist_inv :: "(('a \<times> 'b::zero) list \<times> ('a key_order)) \<Rightarrow> bool"
  where "oalist_inv xs \<longleftrightarrow> (0 \<notin> snd ` set (fst xs) \<and> sorted_wrt (lt_of_key_order (snd xs)) (map fst (fst xs)))"

lemma oalist_invI:
  assumes "0 \<notin> snd ` set xs" and "sorted_wrt (lt_of_key_order ko) (map fst xs)"
  shows "oalist_inv (xs, ko)"
  unfolding oalist_inv_def using assms unfolding fst_conv snd_conv by blast

lemma oalist_invD1:
  assumes "oalist_inv (xs, ko)"
  shows "0 \<notin> snd ` set xs"
  using assms unfolding oalist_inv_def fst_conv by blast

lemma oalist_invD2:
  assumes "oalist_inv (xs, ko)"
  shows "sorted_wrt (lt_of_key_order ko) (map fst xs)"
  using assms unfolding oalist_inv_def fst_conv snd_conv by blast

lemma oalist_inv_Nil: "oalist_inv ([], ko)"
  by (simp add: oalist_inv_def)

lemma oalist_inv_singleton: "oalist_inv ([(k, v)], ko) \<longleftrightarrow> (v \<noteq> 0)"
  by (auto simp: oalist_inv_def)

lemma oalist_inv_ConsI:
  assumes "oalist_inv (xs, ko)" and "v \<noteq> 0" and "xs \<noteq> [] \<Longrightarrow> lt_of_key_order ko k (fst (hd xs))"
  shows "oalist_inv ((k, v) # xs, ko)"
proof (rule oalist_invI)
  from assms(1) have "0 \<notin> snd ` set xs" by (rule oalist_invD1)
  with assms(2) show "0 \<notin> snd ` set ((k, v) # xs)" by simp
next
  show "sorted_wrt (lt_of_key_order ko) (map fst ((k, v) # xs))"
  proof (cases "xs = []")
    case True
    thus ?thesis by simp
  next
    case False
    then obtain k' v' xs' where xs: "xs = (k', v') # xs'" by (metis list.exhaust prod.exhaust)
    from assms(3)[OF False] have "lt_of_key_order ko k k'" by (simp add: xs)
    moreover from assms(1) have "sorted_wrt (lt_of_key_order ko) (map fst xs)" by (rule oalist_invD2)
    ultimately show "sorted_wrt (lt_of_key_order ko) (map fst ((k, v) # xs))"
      by (simp add: xs sorted_wrt2[OF key_order_lin.transp_less] del: sorted_wrt.simps)
  qed
qed

lemma oalist_inv_ConsD1:
  assumes "oalist_inv (x # xs, ko)"
  shows "oalist_inv (xs, ko)"
proof (rule oalist_invI)
  from assms have "0 \<notin> snd ` set (x # xs)" by (rule oalist_invD1)
  thus "0 \<notin> snd ` set xs" by simp
next
  from assms have "sorted_wrt (lt_of_key_order ko) (map fst (x # xs))" by (rule oalist_invD2)
  thus "sorted_wrt (lt_of_key_order ko) (map fst xs)" by simp
qed

lemma oalist_inv_ConsD2:
  assumes "oalist_inv ((k, v) # xs, ko)"
  shows "v \<noteq> 0"
proof -
  from assms have "0 \<notin> snd ` set ((k, v) # xs)" by (rule oalist_invD1)
  thus ?thesis by auto
qed

lemma oalist_inv_ConsD3:
  assumes "oalist_inv ((k, v) # xs, ko)" and "k' \<in> fst ` set xs"
  shows "lt_of_key_order ko k k'"
proof -
  from assms(2) obtain x where "x \<in> set xs" and "k' = fst x" by fastforce
  from assms(1) have "sorted_wrt (lt_of_key_order ko) (map fst ((k, v) # xs))" by (rule oalist_invD2)
  hence "\<forall>x\<in>set xs. lt_of_key_order ko k (fst x)" by simp
  hence "lt_of_key_order ko k (fst x)" using \<open>x \<in> set xs\<close> ..
  thus ?thesis by (simp only: \<open>k' = fst x\<close>)
qed

lemma oalist_inv_tl:
  assumes "oalist_inv (xs, ko)"
  shows "oalist_inv (tl xs, ko)"
proof (rule oalist_invI)
  from assms have "0 \<notin> snd ` set xs" by (rule oalist_invD1)
  thus "0 \<notin> snd ` set (tl xs)" by (metis (no_types, lifting) image_iff list.set_sel(2) tl_Nil)
next
  show "sorted_wrt (lt_of_key_order ko) (map fst (tl xs))"
    by (metis hd_Cons_tl oalist_invD2 oalist_inv_ConsD1 assms tl_Nil)
qed

lemma oalist_inv_filter:
  assumes "oalist_inv (xs, ko)"
  shows "oalist_inv (filter P xs, ko)"
proof (rule oalist_invI)
  from assms have "0 \<notin> snd ` set xs" by (rule oalist_invD1)
  thus "0 \<notin> snd ` set (filter P xs)" by auto
next
  from assms have "sorted_wrt (lt_of_key_order ko) (map fst xs)" by (rule oalist_invD2)
  thus "sorted_wrt (lt_of_key_order ko) (map fst (filter P xs))" by (induct xs, simp, simp)
qed

lemma oalist_inv_map:
  assumes "oalist_inv (xs, ko)"
    and "\<And>a. snd (f a) = 0 \<Longrightarrow> snd a = 0"
    and "\<And>a b. key_compare ko (fst (f a)) (fst (f b)) = key_compare ko (fst a) (fst b)"
  shows "oalist_inv (map f xs, ko)"
proof (rule oalist_invI)
  show "0 \<notin> snd ` set (map f xs)"
  proof (simp, rule)
    assume "0 \<in> snd ` f ` set xs"
    then obtain a where "a \<in> set xs" and "snd (f a) = 0" by fastforce
    from this(2) have "snd a = 0" by (rule assms(2))
    from assms(1) have "0 \<notin> snd ` set xs" by (rule oalist_invD1)
    moreover from \<open>a \<in> set xs\<close> have "0 \<in> snd ` set xs" by (simp add: \<open>snd a = 0\<close>[symmetric])
    ultimately show False ..
  qed
next
  from assms(1) have "sorted_wrt (lt_of_key_order ko) (map fst xs)" by (rule oalist_invD2)
  hence "sorted_wrt (\<lambda>x y. key_compare ko (fst x) (fst y) = Lt) xs"
    by (simp only: sorted_wrt_map lt_of_key_order_alt)
  thus "sorted_wrt (lt_of_key_order ko) (map fst (map f xs))"
    by (simp add: sorted_wrt_map lt_of_key_order_alt assms(3))
qed

lemma oalist_inv_induct [consumes 1, case_names Nil Cons]:
  assumes "oalist_inv (xs, ko)"
  assumes "P []"
  assumes "\<And>k v xs. oalist_inv ((k, v) # xs, ko) \<Longrightarrow> oalist_inv (xs, ko) \<Longrightarrow> v \<noteq> 0 \<Longrightarrow>
              (\<And>k'. k' \<in> fst ` set xs \<Longrightarrow> lt_of_key_order ko k k') \<Longrightarrow> P xs \<Longrightarrow> P ((k, v) # xs)"
  shows "P xs"
  using assms(1)
proof (induct xs)
  case Nil
  from assms(2) show ?case .
next
  case (Cons x xs)
  obtain k v where x: "x = (k, v)" by fastforce
  from Cons(2) have "oalist_inv ((k, v) # xs, ko)" and "oalist_inv (xs, ko)" and "v \<noteq> 0" unfolding x
    by (this, rule oalist_inv_ConsD1, rule oalist_inv_ConsD2)
  moreover from Cons(2) have "lt_of_key_order ko k k'" if "k' \<in> fst ` set xs" for k' using that
    unfolding x by (rule oalist_inv_ConsD3)
  moreover from \<open>oalist_inv (xs, ko)\<close> have "P xs" by (rule Cons(1))
  ultimately show ?case unfolding x by (rule assms(3))
qed

subsection \<open>Operations on Lists of Pairs\<close>

type_synonym ('a, 'b) comp_opt = "'a \<Rightarrow> 'b \<Rightarrow> (order option)"

context fixes ko :: "'a key_order"
begin

fun lookup_pair :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b::zero"
where
  "lookup_pair [] x = 0"|
  "lookup_pair ((k, v) # xs) x =
    (case key_compare ko x k of
       Lt \<Rightarrow> 0
     | Eq \<Rightarrow> v
     | Gt \<Rightarrow> lookup_pair xs x)"

fun update_by_pair :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "update_by_pair (k, v) [] = (if v = 0 then [] else [(k, v)])"
| "update_by_pair (k, v) ((k', v') # xs) =
  (case key_compare ko k k' of Lt \<Rightarrow> (if v = 0 then (k', v') # xs else (k, v) # (k', v') # xs)
                     | Eq \<Rightarrow> (if v = 0 then xs else (k, v) # xs)
                   | Gt \<Rightarrow> (k', v') # update_by_pair (k, v) xs)"

(* TODO: Add update_by_gr_pair. *)

definition sort_oalist :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
  where "sort_oalist xs = foldr update_by_pair xs []"

fun update_by_fun_pair :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "update_by_fun_pair k f [] = (let v = f 0 in if v = 0 then [] else [(k, v)])"
| "update_by_fun_pair k f ((k', v') # xs) =
  (case key_compare ko k k' of Lt \<Rightarrow> (let v = f 0 in if v = 0 then (k', v') # xs else (k, v) # (k', v') # xs)
                     | Eq \<Rightarrow> (let v = f v' in if v = 0 then xs else (k, v) # xs)
                   | Gt \<Rightarrow> (k', v') # update_by_fun_pair k f xs)"

definition update_by_fun_gr_pair :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
  where "update_by_fun_gr_pair k f xs =
          (if xs = [] then
            (let v = f 0 in if v = 0 then [] else [(k, v)])
          else if key_compare ko k (fst (last xs)) = Gt then
            (let v = f 0 in if v = 0 then xs else xs @ [(k, v)])
          else
            update_by_fun_pair k f xs
          )"

fun map_pair :: "(('a \<times> 'b) \<Rightarrow> ('a \<times> 'c)) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list"
where
  "map_pair f [] = []"
| "map_pair f (kv # xs) =
    (let (k, v) = f kv; aux = map_pair f xs in if v = 0 then aux else (k, v) # aux)"

text \<open>The difference between @{const List.map} and @{const map_pair} is that the latter removes
  @{term 0} values, whereas the former does not.\<close>

abbreviation map_val_pair :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list"
  where "map_val_pair f \<equiv> map_pair (\<lambda>(k, v). (k, f k v))"

fun map2_val_pair :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a key_order \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'd) list) \<Rightarrow> ('a key_order \<Rightarrow> ('a \<times> 'c) list \<Rightarrow> ('a \<times> 'd) list) \<Rightarrow>
                     ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list \<Rightarrow> ('a \<times> 'd::zero) list"
where
  "map2_val_pair f g h xs [] = g ko xs"
| "map2_val_pair f g h [] ys = h ko ys"
| "map2_val_pair f g h ((kx, vx) # xs) ((ky, vy) # ys) =
    (case key_compare ko kx ky of
             Lt    \<Rightarrow> (let v = f kx vx 0; aux = map2_val_pair f g h xs ((ky, vy) # ys) in if v = 0 then aux else (kx, v) # aux)
           | Eq   \<Rightarrow> (let v = f kx vx vy; aux = map2_val_pair f g h xs ys in if v = 0 then aux else (kx, v) # aux)
           | Gt \<Rightarrow> (let v = f ky 0 vy; aux = map2_val_pair f g h ((kx, vx) # xs) ys in if v = 0 then aux else (ky, v) # aux))"

fun lex_ord_pair :: "('a \<Rightarrow> (('b, 'c) comp_opt)) \<Rightarrow> (('a \<times> 'b::zero) list, ('a \<times> 'c::zero) list) comp_opt"
where
  "lex_ord_pair f []       []       = Some Eq"|
  "lex_ord_pair f []       ((ky, vy) # ys) =
    (let aux = f ky 0 vy in if aux = Some Eq then lex_ord_pair f [] ys else aux)"|
  "lex_ord_pair f ((kx, vx) # xs) []       =
    (let aux = f kx vx 0 in if aux = Some Eq then lex_ord_pair f xs [] else aux)"|
  "lex_ord_pair f ((kx, vx) # xs) ((ky, vy) # ys) =
    (case key_compare ko kx ky of
             Lt    \<Rightarrow> (let aux = f kx vx 0 in if aux = Some Eq then lex_ord_pair f xs ((ky, vy) # ys) else aux)
           | Eq   \<Rightarrow> (let aux = f kx vx vy in if aux = Some Eq then lex_ord_pair f xs ys else aux)
           | Gt \<Rightarrow> (let aux = f ky 0 vy in if aux = Some Eq then lex_ord_pair f ((kx, vx) # xs) ys else aux))"

fun prod_ord_pair :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list \<Rightarrow> bool"
where
  "prod_ord_pair f []       []       = True"|
  "prod_ord_pair f []       ((ky, vy) # ys) = (f ky 0 vy \<and> prod_ord_pair f [] ys)"|
  "prod_ord_pair f ((kx, vx) # xs) []       = (f kx vx 0 \<and> prod_ord_pair f xs [])"|
  "prod_ord_pair f ((kx, vx) # xs) ((ky, vy) # ys) =
    (case key_compare ko kx ky of
             Lt    \<Rightarrow> (f kx vx 0 \<and> prod_ord_pair f xs ((ky, vy) # ys))
           | Eq   \<Rightarrow> (f kx vx vy \<and> prod_ord_pair f xs ys)
           | Gt \<Rightarrow> (f ky 0 vy \<and> prod_ord_pair f ((kx, vx) # xs) ys))"

text \<open>@{const prod_ord_pair} is actually just a special case of @{const lex_ord_pair}, as proved below
  in lemma ``prod_ord_pair_eq_lex_ord_pair''.\<close>

subsubsection \<open>@{const lookup_pair}\<close>

lemma lookup_pair_eq_0:
  assumes "oalist_inv (xs, ko)"
  shows "lookup_pair xs k = 0 \<longleftrightarrow> (k \<notin> fst ` set xs)"
  using assms
proof (induct xs rule: oalist_inv_induct)
  case Nil
  show ?case by simp
next
  case (Cons k' v' xs)
  show ?case
  proof (simp add: Cons(3) key_compare_Eq split: order.splits, rule, simp_all only: atomize_imp[symmetric])
    assume "key_compare ko k k' = Lt"
    hence "k \<noteq> k'" by auto
    moreover have "k \<notin> fst ` set xs"
    proof
      assume "k \<in> fst ` set xs"
      hence "lt_of_key_order ko k' k" by (rule Cons(4))
      with \<open>key_compare ko k k' = Lt\<close> show False by (simp add: lt_of_key_order_alt[symmetric])
    qed
    ultimately show "k \<noteq> k' \<and> k \<notin> fst ` set xs" ..
  next
    assume "key_compare ko k k' = Gt"
    hence "k \<noteq> k'" by auto
    thus "(local.lookup_pair xs k = 0) = (k \<noteq> k' \<and> k \<notin> fst ` set xs)" by (simp add: Cons(5))
  qed
qed

lemma lookup_pair_eq_value:
  assumes "oalist_inv (xs, ko)" and "v \<noteq> 0"
  shows "lookup_pair xs k = v \<longleftrightarrow> ((k, v) \<in> set xs)"
  using assms(1)
proof (induct xs rule: oalist_inv_induct)
  case Nil
  from assms(2) show ?case by simp
next
  case (Cons k' v' xs)
  have *: "(k', u) \<notin> set xs" for u
  proof
    assume "(k', u) \<in> set xs"
    hence "fst (k', u) \<in> fst ` set xs" by fastforce
    hence "k' \<in> fst ` set xs" by simp
    hence "lt_of_key_order ko k' k'" by (rule Cons(4))
    thus False by (simp add: lt_of_key_order_alt[symmetric])
  qed
  show ?case
  proof (simp add: assms(2) Cons(5) key_compare_Eq split: order.split, intro conjI impI)
    assume "key_compare ko k k' = Lt"
    show "(k, v) \<notin> set xs"
    proof
      assume "(k, v) \<in> set xs"
      hence "fst (k, v) \<in> fst ` set xs" by fastforce
      hence "k \<in> fst ` set xs" by simp
      hence "lt_of_key_order ko k' k" by (rule Cons(4))
      with \<open>key_compare ko k k' = Lt\<close> show False by (simp add: lt_of_key_order_alt[symmetric])
    qed
  qed (auto simp: *)
qed

lemma lookup_pair_eq_valueI:
  assumes "oalist_inv (xs, ko)" and "(k, v) \<in> set xs"
  shows "lookup_pair xs k = v"
proof -
  from assms(2) have "v \<in> snd ` set xs" by force
  moreover from assms(1) have "0 \<notin> snd ` set xs" by (rule oalist_invD1)
  ultimately have "v \<noteq> 0" by blast
  with assms show ?thesis by (simp add: lookup_pair_eq_value)
qed

lemma lookup_pair_inj:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)" and "lookup_pair xs = lookup_pair ys"
  shows "xs = ys"
  using assms
proof (induct xs arbitrary: ys rule: oalist_inv_induct)
  case Nil
  thus ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k' v' ys)
    have "v' = lookup_pair ((k', v') # ys) k'" by simp
    also have "... = lookup_pair [] k'" by (simp only: Cons(6))
    also have "... = 0" by simp
    finally have "v' = 0" .
    with Cons(3) show ?case ..
  qed
next
  case *: (Cons k v xs)
  from *(6, 7) show ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    have "v = lookup_pair ((k, v) # xs) k" by simp
    also have "... = lookup_pair [] k" by (simp only: Nil)
    also have "... = 0" by simp
    finally have "v = 0" .
    with *(3) show ?case ..
  next
    case (Cons k' v' ys)
    show ?case
    proof (cases "key_compare ko k k'")
      case Lt
      hence "\<not> lt_of_key_order ko k' k" by (simp add: lt_of_key_order_alt[symmetric])
      with Cons(4) have "k \<notin> fst ` set ys" by blast
      moreover from Lt have "k \<noteq> k'" by auto
      ultimately have "k \<notin> fst ` set ((k', v') # ys)" by simp
      hence "0 = lookup_pair ((k', v') # ys) k"
        by (simp add: lookup_pair_eq_0[OF Cons(1)] del: lookup_pair.simps)
      also have "... = lookup_pair ((k, v) # xs) k" by (simp only: Cons(6))
      also have "... = v" by simp
      finally have "v = 0" by simp
      with *(3) show ?thesis ..
    next
      case Eq
      hence "k' = k" by (simp only: key_compare_Eq)
      have "v' = lookup_pair ((k', v') # ys) k'" by simp
      also have "... = lookup_pair ((k, v) # xs) k" by (simp only: Cons(6) \<open>k' = k\<close>)
      also have "... = v" by simp
      finally have "v' = v" .
      moreover note \<open>k' = k\<close>
      moreover from Cons(2) have "xs = ys"
      proof (rule *(5))
        show "lookup_pair xs = lookup_pair ys"
        proof
          fix k0
          show "lookup_pair xs k0 = lookup_pair ys k0"
          proof (cases "lt_of_key_order ko k k0")
            case True
            hence eq: "key_compare ko k0 k = Gt"
              by (simp add: key_compare_Gt lt_of_key_order_alt)
            have "lookup_pair xs k0 = lookup_pair ((k, v) # xs) k0" by (simp add: eq)
            also have "... = lookup_pair ((k, v') # ys) k0" by (simp only: Cons(6) \<open>k' = k\<close>)
            also have "... = lookup_pair ys k0" by (simp add: eq)
            finally show ?thesis .
          next
            case False
            with *(4) have "k0 \<notin> fst ` set xs" by blast
            with *(2) have eq: "lookup_pair xs k0 = 0" by (simp add: lookup_pair_eq_0)
            from False Cons(4) have "k0 \<notin> fst ` set ys" unfolding \<open>k' = k\<close> by blast
            with Cons(2) have "lookup_pair ys k0 = 0" by (simp add: lookup_pair_eq_0)
            with eq show ?thesis by simp
          qed
        qed
      qed
      ultimately show ?thesis by simp
    next
      case Gt
      hence "\<not> lt_of_key_order ko k k'" by (simp add: key_compare_Gt lt_of_key_order_alt[symmetric])
      with *(4) have "k' \<notin> fst ` set xs" by blast
      moreover from Gt have "k' \<noteq> k" by auto
      ultimately have "k' \<notin> fst ` set ((k, v) # xs)" by simp
      hence "0 = lookup_pair ((k, v) # xs) k'"
        by (simp add: lookup_pair_eq_0[OF *(1)] del: lookup_pair.simps)
      also have "... = lookup_pair ((k', v') # ys) k'" by (simp only: Cons(6))
      also have "... = v'" by simp
      finally have "v' = 0" by simp
      with Cons(3) show ?thesis ..
    qed
  qed
qed

lemma lookup_pair_tl:
  assumes "oalist_inv (xs, ko)"
  shows "lookup_pair (tl xs) k =
          (if (\<forall>k'\<in>fst ` set xs. le_of_key_order ko k k') then 0 else lookup_pair xs k)"
proof -
  from assms have 1: "oalist_inv (tl xs, ko)" by (rule oalist_inv_tl)
  show ?thesis
  proof (split if_split, intro conjI impI)
    assume *: "\<forall>x\<in>fst ` set xs. le_of_key_order ko k x"
    show "lookup_pair (tl xs) k = 0"
    proof (simp add: lookup_pair_eq_0[OF 1], rule)
      assume k_in: "k \<in> fst ` set (tl xs)"
      hence "xs \<noteq> []" by auto
      then obtain k' v' ys where xs: "xs = (k', v') # ys" using prod.exhaust list.exhaust by metis
      have "k' \<in> fst ` set xs" unfolding xs by fastforce
      with * have "le_of_key_order ko k k'" ..
      from assms have "oalist_inv ((k', v') # ys, ko)" by (simp only: xs)
      moreover from k_in have "k \<in> fst ` set ys" by (simp add: xs)
      ultimately have "lt_of_key_order ko k' k" by (rule oalist_inv_ConsD3)
      with \<open>le_of_key_order ko k k'\<close> show False by simp
    qed
  next
    assume "\<not> (\<forall>k'\<in>fst ` set xs. le_of_key_order ko k k')"
    hence "\<exists>x\<in>fst ` set xs. \<not> le_of_key_order ko k x" by simp
    then obtain k'' where k''_in: "k'' \<in> fst ` set xs" and "\<not> le_of_key_order ko k k''" ..
    from this(2) have "lt_of_key_order ko k'' k" by simp
    from k''_in have "xs \<noteq> []" by auto
    then obtain k' v' ys where xs: "xs = (k', v') # ys" using prod.exhaust list.exhaust by metis
    from k''_in have "k'' = k' \<or> k'' \<in> fst ` set ys" by (simp add: xs)
    hence "lt_of_key_order ko k' k"
    proof
      assume "k'' = k'"
      with \<open>lt_of_key_order ko k'' k\<close> show ?thesis by simp
    next
      from assms have "oalist_inv ((k', v') # ys, ko)" by (simp only: xs)
      moreover assume "k'' \<in> fst ` set ys"
      ultimately have "lt_of_key_order ko k' k''" by (rule oalist_inv_ConsD3)
      thus ?thesis using \<open>lt_of_key_order ko k'' k\<close> by (rule key_order_lin.less_trans)
    qed
    hence "key_compare ko k k' = Gt" by (simp add: key_compare_Gt lt_of_key_order_alt)
    thus "lookup_pair (tl xs) k = lookup_pair xs k" by (simp add: xs lt_of_key_order_alt)
  qed
qed

lemma lookup_pair_filter:
  assumes "oalist_inv (xs, ko)"
  shows "lookup_pair (filter P xs) k = (let v = lookup_pair xs k in if P (k, v) then v else 0)"
  using assms
proof (induct xs rule: oalist_inv_induct)
  case Nil
  show ?case by simp
next
  case (Cons k' v' xs)
  show ?case
  proof (simp add: Cons(5) Let_def key_compare_Eq split: order.split, intro conjI impI)
    show "lookup_pair xs k' = 0"
    proof (simp add: lookup_pair_eq_0 Cons(2), rule)
      assume "k' \<in> fst ` set xs"
      hence "lt_of_key_order ko k' k'" by (rule Cons(4))
      thus False by simp
    qed
  next
    assume "key_compare ko k k' = Lt"
    hence "lt_of_key_order ko k k'" by (simp only: lt_of_key_order_alt)
    show "lookup_pair xs k = 0"
    proof (simp add: lookup_pair_eq_0 Cons(2), rule)
      assume "k \<in> fst ` set xs"
      hence "lt_of_key_order ko k' k" by (rule Cons(4))
      with \<open>lt_of_key_order ko k k'\<close> show False by simp
    qed
  qed
qed

lemma lookup_pair_map:
  assumes "oalist_inv (xs, ko)"
    and "\<And>k'. snd (f (k', 0)) = 0"
    and "\<And>a b. key_compare ko (fst (f a)) (fst (f b)) = key_compare ko (fst a) (fst b)"
  shows "lookup_pair (map f xs) (fst (f (k, v))) = snd (f (k, lookup_pair xs k))"
  using assms(1)
proof (induct xs rule: oalist_inv_induct)
  case Nil
  show ?case by (simp add: assms(2))
next
  case (Cons k' v' xs)
  obtain k'' v'' where f: "f (k', v') = (k'', v'')" by fastforce
  have "key_compare ko k k' = key_compare ko (fst (f (k, v))) (fst (f (k', v')))"
    by (simp add: assms(3))
  also have "... = key_compare ko (fst (f (k, v))) k''" by (simp add: f)
  finally have eq: "key_compare ko k k' = key_compare ko (fst (f (k, v))) k''" .
  show ?case
  proof (simp add: assms(2) split: order.split, intro conjI impI, simp add: key_compare_Eq)
    assume "k = k'"
    hence "lookup_pair (f (k', v') # map f xs) (fst (f (k', v))) =
            lookup_pair (f (k', v') # map f xs) (fst (f (k, v)))" by simp
    also have "... = snd (f (k', v'))" by (simp add: f eq[symmetric], simp add: \<open>k = k'\<close>)
    finally show "lookup_pair (f (k', v') # map f xs) (fst (f (k', v))) = snd (f (k', v'))" .
  qed (simp_all add: f eq Cons(5))
qed

lemma lookup_pair_Cons:
  assumes "oalist_inv ((k, v) # xs, ko)"
  shows "lookup_pair ((k, v) # xs) k0 = (if k = k0 then v else lookup_pair xs k0)"
proof (simp add: key_compare_Eq split: order.split, intro impI)
  assume "key_compare ko k0 k = Lt"
  from assms have inv: "oalist_inv (xs, ko)" by (rule oalist_inv_ConsD1)
  show "lookup_pair xs k0 = 0"
  proof (simp only: lookup_pair_eq_0[OF inv], rule)
    assume "k0 \<in> fst ` set xs"
    with assms have "lt_of_key_order ko k k0" by (rule oalist_inv_ConsD3)
    with \<open>key_compare ko k0 k = Lt\<close> show False by (simp add: lt_of_key_order_alt[symmetric])
  qed
qed

subsubsection \<open>@{const update_by_pair}\<close>

lemma set_update_by_pair_subset: "set (update_by_pair kv xs) \<subseteq> insert kv (set xs)"
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  have 1: "set xs \<subseteq> insert a (insert b (set xs))" for a b by auto
  have 2: "set (update_by_pair kv xs) \<subseteq> insert kv (insert (k', v') (set xs))" for kv
    using Cons by blast
  show ?case by (simp add: x kv 1 2 split: order.split)
qed

lemma update_by_pair_sorted:
  assumes "sorted_wrt (lt_of_key_order ko) (map fst xs)"
  shows "sorted_wrt (lt_of_key_order ko) (map fst (update_by_pair kv xs))"
  using assms
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  from Cons(2) have 1: "sorted_wrt (lt_of_key_order ko) (k' # (map fst xs))" by (simp add: x)
  hence 2: "sorted_wrt (lt_of_key_order ko) (map fst xs)" using sorted_wrt.elims(3) by fastforce
  hence 3: "sorted_wrt (lt_of_key_order ko) (map fst (update_by_pair (k, u) xs))" for u by (rule Cons(1))
  have 4: "sorted_wrt (lt_of_key_order ko) (k' # map fst (update_by_pair (k, u) xs))"
    if *: "key_compare ko k k' = Gt" for u
  proof (simp, intro conjI ballI)
    fix y
    assume "y \<in> set (update_by_pair (k, u) xs)"
    also from set_update_by_pair_subset have "... \<subseteq> insert (k, u) (set xs)" .
    finally have "y = (k, u) \<or> y \<in> set xs" by simp
    thus "lt_of_key_order ko k' (fst y)"
    proof
      assume "y = (k, u)"
      hence "fst y = k" by simp
      with * show ?thesis by (simp only: lt_of_key_order_alt key_compare_Gt)
    next
      from 1 have 5: "\<forall>y \<in> fst ` set xs. lt_of_key_order ko k' y" by simp
      assume "y \<in> set xs"
      hence "fst y \<in> fst ` set xs" by simp
      with 5 show ?thesis ..
    qed
  qed (fact 3)
  show ?case
    by (simp add: kv x 1 2 4 sorted_wrt2[OF key_order_lin.transp_less] split: order.split del: sorted_wrt.simps,
        intro conjI impI, simp add: 1 key_compare_Eq del: sorted_wrt.simps, simp add: lt_of_key_order_alt)
qed

lemma update_by_pair_not_0:
  assumes "0 \<notin> snd ` set xs"
  shows "0 \<notin> snd ` set (update_by_pair kv xs)"
  using assms
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  from Cons(2) have 1: "v' \<noteq> 0" and 2: "0 \<notin> snd ` set xs" by (auto simp: x)
  from 2 have 3: "0 \<notin> snd ` set (update_by_pair (k, u) xs)" for u by (rule Cons(1))
  show ?case by (auto simp: kv x 1 2 3 split: order.split)
qed

corollary oalist_inv_update_by_pair:
  assumes "oalist_inv (xs, ko)"
  shows "oalist_inv (update_by_pair kv xs, ko)"
proof (rule oalist_invI)
  from assms have "0 \<notin> snd ` set xs" by (rule oalist_invD1)
  thus "0 \<notin> snd ` set (update_by_pair kv xs)" by (rule update_by_pair_not_0)
next
  from assms have "sorted_wrt (lt_of_key_order ko) (map fst xs)" by (rule oalist_invD2)
  thus "sorted_wrt (lt_of_key_order ko) (map fst (update_by_pair kv xs))" by (rule update_by_pair_sorted)
qed

lemma update_by_pair_less:
  assumes "v \<noteq> 0" and "xs = [] \<or> key_compare ko k (fst (hd xs)) = Lt"
  shows "update_by_pair (k, v) xs = (k, v) # xs"
  using assms(2)
proof (induct xs)
case Nil
  from assms(1) show ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  from Cons(2) have "key_compare ko k k' = Lt" by (simp add: x)
  with assms(1) show ?case by (simp add: x)
qed

lemma lookup_pair_update_by_pair:
  assumes "oalist_inv (xs, ko)"
  shows "lookup_pair (update_by_pair (k1, v) xs) k2 = (if k1 = k2 then v else lookup_pair xs k2)"
  using assms
proof (induct xs arbitrary: v rule: oalist_inv_induct)
  case Nil
  show ?case by (simp split: order.split, simp add: key_compare_Eq)
next
  case (Cons k' v' xs)
  show ?case
  proof (split if_split, intro conjI impI)
    assume "k1 = k2"
    with Cons(5) have eq: "lookup_pair (update_by_pair (k2, u) xs) k2 = u" for u
      by (simp del: update_by_pair.simps)
    show "lookup_pair (update_by_pair (k1, v) ((k', v') # xs)) k2 = v"
    proof (simp add: \<open>k1 = k2\<close> eq split: order.split, intro conjI impI)
      assume "key_compare ko k2 k' = Eq"
      hence "\<not> lt_of_key_order ko k' k2" by (simp add: lt_of_key_order_alt key_compare_Eq)
      with Cons(4) have "k2 \<notin> fst ` set xs" by auto
      thus "lookup_pair xs k2 = 0" using Cons(2) by (simp add: lookup_pair_eq_0)
    qed
  next
    assume "k1 \<noteq> k2"
    with Cons(5) have eq: "lookup_pair (update_by_pair (k1, u) xs) k2 = lookup_pair xs k2" for u
      by (simp del: update_by_pair.simps)
    have *: "lookup_pair xs k2 = 0" if "lt_of_key_order ko k2 k'"
    proof -
      from \<open>lt_of_key_order ko k2 k'\<close> have "\<not> lt_of_key_order ko k' k2" by auto
      with Cons(4) have "k2 \<notin> fst ` set xs" by auto
      thus "lookup_pair xs k2 = 0" using Cons(2) by (simp add: lookup_pair_eq_0)
    qed
    show "lookup_pair (update_by_pair (k1, v) ((k', v') # xs)) k2 = lookup_pair ((k', v') # xs) k2"
      by (simp add: \<open>k1 \<noteq> k2\<close> eq split: order.split,
          auto intro: * simp: \<open>k1 \<noteq> k2\<close>[symmetric] key_compare_Eq key_compare_Gt lt_of_key_order_alt[symmetric])
  qed
qed

corollary update_by_pair_id:
  assumes "oalist_inv (xs, ko)" and "lookup_pair xs k = v"
  shows "update_by_pair (k, v) xs = xs"
proof (rule lookup_pair_inj, rule oalist_inv_update_by_pair)
  show "lookup_pair (update_by_pair (k, v) xs) = lookup_pair xs"
  proof
    fix k0
    from assms(2) show "lookup_pair (update_by_pair (k, v) xs) k0 = lookup_pair xs k0"
      by (auto simp: lookup_pair_update_by_pair[OF assms(1)])
  qed
qed fact+

lemma set_update_by_pair:
  assumes "oalist_inv (xs, ko)" and "v \<noteq> 0"
  shows "set (update_by_pair (k, v) xs) = insert (k, v) (set xs - range (Pair k))" (is "?A = ?B")
proof (rule set_eqI)
  fix x::"'a \<times> 'b"
  obtain k' v' where x: "x = (k', v')" by fastforce
  from assms(1) have inv: "oalist_inv (update_by_pair (k, v) xs, ko)" by (rule oalist_inv_update_by_pair)
  show "(x \<in> ?A) \<longleftrightarrow> (x \<in> ?B)"
  proof (cases "v' = 0")
    case True
    have "0 \<notin> snd ` set (update_by_pair (k, v) xs)" and "0 \<notin> snd ` set xs"
      by (rule oalist_invD1, fact)+
    hence "(k', 0) \<notin> set (update_by_pair (k, v) xs)" and "(k', 0) \<notin> set xs"
      using image_iff by fastforce+
    thus ?thesis by (simp add: x True assms(2))
  next
    case False
    show ?thesis
      by (auto simp: x lookup_pair_eq_value[OF inv False, symmetric] lookup_pair_eq_value[OF assms(1) False]
          lookup_pair_update_by_pair[OF assms(1)])
  qed
qed

subsubsection \<open>@{const update_by_fun_pair} and @{const update_by_fun_gr_pair}\<close>

lemma update_by_fun_pair_eq_update_by_pair:
  assumes "oalist_inv (xs, ko)"
  shows "update_by_fun_pair k f xs = update_by_pair (k, f (lookup_pair xs k)) xs"
  using assms by (induct xs rule: oalist_inv_induct, simp, simp split: order.split)

corollary oalist_inv_update_by_fun_pair:
  assumes "oalist_inv (xs, ko)"
  shows "oalist_inv (update_by_fun_pair k f xs, ko)"
  unfolding update_by_fun_pair_eq_update_by_pair[OF assms] using assms by (rule oalist_inv_update_by_pair)

corollary lookup_pair_update_by_fun_pair:
  assumes "oalist_inv (xs, ko)"
  shows "lookup_pair (update_by_fun_pair k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_pair xs k2)"
  by (simp add: update_by_fun_pair_eq_update_by_pair[OF assms] lookup_pair_update_by_pair[OF assms])

lemma update_by_fun_pair_gr:
  assumes "oalist_inv (xs, ko)" and "xs = [] \<or> key_compare ko k (fst (last xs)) = Gt"
  shows "update_by_fun_pair k f xs = xs @ (if f 0 = 0 then [] else [(k, f 0)])"
  using assms
proof (induct xs rule: oalist_inv_induct)
  case Nil
  show ?case by simp
next
  case (Cons k' v' xs)
  from Cons(6) have 1: "key_compare ko k (fst (last ((k', v') # xs))) = Gt" by simp
  have eq1: "key_compare ko k k' = Gt"
  proof (cases "xs = []")
    case True
    with 1 show ?thesis by simp
  next
    case False
    have "lt_of_key_order ko k' (fst (last xs))" by (rule Cons(4), simp add: False)
    from False 1 have "key_compare ko k (fst (last xs)) = Gt" by simp
    moreover from \<open>lt_of_key_order ko k' (fst (last xs))\<close> have "key_compare ko (fst (last xs)) k' = Gt"
      by (simp add: key_compare_Gt lt_of_key_order_alt)
    ultimately show ?thesis
      by (meson key_compare_Gt key_order_lin.less_trans lt_of_key_order_alt)
  qed
  have eq2: "update_by_fun_pair k f xs = xs @ (if f 0 = 0 then [] else [(k, f 0)])"
  proof (rule Cons(5), simp only: disj_commute[of "xs = []"], rule disjCI)
    assume "xs \<noteq> []"
    with 1 show "key_compare ko k (fst (last xs)) = Gt" by simp
  qed
  show ?case by (simp split: order.split add: Let_def eq1 eq2)
qed

corollary update_by_fun_gr_pair_eq_update_by_fun_pair:
  assumes "oalist_inv (xs, ko)"
  shows "update_by_fun_gr_pair k f xs = update_by_fun_pair k f xs"
  by (simp add: update_by_fun_gr_pair_def Let_def update_by_fun_pair_gr[OF assms] split: order.split)

corollary oalist_inv_update_by_fun_gr_pair:
  assumes "oalist_inv (xs, ko)"
  shows "oalist_inv (update_by_fun_gr_pair k f xs, ko)"
  unfolding update_by_fun_pair_eq_update_by_pair[OF assms] update_by_fun_gr_pair_eq_update_by_fun_pair[OF assms]
  using assms by (rule oalist_inv_update_by_pair)

corollary lookup_pair_update_by_fun_gr_pair:
  assumes "oalist_inv (xs, ko)"
  shows "lookup_pair (update_by_fun_gr_pair k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_pair xs k2)"
  by (simp add: update_by_fun_pair_eq_update_by_pair[OF assms]
      update_by_fun_gr_pair_eq_update_by_fun_pair[OF assms] lookup_pair_update_by_pair[OF assms])

subsubsection \<open>@{const map_pair}\<close>

lemma map_pair_subset: "set (map_pair f xs) \<subseteq> f ` set xs"
proof (induct xs rule: map_pair.induct)
  case (1 f)
  show ?case by simp
next
  case (2 f kv xs)
  obtain k v where f: "f kv = (k, v)" by fastforce
  from f[symmetric] refl have *: "set (map_pair f xs) \<subseteq> f ` set xs" by (rule 2)
  show ?case by (simp add: f Let_def, intro conjI impI subset_insertI2 *)
qed

lemma oalist_inv_map_pair:
  assumes "oalist_inv (xs, ko)"
    and "\<And>a b. key_compare ko (fst (f a)) (fst (f b)) = key_compare ko (fst a) (fst b)"
  shows "oalist_inv (map_pair f xs, ko)"
  using assms(1)
proof (induct xs rule: oalist_inv_induct)
  case Nil
  from oalist_inv_Nil show ?case by simp
next
  case (Cons k v xs)
  obtain k' v' where f: "f (k, v) = (k', v')" by fastforce
  show ?case
  proof (simp add: f Let_def Cons(5), rule)
    assume "v' \<noteq> 0"
    with Cons(5) show "oalist_inv ((k', v') # map_pair f xs, ko)"
    proof (rule oalist_inv_ConsI)
      assume "map_pair f xs \<noteq> []"
      hence "hd (map_pair f xs) \<in> set (map_pair f xs)" by simp
      also have "... \<subseteq> f ` set xs" by (fact map_pair_subset)
      finally obtain x where "x \<in> set xs" and eq: "hd (map_pair f xs) = f x" ..
      from this(1) have "fst x \<in> fst ` set xs" by fastforce
      hence "lt_of_key_order ko k (fst x)" by (rule Cons(4))
      hence "lt_of_key_order ko (fst (f (k, v))) (fst (f x))"
        by (simp add: lt_of_key_order_alt assms(2))
      thus "lt_of_key_order ko k' (fst (hd (map_pair f xs)))" by (simp add: f eq)
    qed
  qed
qed

lemma lookup_pair_map_pair:
  assumes "oalist_inv (xs, ko)"
    and "\<And>k'. snd (f (k', 0)) = 0"
    and "\<And>a b. key_compare ko (fst (f a)) (fst (f b)) = key_compare ko (fst a) (fst b)"
  shows "lookup_pair (map_pair f xs) (fst (f (k, v))) = snd (f (k, lookup_pair xs k))"
  using assms(1)
proof (induct xs rule: oalist_inv_induct)
  case Nil
  show ?case by (simp add: assms(2))
next
  case (Cons k' v' xs)
  obtain k'' v'' where f: "f (k', v') = (k'', v'')" by fastforce
  have "key_compare ko (fst (f (k, v))) k'' = key_compare ko (fst (f (k, v))) (fst (f (k', v')))"
    by (simp add: f)
  also have "... = key_compare ko k k'"
    by (simp add: assms(3))
  finally have eq: "key_compare ko (fst (f (k, v))) k'' = key_compare ko k k'" .
  have *: "lookup_pair xs k = 0" if "key_compare ko k k' \<noteq> Gt"
  proof (simp add: lookup_pair_eq_0[OF Cons(2)], rule)
    assume "k \<in> fst ` set xs"
    hence "lt_of_key_order ko k' k" by (rule Cons(4))
    hence "key_compare ko k k' = Gt" by (simp add: key_compare_Gt lt_of_key_order_alt)
    with \<open>key_compare ko k k' \<noteq> Gt\<close> show False ..
  qed
  show ?case
  proof (simp add: assms(2) f Let_def eq Cons(5) split: order.split, intro conjI impI)
    assume "key_compare ko k k' = Lt"
    hence "key_compare ko k k' \<noteq> Gt" by simp
    hence "lookup_pair xs k = 0" by (rule *)
    thus "snd (f (k, lookup_pair xs k)) = 0" by (simp add: assms(2))
  next
    assume "v'' = 0"
    assume "key_compare ko k k' = Eq"
    hence "k = k'" and "key_compare ko k k' \<noteq> Gt" by (simp only: key_compare_Eq, simp)
    from this(2) have "lookup_pair xs k = 0" by (rule *)
    hence "snd (f (k, lookup_pair xs k)) = 0" by (simp add: assms(2))
    also have "... = snd (f (k, v'))" by (simp add: \<open>k = k'\<close> f \<open>v'' = 0\<close>)
    finally show "snd (f (k, lookup_pair xs k)) = snd (f (k, v'))" .
  qed (simp add: f key_compare_Eq)
qed

lemma oalist_inv_map_val_pair:
  assumes "oalist_inv (xs, ko)"
  shows "oalist_inv (map_val_pair f xs, ko)"
  by (rule oalist_inv_map_pair, fact assms, auto)

lemma lookup_pair_map_val_pair:
  assumes "oalist_inv (xs, ko)" and "\<And>k'. f k' 0 = 0"
  shows "lookup_pair (map_val_pair f xs) k = f k (lookup_pair xs k)"
proof -
  let ?f = "\<lambda>(k', v'). (k', f k' v')"
  have "lookup_pair (map_val_pair f xs) k = lookup_pair (map_val_pair f xs) (fst (?f (k, 0)))"
    by simp
  also have "... = snd (?f (k, local.lookup_pair xs k))"
    by (rule lookup_pair_map_pair, fact assms(1), auto simp: assms(2))
  also have "... = f k (lookup_pair xs k)" by simp
  finally show ?thesis .
qed

subsubsection \<open>@{const map2_val_pair}\<close>

definition map2_val_compat :: "('a key_order \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list) \<Rightarrow> bool"
  where "map2_val_compat f \<longleftrightarrow> (\<forall>zs. (oalist_inv (zs, ko) \<longrightarrow> (oalist_inv (f ko zs, ko) \<and> fst ` set (f ko zs) \<subseteq> fst ` set zs)))"

lemma map2_val_compatI:
  assumes "\<And>zs. oalist_inv (zs, ko) \<Longrightarrow> oalist_inv (f ko zs, ko)"
    and "\<And>zs. oalist_inv (zs, ko) \<Longrightarrow> fst ` set (f ko zs) \<subseteq> fst ` set zs"
  shows "map2_val_compat f"
  unfolding map2_val_compat_def using assms by blast

lemma map2_val_compatD1:
  assumes "map2_val_compat f" and "oalist_inv (zs, ko)"
  shows "oalist_inv (f ko zs, ko)"
  using assms unfolding map2_val_compat_def by blast

lemma map2_val_compatD2:
  assumes "map2_val_compat f" and "oalist_inv (zs, ko)"
  shows "fst ` set (f ko zs) \<subseteq> fst ` set zs"
  using assms unfolding map2_val_compat_def by blast

lemma map2_val_compat_Nil:
  assumes "map2_val_compat (f::'a key_order \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list)"
  shows "f ko [] = []"
proof -
  from assms oalist_inv_Nil have "fst ` set (f ko []) \<subseteq> fst ` set ([]::('a \<times> 'b) list)"
    by (rule map2_val_compatD2)
  thus ?thesis by simp
qed

lemma fst_map2_val_pair_subset:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)"
  assumes "map2_val_compat g" and "map2_val_compat h"
  shows "fst ` set (map2_val_pair f g h xs ys) \<subseteq> fst ` set xs \<union> fst ` set ys"
  using assms
proof (induct f g h xs ys rule: map2_val_pair.induct)
  case (1 f g h xs)
  show ?case by (simp, rule map2_val_compatD2, fact+)
next
  case (2 f g h v va)
  show ?case by (simp del: set_simps(2), rule map2_val_compatD2, fact+)
next
  case (3 f g h kx vx xs ky vy ys)
  from 3(4) have "oalist_inv (xs, ko)" by (rule oalist_inv_ConsD1)
  from 3(5) have "oalist_inv (ys, ko)" by (rule oalist_inv_ConsD1)
  show ?case
  proof (simp split: order.split, intro conjI impI)
    assume "key_compare ko kx ky = Lt"
    hence "fst ` set (map2_val_pair f g h xs ((ky, vy) # ys)) \<subseteq> fst ` set xs \<union> fst ` set ((ky, vy) # ys)"
      using refl \<open>oalist_inv (xs, ko)\<close> 3(5, 6, 7) by (rule 3(2))
    thus "fst ` set (let v = f kx vx 0; aux = map2_val_pair f g h xs ((ky, vy) # ys)
                       in if v = 0 then aux else (kx, v) # aux)
          \<subseteq> insert ky (insert kx (fst ` set xs \<union> fst ` set ys))" by (auto simp: Let_def)
  next
    assume "key_compare ko kx ky = Eq"
    hence "fst ` set (map2_val_pair f g h xs ys) \<subseteq> fst ` set xs \<union> fst ` set ys"
      using refl \<open>oalist_inv (xs, ko)\<close> \<open>oalist_inv (ys, ko)\<close> 3(6, 7) by (rule 3(1))
    thus "fst ` set (let v = f kx vx vy; aux = map2_val_pair f g h xs ys in if v = 0 then aux else (kx, v) # aux)
          \<subseteq> insert ky (insert kx (fst ` set xs \<union> fst ` set ys))" by (auto simp: Let_def)
  next
    assume "key_compare ko kx ky = Gt"
    hence "fst ` set (map2_val_pair f g h ((kx, vx) # xs) ys) \<subseteq> fst ` set ((kx, vx) # xs) \<union> fst ` set ys"
      using refl 3(4) \<open>oalist_inv (ys, ko)\<close> 3(6, 7) by (rule 3(3))
    thus "fst ` set (let v = f ky 0 vy; aux = map2_val_pair f g h ((kx, vx) # xs) ys
                        in if v = 0 then aux else (ky, v) # aux)
          \<subseteq> insert ky (insert kx (fst ` set xs \<union> fst ` set ys))" by (auto simp: Let_def)
  qed
qed

lemma oalist_inv_map2_val_pair:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)"
  assumes "map2_val_compat g" and "map2_val_compat h"
  shows "oalist_inv (map2_val_pair f g h xs ys, ko)"
  using assms(1, 2)
proof (induct xs arbitrary: ys rule: oalist_inv_induct)
  case Nil
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis by (simp add: Nil, rule map2_val_compatD1, fact assms(3), fact oalist_inv_Nil)
  next
    case (Cons y ys')
    show ?thesis by (simp add: Cons, rule map2_val_compatD1, fact assms(4), simp only: Cons[symmetric], fact Nil)
  qed
next
  case *: (Cons k v xs)
  from *(6) show ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    show ?case by (simp, rule map2_val_compatD1, fact assms(3), fact *(1))
  next
    case (Cons k' v' ys)
    show ?case
    proof (simp split: order.split, intro conjI impI)
      assume "key_compare ko k k' = Lt"
      hence 0: "lt_of_key_order ko k k'" by (simp only: lt_of_key_order_alt)
      from Cons(1) have 1: "oalist_inv (map2_val_pair f g h xs ((k', v') # ys), ko)" by (rule *(5))
      show "oalist_inv (let v = f k v 0; aux = map2_val_pair f g h xs ((k', v') # ys)
              in if v = 0 then aux else (k, v) # aux, ko)"
      proof (simp add: Let_def, intro conjI impI)
        assume "f k v 0 \<noteq> 0"
        with 1 show "oalist_inv ((k, f k v 0) # map2_val_pair f g h xs ((k', v') # ys), ko)"
        proof (rule oalist_inv_ConsI)
          define k0 where "k0 = fst (hd (local.map2_val_pair f g h xs ((k', v') # ys)))"
          assume "map2_val_pair f g h xs ((k', v') # ys) \<noteq> []"
          hence "k0 \<in> fst ` set (map2_val_pair f g h xs ((k', v') # ys))" by (simp add: k0_def)
          also from *(2) Cons(1) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ((k', v') # ys)"
            by (rule fst_map2_val_pair_subset)
          finally have "k0 \<in> fst ` set xs \<or> k0 = k' \<or> k0 \<in> fst ` set ys" by auto
          thus "lt_of_key_order ko k k0"
          proof (elim disjE)
            assume "k0 = k'"
            with 0 show ?thesis by simp
          next
            assume "k0 \<in> fst ` set ys"
            hence "lt_of_key_order ko k' k0" by (rule Cons(4))
            with 0 show ?thesis by (rule key_order_lin.less_trans)
          qed (rule *(4))
        qed
      qed (rule 1)
    next
      assume "key_compare ko k k' = Eq"
      hence "k = k'" by (simp only: key_compare_Eq)
      from Cons(2) have 1: "oalist_inv (map2_val_pair f g h xs ys, ko)" by (rule *(5))
      show "oalist_inv (let v = f k v v'; aux = map2_val_pair f g h xs ys in if v = 0 then aux else (k, v) # aux, ko)"
      proof (simp add: Let_def, intro conjI impI)
        assume "f k v v' \<noteq> 0"
        with 1 show "oalist_inv ((k, f k v v') # map2_val_pair f g h xs ys, ko)"
        proof (rule oalist_inv_ConsI)
          define k0 where "k0 = fst (hd (map2_val_pair f g h xs ys))"
          assume "map2_val_pair f g h xs ys \<noteq> []"
          hence "k0 \<in> fst ` set (map2_val_pair f g h xs ys)" by (simp add: k0_def)
          also from *(2) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ys"
            by (rule fst_map2_val_pair_subset)
          finally show "lt_of_key_order ko k k0"
          proof
            assume "k0 \<in> fst ` set ys"
            hence "lt_of_key_order ko k' k0" by (rule Cons(4))
            thus ?thesis by (simp only: \<open>k = k'\<close>)
          qed (rule *(4))
        qed
      qed (rule 1)
    next
      assume "key_compare ko k k' = Gt"
      hence 0: "lt_of_key_order ko k' k" by (simp only: lt_of_key_order_alt key_compare_Gt)
      show "oalist_inv (let va = f k' 0 v'; aux = map2_val_pair f g h ((k, v) # xs) ys
              in if va = 0 then aux else (k', va) # aux, ko)"
      proof (simp add: Let_def, intro conjI impI)
        assume "f k' 0 v' \<noteq> 0"
        with Cons(5) show "oalist_inv ((k', f k' 0 v') # map2_val_pair f g h ((k, v) # xs) ys, ko)"
        proof (rule oalist_inv_ConsI)
          define k0 where "k0 = fst (hd (map2_val_pair f g h ((k, v) # xs) ys))"
          assume "map2_val_pair f g h ((k, v) # xs) ys \<noteq> []"
          hence "k0 \<in> fst ` set (map2_val_pair f g h ((k, v) # xs) ys)" by (simp add: k0_def)
          also from *(1) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set ((k, v) # xs) \<union> fst ` set ys"
            by (rule fst_map2_val_pair_subset)
          finally have "k0 = k \<or> k0 \<in> fst ` set xs \<or> k0 \<in> fst ` set ys" by auto
          thus "lt_of_key_order ko k' k0"
          proof (elim disjE)
            assume "k0 = k"
            with 0 show ?thesis by simp
          next
            assume "k0 \<in> fst ` set xs"
            hence "lt_of_key_order ko k k0" by (rule *(4))
            with 0 show ?thesis by (rule key_order_lin.less_trans)
          qed (rule Cons(4))
        qed
      qed (rule Cons(5))
    qed
  qed
qed

lemma lookup_pair_map2_val_pair:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)"
  assumes "map2_val_compat g" and "map2_val_compat h"
  assumes "\<And>zs. oalist_inv (zs, ko) \<Longrightarrow> g ko zs = map_val_pair (\<lambda>k v. f k v 0) zs"
    and "\<And>zs. oalist_inv (zs, ko) \<Longrightarrow> h ko zs = map_val_pair (\<lambda>k. f k 0) zs"
    and "\<And>k. f k 0 0 = 0"
  shows "lookup_pair (map2_val_pair f g h xs ys) k0 = f k0 (lookup_pair xs k0) (lookup_pair ys k0)"
  using assms(1, 2)
proof (induct xs arbitrary: ys rule: oalist_inv_induct)
  case Nil
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis by (simp add: Nil map2_val_compat_Nil[OF assms(3)] assms(7))
  next
    case (Cons y ys')
    then obtain k v ys' where ys: "ys = (k, v) # ys'" by fastforce
    from Nil have "lookup_pair (h ko ys) k0 = lookup_pair (map_val_pair (\<lambda>k. f k 0) ys) k0"
      by (simp only: assms(6))
    also have "... = f k0 0 (lookup_pair ys k0)" by (rule lookup_pair_map_val_pair, fact Nil, fact assms(7))
    finally have "lookup_pair (h ko ((k, v) # ys')) k0 = f k0 0 (lookup_pair ((k, v) # ys') k0)"
      by (simp only: ys)
    thus ?thesis by (simp add: ys)
  qed
next
  case *: (Cons k v xs)
  from *(6) show ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    from *(1) have "lookup_pair (g ko ((k, v) # xs)) k0 = lookup_pair (map_val_pair (\<lambda>k v. f k v 0) ((k, v) # xs)) k0"
      by (simp only: assms(5))
    also have "... = f k0 (lookup_pair ((k, v) # xs) k0) 0"
      by (rule lookup_pair_map_val_pair, fact *(1), fact assms(7))
    finally show ?case by simp
  next
    case (Cons k' v' ys)
    show ?case
    proof (cases "key_compare ko k0 k = Lt \<and> key_compare ko k0 k' = Lt")
      case True
      hence 1: "key_compare ko k0 k = Lt" and 2: "key_compare ko k0 k' = Lt" by simp_all
      hence eq: "f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0) = 0"
        by (simp add: assms(7))
      from *(1) Cons(1) assms(3, 4) have inv: "oalist_inv (map2_val_pair f g h ((k, v) # xs) ((k', v') # ys), ko)"
        by (rule oalist_inv_map2_val_pair)
      show ?thesis
      proof (simp only: eq lookup_pair_eq_0[OF inv], rule)
        assume "k0 \<in> fst ` set (local.map2_val_pair f g h ((k, v) # xs) ((k', v') # ys))"
        also from *(1) Cons(1) assms(3, 4) have "... \<subseteq> fst ` set ((k, v) # xs) \<union> fst ` set ((k', v') # ys)"
          by (rule fst_map2_val_pair_subset)
        finally have "k0 \<in> fst ` set xs \<or> k0 \<in> fst ` set ys" using 1 2 by auto
        thus False
        proof
          assume "k0 \<in> fst ` set xs"
          hence "lt_of_key_order ko k k0" by (rule *(4))
          with 1 show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt_of_key_order ko k' k0" by (rule Cons(4))
          with 2 show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
        qed
      qed
    next
      case False
      show ?thesis
      proof (simp split: order.split del: lookup_pair.simps, intro conjI impI)
        assume "key_compare ko k k' = Lt"
        with False have "key_compare ko k0 k \<noteq> Lt" by (auto simp: lt_of_key_order_alt[symmetric])
        show "lookup_pair (let v = f k v 0; aux = map2_val_pair f g h xs ((k', v') # ys)
                            in if v = 0 then aux else (k, v) # aux) k0 =
              f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
        proof (cases "key_compare ko k0 k")
          case Lt
          with \<open>key_compare ko k0 k \<noteq> Lt\<close> show ?thesis ..
        next
          case Eq
          hence "k0 = k" by (simp only: key_compare_Eq)
          with \<open>key_compare ko k k' = Lt\<close> have "key_compare ko k0 k' = Lt" by simp
          hence eq1: "lookup_pair ((k', v') # ys) k = 0" by (simp add: \<open>k0 = k\<close>)
          have eq2: "lookup_pair ((k, v) # xs) k = v" by simp
          show ?thesis
          proof (simp add: Let_def eq1 eq2 \<open>k0 = k\<close> del: lookup_pair.simps, intro conjI impI)
            from *(2) Cons(1) assms(3, 4) have inv: "oalist_inv (map2_val_pair f g h xs ((k', v') # ys), ko)"
              by (rule oalist_inv_map2_val_pair)
            show "lookup_pair (map2_val_pair f g h xs ((k', v') # ys)) k = 0"
            proof (simp only: lookup_pair_eq_0[OF inv], rule)
              assume "k \<in> fst ` set (local.map2_val_pair f g h xs ((k', v') # ys))"
              also from *(2) Cons(1) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ((k', v') # ys)"
                by (rule fst_map2_val_pair_subset)
              finally have "k \<in> fst ` set xs \<or> k \<in> fst ` set ys" using \<open>key_compare ko k k' = Lt\<close>
                by auto
              thus False
              proof
                assume "k \<in> fst ` set xs"
                hence "lt_of_key_order ko k k" by (rule *(4))
                thus ?thesis by simp
              next
                assume "k \<in> fst ` set ys"
                hence "lt_of_key_order ko k' k" by (rule Cons(4))
                with \<open>key_compare ko k k' = Lt\<close> show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
              qed
            qed
          qed simp
        next
          case Gt
          hence eq1: "lookup_pair ((k, v) # xs) k0 = lookup_pair xs k0"
            and eq2: "lookup_pair ((k, f k v 0) # map2_val_pair f g h xs ((k', v') # ys)) k0 =
                  lookup_pair (map2_val_pair f g h xs ((k', v') # ys)) k0" by simp_all
          show ?thesis
            by (simp add: Let_def eq1 eq2 del: lookup_pair.simps, rule *(5), fact Cons(1))
        qed
      next
        assume "key_compare ko k k' = Eq"
        hence "k = k'" by (simp only: key_compare_Eq)
        with False have "key_compare ko k0 k' \<noteq> Lt" by (auto simp: lt_of_key_order_alt[symmetric])
        show "lookup_pair (let v = f k v v'; aux = map2_val_pair f g h xs ys in
                            if v = 0 then aux else (k, v) # aux) k0 =
              f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
        proof (cases "key_compare ko k0 k'")
          case Lt
          with \<open>key_compare ko k0 k' \<noteq> Lt\<close> show ?thesis ..
        next
          case Eq
          hence "k0 = k'" by (simp only: key_compare_Eq)
          show ?thesis
          proof (simp add: Let_def \<open>k = k'\<close> \<open>k0 = k'\<close>, intro impI)
            from *(2) Cons(2) assms(3, 4) have inv: "oalist_inv (map2_val_pair f g h xs ys, ko)"
              by (rule oalist_inv_map2_val_pair)
            show "lookup_pair (map2_val_pair f g h xs ys) k' = 0"
            proof (simp only: lookup_pair_eq_0[OF inv], rule)
              assume "k' \<in> fst ` set (map2_val_pair f g h xs ys)"
              also from *(2) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set xs \<union> fst ` set ys"
                by (rule fst_map2_val_pair_subset)
              finally show False
              proof
                assume "k' \<in> fst ` set ys"
                hence "lt_of_key_order ko k' k'" by (rule Cons(4))
                thus ?thesis by simp
              next
                assume "k' \<in> fst ` set xs"
                hence "lt_of_key_order ko k k'" by (rule *(4))
                thus ?thesis by (simp add: \<open>k = k'\<close>)
              qed
            qed
          qed
        next
          case Gt
          hence eq1: "lookup_pair ((k, v) # xs) k0 = lookup_pair xs k0"
            and eq2: "lookup_pair ((k', v') # ys) k0 = lookup_pair ys k0"
            and eq3: "lookup_pair ((k, f k v v') # map2_val_pair f g h xs ys) k0 =
                  lookup_pair (map2_val_pair f g h xs ys) k0" by (simp_all add: \<open>k = k'\<close>)
          show ?thesis by (simp add: Let_def eq1 eq2 eq3 del: lookup_pair.simps, rule *(5), fact Cons(2))
        qed
      next
        assume "key_compare ko k k' = Gt"
        hence "key_compare ko k' k = Lt" by (simp only: key_compare_Gt)
        with False have "key_compare ko k0 k' \<noteq> Lt" by (auto simp: lt_of_key_order_alt[symmetric])
        show "lookup_pair (let va = f k' 0 v'; aux = map2_val_pair f g h ((k, v) # xs) ys
                            in if va = 0 then aux else (k', va) # aux) k0 =
              f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
        proof (cases "key_compare ko k0 k'")
          case Lt
          with \<open>key_compare ko k0 k' \<noteq> Lt\<close> show ?thesis ..
        next
          case Eq
          hence "k0 = k'" by (simp only: key_compare_Eq)
          with \<open>key_compare ko k' k = Lt\<close> have "key_compare ko k0 k = Lt" by simp
          hence eq1: "lookup_pair ((k, v) # xs) k' = 0" by (simp add: \<open>k0 = k'\<close>)
          have eq2: "lookup_pair ((k', v') # ys) k' = v'" by simp
          show ?thesis
          proof (simp add: Let_def eq1 eq2 \<open>k0 = k'\<close> del: lookup_pair.simps, intro conjI impI)
            from *(1) Cons(2) assms(3, 4) have inv: "oalist_inv (map2_val_pair f g h ((k, v) # xs) ys, ko)"
              by (rule oalist_inv_map2_val_pair)
            show "lookup_pair (map2_val_pair f g h ((k, v) # xs) ys) k' = 0"
            proof (simp only: lookup_pair_eq_0[OF inv], rule)
              assume "k' \<in> fst ` set (map2_val_pair f g h ((k, v) # xs) ys)"
              also from *(1) Cons(2) assms(3, 4) have "... \<subseteq> fst ` set ((k, v) # xs) \<union> fst ` set ys"
                by (rule fst_map2_val_pair_subset)
              finally have "k' \<in> fst ` set xs \<or> k' \<in> fst ` set ys" using \<open>key_compare ko k' k = Lt\<close>
                by auto
              thus False
              proof
                assume "k' \<in> fst ` set ys"
                hence "lt_of_key_order ko k' k'" by (rule Cons(4))
                thus ?thesis by simp
              next
                assume "k' \<in> fst ` set xs"
                hence "lt_of_key_order ko k k'" by (rule *(4))
                with \<open>key_compare ko k' k = Lt\<close> show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
              qed
            qed
          qed simp
        next
          case Gt
          hence eq1: "lookup_pair ((k', v') # ys) k0 = lookup_pair ys k0"
            and eq2: "lookup_pair ((k', f k' 0 v') # map2_val_pair f g h ((k, v) # xs) ys) k0 =
                  lookup_pair (map2_val_pair f g h ((k, v) # xs) ys) k0" by simp_all
          show ?thesis by (simp add: Let_def eq1 eq2 del: lookup_pair.simps, rule Cons(5))
        qed
      qed
    qed
  qed
qed

lemma map2_val_pair_singleton_eq_update_by_fun_pair:
  assumes "oalist_inv (xs, ko)"
  assumes "\<And>k x. f k x 0 = x" and "\<And>zs. oalist_inv (zs, ko) \<Longrightarrow> g ko zs = zs"
    and "h ko [(k, v)] = map_val_pair (\<lambda>k. f k 0) [(k, v)]"
  shows "map2_val_pair f g h xs [(k, v)] = update_by_fun_pair k (\<lambda>x. f k x v) xs"
  using assms(1)
proof (induct xs rule: oalist_inv_induct)
  case Nil
  show ?case by (simp add: Let_def assms(4))
next
  case (Cons k' v' xs)
  show ?case
  proof (cases "key_compare ko k' k")
    case Lt
    hence gr: "key_compare ko k k' = Gt" by (simp only: key_compare_Gt)
    show ?thesis by (simp add: Lt gr Let_def assms(2) Cons(3, 5))
  next
    case Eq
    hence eq1: "key_compare ko k k' = Eq" and eq2: "k = k'" by (simp_all only: key_compare_Eq)
    show ?thesis by (simp add: Eq eq1 eq2 Let_def assms(3)[OF Cons(2)])
  next
    case Gt
    hence less: "key_compare ko k k' = Lt" by (simp only: key_compare_Gt)
    show ?thesis by (simp add: Gt less Let_def assms(3)[OF Cons(1)])
  qed
qed

subsubsection \<open>@{const lex_ord_pair}\<close>

lemma lex_ord_pair_EqI:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)"
    and "\<And>k. k \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> f k (lookup_pair xs k) (lookup_pair ys k) = Some Eq"
  shows "lex_ord_pair f xs ys = Some Eq"
  using assms
proof (induct xs arbitrary: ys rule: oalist_inv_induct)
  case Nil
  thus ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v ys)
    show ?case
    proof (simp add: Let_def, intro conjI impI, rule Cons(5))
      fix k0
      assume "k0 \<in> fst ` set [] \<union> fst ` set ys"
      hence "k0 \<in> fst ` set ys" by simp
      hence "lt_of_key_order ko k k0" by (rule Cons(4))
      hence "f k0 (lookup_pair [] k0) (lookup_pair ys k0) = f k0 (lookup_pair [] k0) (lookup_pair ((k, v) # ys) k0)"
        by (auto simp add: lookup_pair_Cons[OF Cons(1)] simp del: lookup_pair.simps)
      also have "... = Some Eq" by (rule Cons(6), simp add: \<open>k0 \<in> fst ` set ys\<close>)
      finally show "f k0 (lookup_pair [] k0) (lookup_pair ys k0) = Some Eq" .
    next
      have "f k 0 v = f k (lookup_pair [] k) (lookup_pair ((k, v) # ys) k)" by simp
      also have "... = Some Eq" by (rule Cons(6), simp)
      finally show "f k 0 v = Some Eq" .
    qed
  qed
next
  case *: (Cons k v xs)
  from *(6, 7) show ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    show ?case
    proof (simp add: Let_def, intro conjI impI, rule *(5), rule oalist_inv_Nil)
      fix k0
      assume "k0 \<in> fst ` set xs \<union> fst ` set []"
      hence "k0 \<in> fst ` set xs" by simp
      hence "lt_of_key_order ko k k0" by (rule *(4))
      hence "f k0 (lookup_pair xs k0) (lookup_pair [] k0) = f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair [] k0)"
        by (auto simp add: lookup_pair_Cons[OF *(1)] simp del: lookup_pair.simps)
      also have "... = Some Eq" by (rule Nil, simp add: \<open>k0 \<in> fst ` set xs\<close>)
      finally show "f k0 (lookup_pair xs k0) (lookup_pair [] k0) = Some Eq" .
    next
      have "f k v 0 = f k (lookup_pair ((k, v) # xs) k) (lookup_pair [] k)" by simp
      also have "... = Some Eq" by (rule Nil, simp)
      finally show "f k v 0 = Some Eq" .
    qed
  next
    case (Cons k' v' ys)
    show ?case
    proof (simp split: order.split, intro conjI impI)
      assume "key_compare ko k k' = Lt"
      show "(let aux = f k v 0 in if aux = Some Eq then lex_ord_pair f xs ((k', v') # ys) else aux) = Some Eq"
      proof (simp add: Let_def, intro conjI impI, rule *(5), rule Cons(1))
        fix k0
        assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ((k', v') # ys)"
        hence "k0 \<in> fst ` set xs \<or> k0 = k' \<or> k0 \<in> fst ` set ys" by auto
        hence "k0 \<noteq> k"
        proof (elim disjE)
          assume "k0 \<in> fst ` set xs"
          hence "lt_of_key_order ko k k0" by (rule *(4))
          thus ?thesis by simp
        next
          assume "k0 = k'"
          with \<open>key_compare ko k k' = Lt\<close> show ?thesis by auto
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt_of_key_order ko k' k0" by (rule Cons(4))
          with \<open>key_compare ko k k' = Lt\<close> show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
        qed
        hence "f k0 (lookup_pair xs k0) (lookup_pair ((k', v') # ys) k0) =
                f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
          by (auto simp add: lookup_pair_Cons[OF *(1)] simp del: lookup_pair.simps)
        also have "... = Some Eq" by (rule Cons(6), rule set_rev_mp, fact k0_in, auto)
        finally show "f k0 (lookup_pair xs k0) (lookup_pair ((k', v') # ys) k0) = Some Eq" .
      next
        have "f k v 0 = f k (lookup_pair ((k, v) # xs) k) (lookup_pair ((k', v') # ys) k)"
          by (simp add: \<open>key_compare ko k k' = Lt\<close>)
        also have "... = Some Eq" by (rule Cons(6), simp)
        finally show "f k v 0 = Some Eq" .
      qed
    next
      assume "key_compare ko k k' = Eq"
      hence "k = k'" by (simp only: key_compare_Eq)
      show "(let aux = f k v v' in if aux = Some Eq then lex_ord_pair f xs ys else aux) = Some Eq"
      proof (simp add: Let_def, intro conjI impI, rule *(5), rule Cons(2))
        fix k0
        assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ys"
        hence "k0 \<noteq> k'"
        proof
          assume "k0 \<in> fst ` set xs"
          hence "lt_of_key_order ko k k0" by (rule *(4))
          thus ?thesis by (simp add: \<open>k = k'\<close>)
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt_of_key_order ko k' k0" by (rule Cons(4))
          thus ?thesis by simp
        qed
        hence "f k0 (lookup_pair xs k0) (lookup_pair ys k0) =
                f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
          by (simp add: lookup_pair_Cons[OF *(1)] lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps,
              auto simp: \<open>k = k'\<close>)
        also have "... = Some Eq" by (rule Cons(6), rule set_rev_mp, fact k0_in, auto)
        finally show "f k0 (lookup_pair xs k0) (lookup_pair ys k0) = Some Eq" .
      next
        have "f k v v' = f k (lookup_pair ((k, v) # xs) k) (lookup_pair ((k', v') # ys) k)"
          by (simp add: \<open>k = k'\<close>)
        also have "... = Some Eq" by (rule Cons(6), simp)
        finally show "f k v v' = Some Eq" .
      qed
    next
      assume "key_compare ko k k' = Gt"
      hence "key_compare ko k' k = Lt" by (simp only: key_compare_Gt)
      show "(let aux = f k' 0 v' in if aux = Some Eq then lex_ord_pair f ((k, v) # xs) ys else aux) = Some Eq"
      proof (simp add: Let_def, intro conjI impI, rule Cons(5))
        fix k0
        assume k0_in: "k0 \<in> fst ` set ((k, v) # xs) \<union> fst ` set ys"
        hence "k0 \<in> fst ` set xs \<or> k0 = k \<or> k0 \<in> fst ` set ys" by auto
        hence "k0 \<noteq> k'"
        proof (elim disjE)
          assume "k0 \<in> fst ` set xs"
          hence "lt_of_key_order ko k k0" by (rule *(4))
          with \<open>key_compare ko k' k = Lt\<close> show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
        next
          assume "k0 = k"
          with \<open>key_compare ko k' k = Lt\<close> show ?thesis by auto
        next
          assume "k0 \<in> fst ` set ys"
          hence "lt_of_key_order ko k' k0" by (rule Cons(4))
          thus ?thesis by simp
        qed
        hence "f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ys k0) =
                f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ((k', v') # ys) k0)"
          by (auto simp add: lookup_pair_Cons[OF Cons(1)] simp del: lookup_pair.simps)
        also have "... = Some Eq" by (rule Cons(6), rule set_rev_mp, fact k0_in, auto)
        finally show "f k0 (lookup_pair ((k, v) # xs) k0) (lookup_pair ys k0) = Some Eq" .
      next
        have "f k' 0 v' = f k' (lookup_pair ((k, v) # xs) k') (lookup_pair ((k', v') # ys) k')"
          by (simp add: \<open>key_compare ko k' k = Lt\<close>)
        also have "... = Some Eq" by (rule Cons(6), simp)
        finally show "f k' 0 v' = Some Eq" .
      qed
    qed
  qed
qed

lemma lex_ord_pair_valI:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)" and "aux \<noteq> Some Eq"
  assumes "k \<in> fst ` set xs \<union> fst ` set ys" and "aux = f k (lookup_pair xs k) (lookup_pair ys k)"
    and "\<And>k'. k' \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> lt_of_key_order ko k' k \<Longrightarrow>
              f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq"
  shows "lex_ord_pair f xs ys = aux"
  using assms(1, 2, 4, 5, 6)
proof (induct xs arbitrary: ys rule: oalist_inv_induct)
  case Nil
  thus ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    from Nil(1) show ?case by simp
  next
    case (Cons k' v' ys)
    from Cons(6) have "k = k' \<or> k \<in> fst ` set ys" by simp
    thus ?case
    proof
      assume "k = k'"
      with Cons(7) have "f k' 0 v' = aux" by simp
      thus ?thesis by (simp add: Let_def \<open>k = k'\<close> assms(3))
    next
      assume "k \<in> fst `set ys"
      hence "lt_of_key_order ko k' k" by (rule Cons(4))
      hence "key_compare ko k k' = Gt" by (simp add: lt_of_key_order_alt key_compare_Gt)
      hence eq1: "lookup_pair ((k', v') # ys) k = lookup_pair ys k" by simp
      have "f k' (lookup_pair [] k') (lookup_pair ((k', v') # ys) k') = Some Eq"
        by (rule Cons(8), simp, fact)
      hence eq2: "f k' 0 v' = Some Eq" by simp
      show ?thesis
      proof (simp add: Let_def eq2, rule Cons(5))
        from \<open>k \<in> fst `set ys\<close> show "k \<in> fst ` set [] \<union> fst ` set ys" by simp
      next
        show "aux = f k (lookup_pair [] k) (lookup_pair ys k)" by (simp only: Cons(7) eq1)
      next
        fix k0
        assume "lt_of_key_order ko k0 k"
        assume "k0 \<in> fst ` set [] \<union> fst ` set ys"
        hence k0_in: "k0 \<in> fst ` set ys" by simp
        hence "lt_of_key_order ko k' k0" by (rule Cons(4))
        hence "key_compare ko k0 k' = Gt" by (simp add: lt_of_key_order_alt key_compare_Gt)
        hence "f k0 (lookup_pair [] k0) (lookup_pair ys k0) =
                f k0 (lookup_pair [] k0) (lookup_pair ((k', v') # ys) k0)" by simp
        also have "... = Some Eq" by (rule Cons(8), simp add: k0_in, fact)
        finally show "f k0 (lookup_pair [] k0) (lookup_pair ys k0) = Some Eq" .
      qed
    qed
  qed
next
  case *: (Cons k' v' xs)
  from *(6, 7, 8, 9) show ?case
  proof (induct ys rule: oalist_inv_induct)
    case Nil
    from Nil(1) have "k = k' \<or> k \<in> fst ` set xs" by simp
    thus ?case
    proof
      assume "k = k'"
      with Nil(2) have "f k' v' 0 = aux" by simp
      thus ?thesis by (simp add: Let_def \<open>k = k'\<close> assms(3))
    next
      assume "k \<in> fst ` set xs"
      hence "lt_of_key_order ko k' k" by (rule *(4))
      hence "key_compare ko k k' = Gt" by (simp add: lt_of_key_order_alt key_compare_Gt)
      hence eq1: "lookup_pair ((k', v') # xs) k = lookup_pair xs k" by simp
      have "f k' (lookup_pair ((k', v') # xs) k') (lookup_pair [] k') = Some Eq"
        by (rule Nil(3), simp, fact)
      hence eq2: "f k' v' 0 = Some Eq" by simp
      show ?thesis
      proof (simp add: Let_def eq2, rule *(5), fact oalist_inv_Nil)
        from \<open>k \<in> fst `set xs\<close> show "k \<in> fst ` set xs \<union> fst ` set []" by simp
      next
        show "aux = f k (lookup_pair xs k) (lookup_pair [] k)" by (simp only: Nil(2) eq1)
      next
        fix k0
        assume "lt_of_key_order ko k0 k"
        assume "k0 \<in> fst ` set xs \<union> fst ` set []"
        hence k0_in: "k0 \<in> fst ` set xs" by simp
        hence "lt_of_key_order ko k' k0" by (rule *(4))
        hence "key_compare ko k0 k' = Gt" by (simp add: lt_of_key_order_alt key_compare_Gt)
        hence "f k0 (lookup_pair xs k0) (lookup_pair [] k0) =
                f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair [] k0)" by simp
        also have "... = Some Eq" by (rule Nil(3), simp add: k0_in, fact)
        finally show "f k0 (lookup_pair xs k0) (lookup_pair [] k0) = Some Eq" .
      qed
    qed
  next
    case (Cons k'' v'' ys)

    have 0: thesis if 1: "lt_of_key_order ko k k'" and 2: "lt_of_key_order ko k k''" for thesis
    proof -
      from 1 have "k \<noteq> k'" by simp
      moreover from 2 have "k \<noteq> k''" by simp
      ultimately have "k \<in> fst ` set xs \<or> k \<in> fst ` set ys" using Cons(6) by simp
      thus ?thesis
      proof
        assume "k \<in> fst ` set xs"
        hence "lt_of_key_order ko k' k" by (rule *(4))
        with 1 show ?thesis by simp
      next
        assume "k \<in> fst ` set ys"
        hence "lt_of_key_order ko k'' k" by (rule Cons(4))
        with 2 show ?thesis by simp
      qed
    qed

    show ?case
    proof (simp split: order.split, intro conjI impI)
      assume Lt: "key_compare ko k' k'' = Lt"
      show "(let aux = f k' v' 0 in if aux = Some Eq then lex_ord_pair f xs ((k'', v'') # ys) else aux) = aux"
      proof (simp add: Let_def split: order.split, intro conjI impI)
        assume "f k' v' 0 = Some Eq"
        have "k \<noteq> k'"
        proof
          assume "k = k'"
          have "aux = f k v' 0" by (simp add: Cons(7) \<open>k = k'\<close> Lt)
          with \<open>f k' v' 0 = Some Eq\<close> assms(3) show False by (simp add: \<open>k = k'\<close>)
        qed
        from Cons(1) show "lex_ord_pair f xs ((k'', v'') # ys) = aux"
        proof (rule *(5))
          from Cons(6) \<open>k \<noteq> k'\<close> show "k \<in> fst ` set xs \<union> fst ` set ((k'', v'') # ys)" by simp
        next
          show "aux = f k (lookup_pair xs k) (lookup_pair ((k'', v'') # ys) k)"
            by (simp add: Cons(7) lookup_pair_Cons[OF *(1)] \<open>k \<noteq> k'\<close>[symmetric] del: lookup_pair.simps)
        next
          fix k0
          assume "lt_of_key_order ko k0 k"
          assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ((k'', v'') # ys)"
          also have "... \<subseteq> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by fastforce
          finally have k0_in': "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" .
          have "k' \<noteq> k0"
          proof
            assume "k' = k0"
            with k0_in have "k' \<in> fst ` set xs \<union> fst ` set ((k'', v'') # ys)" by simp
            with Lt have "k' \<in> fst ` set xs \<or> k' \<in> fst ` set ys" by auto
            thus False
            proof
              assume "k' \<in> fst ` set xs"
              hence "lt_of_key_order ko k' k'" by (rule *(4))
              thus ?thesis by simp
            next
              assume "k' \<in> fst ` set ys"
              hence "lt_of_key_order ko k'' k'" by (rule Cons(4))
              with Lt show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
            qed
          qed
          hence "f k0 (lookup_pair xs k0) (lookup_pair ((k'', v'') # ys) k0) =
                  f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ((k'', v'') # ys) k0)"
            by (simp add: lookup_pair_Cons[OF *(1)] del: lookup_pair.simps)
          also from k0_in' \<open>lt_of_key_order ko k0 k\<close> have "... = Some Eq" by (rule Cons(8))
          finally show "f k0 (lookup_pair xs k0) (lookup_pair ((k'', v'') # ys) k0) = Some Eq" .
        qed
      next
        assume "f k' v' 0 \<noteq> Some Eq"
        have "\<not> lt_of_key_order ko k' k"
        proof
          have "k' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by simp
          moreover assume "lt_of_key_order ko k' k"
          ultimately have "f k' (lookup_pair ((k', v') # xs) k') (lookup_pair ((k'', v'') # ys) k') = Some Eq"
            by (rule Cons(8))
          hence "f k' v' 0 = Some Eq" by (simp add: Lt)
          with \<open>f k' v' 0 \<noteq> Some Eq\<close> show False ..
        qed
        moreover have "\<not> lt_of_key_order ko k k'"
        proof
          assume "lt_of_key_order ko k k'"
          moreover from this Lt have "lt_of_key_order ko k k''"
            by (simp add: lt_of_key_order_alt[symmetric])
          ultimately show False by (rule 0)
        qed
        ultimately have "k = k'" by simp
        show "f k' v' 0 = aux" by (simp add: Cons(7) \<open>k = k'\<close> Lt)
      qed
    next
      assume "key_compare ko k' k'' = Eq"
      hence "k' = k''" by (simp only: key_compare_Eq)
      show "(let aux = f k' v' v'' in if aux = Some Eq then lex_ord_pair f xs ys else aux) = aux"
      proof (simp add: Let_def \<open>k' = k''\<close> split: order.split, intro conjI impI)
        assume "f k'' v' v'' = Some Eq"
        have "k \<noteq> k''"
        proof
          assume "k = k''"
          have "aux = f k v' v''" by (simp add: Cons(7) \<open>k = k''\<close> \<open>k' = k''\<close>)
          with \<open>f k'' v' v'' = Some Eq\<close> assms(3) show False by (simp add: \<open>k = k''\<close>)
        qed
        from Cons(2) show "lex_ord_pair f xs ys = aux"
        proof (rule *(5))
          from Cons(6) \<open>k \<noteq> k''\<close> show "k \<in> fst ` set xs \<union> fst ` set ys" by (simp add: \<open>k' = k''\<close>)
        next
          show "aux = f k (lookup_pair xs k) (lookup_pair ys k)"
            by (simp add: Cons(7) lookup_pair_Cons[OF *(1)] lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps,
                simp add: \<open>k' = k''\<close> \<open>k \<noteq> k''\<close>[symmetric])
        next
          fix k0
          assume "lt_of_key_order ko k0 k"
          assume k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ys"
          also have "... \<subseteq> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by fastforce
          finally have k0_in': "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" .
          have "k'' \<noteq> k0"
          proof
            assume "k'' = k0"
            with k0_in have "k'' \<in> fst ` set xs \<union> fst ` set ys" by simp
            thus False
            proof
              assume "k'' \<in> fst ` set xs"
              hence "lt_of_key_order ko k' k''" by (rule *(4))
              thus ?thesis by (simp add: \<open>k' = k''\<close>)
            next
              assume "k'' \<in> fst ` set ys"
              hence "lt_of_key_order ko k'' k''" by (rule Cons(4))
              thus ?thesis by simp
            qed
          qed
          hence "f k0 (lookup_pair xs k0) (lookup_pair ys k0) =
                  f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ((k'', v'') # ys) k0)"
            by (simp add: lookup_pair_Cons[OF *(1)] lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps,
                simp add: \<open>k' = k''\<close>)
          also from k0_in' \<open>lt_of_key_order ko k0 k\<close> have "... = Some Eq" by (rule Cons(8))
          finally show "f k0 (lookup_pair xs k0) (lookup_pair ys k0) = Some Eq" .
        qed
      next
        assume "f k'' v' v'' \<noteq> Some Eq"
        have "\<not> lt_of_key_order ko k'' k"
        proof
          have "k'' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by simp
          moreover assume "lt_of_key_order ko k'' k"
          ultimately have "f k'' (lookup_pair ((k', v') # xs) k'') (lookup_pair ((k'', v'') # ys) k'') = Some Eq"
            by (rule Cons(8))
          hence "f k'' v' v'' = Some Eq" by (simp add: \<open>k' = k''\<close>)
          with \<open>f k'' v' v'' \<noteq> Some Eq\<close> show False ..
        qed
        moreover have "\<not> lt_of_key_order ko k k''"
        proof
          assume "lt_of_key_order ko k k''"
          hence "lt_of_key_order ko k k'" by (simp only: \<open>k' = k''\<close>)
          thus False using \<open>lt_of_key_order ko k k''\<close> by (rule 0)
        qed
        ultimately have "k = k''" by simp
        show "f k'' v' v'' = aux" by (simp add: Cons(7) \<open>k = k''\<close> \<open>k' = k''\<close>)
      qed
    next
      assume Gt: "key_compare ko k' k'' = Gt"
      hence Lt: "key_compare ko k'' k' = Lt" by (simp only: key_compare_Gt)
      show "(let aux = f k'' 0 v'' in if aux = Some Eq then lex_ord_pair f ((k', v') # xs) ys else aux) = aux"
      proof (simp add: Let_def split: order.split, intro conjI impI)
        assume "f k'' 0 v'' = Some Eq"
        have "k \<noteq> k''"
        proof
          assume "k = k''"
          have "aux = f k 0 v''" by (simp add: Cons(7) \<open>k = k''\<close> Lt)
          with \<open>f k'' 0 v'' = Some Eq\<close> assms(3) show False by (simp add: \<open>k = k''\<close>)
        qed
        show "lex_ord_pair f ((k', v') # xs) ys = aux"
        proof (rule Cons(5))
          from Cons(6) \<open>k \<noteq> k''\<close> show "k \<in> fst ` set ((k', v') # xs) \<union> fst ` set ys" by simp
        next
          show "aux = f k (lookup_pair ((k', v') # xs) k) (lookup_pair ys k)"
            by (simp add: Cons(7) lookup_pair_Cons[OF Cons(1)] \<open>k \<noteq> k''\<close>[symmetric] del: lookup_pair.simps)
        next
          fix k0
          assume "lt_of_key_order ko k0 k"
          assume k0_in: "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ys"
          also have "... \<subseteq> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by fastforce
          finally have k0_in': "k0 \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" .
          have "k'' \<noteq> k0"
          proof
            assume "k'' = k0"
            with k0_in have "k'' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ys" by simp
            with Lt have "k'' \<in> fst ` set xs \<or> k'' \<in> fst ` set ys" by auto
            thus False
            proof
              assume "k'' \<in> fst ` set xs"
              hence "lt_of_key_order ko k' k''" by (rule *(4))
              with Lt show ?thesis by (simp add: lt_of_key_order_alt[symmetric])
            next
              assume "k'' \<in> fst ` set ys"
              hence "lt_of_key_order ko k'' k''" by (rule Cons(4))
              thus ?thesis by simp
            qed
          qed
          hence "f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ys k0) =
                  f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ((k'', v'') # ys) k0)"
            by (simp add: lookup_pair_Cons[OF Cons(1)] del: lookup_pair.simps)
          also from k0_in' \<open>lt_of_key_order ko k0 k\<close> have "... = Some Eq" by (rule Cons(8))
          finally show "f k0 (lookup_pair ((k', v') # xs) k0) (lookup_pair ys k0) = Some Eq" .
        qed
      next
        assume "f k'' 0 v'' \<noteq> Some Eq"
        have "\<not> lt_of_key_order ko k'' k"
        proof
          have "k'' \<in> fst ` set ((k', v') # xs) \<union> fst ` set ((k'', v'') # ys)" by simp
          moreover assume "lt_of_key_order ko k'' k"
          ultimately have "f k'' (lookup_pair ((k', v') # xs) k'') (lookup_pair ((k'', v'') # ys) k'') = Some Eq"
            by (rule Cons(8))
          hence "f k'' 0 v'' = Some Eq" by (simp add: Lt)
          with \<open>f k'' 0 v'' \<noteq> Some Eq\<close> show False ..
        qed
        moreover have "\<not> lt_of_key_order ko k k''"
        proof
          assume "lt_of_key_order ko k k''"
          with Lt have "lt_of_key_order ko k k'" by (simp add: lt_of_key_order_alt[symmetric])
          thus False using \<open>lt_of_key_order ko k k''\<close> by (rule 0)
        qed
        ultimately have "k = k''" by simp
        show "f k'' 0 v'' = aux" by (simp add: Cons(7) \<open>k = k''\<close> Lt)
      qed
    qed
  qed
qed

lemma lex_ord_pair_EqD:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)" and "lex_ord_pair f xs ys = Some Eq"
    and "k \<in> fst ` set xs \<union> fst ` set ys"
  shows "f k (lookup_pair xs k) (lookup_pair ys k) = Some Eq"
proof (rule ccontr)
  let ?A = "(fst ` set xs \<union> fst ` set ys) \<inter> {k. f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq}"
  define k0 where "k0 = key_order_lin.Min ko ?A"
  have "finite ?A" by auto
  assume "f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq"
  with assms(4) have "k \<in> ?A" by simp
  hence "?A \<noteq> {}" by blast
  with \<open>finite ?A\<close> have "k0 \<in> ?A" unfolding k0_def by (rule key_order_lin.Min_in)
  hence k0_in: "k0 \<in> fst ` set xs \<union> fst ` set ys"
    and neq: "f k0 (lookup_pair xs k0) (lookup_pair ys k0) \<noteq> Some Eq" by simp_all
  have "le_of_key_order ko k0 k'" if "k' \<in> ?A" for k' unfolding k0_def using \<open>finite ?A\<close> that
    by (rule key_order_lin.Min_le)
  hence "f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq"
    if "k' \<in> fst ` set xs \<union> fst ` set ys" and "lt_of_key_order ko k' k0" for k' using that by fastforce
  with assms(1, 2) neq k0_in refl have "lex_ord_pair f xs ys = f k0 (lookup_pair xs k0) (lookup_pair ys k0)"
    by (rule lex_ord_pair_valI)
  with assms(3) neq show False by simp
qed

lemma lex_ord_pair_valE:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)" and "lex_ord_pair f xs ys = aux"
    and "aux \<noteq> Some Eq"
  obtains k where "k \<in> fst ` set xs \<union> fst ` set ys" and "aux = f k (lookup_pair xs k) (lookup_pair ys k)"
    and "\<And>k'. k' \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> lt_of_key_order ko k' k \<Longrightarrow>
            f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq"
proof -
  let ?A = "(fst ` set xs \<union> fst ` set ys) \<inter> {k. f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq}"
  define k where "k = key_order_lin.Min ko ?A"
  have "finite ?A" by auto
  have "\<exists>k \<in> fst ` set xs \<union> fst ` set ys. f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq" (is ?prop)
  proof (rule ccontr)
    assume "\<not> ?prop"
    hence "f k (lookup_pair xs k) (lookup_pair ys k) = Some Eq"
      if "k \<in> fst ` set xs \<union> fst ` set ys" for k using that by auto
    with assms(1, 2) have "lex_ord_pair f xs ys = Some Eq" by (rule lex_ord_pair_EqI)
    with assms(3, 4) show False by simp
  qed
  then obtain k0 where "k0 \<in> fst ` set xs \<union> fst ` set ys"
    and "f k0 (lookup_pair xs k0) (lookup_pair ys k0) \<noteq> Some Eq" ..
  hence "k0 \<in> ?A" by simp
  hence "?A \<noteq> {}" by blast
  with \<open>finite ?A\<close> have "k \<in> ?A" unfolding k_def by (rule key_order_lin.Min_in)
  hence k_in: "k \<in> fst ` set xs \<union> fst ` set ys"
    and neq: "f k (lookup_pair xs k) (lookup_pair ys k) \<noteq> Some Eq" by simp_all
  have "le_of_key_order ko k k'" if "k' \<in> ?A" for k' unfolding k_def using \<open>finite ?A\<close> that
    by (rule key_order_lin.Min_le)
  hence *: "\<And>k'. k' \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> lt_of_key_order ko k' k \<Longrightarrow>
            f k' (lookup_pair xs k') (lookup_pair ys k') = Some Eq" by fastforce
  with assms(1, 2) neq k_in refl have "lex_ord_pair f xs ys = f k (lookup_pair xs k) (lookup_pair ys k)"
    by (rule lex_ord_pair_valI)
  hence "aux = f k (lookup_pair xs k) (lookup_pair ys k)" by (simp only: assms(3))
  with k_in show ?thesis using * ..
qed

subsubsection \<open>@{const prod_ord_pair}\<close>

lemma prod_ord_pair_eq_lex_ord_pair:
  "prod_ord_pair P xs ys = (lex_ord_pair (\<lambda>k x y. if P k x y then Some Eq else None) xs ys = Some Eq)"
proof (induct P xs ys rule: prod_ord_pair.induct)
  case (1 P)
  show ?case by simp
next
  case (2 P ky vy ys)
  thus ?case by simp
next
  case (3 P kx vx xs)
  thus ?case by simp
next
  case (4 P kx vx xs ky vy ys)
  show ?case
  proof (cases "key_compare ko kx ky")
    case Lt
    thus ?thesis by (simp add: 4(2)[OF Lt])
  next
    case Eq
    thus ?thesis by (simp add: 4(1)[OF Eq])
  next
    case Gt
    thus ?thesis by (simp add: 4(3)[OF Gt])
  qed
qed

lemma prod_ord_pairI:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)"
    and "\<And>k. k \<in> fst ` set xs \<union> fst ` set ys \<Longrightarrow> P k (lookup_pair xs k) (lookup_pair ys k)"
  shows "prod_ord_pair P xs ys"
  unfolding prod_ord_pair_eq_lex_ord_pair by (rule lex_ord_pair_EqI, fact, fact, simp add: assms(3))

lemma prod_ord_pairD:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)" and "prod_ord_pair P xs ys"
    and "k \<in> fst ` set xs \<union> fst ` set ys"
  shows "P k (lookup_pair xs k) (lookup_pair ys k)"
proof -
  from assms have "(if P k (lookup_pair xs k) (lookup_pair ys k) then Some Eq else None) = Some Eq"
    unfolding prod_ord_pair_eq_lex_ord_pair by (rule lex_ord_pair_EqD)
  thus ?thesis by (simp split: if_splits)
qed

corollary prod_ord_pair_alt:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)"
  shows "(prod_ord_pair P xs ys) \<longleftrightarrow> (\<forall>k\<in>fst ` set xs \<union> fst ` set ys. P k (lookup_pair xs k) (lookup_pair ys k))"
  using prod_ord_pairI[OF assms] prod_ord_pairD[OF assms] by meson

subsubsection \<open>@{const sort_oalist}\<close>

lemma oalist_inv_foldr_update_by_pair:
  assumes "oalist_inv (ys, ko)"
  shows "oalist_inv (foldr update_by_pair xs ys, ko)"
proof (induct xs)
  case Nil
  from assms show ?case by simp
next
  case (Cons x xs)
  hence "oalist_inv (update_by_pair x (foldr update_by_pair xs ys), ko)"
    by (rule oalist_inv_update_by_pair)
  thus ?case by simp
qed

corollary oalist_inv_sort_oalist: "oalist_inv (sort_oalist xs, ko)"
proof -
  from oalist_inv_Nil have "oalist_inv (foldr local.update_by_pair xs [], ko)"
    by (rule oalist_inv_foldr_update_by_pair)
  thus "oalist_inv (sort_oalist xs, ko)" by (simp only: sort_oalist_def)
qed

lemma sort_oalist_id:
  assumes "oalist_inv (xs, ko)"
  shows "sort_oalist xs = xs"
proof -
  have "foldr update_by_pair xs ys = xs @ ys" if "oalist_inv (xs @ ys, ko)" for ys using assms that
  proof (induct xs rule: oalist_inv_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v xs)
    from Cons(6) have *: "oalist_inv ((k, v) # (xs @ ys), ko)" by simp
    hence 1: "oalist_inv (xs @ ys, ko)" by (rule oalist_inv_ConsD1)
    hence 2: "foldr update_by_pair xs ys = xs @ ys" by (rule Cons(5))
    show ?case
    proof (simp add: 2, rule update_by_pair_less)
      from * show "v \<noteq> 0" by (auto simp: oalist_inv_def)
    next
      have "key_compare ko k (fst (hd (xs @ ys))) = Lt \<or> xs @ ys = []"
      proof (rule disjCI)
        assume "xs @ ys \<noteq> []"
        then obtain k'' v'' zs where eq: "xs @ ys = (k'', v'') # zs"
          using list.exhaust prod.exhaust by metis
        from * have "lt_of_key_order ko k k''" by (simp add: eq oalist_inv_def)
        thus "key_compare ko k (fst (hd (xs @ ys))) = Lt" by (simp add: eq lt_of_key_order_alt)
      qed
      thus "xs @ ys = [] \<or> key_compare ko k (fst (hd (xs @ ys))) = Lt" by auto
    qed
  qed
  with assms show ?thesis by (simp add: sort_oalist_def)
qed

end

lemma set_sort_oalist:
  assumes "oalist_inv (xs, ko1)"
  shows "set (sort_oalist ko2 xs) = set xs"
proof -
  have rl: "set (foldr (update_by_pair ko2) xs ys) = set xs \<union> set ys"
    if "oalist_inv (ys, ko2)" and "fst ` set xs \<inter> fst ` set ys = {}" for ys
    using assms that(2)
  proof (induct xs rule: oalist_inv_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v xs)
    from Cons(6) have "k \<notin> fst ` set ys" and "fst ` set xs \<inter> fst ` set ys = {}" by simp_all
    from this(2) have eq1: "set (foldr (update_by_pair ko2) xs ys) = set xs \<union> set ys" by (rule Cons(5))
    have "\<not> lt_of_key_order ko1 k k" by auto
    with Cons(4) have "k \<notin> fst ` set xs" by blast
    with \<open>k \<notin> fst ` set ys\<close> have "k \<notin> fst ` (set xs \<union> set ys)" by (simp add: image_Un)
    hence "(set xs \<union> set ys) \<inter> range (Pair k) = {}" by (smt Int_emptyI fstI image_iff)
    hence eq2: "(set xs \<union> set ys) - range (Pair k) = set xs \<union> set ys" by (rule Diff_triv)
    from \<open>oalist_inv (ys, ko2)\<close> have "oalist_inv (foldr (update_by_pair ko2) xs ys, ko2)"
      by (rule oalist_inv_foldr_update_by_pair)
    hence "set (update_by_pair ko2 (k, v) (foldr (update_by_pair ko2) xs ys)) =
            insert (k, v) (set (foldr (update_by_pair ko2) xs ys) - range (Pair k))"
      using Cons(3) by (rule set_update_by_pair)
    also have "... = insert (k, v) (set xs \<union> set ys)" by (simp only: eq1 eq2)
    finally show ?case by simp
  qed
  have "set (foldr (update_by_pair ko2) xs []) = set xs \<union> set []"
    by (rule rl, fact oalist_inv_Nil, simp)
  thus ?thesis by (simp add: sort_oalist_def)
qed

lemma lookup_pair_eqI:
  assumes "oalist_inv (xs, ox)" and "oalist_inv (ys, oy)" and "set xs = set ys"
  shows "lookup_pair ox xs = lookup_pair oy ys"
proof
  fix k
  show "lookup_pair ox xs k = lookup_pair oy ys k"
  proof (cases "lookup_pair oy ys k = 0")
    case True
    with assms(2) have "k \<notin> fst ` set ys" by (simp add: lookup_pair_eq_0)
    with assms(1) show ?thesis by (simp add: True assms(3)[symmetric] lookup_pair_eq_0)
  next
    case False
    define v where "v = lookup_pair oy ys k"
    from False have "v \<noteq> 0" by (simp add: v_def)
    with assms(2) v_def[symmetric] have "(k, v) \<in> set ys" by (simp add: lookup_pair_eq_value)
    with assms(1) \<open>v \<noteq> 0\<close> have "lookup_pair ox xs k = v"
      by (simp add: assms(3)[symmetric] lookup_pair_eq_value)
    thus ?thesis by (simp only: v_def)
  qed
qed

corollary lookup_pair_sort_oalist:
  assumes "oalist_inv (xs, ko1)"
  shows "lookup_pair ko2 (sort_oalist ko2 xs) = lookup_pair ko1 xs"
  by (rule lookup_pair_eqI, rule oalist_inv_sort_oalist, fact, rule set_sort_oalist, fact)

subsection \<open>Operations on Raw Ordered Associative Lists\<close>

type_synonym ('a, 'b) oalist_raw = "('a \<times> 'b) list \<times> 'a key_order"

fun sort_oalist_aux :: "'a key_order \<Rightarrow> ('a, 'b) oalist_raw \<Rightarrow> ('a \<times> 'b::zero) list"
  where "sort_oalist_aux ko (xs, ox) = (if ko = ox then xs else sort_oalist ko xs)"

fun lookup_raw :: "('a, 'b) oalist_raw \<Rightarrow> 'a \<Rightarrow> 'b::zero"
  where "lookup_raw (xs, ko) = lookup_pair ko xs"

definition sorted_domain_raw :: "'a key_order \<Rightarrow> ('a, 'b::zero) oalist_raw \<Rightarrow> 'a list"
  where "sorted_domain_raw ko xs = map fst (sort_oalist_aux ko xs)"

definition except_min_raw :: "'a key_order \<Rightarrow> ('a, 'b) oalist_raw \<Rightarrow> ('a, 'b::zero) oalist_raw"
  where "except_min_raw ko xs = (List.tl (sort_oalist_aux ko xs), ko)"

fun min_key_val_raw :: "'a key_order \<Rightarrow> ('a, 'b) oalist_raw \<Rightarrow> ('a \<times> 'b::zero)"
  where "min_key_val_raw ko (xs, ox) =
      (if ko = ox then List.hd else min_list_param (\<lambda>x y. le_of_key_order ko (fst x) (fst y))) xs"

fun update_by_raw :: "('a \<times> 'b) \<Rightarrow> ('a, 'b) oalist_raw \<Rightarrow> ('a, 'b::zero) oalist_raw"
  where "update_by_raw kv (xs, ko) = (update_by_pair ko kv xs, ko)"

fun update_by_fun_raw :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist_raw \<Rightarrow> ('a, 'b::zero) oalist_raw"
  where "update_by_fun_raw k f (xs, ko) = (update_by_fun_pair ko k f xs, ko)"

fun update_by_fun_gr_raw :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist_raw \<Rightarrow> ('a, 'b::zero) oalist_raw"
  where "update_by_fun_gr_raw k f (xs, ko) = (update_by_fun_gr_pair ko k f xs, ko)"

fun filter_raw :: "(('a \<times> 'b) \<Rightarrow> bool) \<Rightarrow> ('a, 'b) oalist_raw \<Rightarrow> ('a, 'b::zero) oalist_raw"
  where "filter_raw P (xs, ko) = (filter P xs, ko)"

fun map_raw :: "(('a \<times> 'b) \<Rightarrow> ('a \<times> 'c)) \<Rightarrow> ('a, 'b::zero) oalist_raw \<Rightarrow> ('a, 'c::zero) oalist_raw"
  where "map_raw f (xs, ko) = (map_pair f xs, ko)"

abbreviation map_val_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b::zero) oalist_raw \<Rightarrow> ('a, 'c::zero) oalist_raw"
  where "map_val_raw f \<equiv> map_raw (\<lambda>(k, v). (k, f k v))"

fun map2_val_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> (('a, 'b) oalist_raw \<Rightarrow> ('a, 'd) oalist_raw) \<Rightarrow>
                      (('a, 'c) oalist_raw \<Rightarrow> ('a, 'd) oalist_raw) \<Rightarrow>
                      ('a, 'b::zero) oalist_raw \<Rightarrow> ('a, 'c::zero) oalist_raw \<Rightarrow>
                      ('a, 'd::zero) oalist_raw"
  where "map2_val_raw f g h (xs, ox) ys =
            (map2_val_pair ox f (\<lambda>ko zs. fst (g (zs, ko))) (\<lambda>ko zs. fst (h (zs, ko)))
                    xs (sort_oalist_aux ox ys), ox)"

definition lex_ord_raw :: "('a key_order) \<Rightarrow> ('a \<Rightarrow> (('b, 'c) comp_opt)) \<Rightarrow>
                      (('a, 'b::zero) oalist_raw, ('a, 'c::zero) oalist_raw) comp_opt"
  where "lex_ord_raw ko f xs ys = lex_ord_pair ko f (sort_oalist_aux ko xs) (sort_oalist_aux ko ys)"

fun prod_ord_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b::zero) oalist_raw \<Rightarrow>
                      ('a, 'c::zero) oalist_raw \<Rightarrow> bool"
  where "prod_ord_raw f (xs, ox) ys = prod_ord_pair ox f xs (sort_oalist_aux ox ys)"

fun oalist_eq_raw :: "('a, 'b) oalist_raw \<Rightarrow> ('a, 'b::zero) oalist_raw \<Rightarrow> bool"
  where "oalist_eq_raw (xs, ox) ys = (xs = (sort_oalist_aux ox ys))"

fun sort_oalist_raw :: "('a, 'b) oalist_raw \<Rightarrow> ('a, 'b::zero) oalist_raw"
  where "sort_oalist_raw (xs, ko) = (sort_oalist ko xs, ko)"

subsubsection \<open>@{const sort_oalist_aux}\<close>

lemma set_sort_oalist_aux:
  assumes "oalist_inv xs"
  shows "set (sort_oalist_aux ko xs) = set (fst xs)"
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  from assms show ?thesis by (simp add: xs set_sort_oalist)
qed

lemma oalist_inv_sort_oalist_aux:
  assumes "oalist_inv xs"
  shows "oalist_inv (sort_oalist_aux ko xs, ko)"
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  from assms show ?thesis by (simp add: xs oalist_inv_sort_oalist)
qed

lemma lookup_pair_sort_oalist_aux:
  assumes "oalist_inv xs"
  shows "lookup_pair ko (sort_oalist_aux ko xs) = lookup_raw xs"
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  from assms show ?thesis by (simp add: xs lookup_pair_sort_oalist)
qed

subsubsection \<open>@{const lookup_raw}\<close>

lemma lookup_raw_inj:
  assumes "oalist_inv (xs, ko)" and "oalist_inv (ys, ko)" and "lookup_raw (xs, ko) = lookup_raw (ys, ko)"
  shows "xs = ys"
  using assms unfolding lookup_raw.simps by (rule lookup_pair_inj)

subsubsection \<open>@{const sorted_domain_raw}\<close>

lemma set_sorted_domain_raw:
  assumes "oalist_inv xs"
  shows "set (sorted_domain_raw ko xs) = fst ` set (fst xs)"
  using assms by (simp add: sorted_domain_raw_def set_sort_oalist_aux)

corollary in_sorted_domain_raw_iff_lookup_raw:
  assumes "oalist_inv xs"
  shows "k \<in> set (sorted_domain_raw ko xs) \<longleftrightarrow> (lookup_raw xs k \<noteq> 0)"
  unfolding set_sorted_domain_raw[OF assms]
proof -
  obtain xs' ko' where xs: "xs = (xs', ko')" by fastforce
  from assms show "k \<in> fst ` set (fst xs) \<longleftrightarrow> (lookup_raw xs k \<noteq> 0)"
    by (simp add: xs lookup_pair_eq_0)
qed

lemma sorted_sorted_domain_raw:
  assumes "oalist_inv xs"
  shows "sorted_wrt (lt_of_key_order ko) (sorted_domain_raw ko xs)"
  unfolding sorted_domain_raw_def by (rule oalist_invD2, rule oalist_inv_sort_oalist_aux, fact)

subsubsection \<open>@{const except_min_raw}\<close>

lemma oalist_inv_except_min_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (except_min_raw ko xs)"
  unfolding except_min_raw_def by (rule oalist_inv_tl, rule oalist_inv_sort_oalist_aux, fact)

lemma lookup_raw_except_min_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (except_min_raw ko xs) k =
          (if (\<forall>k'\<in>fst ` set (fst xs). le_of_key_order ko k k') then 0 else lookup_raw xs k)"
  using assms by (simp add: except_min_raw_def lookup_pair_tl oalist_inv_sort_oalist_aux
      lookup_pair_sort_oalist_aux  set_sort_oalist_aux split del: if_split cong: if_cong)

subsubsection \<open>@{const min_key_val_raw}\<close>

lemma min_key_val_raw_in:
  assumes "fst xs \<noteq> []"
  shows "min_key_val_raw ko xs \<in> set (fst xs)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms have "xs' \<noteq> []" by (simp add: xs)
  show ?thesis unfolding xs
  proof (simp, intro conjI impI)
    from \<open>xs' \<noteq> []\<close> show "hd xs' \<in> set xs'" by simp
  next
    from \<open>xs' \<noteq> []\<close> show "min_list_param (\<lambda>x y. le_of_key_order ko (fst x) (fst y)) xs' \<in> set xs'"
      by (rule min_list_param_in)
  qed
qed

lemma snd_min_key_val_raw:
  assumes "oalist_inv xs" and "fst xs \<noteq> []"
  shows "snd (min_key_val_raw ko xs) = lookup_raw xs (fst (min_key_val_raw ko xs))"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv (xs', ox)" by (simp only: xs)
  from assms(2) have "min_key_val_raw ko xs \<in> set (fst xs)" by (rule min_key_val_raw_in)
  hence *: "min_key_val_raw ko (xs', ox) \<in> set xs'" by (simp add: xs)
  show ?thesis unfolding xs lookup_raw.simps
    by (rule sym, rule lookup_pair_eq_valueI, fact, simp add: * del: min_key_val_raw.simps)
qed

lemma min_key_val_raw_minimal:
  assumes "oalist_inv xs" and "z \<in> set (fst xs)"
  shows "le_of_key_order ko (fst (min_key_val_raw ko xs)) (fst z)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms have "oalist_inv (xs', ox)" and "z \<in> set xs'" by (simp_all add: xs)
  show ?thesis unfolding xs
  proof (simp, intro conjI impI)
    from \<open>z \<in> set xs'\<close> have "xs' \<noteq> []" by auto
    then obtain k v ys where xs': "xs' = (k, v) # ys" using prod.exhaust list.exhaust by metis
    from \<open>z \<in> set xs'\<close> have "z = (k, v) \<or> z \<in> set ys" by (simp add: xs')
    thus "le_of_key_order ox (fst (hd xs')) (fst z)"
    proof
      assume "z = (k, v)"
      show ?thesis by (simp add: xs' \<open>z = (k, v)\<close>)
    next
      assume "z \<in> set ys"
      hence "fst z \<in> fst ` set ys" by fastforce
      with \<open>oalist_inv (xs', ox)\<close>[simplified xs'] have "lt_of_key_order ox k (fst z)" by (rule oalist_inv_ConsD3)
      thus ?thesis by (simp add: xs')
    qed
  next
    show "le_of_key_order ko (fst (min_list_param (\<lambda>x y. le_of_key_order ko (fst x) (fst y)) xs')) (fst z)"
    proof (rule min_list_param_minimal[of "\<lambda>x y. le_of_key_order ko (fst x) (fst y)"])
      show "transp (\<lambda>x y. le_of_key_order ko (fst x) (fst y))"
        by (metis (no_types, lifting) key_order_lin.order.trans transpI)
    qed (auto intro: \<open>z \<in> set xs'\<close>)
  qed
qed

subsubsection \<open>@{const filter_raw}\<close>

lemma oalist_inv_filter_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (filter_raw P xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs filter_raw.simps by (rule oalist_inv_filter)
qed

lemma lookup_raw_filter_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (filter_raw P xs) k = (let v = lookup_raw xs k in if P (k, v) then v else 0)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs lookup_raw.simps filter_raw.simps by (rule lookup_pair_filter)
qed

subsubsection \<open>@{const update_by_raw}\<close>

lemma oalist_inv_update_by_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (update_by_raw kv xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs update_by_raw.simps by (rule oalist_inv_update_by_pair)
qed

lemma lookup_raw_update_by_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (update_by_raw (k1, v) xs) k2 = (if k1 = k2 then v else lookup_raw xs k2)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs lookup_raw.simps update_by_raw.simps by (rule lookup_pair_update_by_pair)
qed

subsubsection \<open>@{const update_by_fun_raw} and @{const update_by_fun_gr_raw}\<close>

lemma update_by_fun_raw_eq_update_by_raw:
  assumes "oalist_inv xs"
  shows "update_by_fun_raw k f xs = update_by_raw (k, f (lookup_raw xs k)) xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv (xs', ko)" by (simp only: xs)
  show ?thesis unfolding xs update_by_fun_raw.simps lookup_raw.simps update_by_raw.simps
    by (rule, rule conjI, rule update_by_fun_pair_eq_update_by_pair, fact, fact refl)
qed

corollary oalist_inv_update_by_fun_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (update_by_fun_raw k f xs)"
  unfolding update_by_fun_raw_eq_update_by_raw[OF assms] using assms by (rule oalist_inv_update_by_raw)

corollary lookup_raw_update_by_fun_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (update_by_fun_raw k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_raw xs k2)"
  using assms by (simp add: update_by_fun_raw_eq_update_by_raw lookup_raw_update_by_raw)

lemma update_by_fun_gr_raw_eq_update_by_fun_raw:
  assumes "oalist_inv xs"
  shows "update_by_fun_gr_raw k f xs = update_by_fun_raw k f xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv (xs', ko)" by (simp only: xs)
  show ?thesis unfolding xs update_by_fun_raw.simps lookup_raw.simps update_by_fun_gr_raw.simps
    by (rule, rule conjI, rule update_by_fun_gr_pair_eq_update_by_fun_pair, fact, fact refl)
qed

corollary oalist_inv_update_by_fun_gr_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (update_by_fun_gr_raw k f xs)"
  unfolding update_by_fun_gr_raw_eq_update_by_fun_raw[OF assms] using assms by (rule oalist_inv_update_by_fun_raw)

corollary lookup_raw_update_by_fun_gr_raw:
  assumes "oalist_inv xs"
  shows "lookup_raw (update_by_fun_gr_raw k1 f xs) k2 = (if k1 = k2 then f else id) (lookup_raw xs k2)"
  using assms by (simp add: update_by_fun_gr_raw_eq_update_by_fun_raw lookup_raw_update_by_fun_raw)

subsubsection \<open>@{const map_raw} and @{const map_val_raw}\<close>

lemma oalist_inv_map_raw:
  assumes "oalist_inv xs"
    and "\<And>a b. key_compare (snd xs) (fst (f a)) (fst (f b)) = key_compare (snd xs) (fst a) (fst b)"
  shows "oalist_inv (map_raw f xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms(1) have "oalist_inv (xs', ko)" by (simp only: xs)
  moreover from assms(2) have "\<And>a b. key_compare ko (fst (f a)) (fst (f b)) = key_compare ko (fst a) (fst b)"
    by (simp add: xs)
  ultimately show ?thesis unfolding xs map_raw.simps by (rule oalist_inv_map_pair)
qed

lemma lookup_raw_map_raw:
  assumes "oalist_inv xs"
    and "\<And>k'. snd (f (k', 0)) = 0"
    and "\<And>a b. key_compare (snd xs) (fst (f a)) (fst (f b)) = key_compare (snd xs) (fst a) (fst b)"
  shows "lookup_raw (map_raw f xs) (fst (f (k, v))) = snd (f (k, lookup_raw xs k))"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms(1) have "oalist_inv (xs', ko)" by (simp only: xs)
  moreover note assms(2)
  moreover from assms(3) have "\<And>a b. key_compare ko (fst (f a)) (fst (f b)) = key_compare ko (fst a) (fst b)"
    by (simp add: xs)
  ultimately show ?thesis unfolding xs lookup_raw.simps map_raw.simps by (rule lookup_pair_map_pair)
qed

lemma map_raw_id:
  assumes "oalist_inv xs"
  shows "map_raw id xs = xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv (xs', ko)" by (simp only: xs)
  hence "map_pair id xs' = xs'"
  proof (induct xs' rule: oalist_inv_induct)
    case Nil
    show ?case by simp
  next
    case (Cons k v xs')
    show ?case by (simp add: Let_def Cons(3, 5) id_def[symmetric])
  qed
  thus ?thesis by (simp add: xs)
qed

lemma oalist_inv_map_val_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (map_val_raw f xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs map_raw.simps by (rule oalist_inv_map_val_pair)
qed

lemma lookup_raw_map_val_raw:
  assumes "oalist_inv xs" and "\<And>k'. f k' 0 = 0"
  shows "lookup_raw (map_val_raw f xs) k = f k (lookup_raw xs k)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms show ?thesis unfolding xs map_raw.simps lookup_raw.simps by (rule lookup_pair_map_val_pair)
qed

subsubsection \<open>@{const map2_val_raw}\<close>

definition map2_val_compat' :: "(('a, 'b::zero) oalist_raw \<Rightarrow> ('a, 'c::zero) oalist_raw) \<Rightarrow> bool"
  where "map2_val_compat' f \<longleftrightarrow>
      (\<forall>zs. (oalist_inv zs \<longrightarrow> (oalist_inv (f zs) \<and> snd (f zs) = snd zs \<and> fst ` set (fst (f zs)) \<subseteq> fst ` set (fst zs))))"

lemma map2_val_compat'I:
  assumes "\<And>zs. oalist_inv zs \<Longrightarrow> oalist_inv (f zs)"
    and "\<And>zs. oalist_inv zs \<Longrightarrow> snd (f zs) = snd zs"
    and "\<And>zs. oalist_inv zs \<Longrightarrow> fst ` set (fst (f zs)) \<subseteq> fst ` set (fst zs)"
  shows "map2_val_compat' f"
  unfolding map2_val_compat'_def using assms by blast

lemma map2_val_compat'D1:
  assumes "map2_val_compat' f" and "oalist_inv zs"
  shows "oalist_inv (f zs)"
  using assms unfolding map2_val_compat'_def by blast

lemma map2_val_compat'D2:
  assumes "map2_val_compat' f" and "oalist_inv zs"
  shows "snd (f zs) = snd zs"
  using assms unfolding map2_val_compat'_def by blast

lemma map2_val_compat'D3:
  assumes "map2_val_compat' f" and "oalist_inv zs"
  shows "fst ` set (fst (f zs)) \<subseteq> fst ` set (fst zs)"
  using assms unfolding map2_val_compat'_def by blast

lemma map2_val_compat'_map_val_raw: "map2_val_compat' (map_val_raw f)"
proof (rule map2_val_compat'I, erule oalist_inv_map_val_raw)
  fix zs::"('a, 'b) oalist_raw"
  obtain zs' ko where "zs = (zs', ko)" by fastforce
  thus "snd (map_val_raw f zs) = snd zs" by simp
next
  fix zs::"('a, 'b) oalist_raw"
  obtain zs' ko where zs: "zs = (zs', ko)" by fastforce
  show "fst ` set (fst (map_val_raw f zs)) \<subseteq> fst ` set (fst zs)"
  proof (simp add: zs)
    from map_pair_subset have "fst ` set (map_val_pair f zs') \<subseteq> fst ` (\<lambda>(k, v). (k, f k v)) ` set zs'"
      by (rule image_mono)
    also have "... = fst ` set zs'" by force
    finally show "fst ` set (map_val_pair f zs') \<subseteq> fst ` set zs'" .
  qed
qed

lemma map2_val_compat'_id: "map2_val_compat' id"
  by (rule map2_val_compat'I, auto)

lemma map2_val_compat'_imp_map2_val_compat:
  assumes "map2_val_compat' g"
  shows "map2_val_compat ko (\<lambda>ko zs. fst (g (zs, ko)))"
proof (rule map2_val_compatI)
  fix zs::"('a \<times> 'b) list"
  assume a: "oalist_inv (zs, ko)"
  with assms have "oalist_inv (g (zs, ko))" by (rule map2_val_compat'D1)
  hence "oalist_inv (fst (g (zs, ko)), snd (g (zs, ko)))" by simp
  thus "oalist_inv (fst (g (zs, ko)), ko)" using assms a by (simp add: map2_val_compat'D2)
next
  fix zs::"('a \<times> 'b) list"
  assume a: "oalist_inv (zs, ko)"
  with assms have "fst ` set (fst (g (zs, ko))) \<subseteq> fst ` set (fst (zs, ko))" by (rule map2_val_compat'D3)
  thus "fst ` set (fst (g (zs, ko))) \<subseteq> fst ` set zs" by simp
qed

lemma oalist_inv_map2_val_raw:
  assumes "oalist_inv xs" and "oalist_inv ys"
  assumes "map2_val_compat' g" and "map2_val_compat' h"
  shows "oalist_inv (map2_val_raw f g h xs ys)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  let ?ys = "sort_oalist_aux ox ys"
  from assms(1) have "oalist_inv (xs', ox)" by (simp add: xs)
  moreover from assms(2) have "oalist_inv (sort_oalist_aux ox ys, ox)" by (rule oalist_inv_sort_oalist_aux)
  moreover from assms(3) have "map2_val_compat ko (\<lambda>ko zs. fst (g (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  moreover from assms(4) have "map2_val_compat ko (\<lambda>ko zs. fst (h (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  ultimately have "oalist_inv (map2_val_pair ox f (\<lambda>ko zs. fst (g (zs, ko))) (\<lambda>ko zs. fst (h (zs, ko))) xs' ?ys, ox)"
    by (rule oalist_inv_map2_val_pair)
  thus ?thesis by (simp add: xs)
qed

lemma lookup_raw_map2_val_raw:
  assumes "oalist_inv xs" and "oalist_inv ys"
  assumes "map2_val_compat' g" and "map2_val_compat' h"
  assumes "\<And>zs. oalist_inv zs \<Longrightarrow> g zs = map_val_raw (\<lambda>k v. f k v 0) zs"
    and "\<And>zs. oalist_inv zs \<Longrightarrow> h zs = map_val_raw (\<lambda>k. f k 0) zs"
    and "\<And>k. f k 0 0 = 0"
  shows "lookup_raw (map2_val_raw f g h xs ys) k0 = f k0 (lookup_raw xs k0) (lookup_raw ys k0)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  let ?ys = "sort_oalist_aux ox ys"
  from assms(1) have "oalist_inv (xs', ox)" by (simp add: xs)
  moreover from assms(2) have "oalist_inv (sort_oalist_aux ox ys, ox)" by (rule oalist_inv_sort_oalist_aux)
  moreover from assms(3) have "map2_val_compat ko (\<lambda>ko zs. fst (g (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  moreover from assms(4) have "map2_val_compat ko (\<lambda>ko zs. fst (h (zs, ko)))" for ko
    by (rule map2_val_compat'_imp_map2_val_compat)
  ultimately have "lookup_pair ox (map2_val_pair ox f (\<lambda>ko zs. fst (g (zs, ko))) (\<lambda>ko zs. fst (h (zs, ko))) xs' ?ys) k0 =
                      f k0 (lookup_pair ox xs' k0) (lookup_pair ox ?ys k0)" using _ _ assms(7)
  proof (rule lookup_pair_map2_val_pair)
    fix zs::"('a \<times> 'b) list"
    assume "oalist_inv (zs, ox)"
    hence "g (zs, ox) = map_val_raw (\<lambda>k v. f k v 0) (zs, ox)" by (rule assms(5))
    thus "fst (g (zs, ox)) = map_val_pair (\<lambda>k v. f k v 0) zs" by simp
  next
    fix zs::"('a \<times> 'c) list"
    assume "oalist_inv (zs, ox)"
    hence "h (zs, ox) = map_val_raw (\<lambda>k. f k 0) (zs, ox)" by (rule assms(6))
    thus "fst (h (zs, ox)) = map_val_pair (\<lambda>k. f k 0) zs" by simp
  qed
  also from assms(2) have "... = f k0 (lookup_pair ox xs' k0) (lookup_raw ys k0)"
    by (simp only: lookup_pair_sort_oalist_aux)
  finally have *: "lookup_pair ox (map2_val_pair ox f (\<lambda>ko zs. fst (g (zs, ko))) (\<lambda>ko zs. fst (h (zs, ko))) xs' ?ys) k0 =
                    f k0 (lookup_pair ox xs' k0) (lookup_raw ys k0)" .
  thus ?thesis by (simp add: xs)
qed

lemma map2_val_raw_singleton_eq_update_by_fun_raw:
  assumes "oalist_inv xs"
  assumes "\<And>k x. f k x 0 = x" and "\<And>zs. oalist_inv zs \<Longrightarrow> g zs = zs"
    and "\<And>ko. h ([(k, v)], ko) = map_val_raw (\<lambda>k. f k 0) ([(k, v)], ko)"
  shows "map2_val_raw f g h xs ([(k, v)], ko) = update_by_fun_raw k (\<lambda>x. f k x v) xs"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  let ?ys = "sort_oalist ox [(k, v)]"
  from assms(1) have inv: "oalist_inv (xs', ox)" by (simp add: xs)
  show ?thesis
  proof (simp add: xs, intro conjI impI)
    assume "ox = ko"
    from inv have "oalist_inv (xs', ko)" by (simp only: \<open>ox = ko\<close>)
    thus "map2_val_pair ko f (\<lambda>ko zs. fst (g (zs, ko))) (\<lambda>ko zs. fst (h (zs, ko))) xs' [(k, v)] =
              update_by_fun_pair ko k (\<lambda>x. f k x v) xs'"
      using assms(2)
    proof (rule map2_val_pair_singleton_eq_update_by_fun_pair)
      fix zs::"('a \<times> 'b) list"
      assume "oalist_inv (zs, ko)"
      hence "g (zs, ko) = (zs, ko)" by (rule assms(3))
      thus "fst (g (zs, ko)) = zs" by simp
    next
      show "fst (h ([(k, v)], ko)) = map_val_pair (\<lambda>k. f k 0) [(k, v)]" by (simp add: assms(4))
    qed
  next
    show "map2_val_pair ox f (\<lambda>ko zs. fst (g (zs, ko))) (\<lambda>ko zs. fst (h (zs, ko))) xs' (sort_oalist ox [(k, v)]) =
          update_by_fun_pair ox k (\<lambda>x. f k x v) xs'"
    proof (cases "v = 0")
      case True
      have eq1: "sort_oalist ox [(k, 0)] = []" by (simp add: sort_oalist_def)
      from inv have eq2: "g (xs', ox) = (xs', ox)" by (rule assms(3))
      show ?thesis
        by (simp add: True eq1 eq2 assms(2) update_by_fun_pair_eq_update_by_pair[OF inv],
            rule sym, rule update_by_pair_id, fact inv, fact refl)
    next
      case False
      hence "oalist_inv ([(k, v)], ox)" by (simp add: oalist_inv_singleton)
      hence eq: "sort_oalist ox [(k, v)] = [(k, v)]" by (rule sort_oalist_id)
      show ?thesis unfolding eq using inv assms(2)
      proof (rule map2_val_pair_singleton_eq_update_by_fun_pair)
        fix zs::"('a \<times> 'b) list"
        assume "oalist_inv (zs, ox)"
        hence "g (zs, ox) = (zs, ox)" by (rule assms(3))
        thus "fst (g (zs, ox)) = zs" by simp
      next
        show "fst (h ([(k, v)], ox)) = map_val_pair (\<lambda>k. f k 0) [(k, v)]" by (simp add: assms(4))
      qed
    qed
  qed
qed

subsubsection \<open>@{const lex_ord_raw}\<close>

lemma lex_ord_raw_EqI:
  assumes "oalist_inv xs" and "oalist_inv ys"
    and "\<And>k. k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> f k (lookup_raw xs k) (lookup_raw ys k) = Some Eq"
  shows "lex_ord_raw ko f xs ys = Some Eq"
  unfolding lex_ord_raw_def
  by (rule lex_ord_pair_EqI, simp_all add: assms oalist_inv_sort_oalist_aux lookup_pair_sort_oalist_aux set_sort_oalist_aux)

lemma lex_ord_raw_valI:
  assumes "oalist_inv xs" and "oalist_inv ys" and "aux \<noteq> Some Eq"
  assumes "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" and "aux = f k (lookup_raw xs k) (lookup_raw ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> lt_of_key_order ko k' k \<Longrightarrow>
              f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq"
  shows "lex_ord_raw ko f xs ys = aux"
  unfolding lex_ord_raw_def
  using oalist_inv_sort_oalist_aux[OF assms(1)] oalist_inv_sort_oalist_aux[OF assms(2)] assms(3)
proof (rule lex_ord_pair_valI)
  from assms(1, 2, 4) show "k \<in> fst ` set (sort_oalist_aux ko xs) \<union> fst ` set (sort_oalist_aux ko ys)"
    by (simp add: set_sort_oalist_aux)
next
  from assms(1, 2, 5) show "aux = f k (lookup_pair ko (sort_oalist_aux ko xs) k) (lookup_pair ko (sort_oalist_aux ko ys) k)"
    by (simp add: lookup_pair_sort_oalist_aux)
next
  fix k'
  assume "k' \<in> fst ` set (sort_oalist_aux ko xs) \<union> fst ` set (sort_oalist_aux ko ys)"
  with assms(1, 2) have "k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" by (simp add: set_sort_oalist_aux)
  moreover assume "lt_of_key_order ko k' k"
  ultimately have "f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq" by (rule assms(6))
  with assms(1, 2) show "f k' (lookup_pair ko (sort_oalist_aux ko xs) k') (lookup_pair ko (sort_oalist_aux ko ys) k') = Some Eq"
    by (simp add: lookup_pair_sort_oalist_aux)
qed

lemma lex_ord_raw_EqD:
  assumes "oalist_inv xs" and "oalist_inv ys" and "lex_ord_raw ko f xs ys = Some Eq"
    and "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
  shows "f k (lookup_raw xs k) (lookup_raw ys k) = Some Eq"
proof -
  have "f k (lookup_pair ko (sort_oalist_aux ko xs) k) (lookup_pair ko (sort_oalist_aux ko ys) k) = Some Eq"
    by (rule lex_ord_pair_EqD[where f=f],
        simp_all add: oalist_inv_sort_oalist_aux assms lex_ord_raw_def[symmetric] set_sort_oalist_aux del: Un_iff)
  with assms(1, 2) show ?thesis by (simp add: lookup_pair_sort_oalist_aux)
qed

lemma lex_ord_raw_valE:
  assumes "oalist_inv xs" and "oalist_inv ys" and "lex_ord_raw ko f xs ys = aux"
    and "aux \<noteq> Some Eq"
  obtains k where "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
    and "aux = f k (lookup_raw xs k) (lookup_raw ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> lt_of_key_order ko k' k \<Longrightarrow>
            f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq"
proof -
  let ?xs = "sort_oalist_aux ko xs"
  let ?ys = "sort_oalist_aux ko ys"
  from assms(3) have "lex_ord_pair ko f ?xs ?ys = aux" by (simp only: lex_ord_raw_def)
  with oalist_inv_sort_oalist_aux[OF assms(1)] oalist_inv_sort_oalist_aux[OF assms(2)]
  obtain k where a: "k \<in> fst ` set ?xs \<union> fst ` set ?ys"
    and b: "aux = f k (lookup_pair ko ?xs k) (lookup_pair ko ?ys k)"
    and c: "\<And>k'. k' \<in> fst ` set ?xs \<union> fst ` set ?ys \<Longrightarrow> lt_of_key_order ko k' k \<Longrightarrow>
            f k' (lookup_pair ko ?xs k') (lookup_pair ko ?ys k') = Some Eq"
    using assms(4) by (rule lex_ord_pair_valE, blast)
  from a have "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
    by (simp add: set_sort_oalist_aux assms(1, 2))
  moreover from b have "aux = f k (lookup_raw xs k) (lookup_raw ys k)"
    by (simp add: lookup_pair_sort_oalist_aux assms(1, 2))
  moreover have "f k' (lookup_raw xs k') (lookup_raw ys k') = Some Eq"
    if k'_in: "k' \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" and k'_less: "lt_of_key_order ko k' k" for k'
  proof -
    have "f k' (lookup_raw xs k') (lookup_raw ys k') = f k' (lookup_pair ko ?xs k') (lookup_pair ko ?ys k')"
      by (simp add: lookup_pair_sort_oalist_aux assms(1, 2))
    also have "... = Some Eq"
    proof (rule c)
      from k'_in show "k' \<in> fst ` set ?xs \<union> fst ` set ?ys"
        by (simp add:  set_sort_oalist_aux assms(1, 2))
    qed (fact k'_less)
    finally show ?thesis .
  qed
  ultimately show ?thesis ..
qed

subsubsection \<open>@{const prod_ord_raw}\<close>

lemma prod_ord_rawI:
  assumes "oalist_inv xs" and "oalist_inv ys"
    and "\<And>k. k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> P k (lookup_raw xs k) (lookup_raw ys k)"
  shows "prod_ord_raw P xs ys"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv (xs', ox)" by (simp only: xs)
  hence *: "prod_ord_pair ox P xs' (sort_oalist_aux ox ys)" using oalist_inv_sort_oalist_aux
  proof (rule prod_ord_pairI)
    fix k
    assume "k \<in> fst ` set xs' \<union> fst ` set (sort_oalist_aux ox ys)"
    hence "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" by (simp add: xs set_sort_oalist_aux assms(2))
    hence "P k (lookup_raw xs k) (lookup_raw ys k)" by (rule assms(3))
    thus "P k (lookup_pair ox xs' k) (lookup_pair ox (sort_oalist_aux ox ys) k)"
      by (simp add: xs lookup_pair_sort_oalist_aux assms(2))
  qed fact
  thus ?thesis by (simp add: xs)
qed

lemma prod_ord_rawD:
  assumes "oalist_inv xs" and "oalist_inv ys" and "prod_ord_raw P xs ys"
    and "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)"
  shows "P k (lookup_raw xs k) (lookup_raw ys k)"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv (xs', ox)" by (simp only: xs)
  moreover note oalist_inv_sort_oalist_aux[OF assms(2)]
  moreover from assms(3) have "prod_ord_pair ox P xs' (sort_oalist_aux ox ys)" by (simp add: xs)
  moreover from assms(4) have "k \<in> fst ` set xs' \<union> fst ` set (sort_oalist_aux ox ys)"
    by (simp add: xs set_sort_oalist_aux assms(2))
  ultimately have *: "P k (lookup_pair ox xs' k) (lookup_pair ox (sort_oalist_aux ox ys) k)"
    by (rule prod_ord_pairD)
  thus ?thesis by (simp add: xs lookup_pair_sort_oalist_aux assms(2))
qed

corollary prod_ord_raw_alt:
  assumes "oalist_inv xs" and "oalist_inv ys"
  shows "prod_ord_raw P xs ys \<longleftrightarrow>
          (\<forall>k\<in>fst ` set (fst xs) \<union> fst ` set (fst ys). P k (lookup_raw xs k) (lookup_raw ys k))"
  using prod_ord_rawI[OF assms] prod_ord_rawD[OF assms] by meson

subsubsection \<open>@{const oalist_eq_raw}\<close>

lemma oalist_eq_rawI:
  assumes "oalist_inv xs" and "oalist_inv ys"
    and "\<And>k. k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys) \<Longrightarrow> lookup_raw xs k = lookup_raw ys k"
  shows "oalist_eq_raw xs ys"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(1) have "oalist_inv (xs', ox)" by (simp only: xs)
  hence *: "xs' = sort_oalist_aux ox ys" using oalist_inv_sort_oalist_aux[OF assms(2)]
  proof (rule lookup_pair_inj)
    show "lookup_pair ox xs' = lookup_pair ox (sort_oalist_aux ox ys)"
    proof
      fix k
      show "lookup_pair ox xs' k = lookup_pair ox (sort_oalist_aux ox ys) k"
      proof (cases "k \<in> fst ` set xs' \<union> fst ` set (sort_oalist_aux ox ys)")
        case True
        hence "k \<in> fst ` set (fst xs) \<union> fst ` set (fst ys)" by (simp add: xs set_sort_oalist_aux assms(2))
        hence "lookup_raw xs k = lookup_raw ys k" by (rule assms(3))
        thus ?thesis by (simp add: xs lookup_pair_sort_oalist_aux assms(2))
      next
        case False
        hence "k \<notin> fst ` set xs'" and "k \<notin> fst ` set (sort_oalist_aux ox ys)" by simp_all
        with \<open>oalist_inv (xs', ox)\<close> oalist_inv_sort_oalist_aux[OF assms(2)]
        have "lookup_pair ox xs' k = 0" and "lookup_pair ox (sort_oalist_aux ox ys) k = 0"
          by (simp_all add: lookup_pair_eq_0)
        thus ?thesis by simp
      qed
    qed
  qed
  thus ?thesis by (simp add: xs)
qed

lemma oalist_eq_rawD:
  assumes "oalist_inv ys" and "oalist_eq_raw xs ys"
  shows "lookup_raw xs = lookup_raw ys"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms(2) have "xs' = sort_oalist_aux ox ys" by (simp add: xs)
  hence "lookup_pair ox xs' = lookup_pair ox (sort_oalist_aux ox ys)" by simp
  thus ?thesis by (simp add: xs lookup_pair_sort_oalist_aux assms(1))
qed

lemma oalist_eq_raw_alt:
  assumes "oalist_inv xs" and "oalist_inv ys"
  shows "oalist_eq_raw xs ys \<longleftrightarrow> (lookup_raw xs = lookup_raw ys)"
  using oalist_eq_rawI[OF assms] oalist_eq_rawD[OF assms(2)] by metis

subsubsection \<open>@{const sort_oalist_raw}\<close>

lemma oalist_inv_sort_oalist_raw: "oalist_inv (sort_oalist_raw xs)"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  show ?thesis by (simp add: xs oalist_inv_sort_oalist)
qed

lemma sort_oalist_raw_id:
  assumes "oalist_inv xs"
  shows "sort_oalist_raw xs = xs"
proof -
  obtain xs' ko where xs: "xs = (xs', ko)" by fastforce
  from assms have "oalist_inv (xs', ko)" by (simp only: xs)
  hence "sort_oalist ko xs' = xs'" by (rule sort_oalist_id)
  thus ?thesis by (simp add: xs)
qed

subsection \<open>Abstract characterisation\<close>

typedef (overloaded) ('a, 'b) oalist = "{xs::('a, 'b::zero) oalist_raw. oalist_inv xs}"
  morphisms list_of_oalist Abs_oalist
  by (auto intro: oalist_inv_Nil)

lemma oalist_eq_iff: "xs = ys \<longleftrightarrow> list_of_oalist xs = list_of_oalist ys"
  by (simp add: list_of_oalist_inject)

lemma oalist_eqI: "list_of_oalist xs = list_of_oalist ys \<Longrightarrow> xs = ys"
  by (simp add: oalist_eq_iff)

text \<open>Formal, totalized constructor for @{typ "('a, 'b) oalist"}:\<close>

definition OAlist :: "('a \<times> 'b) list \<times> 'a key_order \<Rightarrow> ('a, 'b::zero) oalist" where
  "OAlist xs = Abs_oalist (sort_oalist_raw xs)"

definition [simp]: "oalist_of_list = OAlist"

lemma oalist_inv_list_of_oalist [simp, intro]: "oalist_inv (list_of_oalist xs)"
  using list_of_oalist [of xs] by simp

lemma list_of_oalist_OAlist: "list_of_oalist (OAlist xs) = sort_oalist_raw xs"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  show ?thesis by (simp add: xs OAlist_def Abs_oalist_inverse oalist_inv_sort_oalist)
qed

lemma OAlist_list_of_oalist [simp, code abstype]: "OAlist (list_of_oalist xs) = xs"
proof -
  obtain xs' ox where xs: "list_of_oalist xs = (xs', ox)" by fastforce
  have "oalist_inv (xs', ox)" by (simp add: xs[symmetric])
  thus ?thesis by (simp add: xs OAlist_def sort_oalist_id, simp add: list_of_oalist_inverse xs[symmetric])
qed

lemma list_of_oalist_OAlist_id:
  assumes "oalist_inv xs"
  shows "list_of_oalist (OAlist xs) = xs"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  from assms show ?thesis by (simp add: xs Abs_oalist_inverse OAlist_def sort_oalist_id)
qed

lemma [code abstract]: "list_of_oalist (oalist_of_list xs) = sort_oalist_raw xs"
  by (simp add: list_of_oalist_OAlist)

subsubsection \<open>Fundamental operations\<close>

context
begin

qualified definition lookup :: "('a, 'b::zero) oalist \<Rightarrow> 'a \<Rightarrow> 'b"
  where "lookup xs = lookup_raw (list_of_oalist xs)"

qualified definition sorted_domain :: "'a key_order \<Rightarrow> ('a, 'b::zero) oalist \<Rightarrow> 'a list"
  where "sorted_domain ko xs = sorted_domain_raw ko (list_of_oalist xs)"

qualified definition empty :: "'a key_order \<Rightarrow> ('a, 'b::zero) oalist"
  where "empty ko = OAlist ([], ko)"

qualified definition except_min :: "('a key_order) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b::zero) oalist"
  where "except_min ko xs = OAlist (except_min_raw ko (list_of_oalist xs))"

qualified definition min_key_val :: "('a key_order) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a \<times> 'b::zero)"
  where "min_key_val ko xs = min_key_val_raw ko (list_of_oalist xs)"

qualified definition insert :: "('a \<times> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b::zero) oalist"
  where "insert x xs = OAlist (update_by_raw x (list_of_oalist xs))"

qualified definition update_by_fun :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b::zero) oalist"
  where "update_by_fun k f xs = OAlist (update_by_fun_raw k f (list_of_oalist xs))"

qualified definition update_by_fun_gr :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b::zero) oalist"
  where "update_by_fun_gr k f xs = OAlist (update_by_fun_gr_raw k f (list_of_oalist xs))"

qualified definition filter :: "(('a \<times> 'b) \<Rightarrow> bool) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b::zero) oalist"
  where "filter P xs = OAlist (filter_raw P (list_of_oalist xs))"

qualified definition map_val :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b::zero) oalist \<Rightarrow> ('a, 'c::zero) oalist"
  where "map_val f xs = OAlist (map_val_raw f (list_of_oalist xs))"

qualified definition map2_val :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, 'b::zero) oalist \<Rightarrow> ('a, 'c::zero) oalist \<Rightarrow>
                                        ('a, 'd::zero) oalist"
  where "map2_val f xs ys =
            OAlist (map2_val_raw f (map_val_raw (\<lambda>k b. f k b 0)) (map_val_raw (\<lambda>k. f k 0))
              (list_of_oalist xs) (list_of_oalist ys))"

qualified definition map2_val_rneutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'c::zero) oalist \<Rightarrow>
                                         ('a, 'b::zero) oalist"
  where "map2_val_rneutr f xs ys =
            OAlist (map2_val_raw f id (map_val_raw (\<lambda>k. f k 0)) (list_of_oalist xs) (list_of_oalist ys))"

qualified definition map2_val_neutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b) oalist \<Rightarrow>
                                        ('a, 'b::zero) oalist"
  where "map2_val_neutr f xs ys = OAlist (map2_val_raw f id id (list_of_oalist xs) (list_of_oalist ys))"

qualified definition lex_ord :: "('a key_order) \<Rightarrow> ('a \<Rightarrow> ('b, 'c) comp_opt) \<Rightarrow>
                                (('a, 'b::zero) oalist, ('a, 'c::zero) oalist) comp_opt"
  where "lex_ord ko f xs ys = lex_ord_raw ko f (list_of_oalist xs) (list_of_oalist ys)"

qualified definition prod_ord :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b::zero) oalist \<Rightarrow>
                                  ('a, 'c::zero) oalist \<Rightarrow> bool"
  where "prod_ord f xs ys = prod_ord_raw f (list_of_oalist xs) (list_of_oalist ys)"

qualified definition oalist_eq :: "('a, 'b) oalist \<Rightarrow> ('a, 'b::zero) oalist \<Rightarrow> bool"
  where "oalist_eq xs ys = oalist_eq_raw (list_of_oalist xs) (list_of_oalist ys)"

end

subsubsection \<open>@{const OAlist.sorted_domain}\<close>

lemma set_sorted_domain: "set (OAlist.sorted_domain ko xs) = fst ` set (fst (list_of_oalist xs))"
  unfolding OAlist.sorted_domain_def using oalist_inv_list_of_oalist by (rule set_sorted_domain_raw)

lemma in_sorted_domain_iff_lookup: "k \<in> set (OAlist.sorted_domain ko xs) \<longleftrightarrow> (OAlist.lookup xs k \<noteq> 0)"
  unfolding OAlist.sorted_domain_def OAlist.lookup_def using oalist_inv_list_of_oalist
  by (rule in_sorted_domain_raw_iff_lookup_raw)

lemma sorted_sorted_domain: "sorted_wrt (lt_of_key_order ko) (OAlist.sorted_domain ko xs)"
  unfolding OAlist.sorted_domain_def using oalist_inv_list_of_oalist by (rule sorted_sorted_domain_raw)

subsubsection \<open>@{const OAlist.empty}\<close>

lemma list_of_oalist_empty [simp, code abstract]: "list_of_oalist (OAlist.empty ko) = ([], ko)"
  by (simp add: OAlist.empty_def sort_oalist_def list_of_oalist_OAlist)

lemma lookup_empty: "OAlist.lookup (OAlist.empty ko) k = 0"
  by (simp add: OAlist.lookup_def)

subsubsection \<open>@{const OAlist.except_min}\<close>

lemma list_of_oalist_except_min [simp, code abstract]:
  "list_of_oalist (OAlist.except_min ko xs) = except_min_raw ko (list_of_oalist xs)"
  unfolding OAlist.except_min_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_except_min_raw, fact oalist_inv_list_of_oalist)

lemma lookup_except_min:
  "OAlist.lookup (OAlist.except_min ko xs) k =
        (if (\<forall>k'\<in>fst ` set (fst (list_of_oalist xs)). le_of_key_order ko k k') then 0 else OAlist.lookup xs k)"
  by (simp add: OAlist.lookup_def lookup_raw_except_min_raw split del: if_split cong: if_cong)

subsubsection \<open>@{const OAlist.min_key_val}\<close>

lemma min_key_val_in:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "OAlist.min_key_val ko xs \<in> set (fst (list_of_oalist xs))"
  unfolding OAlist.min_key_val_def using assms by (rule min_key_val_raw_in)

lemma snd_min_key_val:
  assumes "fst (list_of_oalist xs) \<noteq> []"
  shows "snd (OAlist.min_key_val ko xs) = OAlist.lookup xs (fst (OAlist.min_key_val ko xs))"
  unfolding OAlist.lookup_def OAlist.min_key_val_def using oalist_inv_list_of_oalist assms
  by (rule snd_min_key_val_raw)

lemma min_key_val_minimal:
  assumes "z \<in> set (fst (list_of_oalist xs))"
  shows "le_of_key_order ko (fst (OAlist.min_key_val ko xs)) (fst z)"
  unfolding OAlist.min_key_val_def by (rule min_key_val_raw_minimal, fact oalist_inv_list_of_oalist, fact)

subsubsection \<open>@{const OAlist.insert}\<close>

lemma list_of_oalist_insert [simp, code abstract]:
  "list_of_oalist (OAlist.insert x xs) = update_by_raw x (list_of_oalist xs)"
  unfolding OAlist.insert_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_update_by_raw, fact oalist_inv_list_of_oalist)

lemma lookup_insert: "OAlist.lookup (OAlist.insert (k, v) xs) k' = (if k = k' then v else OAlist.lookup xs k')"
  by (simp add: OAlist.lookup_def lookup_raw_update_by_raw split del: if_split cong: if_cong)

subsubsection \<open>@{const OAlist.update_by_fun} and @{const OAlist.update_by_fun_gr}\<close>

lemma list_of_oalist_update_by_fun [simp, code abstract]:
  "list_of_oalist (OAlist.update_by_fun k f xs) = update_by_fun_raw k f (list_of_oalist xs)"
  unfolding OAlist.update_by_fun_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_update_by_fun_raw, fact oalist_inv_list_of_oalist)

lemma lookup_update_by_fun:
  "OAlist.lookup (OAlist.update_by_fun k f xs) k' = (if k = k' then f else id) (OAlist.lookup xs k')"
  by (simp add: OAlist.lookup_def lookup_raw_update_by_fun_raw split del: if_split cong: if_cong)

lemma list_of_oalist_update_by_fun_gr [simp, code abstract]:
  "list_of_oalist (OAlist.update_by_fun_gr k f xs) = update_by_fun_gr_raw k f (list_of_oalist xs)"
  unfolding OAlist.update_by_fun_gr_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_update_by_fun_gr_raw, fact oalist_inv_list_of_oalist)

lemma update_by_fun_gr_eq_update_by_fun: "OAlist.update_by_fun_gr = OAlist.update_by_fun"
  by (rule, rule, rule,
      simp add: OAlist.update_by_fun_gr_def OAlist.update_by_fun_def update_by_fun_gr_raw_eq_update_by_fun_raw)

subsubsection \<open>@{const OAlist.filter}\<close>

lemma list_of_oalist_filter [simp, code abstract]:
  "list_of_oalist (OAlist.filter P xs) = filter_raw P (list_of_oalist xs)"
  unfolding OAlist.filter_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_filter_raw, fact oalist_inv_list_of_oalist)

lemma lookup_filter: "OAlist.lookup (OAlist.filter P xs) k = (let v = OAlist.lookup xs k in if P (k, v) then v else 0)"
  by (simp add: OAlist.lookup_def lookup_raw_filter_raw)

subsubsection \<open>@{const OAlist.map_val}\<close>

lemma list_of_oalist_map_val [simp, code abstract]:
  "list_of_oalist (OAlist.map_val f xs) = map_val_raw f (list_of_oalist xs)"
  unfolding OAlist.map_val_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_map_val_raw, fact oalist_inv_list_of_oalist)

lemma lookup_map_val:
  assumes "\<And>k'. f k' 0 = 0"
  shows "OAlist.lookup (OAlist.map_val f xs) k = f k (OAlist.lookup xs k)"
  by (simp add: OAlist.lookup_def lookup_raw_map_val_raw assms)

subsubsection \<open>@{const OAlist.map2_val}, @{const OAlist.map2_val_rneutr} and @{const OAlist.map2_val_neutr}\<close>

lemma list_of_oalist_map2_val [simp, code abstract]:
  "list_of_oalist (OAlist.map2_val f xs ys) =
      map2_val_raw f (map_val_raw (\<lambda>k b. f k b 0)) (map_val_raw (\<lambda>k. f k 0)) (list_of_oalist xs) (list_of_oalist ys)"
  unfolding OAlist.map2_val_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_map2_val_raw,
      fact oalist_inv_list_of_oalist, fact oalist_inv_list_of_oalist,
      fact map2_val_compat'_map_val_raw, fact map2_val_compat'_map_val_raw)

lemma list_of_oalist_map2_val_rneutr [simp, code abstract]:
  "list_of_oalist (OAlist.map2_val_rneutr f xs ys) =
      map2_val_raw f id (map_val_raw (\<lambda>k c. f k 0 c)) (list_of_oalist xs) (list_of_oalist ys)"
  unfolding OAlist.map2_val_rneutr_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_map2_val_raw,
      fact oalist_inv_list_of_oalist, fact oalist_inv_list_of_oalist,
      fact map2_val_compat'_id, fact map2_val_compat'_map_val_raw)

lemma list_of_oalist_map2_val_neutr [simp, code abstract]:
  "list_of_oalist (OAlist.map2_val_neutr f xs ys) = map2_val_raw f id id (list_of_oalist xs) (list_of_oalist ys)"
  unfolding OAlist.map2_val_neutr_def
  by (rule list_of_oalist_OAlist_id, rule oalist_inv_map2_val_raw,
      fact oalist_inv_list_of_oalist, fact oalist_inv_list_of_oalist,
      fact map2_val_compat'_id, fact map2_val_compat'_id)

lemma lookup_map2_val:
  assumes "\<And>k. f k 0 0 = 0"
  shows "OAlist.lookup (OAlist.map2_val f xs ys) k = f k (OAlist.lookup xs k) (OAlist.lookup ys k)"
  by (simp add: OAlist.lookup_def lookup_raw_map2_val_raw map2_val_compat'_map_val_raw assms)

lemma lookup_map2_val_rneutr:
  assumes "\<And>k x. f k x 0 = x"
  shows "OAlist.lookup (OAlist.map2_val_rneutr f xs ys) k = f k (OAlist.lookup xs k) (OAlist.lookup ys k)"
proof (simp add: OAlist.lookup_def, rule lookup_raw_map2_val_raw)
  fix zs::"('a, 'b) oalist_raw"
  assume "oalist_inv zs"
  thus "id zs = map_val_raw (\<lambda>k v. f k v 0) zs" by (simp add: assms map_raw_id)
qed (fact oalist_inv_list_of_oalist, fact oalist_inv_list_of_oalist,
    fact map2_val_compat'_id, fact map2_val_compat'_map_val_raw, rule refl, simp only: assms)

lemma lookup_map2_val_neutr:
  assumes "\<And>k x. f k x 0 = x" and "\<And>k x. f k 0 x = x"
  shows "OAlist.lookup (OAlist.map2_val_neutr f xs ys) k = f k (OAlist.lookup xs k) (OAlist.lookup ys k)"
proof (simp add: OAlist.lookup_def, rule lookup_raw_map2_val_raw)
  fix zs::"('a, 'b) oalist_raw"
  assume "oalist_inv zs"
  thus "id zs = map_val_raw (\<lambda>k v. f k v 0) zs" by (simp add: assms(1) map_raw_id)
next
  fix zs::"('a, 'b) oalist_raw"
  assume "oalist_inv zs"
  thus "id zs = map_val_raw (\<lambda>k. f k 0) zs" by (simp add: assms(2) map_raw_id)
qed (fact oalist_inv_list_of_oalist, fact oalist_inv_list_of_oalist,
    fact map2_val_compat'_id, fact map2_val_compat'_id, simp only: assms(1))

lemma map2_val_rneutr_singleton_eq_update_by_fun:
  assumes "\<And>a x. f a x 0 = x" and "list_of_oalist ys = ([(k, v)], oy)"
  shows "OAlist.map2_val_rneutr f xs ys = OAlist.update_by_fun k (\<lambda>x. f k x v) xs"
  by (simp add: OAlist.map2_val_rneutr_def OAlist.update_by_fun_def assms map2_val_raw_singleton_eq_update_by_fun_raw)

subsubsection \<open>@{const OAlist.lex_ord}, @{const OAlist.prod_ord} and @{const OAlist.oalist_eq}\<close>

lemma lex_ord_EqI:
  "(\<And>k. k \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys)) \<Longrightarrow>
     f k (OAlist.lookup xs k) (OAlist.lookup ys k) = Some Eq) \<Longrightarrow>
  OAlist.lex_ord ko f xs ys = Some Eq"
  by (simp add: OAlist.lex_ord_def OAlist.lookup_def, rule lex_ord_raw_EqI,
      rule oalist_inv_list_of_oalist, rule oalist_inv_list_of_oalist, blast)

lemma lex_ord_valI:
  assumes "aux \<noteq> Some Eq" and "k \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys))"
  shows "aux = f k (OAlist.lookup xs k) (OAlist.lookup ys k) \<Longrightarrow>
         (\<And>k'. k' \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys)) \<Longrightarrow>
              lt_of_key_order ko k' k \<Longrightarrow> f k' (OAlist.lookup xs k') (OAlist.lookup ys k') = Some Eq) \<Longrightarrow>
          OAlist.lex_ord ko f xs ys = aux"
  by (simp (no_asm_use) add: OAlist.lex_ord_def OAlist.lookup_def, rule lex_ord_raw_valI,
      rule oalist_inv_list_of_oalist, rule oalist_inv_list_of_oalist, rule assms(1), rule assms(2), blast+)

lemma lex_ord_EqD:
  "OAlist.lex_ord ko f xs ys = Some Eq \<Longrightarrow>
   k \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys)) \<Longrightarrow>
   f k (OAlist.lookup xs k) (OAlist.lookup ys k) = Some Eq"
  by (simp add: OAlist.lex_ord_def OAlist.lookup_def, rule lex_ord_raw_EqD[where f=f],
      rule oalist_inv_list_of_oalist, rule oalist_inv_list_of_oalist, assumption, simp)

lemma lex_ord_valE:
  assumes "OAlist.lex_ord ko f xs ys = aux" and "aux \<noteq> Some Eq"
  obtains k where "k \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys))"
    and "aux = f k (OAlist.lookup xs k) (OAlist.lookup ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys)) \<Longrightarrow>
            lt_of_key_order ko k' k \<Longrightarrow> f k' (OAlist.lookup xs k') (OAlist.lookup ys k') = Some Eq"
proof -
  note oalist_inv_list_of_oalist oalist_inv_list_of_oalist
  moreover from assms(1) have "lex_ord_raw ko f (list_of_oalist xs) (list_of_oalist ys) = aux"
    by (simp only: OAlist.lex_ord_def)
  ultimately obtain k where 1: "k \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys))"
    and "aux = f k (lookup_raw (list_of_oalist xs) k) (lookup_raw (list_of_oalist ys) k)"
    and "\<And>k'. k' \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys)) \<Longrightarrow>
            lt_of_key_order ko k' k \<Longrightarrow>
            f k' (lookup_raw (list_of_oalist xs) k') (lookup_raw (list_of_oalist ys) k') = Some Eq"
    using assms(2) by (rule lex_ord_raw_valE, blast)
  from this(2, 3) have "aux = f k (OAlist.lookup xs k) (OAlist.lookup ys k)"
    and "\<And>k'. k' \<in> fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys)) \<Longrightarrow>
            lt_of_key_order ko k' k \<Longrightarrow> f k' (OAlist.lookup xs k') (OAlist.lookup ys k') = Some Eq"
    by (simp_all only: OAlist.lookup_def)
  with 1 show ?thesis ..
qed

lemma prod_ord_alt:
  "OAlist.prod_ord P xs ys \<longleftrightarrow>
                  (\<forall>k\<in>fst ` set (fst (list_of_oalist xs)) \<union> fst ` set (fst (list_of_oalist ys)).
                      P k (OAlist.lookup xs k) (OAlist.lookup ys k))"
  by (simp add: OAlist.prod_ord_def OAlist.lookup_def prod_ord_raw_alt)

lemma oalist_eq_alt: "OAlist.oalist_eq xs ys \<longleftrightarrow> (OAlist.lookup xs = OAlist.lookup ys)"
  by (simp add: OAlist.oalist_eq_def OAlist.lookup_def oalist_eq_raw_alt)

subsection \<open>Experiment\<close>

definition rv_key_order :: "'a::linorder key_order" where "rv_key_order = - key_order_of_le"

lemma equal_key_order_code [code]:
  "HOL.equal key_order_of_le key_order_of_le = True"
  "HOL.equal key_order_of_le rv_key_order = False"
  "HOL.equal rv_key_order key_order_of_le = False"
  "HOL.equal rv_key_order rv_key_order = True"
  sorry

code_datatype key_order_of_le rv_key_order

lemma key_compare_rv_key_order [code]:
  "key_compare rv_key_order = (\<lambda>x y. if x < y then Gt else if x = y then Eq else Lt)"
  unfolding rv_key_order_def by (intro ext, auto simp: key_compare_key_order_of_le)

lemmas [code] = key_compare_key_order_of_le

value [code] "oalist_of_list ([(0::nat, 4::nat), (1, 3), (0, 2), (1, 1)], key_order_of_le)"

value [code] "OAlist.except_min rv_key_order (oalist_of_list ([(1, 3), (0::nat, 4::nat), (0, 2), (1, 1)], key_order_of_le))"

value [code] "OAlist.lookup (oalist_of_list ([(0::nat, 4::nat), (1, 3), (0, 2), (1, 1)], key_order_of_le)) 1"

value [code] "OAlist.prod_ord (\<lambda>_. greater_eq)
                (oalist_of_list ([(1, 4), (0::nat, 4::nat), (1, 3), (0, 2), (3, 1)], key_order_of_le))
                (oalist_of_list ([(0::nat, 4::nat), (1, 3), (2, 2), (1, 1)], rv_key_order))"

value [code] "OAlist.oalist_eq
                (oalist_of_list ([(1, 4), (0::nat, 2::nat), (2, 3)], key_order_of_le))
                (oalist_of_list ([(0::nat, 2::nat), (2, 3), (0, 2), (1, 4)], rv_key_order))"

value [code] "OAlist.map2_val_rneutr (\<lambda>_. minus)
                (oalist_of_list ([(1, 4), (0::nat, 4::nat), (1, 3), (0, 2), (3, 1)], key_order_of_le))
                (oalist_of_list ([(0::nat, 4::nat), (1, 3), (2, 2), (1, 1)], rv_key_order))"

end (* theory *)
