theory OAlist
  imports OAlist_Impl
begin

type_synonym 'a comp_opt = "'a \<Rightarrow> 'a \<Rightarrow> (comparison option)"

subsection \<open>A Type Class for @{term compare} that is independent of order relations\<close>

class compare =
  fixes compare :: "'a comparator"
  assumes compare_greater: "compare x y = GREATER \<longleftrightarrow> compare y x = LESS"
  assumes compare_equal: "compare x y = EQUAL \<longleftrightarrow> x = y"
  assumes compare_trans: "compare x y = LESS \<Longrightarrow> compare y z = LESS \<Longrightarrow> compare x z = LESS"
begin

lemma compare_same [simp]: "compare x x = EQUAL"
  by (simp add: compare_equal)

lemma uminus_compare [simp]: "- compare x y = compare y x"
  by (metis comparison.exhaust local.compare_greater uminus_eq_GREATER_iff uminus_eq_LESS_iff)

lemma comparator_eq_on_compare [simp]: "comparator_eq_on compare D"
  by (unfold_locales, auto simp: compare_equal intro: compare_trans)

abbreviation "less_eq_of_comp \<equiv> c.less_eq_of_comparator compare"
abbreviation "less_of_comp \<equiv> c.less_of_comparator compare"
abbreviation "greater_eq_of_comp \<equiv> c.less_eq_of_comparator (- compare)"
abbreviation "greater_of_comp \<equiv> c.less_of_comparator (- compare)"

lemma less_eq_of_comp_alt: "less_eq_of_comp = (\<lambda>x y. compare x y \<noteq> GREATER)"
  by (meson c.less_eq_of_comparator_def)

lemma less_of_comp_alt: "less_of_comp = (\<lambda>x y. compare x y = LESS)"
  by (meson c.less_of_comparator_def)

lemma reflp_less_eq_of_comp: "reflp less_eq_of_comp"
  by (simp add: c.less_eq_of_comparator_def reflpI)

lemma irreflp_less_of_comp: "irreflp less_of_comp"
  by (simp add: c.less_of_comparator_def irreflpI)

lemma transp_less_eq_of_comp: "transp less_eq_of_comp"
  by (smt c.less_eq_of_comparator_def comparison.exhaust compare_equal compare_trans transpI)

lemma transp_less_of_comp: "transp less_of_comp"
  by (smt c.less_of_comparator_def comparison.exhaust compare_equal compare_trans transpI)

lemma antisymp_less_eq_of_comp: "antisymp less_eq_of_comp"
  by (metis (no_types, lifting) antisympI c.less_eq_of_comparator_def comparison.exhaust compare_equal compare_greater)

lemma asymp_less_of_comp: "asymp less_of_comp"
  by (metis asymp.intros irreflp_def irreflp_less_of_comp transpD transp_less_of_comp)

lemma greater_eq_of_comp_alt: "greater_eq_of_comp = (\<lambda>x y. less_eq_of_comp y x)"
  by (metis c.less_eq_of_comparator_def uminus_compare uminus_apply)

lemma greater_of_comp_alt: "greater_of_comp = (\<lambda>x y. less_of_comp y x)"
  by (metis c.less_of_comparator_def uminus_compare uminus_apply)

fun update_by' :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "update_by' (k, v) [] = (if v = 0 then [] else [(k, v)])"
| "update_by' (k, v) ((k', v') # xs) =
  (case compare k k' of LESS \<Rightarrow> (if v = 0 then (k', v') # xs else (k, v) # (k', v') # xs)
                     | EQUAL \<Rightarrow> (if v = 0 then xs else (k, v) # xs)
                   | GREATER \<Rightarrow> (k', v') # update_by' (k, v) xs)"

fun update_by_fun_raw :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "update_by_fun_raw k f [] = (let v = f 0 in if v = 0 then [] else [(k, v)])"
| "update_by_fun_raw k f ((k', v') # xs) =
  (case compare k k' of LESS \<Rightarrow> (let v = f 0 in if v = 0 then (k', v') # xs else (k, v) # (k', v') # xs)
                     | EQUAL \<Rightarrow> (let v = f v' in if v = 0 then xs else (k, v) # xs)
                   | GREATER \<Rightarrow> (k', v') # update_by_fun_raw k f xs)"

fun update_by_fun_gr_raw :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b::zero) list"
  where "update_by_fun_gr_raw k f xs =
          (if xs = [] then
            (let v = f 0 in if v = 0 then [] else [(k, v)])
          else if compare k (fst (last xs)) = GREATER then
            (let v = f 0 in if v = 0 then xs else xs @ [(k, v)])
          else
            update_by_fun_raw k f xs
          )"

fun map_val_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list"
where
  "map_val_raw f [] = []"
| "map_val_raw f ((kx, vx) # xs) =
    (let v = f kx vx; aux = map_val_raw f xs in if v = 0 then aux else (kx, v) # aux)"

(*
fun map2_val_raw_tr :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list \<Rightarrow> ('a \<times> 'd::zero) list \<Rightarrow>
                        ('a \<times> 'd::zero) list"
where
  "map2_val_raw_tr f [] [] acc = acc"
| "map2_val_raw_tr f [] ((ky, vy) # ys) acc =
    (let v = f ky 0 vy in map2_val_raw_tr f [] ys (if v = 0 then acc else (ky, v) # acc))"
| "map2_val_raw_tr f ((kx, vx) # xs) [] acc =
    (let v = f kx vx 0 in map2_val_raw_tr f xs [] (if v = 0 then acc else (kx, v) # acc))"
| "map2_val_raw_tr f ((kx, vx) # xs) ((ky, vy) # ys) acc =
    (case compare kx ky of LESS \<Rightarrow> (let v = f kx vx 0 in map2_val_raw_tr f xs ((ky, vy) # ys) (if v = 0 then acc else (kx, v) # acc))
                        | EQUAL \<Rightarrow> (let v = f kx vx vy in map2_val_raw_tr f xs ys (if v = 0 then acc else (kx, v) # acc))
                      | GREATER \<Rightarrow> (let v = f ky 0 vy in map2_val_raw_tr f ((kx, vx) # xs) ys (if v = 0 then acc else (ky, v) # acc)))"

definition "map2_val_raw f xs ys = rev (map2_val_raw_tr f xs ys [])"
*)

fun map2_val_neutr_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "map2_val_neutr_raw f xs [] = xs"
| "map2_val_neutr_raw f [] ys = ys"
| "map2_val_neutr_raw f ((kx, vx) # xs) ((ky, vy) # ys) =
    (case compare kx ky of LESS \<Rightarrow> (let v = f kx vx 0; aux = map2_val_neutr_raw f xs ((ky, vy) # ys) in if v = 0 then aux else (kx, v) # aux)
                        | EQUAL \<Rightarrow> (let v = f kx vx vy; aux = map2_val_neutr_raw f xs ys in if v = 0 then aux else (kx, v) # aux)
                      | GREATER \<Rightarrow> (let v = f ky 0 vy; aux = map2_val_neutr_raw f ((kx, vx) # xs) ys in if v = 0 then aux else (ky, v) # aux))"

fun map2_val_rneutr_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list \<Rightarrow> ('a \<times> 'b::zero) list"
where
  "map2_val_rneutr_raw f xs [] = xs"
| "map2_val_rneutr_raw f [] ((ky, vy) # ys) =
    (let v = f ky 0 vy; aux = map2_val_rneutr_raw f [] ys in if v = 0 then aux else (ky, v) # aux)"
| "map2_val_rneutr_raw f ((kx, vx) # xs) ((ky, vy) # ys) =
    (case compare kx ky of LESS \<Rightarrow> (let v = f kx vx 0; aux = map2_val_rneutr_raw f xs ((ky, vy) # ys) in if v = 0 then aux else (kx, v) # aux)
                        | EQUAL \<Rightarrow> (let v = f kx vx vy; aux = map2_val_rneutr_raw f xs ys in if v = 0 then aux else (kx, v) # aux)
                      | GREATER \<Rightarrow> (let v = f ky 0 vy; aux = map2_val_rneutr_raw f ((kx, vx) # xs) ys in if v = 0 then aux else (ky, v) # aux))"

text \<open>In addition to @{const map2_val_rneutr_raw} one could define \<open>map2_val_lneutr_raw\<close> and \<open>map2_val_raw\<close>,
  but we do not need them.\<close>

fun lex_ord_raw :: "('a \<Rightarrow> ('b comp_opt)) \<Rightarrow> (('a \<times> 'b::zero) list) comp_opt"
where
  "lex_ord_raw f []       []       = Some EQUAL"
| "lex_ord_raw f []       ((ky, vy) # ys) =
    (let aux = f ky 0 vy in if aux = Some EQUAL then lex_ord_raw f [] ys else aux)"
| "lex_ord_raw f ((kx, vx) # xs) []       =
    (let aux = f kx vx 0 in if aux = Some EQUAL then lex_ord_raw f xs [] else aux)"
| "lex_ord_raw f ((kx, vx) # xs) ((ky, vy) # ys) =
  (case compare kx ky of LESS    \<Rightarrow> (let aux = f kx vx 0 in if aux = Some EQUAL then lex_ord_raw f xs ((ky, vy) # ys) else aux)
                       | EQUAL   \<Rightarrow> (let aux = f kx vx vy in if aux = Some EQUAL then lex_ord_raw f xs ys else aux)
                       | GREATER \<Rightarrow> (let aux = f ky 0 vy in if aux = Some EQUAL then lex_ord_raw f ((kx, vx) # xs) ys else aux))"

fun prod_ord_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b::zero) list \<Rightarrow> ('a \<times> 'c::zero) list \<Rightarrow> bool"
where
  "prod_ord_raw f []       []       = True"
| "prod_ord_raw f []       ((ky, vy) # ys) = (f ky 0 vy \<and> prod_ord_raw f [] ys)"
| "prod_ord_raw f ((kx, vx) # xs) []       = (f kx vx 0 \<and> prod_ord_raw f xs [])"
| "prod_ord_raw f ((kx, vx) # xs) ((ky, vy) # ys) =
  (case compare kx ky of LESS    \<Rightarrow> (f kx vx 0 \<and> prod_ord_raw f xs ((ky, vy) # ys))
                     | EQUAL   \<Rightarrow> (f kx vx vy \<and> prod_ord_raw f xs ys)
                     | GREATER \<Rightarrow> (f ky 0 vy \<and> prod_ord_raw f ((kx, vx) # xs) ys))"

lemma update_by'_eq_update_by:
  assumes "v \<noteq> 0"
  shows "update_by' (k, v) xs = c.update_by compare k v xs"
proof (induct xs, simp add: assms)
  fix xs and x::"'a \<times> 'b"
  assume IH: "update_by' (k, v) xs = c.update_by compare_class.compare k v xs"
  obtain k' v' where x: "x = (k', v')" by fastforce
  show "update_by' (k, v) (x # xs) = c.update_by compare_class.compare k v (x # xs)"
    by (simp add: x assms IH cong: comparison.case_cong)
qed

lemma set_update_by'_subset: "set (update_by' kv xs) \<subseteq> insert kv (set xs)"
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  have 1: "set xs \<subseteq> insert a (insert b (set xs))" for a b by auto
  have 2: "set (update_by' kv xs) \<subseteq> insert kv (insert (k', v') (set xs))" for kv
    using Cons by blast
  show ?case by (simp add: x kv 1 2 split: comparison.split)
qed

lemma update_by'_sorted:
  assumes "sorted_wrt less_of_comp (map fst xs)"
  shows "sorted_wrt less_of_comp (map fst (update_by' kv xs))"
  using assms
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  from Cons(2) have 1: "sorted_wrt less_of_comp (k' # (map fst xs))" by (simp add: x)
  hence 2: "sorted_wrt less_of_comp (map fst xs)" using sorted_wrt.elims(3) by fastforce
  hence 3: "sorted_wrt less_of_comp (map fst (update_by' (k, u) xs))" for u by (rule Cons(1))
  have 4: "sorted_wrt less_of_comp (k' # map fst (update_by' (k, u) xs))"
    if *: "compare_class.compare k k' = GREATER" for u
  proof (simp, intro conjI ballI)
    fix y
    assume "y \<in> set (update_by' (k, u) xs)"
    also from set_update_by'_subset have "... \<subseteq> insert (k, u) (set xs)" .
    finally have "y = (k, u) \<or> y \<in> set xs" by simp
    thus "less_of_comp k' (fst y)"
    proof
      assume "y = (k, u)"
      hence "fst y = k" by simp
      from * show ?thesis unfolding \<open>fst y = k\<close>
        by (meson c.less_of_comparator_def compare_greater)
    next
      from 1 have 5: "\<forall>y \<in> fst ` set xs. less_of_comp k' y" by simp
      assume "y \<in> set xs"
      hence "fst y \<in> fst ` set xs" by simp
      with 5 show ?thesis ..
    qed
  qed (fact 3)
  show ?case
    by (simp add: kv x 1 2 4 sorted_wrt2[OF transp_less_of_comp] split: comparison.split del: sorted_wrt.simps, intro conjI impI,
        simp add: less_of_comp_alt, simp add: 1 compare_equal del: sorted_wrt.simps)
qed

lemma update_by'_not_zero:
  assumes "0 \<notin> snd ` set xs"
  shows "0 \<notin> snd ` set (update_by' kv xs)"
  using assms
proof (induct xs arbitrary: kv)
  case Nil
  obtain k v where kv: "kv = (k, v)" by fastforce
  thus ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  obtain k v where kv: "kv = (k, v)" by fastforce
  from Cons(2) have 1: "v' \<noteq> 0" and 2: "0 \<notin> snd ` set xs" by (simp add: x, simp)
  from 2 have 3: "0 \<notin> snd ` set (update_by' (k, u) xs)" for u by (rule Cons(1))
  show ?case by (simp add: kv x 1 2 3 split: comparison.split)
qed

lemma update_by'_eq_Cons:
  assumes "v \<noteq> 0" and "xs = [] \<or> compare k (fst (hd xs)) = LESS"
  shows "update_by' (k, v) xs = (k, v) # xs"
  using assms(2)
proof (induct xs)
case Nil
  from assms(1) show ?case by simp
next
  case (Cons x xs)
  obtain k' v' where x: "x = (k', v')" by fastforce
  from Cons(2) have "compare_class.compare k k' = LESS" by (simp add: x)
  with assms(1) show ?case by (simp add: x)
qed

lemma update_by_fun_gr_raw_eq_update_by_fun_raw:
  assumes "sorted_wrt less_of_comp (map fst xs)"
  shows "update_by_fun_gr_raw k f xs = update_by_fun_raw k f xs"
  sorry

lemma map2_val_rneutr_raw_singleton_eq_update_by_fun_raw:
  assumes "\<And>a x. f a x 0 = x"
  shows "map2_val_rneutr_raw f xs [(k, v)] = update_by_fun_raw k (\<lambda>x. f k x v) xs"
  sorry

lemma map2_val_rneutr_raw_eq_map2_val_neutr_raw:
  assumes "\<And>a x. f a x 0 = x" and "\<And>a. f a 0 = id"
  shows "map2_val_rneutr_raw f = map2_val_neutr_raw f"
  sorry

end

subsection \<open>Invariant\<close>

definition oalist_inv :: "('a::compare \<times> 'b::zero) list \<Rightarrow> bool"
  where "oalist_inv xs \<longleftrightarrow> (0 \<notin> snd ` set xs \<and> sorted_wrt less_of_comp (map fst xs))"

lemma oalist_invI:
  assumes "0 \<notin> snd ` set xs" and "sorted_wrt less_of_comp (map fst xs)"
  shows "oalist_inv xs"
  unfolding oalist_inv_def using assms by blast

lemma oalist_invD1:
  assumes "oalist_inv xs"
  shows "0 \<notin> snd ` set xs"
  using assms unfolding oalist_inv_def by blast

lemma oalist_invD2:
  assumes "oalist_inv xs"
  shows "sorted_wrt less_of_comp (map fst xs)"
  using assms unfolding oalist_inv_def by blast

lemma oalist_inv_Nil: "oalist_inv []"
  by (simp add: oalist_inv_def)

lemma oalist_inv_filter:
  assumes "oalist_inv xs"
  shows "oalist_inv (filter P xs)"
proof (rule oalist_invI)
  from assms have "0 \<notin> snd ` set xs" by (rule oalist_invD1)
  thus "0 \<notin> snd ` set (filter P xs)" by auto
next
  from assms have "sorted_wrt less_of_comp (map fst xs)" by (rule oalist_invD2)
  thus "sorted_wrt less_of_comp (map fst (filter P xs))" by (induct xs, simp, simp)
qed

lemma map_val_raw_dom_subset: "fst ` set (map_val_raw f xs) \<subseteq> fst ` set xs"
  by (induct xs rule: map_val_raw.induct, auto simp: Let_def)

lemma oalist_inv_map_val_raw:
  assumes "oalist_inv xs"
  shows "oalist_inv (map_val_raw f xs)"
proof (rule oalist_invI)
  show "0 \<notin> snd ` set (map_val_raw f xs)"
    by (induct xs rule: map_val_raw.induct, simp, simp add: Let_def)
next
  from assms have "sorted_wrt less_of_comp (map fst xs)" by (rule oalist_invD2)
  thus "sorted_wrt less_of_comp (map fst (map_val_raw f xs))"
  proof (induct xs rule: map_val_raw.induct)
    case (1 f)
    show ?case by simp
  next
    case (2 f kx vx xs)
    from 2(2) have 1: "sorted_wrt less_of_comp (kx # (map fst xs))" by simp
    hence 3: "\<forall>y \<in> fst ` set xs. less_of_comp kx y" and "sorted_wrt less_of_comp (map fst xs)"
      by simp_all
    from refl this(2) have 2: "sorted_wrt less_of_comp (map fst (map_val_raw f xs))" by (rule 2(1))
    show ?case
    proof (simp add: Let_def 2, intro impI ballI)
      fix y
      assume "y \<in> set (map_val_raw f xs)"
      hence "fst y \<in> fst ` set (map_val_raw f xs)" by simp
      also have "... \<subseteq> fst ` set xs" by (fact map_val_raw_dom_subset)
      finally have "fst y \<in> fst ` set xs" .
      with 3 show "less_of_comp kx (fst y)" ..
    qed
  qed
qed

subsection \<open>Sorting Associative Lists\<close>

definition sort_alist :: "('a \<times> 'b) list \<Rightarrow> ('a::compare \<times> 'b::zero) list"
  where "sort_alist xs = foldr update_by' xs []"

lemma oalist_inv_sort_alist: "oalist_inv (sort_alist xs)"
  unfolding oalist_inv_def
proof
  have "0 \<notin> snd ` set (foldr update_by' xs ys)" if "0 \<notin> snd ` set ys" for ys using that
  proof (induct xs)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    from Cons(2) have "0 \<notin> snd ` set (foldr update_by' xs ys)" by (rule Cons(1))
    hence "0 \<notin> snd ` set (update_by' x (foldr update_by' xs ys))" by (rule update_by'_not_zero)
    thus ?case by simp
  qed
  thus "0 \<notin> snd ` set (sort_alist xs)" by (simp add: sort_alist_def)
next
  have "sorted_wrt less_of_comp (map fst (foldr update_by' xs ys))"
    if "sorted_wrt less_of_comp (map fst ys)" for ys using that
  proof (induct xs)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    from Cons(2) have "sorted_wrt less_of_comp (map fst (foldr update_by' xs ys))" by (rule Cons(1))
    hence "sorted_wrt less_of_comp (map fst (update_by' x (foldr update_by' xs ys)))"
      by (rule update_by'_sorted)
    thus ?case by simp
  qed
  thus "sorted_wrt less_of_comp (map fst (sort_alist xs))" by (simp add: sort_alist_def)
qed

lemma sort_alist_id:
  assumes "oalist_inv xs"
  shows "sort_alist xs = xs"
proof -
  have "foldr update_by' xs ys = xs @ ys" if "oalist_inv (xs @ ys)" for ys using that
  proof (induct xs)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)
    obtain k v where x: "x = (k, v)" by fastforce
    from Cons(2) have *: "oalist_inv ((k, v) # (xs @ ys))" by (simp add: x)
    hence 1: "oalist_inv (xs @ ys)" by (simp add: oalist_inv_def)
    hence 2: "foldr update_by' xs ys = xs @ ys" by (rule Cons(1))
    show ?case
    proof (simp add: 2 x, rule update_by'_eq_Cons)
      from * show "v \<noteq> 0" by (simp add: oalist_inv_def)
    next
      have "compare_class.compare k (fst (hd (xs @ ys))) = LESS \<or> xs @ ys = []"
      proof (rule disjCI)
        assume "xs @ ys \<noteq> []"
        then obtain k'' v'' zs where eq: "xs @ ys = (k'', v'') # zs"
          by (meson c.update_by.cases)
        from * have "less_of_comp k k''" by (simp add: eq oalist_inv_def)
        thus "compare_class.compare k (fst (hd (xs @ ys))) = LESS" by (simp add: eq less_of_comp_alt)
      qed
      thus "xs @ ys = [] \<or> compare_class.compare k (fst (hd (xs @ ys))) = LESS" by auto
    qed
  qed
  with assms show ?thesis by (simp add: sort_alist_def)
qed

subsection \<open>Abstract characterisation\<close>

typedef (overloaded) ('a, 'b) oalist = "{xs. oalist_inv xs} :: ('a::compare \<times> 'b::zero) list set"
  morphisms list_of_oalist Abs_oalist
  by (auto intro: oalist_inv_Nil)

setup_lifting type_definition_oalist

lemma oalist_eq_iff: "xs = ys \<longleftrightarrow> list_of_oalist xs = list_of_oalist ys"
  by (simp add: list_of_oalist_inject)

lemma oalist_eqI: "list_of_oalist xs = list_of_oalist ys \<Longrightarrow> xs = ys"
  by (simp add: oalist_eq_iff)

text \<open>Formal, totalized constructor for @{typ "('a, 'b) oalist"}:\<close>

definition OAlist :: "('a \<times> 'b) list \<Rightarrow> ('a::compare, 'b::zero) oalist" where
  "OAlist xs = Abs_oalist (sort_alist xs)"

lemma oalist_inv_list_of_oalist [simp, intro]: "oalist_inv (list_of_oalist xs)"
  using list_of_oalist [of xs] by simp

lemma list_of_oalist_OAlist [simp]:
  "list_of_oalist (OAlist xs) = sort_alist xs"
  by (simp add: OAlist_def Abs_oalist_inverse oalist_inv_sort_alist)

lemma OAlist_list_of_oalist [simp, code abstype]: "OAlist (list_of_oalist xs) = xs"
  by (simp add: OAlist_def list_of_oalist_inverse sort_alist_id)

text \<open>Fundamental operations:\<close>

context
begin

qualified definition empty :: "('a::compare, 'b::zero) oalist"
  where "empty = OAlist []"

qualified definition insert :: "('a \<times> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a::compare, 'b::zero) oalist"
  where "insert x xs = OAlist (update_by' x (list_of_oalist xs))"

qualified definition update_by_fun :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a::compare, 'b::zero) oalist"
  where "update_by_fun k f xs = OAlist (update_by_fun_raw k f (list_of_oalist xs))"

qualified definition update_by_fun_gr :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a::compare, 'b::zero) oalist"
  where "update_by_fun_gr k f xs = OAlist (update_by_fun_gr_raw k f (list_of_oalist xs))"

qualified definition map :: "(('a \<times> 'b) \<Rightarrow> ('d \<times> 'c)) \<Rightarrow> ('a::compare, 'b::zero) oalist \<Rightarrow>
                            ('d::compare, 'c::zero) oalist"
  where "map f xs = OAlist (List.map f (list_of_oalist xs))"

qualified definition lookup :: "('a::compare, 'b::zero) oalist \<Rightarrow> 'a \<Rightarrow> 'b"
  where "lookup xs = c.lookup_default compare 0 (list_of_oalist xs)"

qualified definition filter :: "(('a \<times> 'b) \<Rightarrow> bool) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a::compare, 'b::zero) oalist"
  where "filter P xs = OAlist (List.filter P (list_of_oalist xs))"

qualified definition map2_val_neutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b) oalist \<Rightarrow>
                                    ('a::compare, 'b::zero) oalist"
  where "map2_val_neutr f xs ys = OAlist (map2_val_neutr_raw f (list_of_oalist xs) (list_of_oalist ys))"

qualified definition map2_val_rneutr :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'c::zero) oalist \<Rightarrow>
                                    ('a::compare, 'b::zero) oalist"
  where "map2_val_rneutr f xs ys = OAlist (map2_val_rneutr_raw f (list_of_oalist xs) (list_of_oalist ys))"

qualified definition lex_ord :: "('a \<Rightarrow> ('b comp_opt)) \<Rightarrow> ('a::compare, 'b::zero) oalist comp_opt"
  where "lex_ord f xs ys = lex_ord_raw f (list_of_oalist xs) (list_of_oalist ys)"

qualified definition prod_ord :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) oalist \<Rightarrow>
                                  ('a::compare, 'b::zero) oalist \<Rightarrow> bool"
  where "prod_ord f xs ys = prod_ord_raw f (list_of_oalist xs) (list_of_oalist ys)"

definition except_min :: "('a, 'b) oalist \<Rightarrow> ('a::compare, 'b::zero) oalist"
  where "except_min xs = OAlist (tl (list_of_oalist xs))"

text \<open>Derived operations\<close>

qualified definition map_val :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b::zero) oalist \<Rightarrow> ('a::compare, 'c::zero) oalist"
  where "map_val f xs = map (\<lambda>x. (fst x, f (fst x) (snd x))) xs"

end

subsection \<open>Executable version obeying invariant\<close>

lemma list_of_oalist_empty [simp, code abstract]: "list_of_oalist OAlist.empty = []"
  by (simp add: OAlist.empty_def sort_alist_def)

lemma list_of_oalist_insert [simp, code abstract]:
  "list_of_oalist (OAlist.insert x xs) = update_by' x (list_of_oalist xs)"
  unfolding OAlist.insert_def
  by (metis (no_types, hide_lams) OAlist_list_of_oalist foldr.simps(2) list_of_oalist_OAlist o_def sort_alist_def)

lemma update_by_fun_gr_eq_update_by_fun: "OAlist.update_by_fun_gr = OAlist.update_by_fun"
  apply (rule, rule, rule, simp only: OAlist.update_by_fun_gr_def OAlist.update_by_fun_def)
  by (metis oalist_invD2 oalist_inv_list_of_oalist update_by_fun_gr_raw_eq_update_by_fun_raw)

lemma list_of_oalist_update_by_fun [simp, code abstract]:
  "list_of_oalist (OAlist.update_by_fun k f xs) = update_by_fun_raw k f (list_of_oalist xs)"
  sorry

lemma list_of_oalist_update_by_fun_gr [simp, code abstract]:
  "list_of_oalist (OAlist.update_by_fun_gr k f xs) = update_by_fun_gr_raw k f (list_of_oalist xs)"
  apply (simp only: update_by_fun_gr_eq_update_by_fun list_of_oalist_update_by_fun)
  by (metis oalist_invD2 oalist_inv_list_of_oalist update_by_fun_gr_raw_eq_update_by_fun_raw)

lemma list_of_oalist_filter [simp, code abstract]:
  "list_of_oalist (OAlist.filter P xs) = List.filter P (list_of_oalist xs)"
  by (simp add: OAlist.filter_def, rule sort_alist_id, rule oalist_inv_filter, simp)

lemma list_of_oalist_map_val [simp, code abstract]:
  "list_of_oalist (OAlist.map_val f xs) = map_val_raw f (list_of_oalist xs)"
  sorry

lemma list_of_oalist_map2_val_neutr [simp, code abstract]:
  "list_of_oalist (OAlist.map2_val_neutr f xs ys) = map2_val_neutr_raw f (list_of_oalist xs) (list_of_oalist ys)"
  sorry

lemma list_of_oalist_map2_val_rneutr [simp, code abstract]:
  "list_of_oalist (OAlist.map2_val_rneutr f xs ys) = map2_val_rneutr_raw f (list_of_oalist xs) (list_of_oalist ys)"
  sorry

lemma list_of_oalist_except_min [code abstract]:
  "list_of_oalist (except_min xs) = (tl (list_of_oalist xs))"
  sorry

(* TODO: Prove relationship between operations and "lookup", and prove that "lookup" is injective. *)

subsection \<open>Further Lemmas\<close>

lemma map2_val_rneutr_singleton_eq_update_by_fun:
  assumes "\<And>a x. f a x 0 = x" and "list_of_oalist ys = [(k, v)]"
  shows "OAlist.map2_val_rneutr f xs ys = OAlist.update_by_fun k (\<lambda>x. f k x v) xs"
  by (simp add: OAlist.map2_val_rneutr_def OAlist.update_by_fun_def assms map2_val_rneutr_raw_singleton_eq_update_by_fun_raw)

lemma map2_val_rneutr_eq_map2_val_neutr:
  assumes "\<And>a x. f a x 0 = x" and "\<And>a. f a 0 = id"
  shows "OAlist.map2_val_rneutr f = OAlist.map2_val_neutr f"
  by (rule, rule, simp add: OAlist.map2_val_rneutr_def OAlist.map2_val_neutr_def assms map2_val_rneutr_raw_eq_map2_val_neutr_raw)

text \<open>Explicit executable conversion\<close>

definition [simp]: "oalist_of_list = OAlist"

lemma [code abstract]: "list_of_oalist (oalist_of_list xs) = sort_alist xs"
  by simp

instantiation oalist :: (compare, "{equal,zero}") equal
begin

definition "equal_oalist xs ys \<longleftrightarrow> equal_class.equal (list_of_oalist xs) (list_of_oalist ys)"

instance
  by (standard, simp add: equal_oalist_def equal oalist_eq_iff)

end

lemmas [code] = equal_oalist_def

instantiation nat :: compare
begin

definition compare_nat :: "nat comparator" where
  "compare_nat = comparator_of_le"

instance sorry

end

value [code] "oalist_of_list [(0::nat, 4::nat), (1, 3), (0, 2), (1, 1)]"

value [code] "except_min (oalist_of_list [(1, 3), (0::nat, 4::nat), (0, 2), (1, 1)])"

value [code] "OAlist.lookup (oalist_of_list [(0::nat, 4::nat), (1, 3), (0, 2), (1, 1)]) 1"

value [code] "OAlist.prod_ord (\<lambda>_. less_eq)
                (oalist_of_list [(1, 4), (0::nat, 4::nat), (1, 3), (0, 2), (1, 1)])
                (oalist_of_list [(0::nat, 4::nat), (1, 3), (0, 2), (1, 1)])"

end (* theory *)
