text \<open>Some further general properties of, and functions on, sets and lists.\<close>

theory General_Utils
imports Main
begin
  
section \<open>Sets\<close>

lemma Compr_cong:
  assumes "P = Q" and "\<And>x. P x \<Longrightarrow> f x = g x"
  shows "{f x | x. P x} = {g x | x. Q x}"
  using assms by metis

lemma card_geq_ex_subset:
  assumes "card A \<ge> n"
  obtains B where "card B = n" and "B \<subseteq> A"
  using assms
proof (induct n arbitrary: thesis)
  case base: 0
  show ?case
  proof (rule base(1))
    show "card {} = 0" by simp
  next
    show "{} \<subseteq> A" ..
  qed
next
  case ind: (Suc n)
  from ind(3) have "n < card A" by simp
  obtain B where card: "card B = n" and "B \<subseteq> A"
  proof (rule ind(1))
    from \<open>n < card A\<close> show "n \<le> card A" by simp
  qed
  from \<open>n < card A\<close> have "card A \<noteq> 0" by simp
  with card_infinite[of A] have "finite A" by blast
  let ?C = "A - B"
  have "?C \<noteq> {}"
  proof
    assume "A - B = {}"
    hence "A \<subseteq> B" by simp
    from this \<open>B \<subseteq> A\<close> have "A = B" ..
    from \<open>n < card A\<close> show False unfolding \<open>A = B\<close> card by simp
  qed
  then obtain c where "c \<in> ?C" by auto
  hence "c \<notin> B" by simp
  hence "B - {c} = B" by simp
  show ?case
  proof (rule ind(2))
    thm card_insert
    have "card (B \<union> {c}) = card (insert c B)" by simp
    also have "... = Suc (card (B - {c}))"
      by (rule card_insert, rule finite_subset, fact \<open>B \<subseteq> A\<close>, fact)
    finally show "card (B \<union> {c}) = Suc n" unfolding \<open>B - {c} = B\<close> card .
  next
    show "B \<union> {c} \<subseteq> A" unfolding Un_subset_iff
    proof (intro conjI, fact)
      from \<open>c \<in> ?C\<close> show "{c} \<subseteq> A" by auto
    qed
  qed
qed

lemma card_2_I:
  assumes "x \<noteq> y"
  shows "card {x, y} = 2"
proof -
  from assms have eq: "{y} - {x} = {y}" by simp
  have "card {x, y} = Suc (card ({y} - {x}))" by (rule card_insert, rule, rule)
  also have "... = Suc (card {y})" unfolding eq ..
  also have "... = Suc 1" by simp
  finally show ?thesis by simp
qed

lemma card_2_E:
  assumes "card A = 2"
  obtains x y where "x \<noteq> y" and "A = {x, y}"
proof -
  from assms have "card A > 0" by simp
  hence "A \<noteq> {}" by auto
  then obtain x where "x \<in> A" by auto
  have "A - {x} \<noteq> {}"
  proof
    assume "A - {x} = {}"
    with \<open>A \<noteq> {}\<close> have "A = {x}" by auto
    hence "card A = 1" by simp
    with assms show False by simp
  qed
  then obtain y where "y \<in> A - {x}" by auto
  hence "y \<in> A" and "y \<noteq> x" by auto
  show ?thesis
  proof
    show "A = {x, y}"
    proof (rule card_seteq[symmetric])
      from \<open>card A > 0\<close> show "finite A" by (simp add: card_gt_0_iff)
    next
      from \<open>x \<in> A\<close> \<open>y \<in> A\<close> show "{x, y} \<subseteq> A" by simp
    next
      show "card A \<le> card {x, y}" unfolding assms using \<open>y \<noteq> x\<close> by simp
    qed
  qed (fact \<open>y \<noteq> x\<close>[symmetric])
qed

lemma image_Collect_eqI:
  assumes "\<And>x. P x \<longleftrightarrow> Q x" and "\<And>x. Q x \<Longrightarrow> f x = g x"
  shows "{f x | x. P x} = {g x | x. Q x}"
  using assms by metis

lemma image_image_Collect:
  "f ` {g x | x. P x} = {f (g x) | x. P x}"
  by auto
    
section \<open>Lists\<close>

lemma distinct_reorder: "distinct (xs @ (y # ys)) = distinct (y # (xs @ ys))" by auto
    
lemma set_reorder: "set (xs @ (y # ys)) = set (y # (xs @ ys))" by simp

primrec remdups_wrt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
remdups_wrt_base: "remdups_wrt _ [] = []" |
remdups_wrt_rec: "remdups_wrt f (x # xs) = (if f x \<in> f ` set xs then remdups_wrt f xs else x # remdups_wrt f xs)"
    
lemma set_remdups_wrt: "f ` set (remdups_wrt f xs) = f ` set xs"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_wrt_base ..
next
  case (Cons a xs)
  show ?case unfolding remdups_wrt_rec
  proof (simp only: split: if_splits, intro conjI, intro impI)
    assume "f a \<in> f ` set xs"
      have "f ` set (a # xs) = insert (f a) (f ` set xs)" by simp
    have "f ` set (remdups_wrt f xs) = f ` set xs" by fact
    also from \<open>f a \<in> f ` set xs\<close> have "... = insert (f a) (f ` set xs)" by (simp add: insert_absorb)
    also have "... = f ` set (a # xs)" by simp
    finally show "f ` set (remdups_wrt f xs) = f ` set (a # xs)" .
  qed (simp add: Cons.hyps)
qed

lemma subset_remdups_wrt: "set (remdups_wrt f xs) \<subseteq> set xs"
  by (induct xs, auto)

lemma remdups_wrt_distinct_wrt:
  assumes "x \<in> set (remdups_wrt f xs)" and "y \<in> set (remdups_wrt f xs)" and "x \<noteq> y"
  shows "f x \<noteq> f y"
  using assms(1) assms(2)
proof (induct xs)
  case Nil
  thus ?case unfolding remdups_wrt_base by simp
next
  case (Cons a xs)
  from Cons(2) Cons(3) show ?case unfolding remdups_wrt_rec
  proof (simp only: split: if_splits)
    assume "x \<in> set (remdups_wrt f xs)" and "y \<in> set (remdups_wrt f xs)"
    thus "f x \<noteq> f y" by (rule Cons.hyps)
  next
    assume "\<not> True"
    thus "f x \<noteq> f y" by simp
  next
    assume "f a \<notin> f ` set xs" and xin: "x \<in> set (a # remdups_wrt f xs)" and yin: "y \<in> set (a # remdups_wrt f xs)"
    from yin have y: "y = a \<or> y \<in> set (remdups_wrt f xs)" by simp
    from xin have "x = a \<or> x \<in> set (remdups_wrt f xs)" by simp
    thus "f x \<noteq> f y"
    proof
      assume "x = a"
      from y show ?thesis
      proof
        assume "y = a"
        with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>x = a\<close> by simp
      next
        assume "y \<in> set (remdups_wrt f xs)"
        have "y \<in> set xs" by (rule, fact, rule subset_remdups_wrt)
        hence "f y \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>x = a\<close> by auto
      qed
    next
      assume "x \<in> set (remdups_wrt f xs)"
      from y show ?thesis
      proof
        assume "y = a"
        have "x \<in> set xs" by (rule, fact, rule subset_remdups_wrt)
        hence "f x \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>y = a\<close> by auto
      next
        assume "y \<in> set (remdups_wrt f xs)"
        with \<open>x \<in> set (remdups_wrt f xs)\<close> show ?thesis by (rule Cons.hyps)
      qed
    qed
  qed
qed
  
lemma distinct_remdups_wrt: "distinct (remdups_wrt f xs)"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_wrt_base by simp
next
  case (Cons a xs)
  show ?case unfolding remdups_wrt_rec
  proof (split if_split, intro conjI impI, rule Cons.hyps)
    assume "f a \<notin> f ` set xs"
    hence "a \<notin> set xs" by auto
    hence "a \<notin> set (remdups_wrt f xs)" using subset_remdups_wrt[of f xs] by auto
    with Cons.hyps show "distinct (a # remdups_wrt f xs)" by simp
  qed
qed

lemma map_remdups_wrt: "map f (remdups_wrt f xs) = remdups (map f xs)"
  by (induct xs, auto)

lemma remdups_wrt_append:
  "remdups_wrt f (xs @ ys) = (filter (\<lambda>a. f a \<notin> f ` set ys) (remdups_wrt f xs)) @ (remdups_wrt f ys)"
  by (induct xs, auto)

lemma distinctI:
  assumes "\<And>i j. i < j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<noteq> xs ! j"
  shows "distinct xs"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp, intro conjI, rule)
    assume "x \<in> set xs"
    then obtain j where "j < length xs" and "x = xs ! j" by (metis in_set_conv_nth)
    hence "Suc j < length (x # xs)" by simp
    have "(x # xs) ! 0 \<noteq> (x # xs) ! (Suc j)" by (rule Cons(2), simp, simp, fact)
    thus False by (simp add: \<open>x = xs ! j\<close>)
  next
    show "distinct xs"
    proof (rule Cons(1))
      fix i j
      assume "i < j" and "i < length xs" and "j < length xs"
      hence "Suc i < Suc j" and "Suc i < length (x # xs)" and "Suc j < length (x # xs)" by simp_all
      hence "(x # xs) ! (Suc i) \<noteq> (x # xs) ! (Suc j)" by (rule Cons(2))
      thus "xs ! i \<noteq> xs ! j" by simp
    qed
  qed
qed

lemma filter_nth_pairE:
  assumes "i < j" and "i < length (filter P xs)" and "j < length (filter P xs)"
  obtains i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
    and "(filter P xs) ! i = xs ! i'" and "(filter P xs) ! j = xs ! j'"
  using assms
proof (induct xs arbitrary: i j thesis)
  case Nil
  from Nil(3) show ?case by simp
next
  case (Cons x xs)
  let ?ys = "filter P (x # xs)"
  show ?case
  proof (cases "P x")
    case True
    hence *: "?ys = x # (filter P xs)" by simp
    from \<open>i < j\<close> obtain j0 where j: "j = Suc j0" using lessE by blast
    have len_ys: "length ?ys = Suc (length (filter P xs))" and ys_j: "?ys ! j = (filter P xs) ! j0"
      by (simp only: * length_Cons, simp only: j * nth_Cons_Suc)
    from Cons(5) have "j0 < length (filter P xs)" unfolding len_ys j by auto
    show ?thesis
    proof (cases "i = 0")
      case True
      from \<open>j0 < length (filter P xs)\<close> obtain j' where "j' < length xs" and **: "(filter P xs) ! j0 = xs ! j'"
        by (metis (no_types, lifting) in_set_conv_nth mem_Collect_eq nth_mem set_filter)
      have "0 < Suc j'" by simp
      thus ?thesis
        by (rule Cons(2), simp, simp add: \<open>j' < length xs\<close>, simp only: True * nth_Cons_0,
            simp only: ys_j nth_Cons_Suc **)
    next
      case False
      then obtain i0 where i: "i = Suc i0" using lessE by blast
      have ys_i: "?ys ! i = (filter P xs) ! i0" by (simp only: i * nth_Cons_Suc)
      from Cons(3) have "i0 < j0" by (simp add: i j)
      from Cons(4) have "i0 < length (filter P xs)" unfolding len_ys i by auto
      from _ \<open>i0 < j0\<close> this \<open>j0 < length (filter P xs)\<close> obtain i' j'
        where "i' < j'" and "i' < length xs" and "j' < length xs"
          and i': "filter P xs ! i0 = xs ! i'" and j': "filter P xs ! j0 = xs ! j'"
        by (rule Cons(1))
      from \<open>i' < j'\<close> have "Suc i' < Suc j'" by simp
      thus ?thesis
        by (rule Cons(2), simp add: \<open>i' < length xs\<close>, simp add: \<open>j' < length xs\<close>,
            simp only: ys_i nth_Cons_Suc i', simp only: ys_j nth_Cons_Suc j')
    qed
  next
    case False
    hence *: "?ys = filter P xs" by simp
    with Cons(4) Cons(5) have "i < length (filter P xs)" and "j < length (filter P xs)" by simp_all
    with _ \<open>i < j\<close> obtain i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
      and i': "filter P xs ! i = xs ! i'" and j': "filter P xs ! j = xs ! j'"
      by (rule Cons(1))
    from \<open>i' < j'\<close> have "Suc i' < Suc j'" by simp
    thus ?thesis
      by (rule Cons(2), simp add: \<open>i' < length xs\<close>, simp add: \<open>j' < length xs\<close>,
          simp only: * nth_Cons_Suc i', simp only: * nth_Cons_Suc j')
  qed
qed

lemma distinct_filterI:
  assumes "\<And>i j. i < j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> P (xs ! i) \<Longrightarrow> P (xs ! j) \<Longrightarrow> xs ! i \<noteq> xs ! j"
  shows "distinct (filter P xs)"
proof (rule distinctI)
  fix i j::nat
  assume "i < j" and "i < length (filter P xs)" and "j < length (filter P xs)"
  then obtain i' j' where "i' < j'" and "i' < length xs" and "j' < length xs"
    and i: "(filter P xs) ! i = xs ! i'" and j: "(filter P xs) ! j = xs ! j'" by (rule filter_nth_pairE)
  from \<open>i' < j'\<close> \<open>i' < length xs\<close> \<open>j' < length xs\<close> show "(filter P xs) ! i \<noteq> (filter P xs) ! j" unfolding i j
  proof (rule assms)
    from \<open>i < length (filter P xs)\<close> show "P (xs ! i')" unfolding i[symmetric] using nth_mem by force
  next
    from \<open>j < length (filter P xs)\<close> show "P (xs ! j')" unfolding j[symmetric] using nth_mem by force
  qed
qed

lemma set_zip_map: "set (zip (map f xs) (map g xs)) = (\<lambda>x. (f x, g x)) ` (set xs)"
proof -
  have "{(map f xs ! i, map g xs ! i) |i. i < length xs} = {(f (xs ! i), g (xs ! i)) |i. i < length xs}"
  proof (rule Collect_eqI, rule, elim exE conjE, intro exI conjI, simp add: map_nth, assumption,
      elim exE conjE, intro exI)
    fix x i
    assume "x = (f (xs ! i), g (xs ! i))" and "i < length xs"
    thus "x = (map f xs ! i, map g xs ! i) \<and> i < length xs" by (simp add: map_nth)
  qed
  also have "... = (\<lambda>x. (f x, g x)) ` {xs ! i | i. i < length xs}" by blast
  finally show "set (zip (map f xs) (map g xs)) = (\<lambda>x. (f x, g x)) ` (set xs)"
    by (simp add: set_zip set_conv_nth[symmetric])
qed

lemma set_zip_map1: "set (zip (map f xs) xs) = (\<lambda>x. (f x, x)) ` (set xs)"
proof -
  have "set (zip (map f xs) (map id xs)) = (\<lambda>x. (f x, id x)) ` (set xs)" by (rule set_zip_map)
  thus ?thesis by simp
qed

lemma set_zip_map2: "set (zip xs (map f xs)) = (\<lambda>x. (x, f x)) ` (set xs)"
proof -
  have "set (zip (map id xs) (map f xs)) = (\<lambda>x. (id x, f x)) ` (set xs)" by (rule set_zip_map)
  thus ?thesis by simp
qed

fun (in ord) max_list :: "'a list \<Rightarrow> 'a" where
  "max_list (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> max x (max_list xs))"

lemma (in linorder) max_list_Max: "xs \<noteq> [] \<Longrightarrow> max_list xs = Max (set xs)"
  by (induct xs rule: induct_list012, auto)

subsection \<open>@{const map_of}\<close>

lemma map_of_filter: "map_of (filter (\<lambda>x. fst x = y) xs) y = map_of xs y"
  by (induct xs, auto)

lemma map_of_remdups_wrt: "map_of (remdups_wrt fst (rev xs)) = map_of xs"
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "dom [fst x \<mapsto> snd x] \<inter> dom (map_of [a\<leftarrow>remdups_wrt fst (rev xs) . fst a \<noteq> fst x]) = {}"
    by (auto simp add: dom_map_of_conv_image_fst)
  hence eq: "[fst x \<mapsto> snd x] ++ map_of [a\<leftarrow>remdups_wrt fst (rev xs) . fst a \<noteq> fst x] =
          map_of [a\<leftarrow>remdups_wrt fst (rev xs) . fst a \<noteq> fst x] ++ [fst x \<mapsto> snd x]"
    by (rule map_add_comm)
  show ?case
  proof (simp add: remdups_wrt_append eq, rule, simp, rule)
    fix y
    assume "y \<noteq> fst x"
    have *: "filter (\<lambda>x. fst x = y) (remdups_wrt fst (rev xs)) =
          filter (\<lambda>x. fst x = y) (filter (\<lambda>a. fst a \<noteq> fst x) (remdups_wrt fst (rev xs)))"
      by (simp, rule filter_cong, auto simp add: \<open>y \<noteq> fst x\<close>)
    have "map_of xs y = map_of (remdups_wrt fst (rev xs)) y" by (simp only: Cons)
    also have "... = map_of (filter (\<lambda>x. fst x = y) (remdups_wrt fst (rev xs))) y"
      by (rule map_of_filter[symmetric])
    also have "... = map_of (filter (\<lambda>x. fst x = y) (filter (\<lambda>a. fst a \<noteq> fst x) (remdups_wrt fst (rev xs)))) y"
      by (simp only: *)
    also have "... = map_of [a\<leftarrow>remdups_wrt fst (rev xs) . fst a \<noteq> fst x] y" by (rule map_of_filter)
    finally show "map_of [a\<leftarrow>remdups_wrt fst (rev xs) . fst a \<noteq> fst x] y = map_of xs y" by (simp only:)
  qed
qed

subsection \<open>@{term map_dup}\<close>

primrec map_dup :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_dup _ _ [] = []"|
  "map_dup f g (x # xs) = (if x \<in> set xs then g x else f x) # (map_dup f g xs)"

lemma length_map_dup[simp]: "length (map_dup f g xs) = length xs"
  by (induct xs, simp_all)

lemma map_dup_distinct:
  assumes "distinct xs"
  shows "map_dup f g xs = map f xs"
  using assms by (induct xs, simp_all)

lemma filter_map_dup_const:
  "filter (\<lambda>x. x \<noteq> c) (map_dup f (\<lambda>_. c) xs) = filter (\<lambda>x. x \<noteq> c) (map f (remdups xs))"
  by (induct xs, simp_all)

lemma filter_zip_map_dup_const:
  "filter (\<lambda>(a, b). a \<noteq> c) (zip (map_dup f (\<lambda>_. c) xs) xs) =
    filter (\<lambda>(a, b). a \<noteq> c) (zip (map f (remdups xs)) (remdups xs))"
  by (induct xs, simp_all)

end (* theory *)
