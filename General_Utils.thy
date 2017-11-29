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

definition remove::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "remove a A \<equiv> A - {a}"
definition replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "replace a b A \<equiv> insert b (remove a A)"
    
lemma in_remove:
  fixes A a x
  shows "x \<in> (remove a A) \<longleftrightarrow> (x \<in> A \<and> x \<noteq> a)"
  unfolding remove_def by simp
    
lemma in_removeI[intro]:
  fixes A a x
  assumes "x \<in> A" and "x \<noteq> a"
  shows "x \<in> (remove a A)"
  using assms unfolding in_remove by simp
    
lemma in_removeE[elim]:
  fixes P A a x
  assumes "x \<in> A \<Longrightarrow> x \<noteq> a \<Longrightarrow> P" and "x \<in> (remove a A)"
  shows P
  using assms unfolding in_remove by simp
    
lemma in_removeD1:
  fixes A a x
  assumes "x \<in> (remove a A)"
  shows "x \<in> A"
  using assms unfolding in_remove by simp
  
lemma in_removeD2:
  fixes A a x
  assumes "x \<in> (remove a A)"
  shows "x \<noteq> a"
  using assms unfolding in_remove by simp
    
lemma remove_subset:
  fixes A a
  shows "remove a A \<subseteq> A"
  by (auto simp add: in_remove)
    
lemma in_replace:
  fixes A a b x
  shows "x \<in> (replace a b A) \<longleftrightarrow> (x = b \<or> (x \<in> A \<and> x \<noteq> a))"
  unfolding replace_def remove_def by simp
    
lemma in_replaceI:
  fixes A a b x
  assumes "x = b \<or> (x \<in> A \<and> x \<noteq> a)"
  shows "x \<in> (replace a b A)"
  using assms unfolding in_replace by simp
       
lemma in_replaceI1:
  fixes A a b
  shows "b \<in> (replace a b A)"
  unfolding in_replace by simp
    
lemma in_replaceI2:
  fixes A a b x
  assumes "x \<in> A" and "x \<noteq> a"
  shows "x \<in> (replace a b A)"
  using assms unfolding in_replace by simp
    
lemma in_replaceE[elim]:
  fixes P A a b x
  assumes "(x = b \<or> (x \<in> A \<and> x \<noteq> a)) \<Longrightarrow> P" and "x \<in> (replace a b A)"
  shows P
  using assms unfolding in_replace by simp
    
lemma in_replaceD:
  fixes A a b x
  assumes "x \<in> (replace a b A)"
  shows "x = b \<or> (x \<in> A \<and> x \<noteq> a)"
  using assms unfolding in_replace by simp
    
lemma replace_same:
  assumes "a \<in> A"
  shows "replace a a A = A"
  using assms by (auto simp add: in_replace)
    
lemma replace_remove:
  fixes A a b
  assumes "b \<notin> A"
  shows "remove b (replace a b A) = remove a A"
  using assms unfolding remove_def replace_def by simp
    
lemma replace_replace:
  fixes A a b c
  assumes "b \<notin> A"
  shows "replace b c (replace a b A) = replace a c A"
  using assms unfolding remove_def replace_def by simp
    
section \<open>Lists\<close>
  
lemma replace_Cons:
  assumes "x \<notin> set xs"
  shows "set (y # xs) = replace x y (set (x # xs))"
proof (rule set_eqI)
  fix a
  show "(a \<in> set (y # xs)) = (a \<in> replace x y (set (x # xs)))"
  proof
    assume "a \<in> set (y # xs)"
    hence "a = y \<or> a \<in> set xs" by simp
    thus "a \<in> replace x y (set (x # xs))"
    proof
      assume "a = y"
      show ?thesis by (rule in_replaceI, rule disjI1, fact)
    next
      assume "a \<in> set xs"
      show ?thesis
      proof (rule in_replaceI, intro disjI2 conjI)
        from \<open>a \<in> set xs\<close> show "a \<in> set (x # xs)" by simp
      next
        from \<open>a \<in> set xs\<close> assms show "a \<noteq> x" by auto
      qed
    qed
  next
    assume "a \<in> replace x y (set (x # xs))"
    hence "a = y \<or> (a \<in> set (x # xs) \<and> a \<noteq> x)" by (rule in_replaceD)
    thus "a \<in> set (y # xs)"
    proof
      assume "a = y"
      show ?thesis unfolding \<open>a = y\<close> by simp
    next
      assume "a \<in> set (x # xs) \<and> a \<noteq> x"
      hence "a \<in> set xs" by auto
      thus ?thesis by simp
    qed
  qed
qed

lemma distinct_reorder: "distinct (xs @ (y # ys)) = distinct (y # (xs @ ys))" by auto
    
lemma set_reorder: "set (xs @ (y # ys)) = set (y # (xs @ ys))" by simp

primrec remdups_by :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
remdups_by_base: "remdups_by _ [] = []" |
remdups_by_rec: "remdups_by f (x # xs) = (if f x \<in> f ` set xs then remdups_by f xs else x # remdups_by f xs)"
    
lemma set_remdups_by: "f ` set (remdups_by f xs) = f ` set xs"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_by_base ..
next
  case (Cons a xs)
  show ?case unfolding remdups_by_rec
  proof (simp only: split: if_splits, intro conjI, intro impI)
    assume "f a \<in> f ` set xs"
      have "f ` set (a # xs) = insert (f a) (f ` set xs)" by simp
    have "f ` set (remdups_by f xs) = f ` set xs" by fact
    also from \<open>f a \<in> f ` set xs\<close> have "... = insert (f a) (f ` set xs)" by (simp add: insert_absorb)
    also have "... = f ` set (a # xs)" by simp
    finally show "f ` set (remdups_by f xs) = f ` set (a # xs)" .
  qed (simp add: Cons.hyps)
qed

lemma subset_remdups_by: "set (remdups_by f xs) \<subseteq> set xs"
  by (induct xs, auto)

lemma remdups_by_distinct_by:
  assumes "x \<in> set (remdups_by f xs)" and "y \<in> set (remdups_by f xs)" and "x \<noteq> y"
  shows "f x \<noteq> f y"
  using assms(1) assms(2)
proof (induct xs)
  case Nil
  thus ?case unfolding remdups_by_base by simp
next
  case (Cons a xs)
  from Cons(2) Cons(3) show ?case unfolding remdups_by_rec
  proof (simp only: split: if_splits)
    assume "x \<in> set (remdups_by f xs)" and "y \<in> set (remdups_by f xs)"
    thus "f x \<noteq> f y" by (rule Cons.hyps)
  next
    assume "\<not> True"
    thus "f x \<noteq> f y" by simp
  next
    assume "f a \<notin> f ` set xs" and xin: "x \<in> set (a # remdups_by f xs)" and yin: "y \<in> set (a # remdups_by f xs)"
    from yin have y: "y = a \<or> y \<in> set (remdups_by f xs)" by simp
    from xin have "x = a \<or> x \<in> set (remdups_by f xs)" by simp
    thus "f x \<noteq> f y"
    proof
      assume "x = a"
      from y show ?thesis
      proof
        assume "y = a"
        with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>x = a\<close> by simp
      next
        assume "y \<in> set (remdups_by f xs)"
        have "y \<in> set xs" by (rule, fact, rule subset_remdups_by)
        hence "f y \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>x = a\<close> by auto
      qed
    next
      assume "x \<in> set (remdups_by f xs)"
      from y show ?thesis
      proof
        assume "y = a"
        have "x \<in> set xs" by (rule, fact, rule subset_remdups_by)
        hence "f x \<in> f ` set xs" by simp
        with \<open>f a \<notin> f ` set xs\<close> show ?thesis unfolding \<open>y = a\<close> by auto
      next
        assume "y \<in> set (remdups_by f xs)"
        with \<open>x \<in> set (remdups_by f xs)\<close> show ?thesis by (rule Cons.hyps)
      qed
    qed
  qed
qed
  
lemma distinct_remdups_by: "distinct (remdups_by f xs)"
proof (induct xs)
  case Nil
  show ?case unfolding remdups_by_base by simp
next
  case (Cons a xs)
  show ?case unfolding remdups_by_rec
  proof (split if_split, intro conjI impI, rule Cons.hyps)
    assume "f a \<notin> f ` set xs"
    hence "a \<notin> set xs" by auto
    hence "a \<notin> set (remdups_by f xs)" using subset_remdups_by[of f xs] by auto
    with Cons.hyps show "distinct (a # remdups_by f xs)" by simp
  qed
qed

lemma (in linorder) sorted_sorted_list_of_set: "sorted (sorted_list_of_set A)"
  using sorted_list_of_set by (cases "finite A") auto

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

lemma map_upt: "map (\<lambda>i. f (xs ! i)) [0..<length xs] = map f xs"
  by (smt atLeast_upt length_map lessThan_iff map_cong map_nth nth_map)

lemma map_upt_zip:
  assumes "length xs = length ys"
  shows "map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length ys] = map (\<lambda>(x, y). f x y) (zip xs ys)" (is "?l = ?r")
proof -
  have len_l: "length ?l = length ys" by simp
  from assms have len_r: "length ?r = length ys" by simp
  show ?thesis
  proof (simp only: list_eq_iff_nth_eq len_l len_r, rule, rule, intro allI impI)
    fix i
    assume "i < length ys"
    hence "i < length ?l" and "i < length ?r" by (simp_all only: len_l len_r)
    thus "map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length ys] ! i = map (\<lambda>(x, y). f x y) (zip xs ys) ! i"
      by simp
  qed
qed

section \<open>Sums\<close>

lemma additive_implies_homogenous:
  assumes "\<And>x y. f (x + y) = f x + ((f (y::'a::monoid_add))::'b::cancel_comm_monoid_add)"
  shows "f 0 = 0"
proof -
  have "f (0 + 0) = f 0 + f 0" by (rule assms)
  hence "f 0 = f 0 + f 0" by simp
  thus "f 0 = 0" by simp
qed

lemma fun_sum_commute:
  assumes "f 0 = 0" and "\<And>x y. f (x + y) = f x + f y"
  shows "f (sum g A) = sum (f \<circ> g) A"
proof (cases "finite A")
case True
  thus ?thesis
  proof (induct A)
    case empty
    thus ?case by (simp add: assms(1))
  next
    case step: (insert a A)
    show ?case by (simp add: sum.insert[OF step(1) step(2)] assms(2) step(3))
  qed
next
  case False
  thus ?thesis by (simp add: assms(1))
qed

lemma fun_sum_commute_canc:
  assumes "\<And>x y. f (x + y) = f x + ((f y)::'a::cancel_comm_monoid_add)"
  shows "f (sum g A) = sum (f \<circ> g) A"
  by (rule fun_sum_commute, rule additive_implies_homogenous, fact+)

lemma fun_sum_list_commute:
  assumes "f 0 = 0" and "\<And>x y. f (x + y) = f x + f y"
  shows "f (sum_list xs) = sum_list (map f xs)"
proof (induct xs)
  case Nil
  thus ?case by (simp add: assms(1))
next
  case (Cons x xs)
  thus ?case by (simp add: assms(2))
qed

lemma fun_sum_list_commute_canc:
  assumes "\<And>x y. f (x + y) = f x + ((f y)::'a::cancel_comm_monoid_add)"
  shows "f (sum_list xs) = sum_list (map f xs)"
  by (rule fun_sum_list_commute, rule additive_implies_homogenous, fact+)

lemma sum_set_upt_eq_sum_list: "(\<Sum>i = m..<n. f i) = (\<Sum>i\<leftarrow>[m..<n]. f i)"
  using sum_set_upt_conv_sum_list_nat by auto

lemma sum_list_upt: "(\<Sum>i\<leftarrow>[0..<(length xs)]. f (xs ! i)) = (\<Sum>x\<leftarrow>xs. f x)"
  by (simp only: map_upt)

lemma sum_list_upt_zip:
  assumes "length xs = length ys"
  shows "(\<Sum>i\<leftarrow>[0..<(length ys)]. f (xs ! i) (ys ! i)) = (\<Sum>(x, y)\<leftarrow>(zip xs ys). f x y)"
  by (simp only: map_upt_zip[OF assms])

lemma sum_list_zeroI:
  assumes "set xs \<subseteq> {0}"
  shows "sum_list xs = 0"
  using assms by (induct xs, auto)

end (* theory *)
