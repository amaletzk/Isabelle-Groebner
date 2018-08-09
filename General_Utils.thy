text \<open>Some further general properties of, and functions on, sets and lists.\<close>

theory General_Utils
  imports Polynomials.Utils Groebner_Bases.General
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

lemma length_le_1:
  assumes "length xs \<le> 1" and "x \<in> set xs" and "y \<in> set xs"
  shows "x = y"
proof (cases xs)
  case Nil
  with assms(2) show ?thesis by simp
next
  case (Cons z zs)
  with assms(1) have "zs = []" by simp
  with Cons assms(2, 3) show ?thesis by simp
qed

subsection \<open>Sequences of Lists\<close>

lemma list_seq_length_mono:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i < j"
  shows "length (seq i) < length (seq j)"
proof -
  from assms(2) obtain k where "j = Suc (i + k)" using less_iff_Suc_add by auto
  show ?thesis unfolding \<open>j = Suc (i + k)\<close>
  proof (induct k)
    case 0
    from assms(1) obtain x where eq: "seq (Suc i) = x # seq i" ..
    show ?case by (simp add: eq)
  next
    case (Suc k)
    from assms(1) obtain x where "seq (Suc (i + Suc k)) = x # seq (i + Suc k)" ..
    hence eq: "seq (Suc (Suc (i + k))) = x # seq (Suc (i + k))" by simp
    note Suc
    also have "length (seq (Suc (i + k))) < length (seq (Suc (i + Suc k)))" by (simp add: eq)
    finally show ?case .
  qed
qed

corollary list_seq_length_mono_weak:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i \<le> j"
  shows "length (seq i) \<le> length (seq j)"
proof (cases "i = j")
  case True
  thus ?thesis by simp
next
  case False
  with assms(2) have "i < j" by simp
  with assms(1) have "length (seq i) < length (seq j)" by (rule list_seq_length_mono)
  thus ?thesis by simp
qed

lemma list_seq_indexE_length:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)"
  obtains j where "i < length (seq j)"
proof (induct i arbitrary: thesis)
  case 0
  have "0 \<le> length (seq 0)" by simp
  also from assms lessI have "... < length (seq (Suc 0))" by (rule list_seq_length_mono)
  finally show ?case by (rule 0)
next
  case (Suc i)
  obtain j where "i < length (seq j)" by (rule Suc(1))
  hence "Suc i \<le> length (seq j)" by simp
  also from assms lessI have "... < length (seq (Suc j))" by (rule list_seq_length_mono)
  finally show ?case by (rule Suc(2))
qed

lemma list_seq_nth:
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i < length (seq j)" and "j \<le> k"
  shows "rev (seq k) ! i = rev (seq j) ! i"
proof -
  from assms(3) obtain l where "k = j + l" using nat_le_iff_add by blast
  show ?thesis unfolding \<open>k = j + l\<close>
  proof (induct l)
    case 0
    show ?case by simp
  next
    case (Suc l)
    note assms(2)
    also from assms(1) le_add1 have "length (seq j) \<le> length (seq (j + l))"
      by (rule list_seq_length_mono_weak)
    finally have i: "i < length (seq (j + l))" .
    from assms(1) obtain x where "seq (Suc (j + l)) = x # seq (j + l)" ..
    thus ?case by (simp add: nth_append i Suc)
  qed
qed

corollary list_seq_nth':
  fixes seq :: "nat \<Rightarrow> 'a list"
  assumes "\<And>i. (\<exists>x. seq (Suc i) = x # seq i)" and "i < length (seq j)" and "i < length (seq k)"
  shows "rev (seq k) ! i = rev (seq j) ! i"
proof (rule linorder_cases)
  assume "j < k"
  hence "j \<le> k" by simp
  with assms(1, 2) show ?thesis by (rule list_seq_nth)
next
  assume "k < j"
  hence "k \<le> j" by simp
  with assms(1, 3) have "rev (seq j) ! i = rev (seq k) ! i" by (rule list_seq_nth)
  thus ?thesis by (rule HOL.sym)
next
  assume "j = k"
  thus ?thesis by simp
qed

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

subsection \<open>@{const filter}\<close>

lemma filter_merge_wrt_1:
  assumes "\<And>y. y \<in> set ys \<Longrightarrow> P y \<Longrightarrow> False"
  shows "filter P (merge_wrt rel xs ys) = filter P xs"
  using assms
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  show ?case by simp
next
  case (2 rel y ys)
  hence "P y \<Longrightarrow> False" and "\<And>z. z \<in> set ys \<Longrightarrow> P z \<Longrightarrow> False" by auto
  thus ?case by (auto simp: filter_empty_conv)
next
  case (3 rel x xs y ys)
  hence "\<not> P y" and x: "\<And>z. z \<in> set ys \<Longrightarrow> P z \<Longrightarrow> False" by auto
  have a: "filter P (merge_wrt rel xs ys) = filter P xs" if "x = y" using that x by (rule 3(1))
  have b: "filter P (merge_wrt rel xs (y # ys)) = filter P xs" if "x \<noteq> y" and "rel x y"
    using that 3(4) by (rule 3(2))
  have c: "filter P (merge_wrt rel (x # xs) ys) = filter P (x # xs)" if "x \<noteq> y" and "\<not> rel x y"
    using that x by (rule 3(3))
  show ?case by (simp add: a b c \<open>\<not> P y\<close>)
qed

lemma filter_merge_wrt_2:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> False"
  shows "filter P (merge_wrt rel xs ys) = filter P ys"
  using assms
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  thus ?case by (auto simp: filter_empty_conv)
next
  case (2 rel y ys)
  show ?case by simp
next
  case (3 rel x xs y ys)
  hence "\<not> P x" and x: "\<And>z. z \<in> set xs \<Longrightarrow> P z \<Longrightarrow> False" by auto
  have a: "filter P (merge_wrt rel xs ys) = filter P ys" if "x = y" using that x by (rule 3(1))
  have b: "filter P (merge_wrt rel xs (y # ys)) = filter P (y # ys)" if "x \<noteq> y" and "rel x y"
    using that x by (rule 3(2))
  have c: "filter P (merge_wrt rel (x # xs) ys) = filter P ys" if "x \<noteq> y" and "\<not> rel x y"
    using that 3(4) by (rule 3(3))
  show ?case by (simp add: a b c \<open>\<not> P x\<close>)
qed

lemma length_filter_le_1:
  assumes "length (filter P xs) \<le> 1" and "i < length xs" and "j < length xs"
    and "P (xs ! i)" and "P (xs ! j)"
  shows "i = j"
proof -
  have *: thesis if "a < b" and "b < length xs"
    and "\<And>as bs cs. as @ ((xs ! a) # (bs @ ((xs ! b) # cs))) = xs \<Longrightarrow> thesis" for a b thesis
  proof (rule that(3))
    from that(1, 2) have 1: "a < length xs" by simp
    with that(1, 2) have 2: "b - Suc a < length (drop (Suc a) xs)" by simp
    from that(1) \<open>a < length xs\<close> have eq: "xs ! b = drop (Suc a) xs ! (b - Suc a)" by simp
    show "(take a xs) @ ((xs ! a) # ((take (b - Suc a) (drop (Suc a) xs)) @ ((xs ! b) #
                  drop (Suc (b - Suc a)) (drop (Suc a) xs)))) = xs"
      by (simp only: eq id_take_nth_drop[OF 1, symmetric] id_take_nth_drop[OF 2, symmetric])
  qed
  show ?thesis
  proof (rule linorder_cases)
    assume "i < j"
    then obtain as bs cs where "as @ ((xs ! i) # (bs @ ((xs ! j) # cs))) = xs"
      using assms(3) by (rule *)
    hence "filter P xs = filter P (as @ ((xs ! i) # (bs @ ((xs ! j) # cs))))" by simp
    also from assms(4, 5) have "... = (filter P as) @ ((xs ! i) # ((filter P bs) @ ((xs ! j) # (filter P cs))))"
      by simp
    finally have "\<not> length (filter P xs) \<le> 1" by simp
    thus ?thesis using assms(1) ..
  next
    assume "j < i"
    then obtain as bs cs where "as @ ((xs ! j) # (bs @ ((xs ! i) # cs))) = xs"
      using assms(2) by (rule *)
    hence "filter P xs = filter P (as @ ((xs ! j) # (bs @ ((xs ! i) # cs))))" by simp
    also from assms(4, 5) have "... = (filter P as) @ ((xs ! j) # ((filter P bs) @ ((xs ! i) # (filter P cs))))"
      by simp
    finally have "\<not> length (filter P xs) \<le> 1" by simp
    thus ?thesis using assms(1) ..
  qed
qed

lemma length_filter_eq [simp]: "length (filter ((=) x) xs) = count_list xs x"
  by (induct xs, simp_all)

subsection \<open>@{const count_list}\<close>

lemma count_list_append [simp]: "count_list (xs @ ys) a = count_list xs a + count_list ys a"
  by (induct xs, simp_all)

lemma count_list_upt [simp]: "count_list [a..<b] x = (if a \<le> x \<and> x < b then 1 else 0)"
proof (cases "a \<le> b")
  case True
  then obtain k where "b = a + k" using le_Suc_ex by blast
  show ?thesis unfolding \<open>b = a + k\<close> by (induct k, simp_all)
next
  case False
  thus ?thesis by simp
qed

subsection \<open>@{const sorted_wrt}\<close>

lemma sorted_wrt_upt_iff: "sorted_wrt rel [a..<b] \<longleftrightarrow> (\<forall>i j. a \<le> i \<longrightarrow> i < j \<longrightarrow> j < b \<longrightarrow> rel i j)"
proof (cases "a \<le> b")
  case True
  then obtain k where "b = a + k" using le_Suc_ex by blast
  show ?thesis unfolding \<open>b = a + k\<close>
  proof (induct k)
    case 0
    show ?case by simp
  next
    case (Suc k)
    show ?case
    proof (simp add: sorted_wrt_append Suc, intro iffI allI ballI impI conjI)
      fix i j
      assume "(\<forall>i\<ge>a. \<forall>j>i. j < a + k \<longrightarrow> rel i j) \<and> (\<forall>x\<in>{a..<a + k}. rel x (a + k))"
      hence 1: "\<And>i' j'. a \<le> i' \<Longrightarrow> i' < j' \<Longrightarrow> j' < a + k \<Longrightarrow> rel i' j'"
        and 2: "\<And>x. a \<le> x \<Longrightarrow> x < a + k \<Longrightarrow> rel x (a + k)" by simp_all
      assume "a \<le> i" and "i < j"
      assume "j < Suc (a + k)"
      hence "j < a + k \<or> j = a + k" by auto
      thus "rel i j"
      proof
        assume "j < a + k"
        with \<open>a \<le> i\<close> \<open>i < j\<close> show ?thesis by (rule 1)
      next
        assume "j = a + k"
        from \<open>a \<le> i\<close> \<open>i < j\<close> show ?thesis unfolding \<open>j = a + k\<close> by (rule 2)
      qed
    next
      fix i j
      assume "\<forall>i\<ge>a. \<forall>j>i. j < Suc (a + k) \<longrightarrow> rel i j" and "a \<le> i" and "i < j" and "j < a + k"
      thus "rel i j" by simp
    next
      fix x
      assume "x \<in> {a..<a + k}"
      hence "a \<le> x" and "x < a + k" by simp_all
      moreover assume "\<forall>i\<ge>a. \<forall>j>i. j < Suc (a + k) \<longrightarrow> rel i j"
      ultimately show "rel x (a + k)" by simp
    qed
  qed
next
  case False
  thus ?thesis by simp
qed

subsection \<open>@{const insort_wrt} and @{const merge_wrt}\<close>

lemma map_insort_wrt:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> r2 (f y) (f x) \<longleftrightarrow> r1 y x"
  shows "map f (insort_wrt r1 y xs) = insort_wrt r2 (f y) (map f xs)"
  using assms
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "x \<in> set (x # xs)" by simp
  hence "r2 (f y) (f x) = r1 y x" by (rule Cons(2))
  moreover have "map f (insort_wrt r1 y xs) = insort_wrt r2 (f y) (map f xs)"
  proof (rule Cons(1))
    fix x'
    assume "x' \<in> set xs"
    hence "x' \<in> set (x # xs)" by simp
    thus "r2 (f y) (f x') = r1 y x'" by (rule Cons(2))
  qed
  ultimately show ?case by simp
qed

lemma insort_wrt_cong:
  assumes "f y = f y'" and "map f xs = map f xs'" and "\<And>x x'. f x = f x' \<Longrightarrow> r y x \<longleftrightarrow> r y' x'"
  shows "map f (insort_wrt r y xs) = map f (insort_wrt r y' xs')"
  using assms(2)
proof (induct xs arbitrary: xs')
  case Nil
  from Nil have "xs' = []" by simp
  with assms(1) show ?case by simp
next
  case (Cons x xs)
  from Cons(2) obtain x' xs0 where xs': "xs' = x' # xs0" and eq1: "f x = f x'" and eq2: "map f xs = map f xs0"
    by auto
  from this(3) have eq3: "map f (insort_wrt r y xs) = map f (insort_wrt r y' xs0)" by (rule Cons(1))
  from \<open>f x = f x'\<close> have eq4: "r y x \<longleftrightarrow> r y' x'" by (rule assms(3))
  show ?case by (simp add: xs' eq1 eq2 eq3 eq4 assms(1))
qed

lemma map_merge_wrt:
  assumes "f ` set xs \<inter> f ` set ys = {}"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> r2 (f x) (f y) \<longleftrightarrow> r1 x y"
  shows "map f (merge_wrt r1 xs ys) = merge_wrt r2 (map f xs) (map f ys)"
  using assms
proof (induct r1 xs ys rule: merge_wrt.induct)
  case (1 uu xs)
  show ?case by simp
next
  case (2 r1 v va)
  show ?case by simp
next
  case (3 r1 x xs y ys)
  from 3(4) have "f x \<noteq> f y" and 1: "f ` set xs \<inter> f ` set (y # ys) = {}"
    and 2: "f ` set (x # xs) \<inter> f ` set ys = {}" by auto
  from this(1) have "x \<noteq> y" by auto
  have eq2: "map f (merge_wrt r1 xs (y # ys)) = merge_wrt r2 (map f xs) (map f (y # ys))"
    if "r1 x y" using \<open>x \<noteq> y\<close> that 1
  proof (rule 3(2))
    fix a b
    assume "a \<in> set xs"
    hence "a \<in> set (x # xs)" by simp
    moreover assume "b \<in> set (y # ys)"
    ultimately show "r2 (f a) (f b) \<longleftrightarrow> r1 a b" by (rule 3(5))
  qed
  have eq3: "map f (merge_wrt r1 (x # xs) ys) = merge_wrt r2 (map f (x # xs)) (map f ys)"
    if "\<not> r1 x y" using \<open>x \<noteq> y\<close> that 2
  proof (rule 3(3))
    fix a b
    assume "a \<in> set (x # xs)"
    assume "b \<in> set ys"
    hence "b \<in> set (y # ys)" by simp
    with \<open>a \<in> set (x # xs)\<close> show "r2 (f a) (f b) \<longleftrightarrow> r1 a b" by (rule 3(5))
  qed
  have eq4: "r2 (f x) (f y) \<longleftrightarrow> r1 x y" by (rule 3(5), simp_all)
  show ?case by (simp add: eq2 eq3 eq4 \<open>f x \<noteq> f y\<close> \<open>x \<noteq> y\<close>)
qed

lemma merge_wrt_cong:
  assumes "map f xs = map f xs'" and "map f ys = map f ys'" and "set xs \<inter> set ys = {}"
    and "set xs' \<inter> set ys' = {}"
    and "\<And>x x' y y'. f x = f x' \<Longrightarrow> f y = f y' \<Longrightarrow> r x y \<longleftrightarrow> r x' y'"
  shows "map f (merge_wrt r xs ys) = map f (merge_wrt r xs' ys')"
  using assms
proof (induct r xs ys arbitrary: xs' ys' rule: merge_wrt.induct)
  case (1 uu xs)
  from 1(2) have "ys' = []" by simp
  with 1(1) show ?case by simp
next
  case (2 rel y ys)
  from 2(1) have "xs' = []" by simp
  from 2(2) obtain y' ys0 where "ys' = y' # ys0" and "f y = f y'" and "map f ys = map f ys0"
    by auto
  with \<open>xs' = []\<close> show ?case by simp
next
  case (3 rel x xs y ys)
  from 3(6) have "x \<noteq> y" and 1: "set xs \<inter> set (y # ys) = {}"
    and 2: "set (x # xs) \<inter> set ys = {}" and 4: "set xs \<inter> set ys = {}" by auto
  from 3(4) obtain x' xs0 where xs': "xs' = x' # xs0" and eq1: "f x = f x'" and eq2: "map f xs = map f xs0"
    by auto
  from 3(5) obtain y' ys0 where ys': "ys' = y' # ys0" and eq3: "f y = f y'" and eq4: "map f ys = map f ys0"
    by auto
  from 3(7) have "x' \<noteq> y'" and 5: "set xs0 \<inter> set ys' = {}" and 6: "set xs' \<inter> set ys0 = {}"
    by (auto simp: xs' ys')
  from eq1 eq3 have eq5: "rel x y \<longleftrightarrow> rel x' y'" by (rule 3(8))
  have eq7: "map f (merge_wrt rel xs (y # ys)) = map f (merge_wrt rel xs0 ys')"
    if "rel x y" using \<open>x \<noteq> y\<close> that eq2 3(5) 1 5 3(8) by (rule 3(2))
  have eq8: "map f (merge_wrt rel (x # xs) ys) = map f (merge_wrt rel xs' ys0)"
    if "\<not> rel x y" using \<open>x \<noteq> y\<close> that 3(4) eq4 2 6 3(8) by (rule 3(3))
  show ?case by (simp add: xs' ys' eq5 eq1 eq2 eq3 eq4 eq7 eq8 \<open>x \<noteq> y\<close> \<open>x' \<noteq> y'\<close>)
qed

subsection \<open>@{const drop}\<close>

lemma nth_in_set_dropI:
  assumes "j \<le> i" and "i < length xs"
  shows "xs ! i \<in> set (drop j xs)"
  using assms
proof (induct xs arbitrary: i j)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases j)
    case 0
    with Cons(3) show ?thesis by (metis drop0 nth_mem)
  next
    case (Suc j0)
    with Cons(2) Suc_le_D obtain i0 where i: "i = Suc i0" by blast
    with Cons(2) have "j0 \<le> i0" by (simp add: \<open>j = Suc j0\<close>)
    moreover from Cons(3) have "i0 < length xs" by (simp add: i)
    ultimately have "xs ! i0 \<in> set (drop j0 xs)" by (rule Cons(1))
    thus ?thesis by (simp add: i \<open>j = Suc j0\<close>)
  qed
qed

subsection \<open>@{const map}\<close>

lemma map_cong_strong:
  assumes "map f xs = map f' ys" and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x = f' y \<Longrightarrow> g x = g' y"
  shows "map g xs = map g' ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons(2) obtain y ys' where ys: "ys = y # ys'" and 1: "f x = f' y" and 2: "map f xs = map f' ys'"
    by auto
  have "g x = g' y" by (rule Cons(3), simp_all add: ys 1)
  moreover from 2 have "map g xs = map g' ys'"
  proof (rule Cons(1))
    fix a b
    assume "a \<in> set xs" and "b \<in> set ys'"
    hence "a \<in> set (x # xs)" and "b \<in> set ys" by (simp_all add: ys)
    moreover assume "f a = f' b"
    ultimately show "g a = g' b" by (rule Cons(3))
  qed
  ultimately show ?case by (simp add: ys)
qed

subsection \<open>@{const sorted_wrt}\<close>

lemma sorted_wrt_cong_strong:
  assumes "sorted_wrt P xs" and "map f xs = map f' ys"
    and "\<And>x1 x2 y1 y2. x1 \<in> set xs \<Longrightarrow> x2 \<in> set xs \<Longrightarrow> y1 \<in> set ys \<Longrightarrow> y2 \<in> set ys \<Longrightarrow>
            f x1 = f' y1 \<Longrightarrow> f x2 = f' y2 \<Longrightarrow> P x1 x2 = Q y1 y2"
  shows "sorted_wrt Q ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons(2) have "sorted_wrt P xs" and 0: "Ball (set xs) (P x)" by simp_all
  from Cons(3) obtain y ys' where ys: "ys = y # ys'" and 1: "f x = f' y" and 2: "map f xs = map f' ys'"
    by auto
  from \<open>sorted_wrt P xs\<close> 2 have "sorted_wrt Q ys'"
  proof (rule Cons(1))
    fix a1 a2 b1 b2
    assume "a1 \<in> set xs" and "a2 \<in> set xs" and "b1 \<in> set ys'" and "b2 \<in> set ys'"
    hence "a1 \<in> set (x # xs)" and "a2 \<in> set (x # xs)" and "b1 \<in> set ys" and "b2 \<in> set ys"
      by (simp_all add: ys)
    moreover assume "f a1 = f' b1" and "f a2 = f' b2"
    ultimately show "P a1 a2 = Q b1 b2" by (rule Cons(4))
  qed
  moreover have "Ball (set ys') (Q y)"
  proof
    fix b
    assume "b \<in> set ys'"
    hence "f' b \<in> f' ` set ys'" by (rule imageI)
    also have "... = set (map f' ys')" by simp
    also have "... = set (map f xs)" by (simp only: 2)
    also have "... = f ` set xs" by simp
    finally obtain a where "a \<in> set xs" and "f' b = f a" ..
    from 0 this(1) have "P x a" ..
    also have "P x a = Q y b" by (rule Cons(4), simp_all add: \<open>a \<in> set xs\<close> \<open>b \<in> set ys'\<close> ys 1 \<open>f' b = f a\<close>)
    finally show "Q y b" .
  qed
  ultimately show ?case by (simp add: ys)
qed

end (* theory *)
