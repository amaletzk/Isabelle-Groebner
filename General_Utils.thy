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

end (* theory *)
