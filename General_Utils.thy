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

end (* theory *)
