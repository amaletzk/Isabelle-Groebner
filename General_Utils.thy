section \<open>Utilities\<close>

theory General_Utils
  imports Polynomials.Utils Groebner_Bases.General
begin

text \<open>Some further general properties of, and functions on, sets and lists.\<close>
  
subsection \<open>Sets\<close>

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

lemma card_2_I: "x \<noteq> y \<Longrightarrow> card {x, y} = 2"
  by simp

lemma card_2_E_1:
  assumes "card A = 2" and "x \<in> A"
  obtains y where "x \<noteq> y" and "A = {x, y}"
proof -
  have "A - {x} \<noteq> {}"
  proof
    assume "A - {x} = {}"
    with assms(2) have "A = {x}" by auto
    hence "card A = 1" by simp
    with assms show False by simp
  qed
  then obtain y where "y \<in> A - {x}" by auto
  hence "y \<in> A" and "x \<noteq> y" by auto
  show ?thesis
  proof
    show "A = {x, y}"
    proof (rule sym, rule card_seteq)
      from assms(1) show "finite A" using card_infinite by fastforce
    next
      from \<open>x \<in> A\<close> \<open>y \<in> A\<close> show "{x, y} \<subseteq> A" by simp
    next
      from \<open>x \<noteq> y\<close> show "card A \<le> card {x, y}" by (simp add: assms(1))
    qed
  qed fact
qed

lemma card_2_E:
  assumes "card A = 2"
  obtains x y where "x \<noteq> y" and "A = {x, y}"
proof -
  from assms have "A \<noteq> {}" by auto
  then obtain x where "x \<in> A" by blast
  with assms obtain y where "x \<noteq> y" and "A = {x, y}" by (rule card_2_E_1)
  thus ?thesis ..
qed

lemma image_Collect_eqI:
  assumes "\<And>x. P x \<longleftrightarrow> Q x" and "\<And>x. Q x \<Longrightarrow> f x = g x"
  shows "{f x | x. P x} = {g x | x. Q x}"
  using assms by metis

lemma image_image_Collect:
  "f ` {g x | x. P x} = {f (g x) | x. P x}"
  by auto

lemma card_le_1I:
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a = b"
  shows "card A \<le> 1"
proof (cases "A = {}")
  case True
  thus ?thesis by simp
next
  case False
  then obtain a where "a \<in> A" by blast
  have "finite {a}" by simp
  moreover have "A \<subseteq> {a}"
  proof
    fix b
    assume "b \<in> A"
    hence "b = a" using \<open>a \<in> A\<close> by (rule assms)
    thus "b \<in> {a}" by simp
  qed
  ultimately have "card A \<le> card {a}" by (rule card_mono)
  thus ?thesis by simp
qed

lemma card_le_1D:
  assumes "finite A" and "card A \<le> 1" and "a \<in> A" and "b \<in> A"
  shows "a = b"
  using assms
proof (induct A)
  case empty
  thus ?case by simp
next
  case (insert a0 A)
  from insert.hyps(1, 2) insert.prems(1) have "A = {}" by simp
  with insert.prems(2, 3) show ?case by simp
qed

lemma card_le_1_iff: "finite A \<Longrightarrow> card A \<le> Suc 0 \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>A. a = b)"
  using card_le_1D card_le_1I by (metis One_nat_def)

lemma subset_imageE_inj:
  assumes "B \<subseteq> f ` A"
  obtains C where "C \<subseteq> A" and "B = f ` C" and "inj_on f C"
proof -
  define g where "g = (\<lambda>x. SOME a. a \<in> A \<and> f a = x)"
  have "g b \<in> A \<and> f (g b) = b" if "b \<in> B" for b
  proof -
    from that assms have "b \<in> f ` A" ..
    then obtain a where "a \<in> A" and "b = f a" ..
    hence "a \<in> A \<and> f a = b" by simp
    thus ?thesis unfolding g_def by (rule someI)
  qed
  hence 1: "\<And>b. b \<in> B \<Longrightarrow> g b \<in> A" and 2: "\<And>b. b \<in> B \<Longrightarrow> f (g b) = b" by simp_all
  let ?C = "g ` B"
  show ?thesis
  proof
    show "?C \<subseteq> A" by (auto intro: 1)
  next
    show "B = f ` ?C"
    proof (rule set_eqI)
      fix b
      show "b \<in> B \<longleftrightarrow> b \<in> f ` ?C"
      proof
        assume "b \<in> B"
        moreover from this have "f (g b) = b" by (rule 2)
        ultimately show "b \<in> f ` ?C" by force
      next
        assume "b \<in> f ` ?C"
        then obtain b' where "b' \<in> B" and "b = f (g b')" unfolding image_image ..
        moreover from this(1) have "f (g b') = b'" by (rule 2)
        ultimately show "b \<in> B" by simp
      qed
    qed
  next
    show "inj_on f ?C"
    proof
      fix x y
      assume "x \<in> ?C"
      then obtain bx where "bx \<in> B" and x: "x = g bx" ..
      moreover from this(1) have "f (g bx) = bx" by (rule 2)
      ultimately have *: "f x = bx" by simp
      assume "y \<in> ?C"
      then obtain "by" where "by \<in> B" and y: "y = g by" ..
      moreover from this(1) have "f (g by) = by" by (rule 2)
      ultimately have "f y = by" by simp
      moreover assume "f x = f y"
      ultimately have "bx = by" using * by simp
      thus "x = y" by (simp only: x y)
    qed
  qed
qed

subsection \<open>Sums\<close>

lemma sum_head_int: "a \<le> (b::int) \<Longrightarrow> sum f {a..b} = f a + sum f {a + 1..b}"
  by (smt atLeastAtMost_iff finite_atLeastAtMost_int simp_from_to sum.insert)

lemma sum_tail_int: "a \<le> (b::int) \<Longrightarrow> sum f {a..b} = f b + sum f {a..b - 1}"
  by (smt Icc_eq_Icc atLeastAtMostPlus1_int_conv finite_atLeastAtMost_int insert_absorb sum.insert)

lemma sum_tail_nat: "0 < b \<Longrightarrow> a \<le> (b::nat) \<Longrightarrow> sum f {a..b} = f b + sum f {a..b - 1}"
  by (metis One_nat_def Suc_pred add.commute not_le sum_cl_ivl_Suc)

corollary sum_tail_nat': "a < (b::nat) \<Longrightarrow> sum f {a..b} = f b + sum f {a..b - 1}"
  by (simp add: sum_tail_nat)

lemma sum_atLeast_Suc_shift: "0 < b \<Longrightarrow> a \<le> b \<Longrightarrow> sum f {Suc a..b} = (\<Sum>i=a..b - 1. f (Suc i))"
  by (metis Suc_diff_1 sum_shift_bounds_cl_Suc_ivl)

corollary sum_atLeast_Suc_shift': "a < b \<Longrightarrow> sum f {Suc a..b} = (\<Sum>i=a..b - 1. f (Suc i))"
  by (simp add: sum_atLeast_Suc_shift)

thm sum_head_Suc

lemma sum_split_nat_ivl:
  "a \<le> Suc j \<Longrightarrow> j \<le> b \<Longrightarrow> sum f {a..j} + sum f {Suc j..b} = sum f {a..b}"
  by (metis Suc_eq_plus1 le_Suc_ex sum_ub_add_nat)

lemma sum_nat_int_conv: "sum f {a..b} = (\<Sum>i=int a..int b. f (nat i))"
  by (metis (mono_tags, lifting) comp_def nat_int sum.atLeast_int_atMost_int_shift sum.cong)

lemma sum_int_nat_conv: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> sum f {a..b} = (\<Sum>i=nat a..nat b. f (int i))"
  by (smt imageE image_int_atLeastAtMost int_nat_eq nat_int sum.cong sum_nat_int_conv)

lemma sum_int_nat_conv': "0 < a \<Longrightarrow> sum f {a..b} = (\<Sum>i=nat a..nat b. f (int i))"
  by (smt atLeastAtMost_iff nat_0_iff sum.cong sum.not_neutral_contains_not_neutral sum_int_nat_conv)
    
subsection \<open>Lists\<close>

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

subsubsection \<open>@{const last}\<close>

lemma last_take_conv_nth: "n < length xs \<Longrightarrow> last (take (Suc n) xs) = xs ! n"
  by (simp add: take_Suc_conv_app_nth)

subsubsection \<open>@{const count_list}\<close>

lemma count_list_eq_0_iff: "count_list xs x = 0 \<longleftrightarrow> x \<notin> set xs"
  by (induct xs) simp_all

lemma count_list_append: "count_list (xs @ ys) x = count_list xs x + count_list ys x"
  by (induct xs) simp_all

lemma count_list_map_ge: "count_list xs x \<le> count_list (map f xs) (f x)"
  by (induct xs) simp_all

lemma count_list_gr_1_E:
  assumes "1 < count_list xs x"
  obtains i j where "i < j" and "j < length xs" and "xs ! i = x" and "xs ! j = x"
proof -
  from assms have "count_list xs x \<noteq> 0" by simp
  hence "x \<in> set xs" by (simp only: count_list_eq_0_iff not_not)
  then obtain ys zs where xs: "xs = ys @ x # zs" and "x \<notin> set ys" by (meson split_list_first)
  hence "count_list xs x = Suc (count_list zs x)" by (simp add: count_list_append)
  with assms have "count_list zs x \<noteq> 0" by simp
  hence "x \<in> set zs" by (simp only: count_list_eq_0_iff not_not)
  then obtain j where "j < length zs" and "x = zs ! j" by (metis in_set_conv_nth)
  show ?thesis
  proof
    show "length ys < length ys + Suc j" by simp
  next
    from \<open>j < length zs\<close> show "length ys + Suc j < length xs" by (simp add: xs)
  next
    show "xs ! length ys = x" by (simp add: xs)
  next
    show "xs ! (length ys + Suc j) = x"
      by (simp only: xs \<open>x = zs ! j\<close> nth_append_length_plus nth_Cons_Suc)
  qed
qed

subsubsection \<open>@{const map_of}\<close>

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

subsubsection \<open>@{const sorted_wrt}\<close>

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

subsubsection \<open>@{const insort_wrt} and @{const merge_wrt}\<close>

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

subsubsection \<open>@{const map}\<close>

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

subsubsection \<open>@{const listset}\<close>

lemma listset_Cons: "listset (x # xs) = (\<Union>y\<in>x. (#) y ` listset xs)"
  by (auto simp: set_Cons_def)

lemma listset_ConsI: "y \<in> x \<Longrightarrow> ys' \<in> listset xs \<Longrightarrow> ys = y # ys' \<Longrightarrow> ys \<in> listset (x # xs)"
  by (simp add: set_Cons_def)

lemma listset_ConsE:
  assumes "ys \<in> listset (x# xs)"
  obtains y ys' where "y \<in> x" and "ys' \<in> listset xs" and "ys = y # ys'"
  using assms by (auto simp: set_Cons_def)

lemma listsetI:
  "length ys = length xs \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> ys ! i \<in> xs ! i) \<Longrightarrow> ys \<in> listset xs"
  by (induct ys xs rule: list_induct2)
     (simp_all, smt Suc_mono list.sel(3) mem_Collect_eq nth_Cons_0 nth_tl set_Cons_def zero_less_Suc)

lemma listsetD:
  assumes "ys \<in> listset xs"
  shows "length ys = length xs" and "\<And>i. i < length xs \<Longrightarrow> ys ! i \<in> xs ! i"
proof -
  from assms have "length ys = length xs \<and> (\<forall>i<length xs. ys ! i \<in> xs ! i)"
  proof (induct xs arbitrary: ys)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    from Cons.prems obtain y ys' where "y \<in> x" and "ys' \<in> listset xs" and ys: "ys = y # ys'"
      by (rule listset_ConsE)
    from this(2) have "length ys' = length xs \<and> (\<forall>i<length xs. ys' ! i \<in> xs ! i)" by (rule Cons.hyps)
    hence 1: "length ys' = length xs" and 2: "\<And>i. i < length xs \<Longrightarrow> ys' ! i \<in> xs ! i" by simp_all
    show ?case
    proof (intro conjI allI impI)
      fix i
      assume "i < length (x # xs)"
      show "ys ! i \<in> (x # xs) ! i"
      proof (cases i)
        case 0
        with \<open>y \<in> x\<close> show ?thesis by (simp add: ys)
      next
        case (Suc j)
        with \<open>i < length (x # xs)\<close> have "j < length xs" by simp
        hence "ys' ! j \<in> xs ! j" by (rule 2)
        thus ?thesis by (simp add: ys \<open>i = Suc j\<close>)
      qed
    qed (simp add: ys 1)
  qed
  thus "length ys = length xs" and "\<And>i. i < length xs \<Longrightarrow> ys ! i \<in> xs ! i" by simp_all
qed

lemma listset_singletonI: "a \<in> A \<Longrightarrow> ys = [a] \<Longrightarrow> ys \<in> listset [A]"
  by simp

lemma listset_singletonE:
  assumes "ys \<in> listset [A]"
  obtains a where "a \<in> A" and "ys = [a]"
  using assms by auto

lemma listset_doubletonI: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> ys = [a, b] \<Longrightarrow> ys \<in> listset [A, B]"
  by (simp add: set_Cons_def)

lemma listset_doubletonE:
  assumes "ys \<in> listset [A, B]"
  obtains a b where "a \<in> A" and "b \<in> B" and "ys = [a, b]"
  using assms by (auto simp: set_Cons_def)

lemma listset_appendI:
  "ys1 \<in> listset xs1 \<Longrightarrow> ys2 \<in> listset xs2 \<Longrightarrow> ys = ys1 @ ys2 \<Longrightarrow> ys \<in> listset (xs1 @ xs2)"
  by (induct xs1 arbitrary: ys ys1 ys2)
      (simp, auto simp del: listset.simps elim!: listset_ConsE intro!: listset_ConsI)

lemma listset_appendE:
  assumes "ys \<in> listset (xs1 @ xs2)"
  obtains ys1 ys2 where "ys1 \<in> listset xs1" and "ys2 \<in> listset xs2" and "ys = ys1 @ ys2"
  using assms
proof (induct xs1 arbitrary: thesis ys)
  case Nil
  have "[] \<in> listset []" by simp
  moreover from Nil(2) have "ys \<in> listset xs2" by simp
  ultimately show ?case by (rule Nil) simp
next
  case (Cons x xs1)
  from Cons.prems(2) have "ys \<in> listset (x # (xs1 @ xs2))" by simp
  then obtain y ys' where "y \<in> x" and "ys' \<in> listset (xs1 @ xs2)" and ys: "ys = y # ys'"
    by (rule listset_ConsE)
  from _ this(2) obtain ys1 ys2 where ys1: "ys1 \<in> listset xs1" and "ys2 \<in> listset xs2"
    and ys': "ys' = ys1 @ ys2" by (rule Cons.hyps)
  show ?case
  proof (rule Cons.prems)
    from \<open>y \<in> x\<close> ys1 refl show "y # ys1 \<in> listset (x # xs1)" by (rule listset_ConsI)
  next
    show "ys = (y # ys1) @ ys2" by (simp add: ys ys')
  qed fact
qed

lemma listset_map_imageI: "ys' \<in> listset xs \<Longrightarrow> ys = map f ys' \<Longrightarrow> ys \<in> listset (map ((`) f) xs)"
  by (induct xs arbitrary: ys ys')
    (simp, auto simp del: listset.simps elim!: listset_ConsE intro!: listset_ConsI)

lemma listset_map_imageE:
  assumes "ys \<in> listset (map ((`) f) xs)"
  obtains ys' where "ys' \<in> listset xs" and "ys = map f ys'"
  using assms
proof (induct xs arbitrary: thesis ys)
  case Nil
  from Nil(2) have "ys = map f []" by simp
  with _ show ?case by (rule Nil) simp
next
  case (Cons x xs)
  from Cons.prems(2) have "ys \<in> listset (f ` x # map ((`) f) xs)" by simp
  then obtain y ys' where "y \<in> f ` x" and "ys' \<in> listset (map ((`) f) xs)" and ys: "ys = y # ys'"
    by (rule listset_ConsE)
  from _ this(2) obtain ys1 where ys1: "ys1 \<in> listset xs" and ys': "ys' = map f ys1" by (rule Cons.hyps)
  from \<open>y \<in> f ` x\<close> obtain y1 where "y1 \<in> x" and y: "y = f y1" ..
  show ?case
  proof (rule Cons.prems)
    from \<open>y1 \<in> x\<close> ys1 refl show "y1 # ys1 \<in> listset (x # xs)" by (rule listset_ConsI)
  qed (simp add: ys ys' y)
qed

lemma listset_permE:
  assumes "ys \<in> listset xs" and "bij_betw f {..<length xs} {..<length xs'}"
    and "\<And>i. i < length xs \<Longrightarrow> xs' ! i = xs ! f i"
  obtains ys' where "ys' \<in> listset xs'" and "length ys' = length ys"
    and "\<And>i. i < length ys \<Longrightarrow> ys' ! i = ys ! f i"
proof -
  from assms(1) have len_ys: "length ys = length xs" by (rule listsetD)
  from assms(2) have "card {..<length xs} = card {..<length xs'}" by (rule bij_betw_same_card)
  hence len_xs: "length xs = length xs'" by simp
  define ys' where "ys' = map (\<lambda>i. ys ! (f i)) [0..<length ys]"
  have 1: "ys' ! i = ys ! f i" if "i < length ys" for i using that by (simp add: ys'_def)
  show ?thesis
  proof
    show "ys' \<in> listset xs'"
    proof (rule listsetI)
      show "length ys' = length xs'" by (simp add: ys'_def len_ys len_xs)

      fix i
      assume "i < length xs'"
      hence "i < length xs" by (simp only: len_xs)
      hence "i < length ys" by (simp only: len_ys)
      hence "ys' ! i = ys ! (f i)" by (rule 1)
      also from assms(1) have "\<dots> \<in> xs ! (f i)"
      proof (rule listsetD)
        from \<open>i < length xs\<close> have "i \<in> {..<length xs}" by simp
        hence "f i \<in> f ` {..<length xs}" by (rule imageI)
        also from assms(2) have "\<dots> = {..<length xs'}" by (simp add: bij_betw_def)
        finally show "f i < length xs" by (simp add: len_xs)
      qed
      also have "\<dots> = xs' ! i" by (rule sym) (rule assms(3), fact)
      finally show "ys' ! i \<in> xs' ! i" .
    qed
  next
    show "length ys' = length ys" by (simp add: ys'_def)
  qed (rule 1)
qed

lemma listset_closed_map:
  assumes "ys \<in> listset xs" and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> x \<Longrightarrow> f y \<in> x"
  shows "map f ys \<in> listset xs"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  from Nil(1) show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain y ys' where "y \<in> x" and "ys' \<in> listset xs" and ys: "ys = y # ys'"
    by (rule listset_ConsE)
  show ?case
  proof (rule listset_ConsI)
    from _ \<open>y \<in> x\<close> show "f y \<in> x" by (rule Cons.prems) simp
  next
    show "map f ys' \<in> listset xs"
    proof (rule Cons.hyps)
      fix x0 y0
      assume "x0 \<in> set xs"
      hence "x0 \<in> set (x # xs)" by simp
      moreover assume "y0 \<in> x0"
      ultimately show "f y0 \<in> x0" by (rule Cons.prems)
    qed fact
  qed (simp add: ys)
qed

lemma listset_closed_map2:
  assumes "ys1 \<in> listset xs" and "ys2 \<in> listset xs"
    and "\<And>x y1 y2. x \<in> set xs \<Longrightarrow> y1 \<in> x \<Longrightarrow> y2 \<in> x \<Longrightarrow> f y1 y2 \<in> x"
  shows "map2 f ys1 ys2 \<in> listset xs"
  using assms
proof (induct xs arbitrary: ys1 ys2)
  case Nil
  from Nil(1) show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain y1 ys1' where "y1 \<in> x" and "ys1' \<in> listset xs" and ys1: "ys1 = y1 # ys1'"
    by (rule listset_ConsE)
  from Cons.prems(2) obtain y2 ys2' where "y2 \<in> x" and "ys2' \<in> listset xs" and ys2: "ys2 = y2 # ys2'"
    by (rule listset_ConsE)
  show ?case
  proof (rule listset_ConsI)
    from _ \<open>y1 \<in> x\<close> \<open>y2 \<in> x\<close> show "f y1 y2 \<in> x" by (rule Cons.prems) simp
  next
    show "map2 f ys1' ys2' \<in> listset xs"
    proof (rule Cons.hyps)
      fix x' y1' y2'
      assume "x' \<in> set xs"
      hence "x' \<in> set (x # xs)" by simp
      moreover assume "y1' \<in> x'" and "y2' \<in> x'"
      ultimately show "f y1' y2' \<in> x'" by (rule Cons.prems)
    qed fact+
  qed (simp add: ys1 ys2)
qed

lemma listset_empty_iff: "listset xs = {} \<longleftrightarrow> {} \<in> set xs"
  by (induct xs) (auto simp: listset_Cons simp del: listset.simps(2))

lemma listset_mono:
  assumes "length xs = length ys" and "\<And>i. i < length ys \<Longrightarrow> xs ! i \<subseteq> ys ! i"
  shows "listset xs \<subseteq> listset ys"
  using assms
proof (induct xs ys rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  show ?case
  proof
    fix zs'
    assume "zs' \<in> listset (x # xs)"
    then obtain z zs where "z \<in> x" and zs: "zs \<in> listset xs" and zs': "zs' = z # zs"
      by (rule listset_ConsE)
    have "0 < length (y # ys)" by simp
    hence "(x # xs) ! 0 \<subseteq> (y # ys) ! 0" by (rule Cons.prems)
    hence "x \<subseteq> y" by simp
    with \<open>z \<in> x\<close> have "z \<in> y" ..
    moreover from zs have "zs \<in> listset ys"
    proof
      show "listset xs \<subseteq> listset ys"
      proof (rule Cons.hyps)
        fix i
        assume "i < length ys"
        hence "Suc i < length (y # ys)" by simp
        hence "(x # xs) ! Suc i \<subseteq> (y # ys) ! Suc i" by (rule Cons.prems)
        thus "xs ! i \<subseteq> ys ! i" by simp
      qed
    qed
    ultimately show "zs' \<in> listset (y # ys)" using zs' by (rule listset_ConsI)
  qed
qed

end (* theory *)
