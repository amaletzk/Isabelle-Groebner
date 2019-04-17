(* Author: Alexander Maletzky *)

section \<open>Utilities\<close>

theory General_Utils
  imports Polynomials.Utils Dube_Prelims
begin

lemma image_image_Collect: "f ` {g x | x. P x} = {f (g x) | x. P x}"
  by auto

subsection \<open>Sums\<close>

lemma sum_head_int: "a \<le> (b::int) \<Longrightarrow> sum f {a..b} = f a + sum f {a + 1..b}"
  by (smt atLeastAtMost_iff finite_atLeastAtMost_int simp_from_to sum.insert)

lemma sum_tail_int: "a \<le> (b::int) \<Longrightarrow> sum f {a..b} = f b + sum f {a..b - 1}"
  by (smt Icc_eq_Icc atLeastAtMostPlus1_int_conv finite_atLeastAtMost_int insert_absorb sum.insert)

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

end (* theory *)
