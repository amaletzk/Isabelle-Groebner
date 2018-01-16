section \<open>Faug\'ere's F4 Algorithm\<close>

theory F4
  imports Groebner_Macaulay Algorithm_Schema
begin

subsection \<open>Lists\<close>

definition insert_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "insert_list x xs = (if x \<in> set xs then xs else x # xs)"

lemma set_insert_list: "set (insert_list x xs) = insert x (set xs)"
  by (auto simp add: insert_list_def)

fun merge_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_wrt _ xs [] = xs"|
  "merge_wrt rel [] ys = ys"|
  "merge_wrt rel (x # xs) (y # ys) =
    (if x = y then
      y # (merge_wrt rel xs ys)
    else if rel x y then
      x # (merge_wrt rel xs (y # ys))
    else
      y # (merge_wrt rel (x # xs) ys)
    )"

lemma set_merge_wrt: "set (merge_wrt rel xs ys) = set xs \<union> set ys"
proof (induct rel xs ys rule: merge_wrt.induct)
  case (1 rel xs)
  show ?case by simp
next
  case (2 rel y ys)
  show ?case by simp
next
  case (3 rel x xs y ys)
  show ?case
  proof (cases "x = y")
    case True
    thus ?thesis by (simp add: 3(1))
  next
    case False
    show ?thesis
    proof (cases "rel x y")
      case True
      with \<open>x \<noteq> y\<close> show ?thesis by (simp add: 3(2) insert_commute)
    next
      case False
      with \<open>x \<noteq> y\<close> show ?thesis by (simp add: 3(3))
    qed
  qed
qed

subsection \<open>Symbolic Preprocessing\<close>

context ordered_powerprod
begin

abbreviation ord_strict_conv (infixl "\<succ>" 50) where "ord_strict_conv \<equiv> (op \<prec>\<inverse>\<inverse>)"

definition keys_to_list :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a list"
  where "keys_to_list p = pps_to_list (keys p)"

definition Keys_to_list :: "('a \<Rightarrow>\<^sub>0 'b::zero) list \<Rightarrow> 'a list"
  where "Keys_to_list ps = fold (\<lambda>p ts. merge_wrt (op \<succ>) (keys_to_list p) ts) ps []"

lemma set_keys_to_list: "set (keys_to_list p) = keys p"
  by (simp add: keys_to_list_def set_pps_to_list)

lemma keys_to_list_zero [simp]: "keys_to_list 0 = []"
  by (simp add: keys_to_list_def pps_to_list_def)

lemma Keys_to_list_Nil [simp]: "Keys_to_list [] = []"
  by (simp add: Keys_to_list_def)

lemma set_fold_merge_wrt_keys_to_list:
  "set (fold (\<lambda>p ts. merge_wrt (op \<succ>) (keys_to_list p) ts) ps ts) = set ts \<union> Keys (set ps)"
proof (induct ps arbitrary: ts)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  show ?case
    by (simp only: fold.simps o_def Cons set_merge_wrt set_simps Keys_insert set_keys_to_list ac_simps)
qed

lemma set_Keys_to_list: "set (Keys_to_list ps) = Keys (set ps)"
  by (simp add: Keys_to_list_def set_fold_merge_wrt_keys_to_list)

end (* ordered_powerprod *)

context gd_powerprod
begin

definition dgrad_set :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a set"
  where "dgrad_set d m = {t. d t \<le> m}"

definition dgrad_set_le :: "('a \<Rightarrow> nat) \<Rightarrow> ('a set) \<Rightarrow> ('a set) \<Rightarrow> bool"
  where "dgrad_set_le d S T \<longleftrightarrow> (\<forall>s\<in>S. \<exists>t\<in>T. d s \<le> d t)"

lemma dgrad_set_leI:
  assumes "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>T. d s \<le> d t"
  shows "dgrad_set_le d S T"
  using assms by (auto simp: dgrad_set_le_def)

lemma dgrad_set_leE:
  assumes "dgrad_set_le d S T" and "s \<in> S"
  obtains t where "t \<in> T" and "d s \<le> d t"
  using assms by (auto simp: dgrad_set_le_def)

lemma dgrad_set_exhaust_expl:
  assumes "finite F"
  shows "F \<subseteq> dgrad_set d (Max (d ` F))"
proof
  fix f
  assume "f \<in> F"
  hence "d f \<in> d ` F" by simp
  with _ have "d f \<le> Max (d ` F)"
  proof (rule Max_ge)
    from assms show "finite (d ` F)" by auto
  qed
  hence "dgrad_set d (d f) \<subseteq> dgrad_set d (Max (d ` F))" by (auto simp: dgrad_set_def)
  moreover have "f \<in> dgrad_set d (d f)" by (simp add: dgrad_set_def)
  ultimately show "f \<in> dgrad_set d (Max (d ` F))" ..
qed

lemma dgrad_set_exhaust:
  assumes "finite F"
  obtains m where "F \<subseteq> dgrad_set d m"
proof
  from assms show "F \<subseteq> dgrad_set d (Max (d ` F))" by (rule dgrad_set_exhaust_expl)
qed

lemma dgrad_set_le_trans [trans]:
  assumes "dgrad_set_le d S T" and "dgrad_set_le d T U"
  shows "dgrad_set_le d S U"
  unfolding dgrad_set_le_def
proof
  fix s
  assume "s \<in> S"
  with assms(1) obtain t where "t \<in> T" and 1: "d s \<le> d t" by (auto simp add: dgrad_set_le_def)
  from assms(2) this(1) obtain u where "u \<in> U" and 2: "d t \<le> d u" by (auto simp add: dgrad_set_le_def)
  from this(1) show "\<exists>u\<in>U. d s \<le> d u"
  proof
    from 1 2 show "d s \<le> d u" by (rule le_trans)
  qed
qed

lemma dgrad_set_le_Un: "dgrad_set_le d (S \<union> T) U \<longleftrightarrow> (dgrad_set_le d S U \<and> dgrad_set_le d T U)"
  by (auto simp add: dgrad_set_le_def)

lemma dgrad_set_le_subset:
  assumes "S \<subseteq> T"
  shows "dgrad_set_le d S T"
  unfolding dgrad_set_le_def using assms by blast

lemma dgrad_set_le_refl: "dgrad_set_le d S S"
  by (rule dgrad_set_le_subset, fact subset_refl)

lemma dgrad_set_le_dgrad_set:
  assumes "dgrad_set_le d F G" and "G \<subseteq> dgrad_set d m"
  shows "F \<subseteq> dgrad_set d m"
proof
  fix f
  assume "f \<in> F"
  with assms(1) obtain g where "g \<in> G" and *: "d f \<le> d g" by (auto simp add: dgrad_set_le_def)
  from assms(2) this(1) have "g \<in> dgrad_set d m" ..
  hence "d g \<le> m" by (simp add: dgrad_set_def)
  with * have "d f \<le> m" by (rule le_trans)
  thus "f \<in> dgrad_set d m" by (simp add: dgrad_set_def)
qed

lemma dgrad_set_le_imp_dgrad_p_set_le:
  assumes "G \<noteq> {}" and "dgrad_set_le d (Keys F) (Keys G)"
  shows "dgrad_p_set_le d F G"
proof (rule dgrad_p_set_leI)
  fix f
  assume "f \<in> F"
  show "\<exists>g\<in>G. dgrad_p d f \<le> dgrad_p d g"
  proof (cases "f = 0")
    case True
    from assms(1) obtain g where "g \<in> G" by blast
    thus ?thesis
    proof
      show "dgrad_p d f \<le> dgrad_p d g" by (simp add: True)
    qed
  next
    case False
    hence "Max (d ` keys f) \<in> d ` keys f" by simp
    then obtain s where "s \<in> keys f" and Max: "Max (d ` keys f) = d s" ..
    have s_max: "u \<in> keys f \<Longrightarrow> d u \<le> d s" for u by (auto simp add: Max[symmetric])
    from \<open>f \<in> F\<close> have "keys f \<subseteq> Keys F" by (rule keys_subset_Keys)
    hence "dgrad_set_le d (keys f) (Keys F)" by (rule dgrad_set_le_subset)
    from this assms(2) have "dgrad_set_le d (keys f) (Keys G)" by (rule dgrad_set_le_trans)
    from this \<open>s \<in> keys f\<close> have "\<exists>t\<in>Keys G. d s \<le> d t" unfolding dgrad_set_le_def ..
    then obtain t where "t \<in> Keys G" and "d s \<le> d t" ..
    from this(1) obtain g where "g \<in> G" and "t \<in> keys g" by (rule in_KeysE)
    show ?thesis
    proof (rule, rule dgrad_p_leI)
      fix u
      assume "u \<in> keys f"
      hence "d u \<le> d s" by (rule s_max)
      also have "... \<le> d t" by fact
      also from \<open>t \<in> keys g\<close> have "... \<le> dgrad_p d g" by (rule dgrad_p_geI)
      finally show "d u \<le> dgrad_p d g" .
    qed fact
  qed
qed

definition sym_preproc_aux_term1 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)) set"
  where "sym_preproc_aux_term1 d =
            {((gs1, ts1, fs1), (gs2::('a \<Rightarrow>\<^sub>0 'b) list, ts2, fs2)). \<exists>t2\<in>set ts2. \<forall>t1\<in>set ts1. t1 \<prec> t2}"

definition sym_preproc_aux_term2 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b::zero) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)) set"
  where "sym_preproc_aux_term2 d =
            {((gs1, ts1, fs1), (gs2::('a \<Rightarrow>\<^sub>0 'b) list, ts2, fs2)). gs1 = gs2 \<and>
                                              dgrad_set_le d (set ts1) (Keys (set gs2) \<union> set ts2)}"

definition sym_preproc_aux_term
  where "sym_preproc_aux_term d = sym_preproc_aux_term1 d \<inter> sym_preproc_aux_term2 d"

lemma wfP_on_ord_strict:
  assumes "dickson_grading (op +) d"
  shows "wfP_on (dgrad_set d m) (op \<prec>)"
proof (rule wfP_onI_min)
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> dgrad_set d m"
  from wf_dickson_less[OF assms, of m] \<open>x \<in> Q\<close> obtain z
    where "z \<in> Q" and *: "\<And>y. dickson_less d m y z \<Longrightarrow> y \<notin> Q" by (rule wfE_min[to_pred], blast)
  from this(1) \<open>Q \<subseteq> dgrad_set d m\<close> have "z \<in> dgrad_set d m" ..
  show "\<exists>z\<in>Q. \<forall>y\<in>dgrad_set d m. y \<prec> z \<longrightarrow> y \<notin> Q"
  proof (intro bexI ballI impI, rule *)
    fix y
    assume "y \<in> dgrad_set d m" and "y \<prec> z"
    from this(1) \<open>z \<in> dgrad_set d m\<close> have "d y \<le> m" and "d z \<le> m" by (simp_all add: dgrad_set_def)
    thus "dickson_less d m y z" using \<open>y \<prec> z\<close> by (rule dickson_lessI)
  qed fact
qed

lemma sym_preproc_aux_term1_wf_on:
  assumes "dickson_grading (op +) d"
  shows "wfP_on {x. set (fst (snd x)) \<subseteq> dgrad_set d m} (\<lambda>x y. (x, y) \<in> sym_preproc_aux_term1 d)"
proof (rule wfP_onI_min)
  let ?B = "dgrad_set d m"
  let ?A = "{x::(('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list). set (fst (snd x)) \<subseteq> ?B}"
  have A_sub_Pow: "set ` fst ` snd ` ?A \<subseteq> Pow ?B" by auto
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  let ?Q = "{ordered_powerprod_lin.Max (set (fst (snd q))) | q. q \<in> Q \<and> fst (snd q) \<noteq> []}"
  show "\<exists>z\<in>Q. \<forall>y\<in>{x. set (fst (snd x)) \<subseteq> dgrad_set d m}. (y, z) \<in> sym_preproc_aux_term1 d \<longrightarrow> y \<notin> Q"
  proof (cases "\<exists>z\<in>Q. fst (snd z) = []")
    case True
    then obtain z where "z \<in> Q" and "fst (snd z) = []" ..
    show ?thesis
    proof (intro bexI ballI impI)
      fix y
      assume "(y, z) \<in> sym_preproc_aux_term1 d"
      then obtain t where "t \<in> set (fst (snd z))" unfolding sym_preproc_aux_term1_def by auto
      with \<open>fst (snd z) = []\<close> show "y \<notin> Q" by simp
    qed fact
  next
    case False
    hence *: "q \<in> Q \<Longrightarrow> fst (snd q) \<noteq> []" for q by blast
    with \<open>x \<in> Q\<close> have "fst (snd x) \<noteq> []" by simp
    from assms have "wfP_on ?B (op \<prec>)" by (rule wfP_on_ord_strict)
    moreover from \<open>x \<in> Q\<close> \<open>fst (snd x) \<noteq> []\<close> have "ordered_powerprod_lin.Max (set (fst (snd x))) \<in> ?Q"
      by blast
    moreover have "?Q \<subseteq> ?B"
    proof (rule, simp, elim exE conjE, simp)
      fix a b c
      assume "(a, b, c) \<in> Q" and "b \<noteq> []"
      from this(1) \<open>Q \<subseteq> ?A\<close> have "(a, b, c) \<in> ?A" ..
      hence "set b \<subseteq> ?B" by simp
      moreover from \<open>b \<noteq> []\<close> have "ordered_powerprod_lin.Max (set b) \<in> set b" by simp
      ultimately show "ordered_powerprod_lin.Max (set b) \<in> ?B" ..
    qed
    ultimately obtain t where "t \<in> ?Q" and min: "\<And>s. s \<prec> t \<Longrightarrow> s \<notin> ?Q" by (rule wfP_onE_min, blast)
    from this(1) obtain z where "z \<in> Q" and "fst (snd z) \<noteq> []"
      and t: "t = ordered_powerprod_lin.Max (set (fst (snd z)))" by blast
    show ?thesis
    proof (intro bexI ballI impI, rule)
      fix y
      assume "y \<in> ?A" and "(y, z) \<in> sym_preproc_aux_term1 d" and "y \<in> Q"
      from this(2) obtain t' where "t' \<in> set (fst (snd z))" and **: "\<And>s. s \<in> set (fst (snd y)) \<Longrightarrow> s \<prec> t'"
        unfolding sym_preproc_aux_term1_def by auto
      from \<open>y \<in> Q\<close> have "fst (snd y) \<noteq> []" by (rule *)
      with \<open>y \<in> Q\<close> have "ordered_powerprod_lin.Max (set (fst (snd y))) \<in> ?Q" (is "?s \<in> _") by blast
      from \<open>fst (snd y) \<noteq> []\<close> have "?s \<in> set (fst (snd y))" by simp
      hence "?s \<prec> t'" by (rule **)
      also from \<open>t' \<in> set (fst (snd z))\<close> have "t' \<preceq> t" unfolding t using \<open>fst (snd z) \<noteq> []\<close> by simp
      finally have "?s \<notin> ?Q" by (rule min)
      from this \<open>?s \<in> ?Q\<close> show False ..
    qed fact
  qed
qed

lemma sym_preproc_aux_term_wf:
  assumes "dickson_grading (op +) d"
  shows "wf (sym_preproc_aux_term d)"
proof (rule wfI_min)
  fix x::"(('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)" and Q
  assume "x \<in> Q"
  let ?A = "Keys (set (fst x)) \<union> set (fst (snd x))"
  have "finite ?A" by (simp add: finite_Keys)
  then obtain m where A: "?A \<subseteq> dgrad_set d m" by (rule dgrad_set_exhaust)
  let ?B = "dgrad_set d m"
  let ?Q = "{q \<in> Q. Keys (set (fst q)) \<union> set (fst (snd q)) \<subseteq> ?B}"
  from assms have "wfP_on {x. set (fst (snd x)) \<subseteq> ?B} (\<lambda>x y. (x, y) \<in> sym_preproc_aux_term1 d)"
    by (rule sym_preproc_aux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by simp
  moreover have "?Q \<subseteq> {x. set (fst (snd x)) \<subseteq> ?B}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> sym_preproc_aux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "Keys (set (fst z)) \<union> set (fst (snd z)) \<subseteq> ?B" by simp_all
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> sym_preproc_aux_term d \<longrightarrow> y \<notin> Q"
  proof (intro bexI allI impI)
    fix y
    assume "(y, z) \<in> sym_preproc_aux_term d"
    hence "(y, z) \<in> sym_preproc_aux_term1 d" and "(y, z) \<in> sym_preproc_aux_term2 d"
      by (simp_all add: sym_preproc_aux_term_def)
    from this(2) have "fst y = fst z"
      and "dgrad_set_le d (set (fst (snd y))) (Keys (set (fst z)) \<union> set (fst (snd z)))"
      by (auto simp add: sym_preproc_aux_term2_def)
    from this(2) a have "set (fst (snd y)) \<subseteq> ?B" by (rule dgrad_set_le_dgrad_set)
    hence "Keys (set (fst y)) \<union> set (fst (snd y)) \<subseteq> ?B" using a by (auto simp add: \<open>fst y = fst z\<close>)
    moreover from \<open>(y, z) \<in> sym_preproc_aux_term1 d\<close> have "y \<notin> ?Q" by (rule *)
    ultimately show "y \<notin> Q" by simp
  qed fact
qed

primrec sym_preproc_addnew :: "('a \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> 'a \<Rightarrow>
                              ('a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)" where
  "sym_preproc_addnew [] ts fs _ = (ts, fs)"|
  "sym_preproc_addnew (g # gs) ts fs t =
    (if lp g adds t then
      (let f = monom_mult 1 (t - lp g) g in
        sym_preproc_addnew gs (merge_wrt (op \<succ>) ts (keys_to_list (tail f))) (insert_list f fs) t
      )
    else
      sym_preproc_addnew gs ts fs t
    )"

lemma fst_sym_preproc_addnew_less:
  assumes "\<And>u. u \<in> set ts \<Longrightarrow> u \<prec> t"
    and "s \<in> set (fst (sym_preproc_addnew gs ts fs t))"
  shows "s \<prec> t"
  using assms
proof (induct gs arbitrary: fs ts)
  case Nil
  from Nil(2) have "s \<in> set ts" by simp
  thus ?case by (rule Nil(1))
next
  case (Cons g gs)
  from Cons(3) show ?case
  proof (simp add: Let_def split: if_splits)
    assume "lp g adds t"
    assume "s \<in> set (fst (sym_preproc_addnew gs (merge_wrt op \<succ> ts (keys_to_list (tail (monom_mult 1 (t - lp g) g))))
                    (insert_list (monom_mult 1 (t - lp g) g) fs) t))"
    with _ show ?thesis
    proof (rule Cons(1))
      fix u
      assume "u \<in> set (merge_wrt op \<succ> ts (keys_to_list (tail (monom_mult 1 (t - lp g) g))))"
      hence "u \<in> set ts \<or> u \<in> keys (tail (monom_mult 1 (t - lp g) g))"
        by (simp add: set_merge_wrt keys_to_list_def set_pps_to_list)
      thus "u \<prec> t"
      proof
        assume "u \<in> set ts"
        thus ?thesis by (rule Cons(2))
      next
        assume "u \<in> keys (tail (monom_mult 1 (t - lp g) g))"
        hence "u \<prec> lp (monom_mult 1 (t - lp g) g)" by (rule keys_tail_less_lp)
        also have "... \<preceq> (t - lp g) + lp g" by (rule lp_monom_mult_le)
        also from \<open>lp g adds t\<close> have "... = t" by (rule adds_minus)
        finally show ?thesis .
      qed
    qed
  next
    assume "s \<in> set (fst (sym_preproc_addnew gs ts fs t))"
    with Cons(2) show ?thesis by (rule Cons(1))
  qed
qed

lemma fst_sym_preproc_addnew_dgrad_set_le:
  assumes "dickson_grading (op +) d"
  shows "dgrad_set_le d (set (fst (sym_preproc_addnew gs ts fs t))) (Keys (set gs) \<union> insert t (set ts))"
proof (induct gs arbitrary: fs ts)
  case Nil
  show ?case by (auto intro: dgrad_set_le_subset)
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    assume "lp g adds t"
    let ?ts = "merge_wrt op \<succ> ts (keys_to_list (tail (monom_mult 1 (t - lp g) g)))"
    let ?fs = "insert_list (monom_mult 1 (t - lp g) g) fs"
    from Cons have "dgrad_set_le d (set (fst (sym_preproc_addnew gs ?ts ?fs t))) (Keys (insert g (set gs)) \<union> insert t (set ts))"
    proof (rule dgrad_set_le_trans)
      show "dgrad_set_le d (Keys (set gs) \<union> insert t (set ?ts)) (Keys (insert g (set gs)) \<union> insert t (set ts))"
        unfolding dgrad_set_le_def set_merge_wrt set_keys_to_list
      proof (intro ballI)
        fix s
        assume "s \<in> Keys (set gs) \<union> insert t (set ts \<union> keys (tail (monom_mult 1 (t - lp g) g)))"
        hence "s \<in> (Keys (set gs) \<union> insert t (set ts)) \<union> keys (tail (monom_mult 1 (t - lp g) g))"
          by simp
        thus "\<exists>t\<in>Keys (insert g (set gs)) \<union> insert t (set ts). d s \<le> d t"
        proof
          assume "s \<in> Keys (set gs) \<union> insert t (set ts)"
          thus ?thesis by (auto simp add: Keys_insert)
        next
          assume "s \<in> keys (tail (monom_mult 1 (t - lp g) g))"
          hence "s \<in> keys (monom_mult 1 (t - lp g) g)" by (simp add: keys_tail)
          from this keys_monom_mult_subset have "s \<in> op + (t - lp g) ` keys g" ..
          then obtain u where "u \<in> keys g" and s: "s = (t - lp g) + u" ..
          have "d s = d (t - lp g) \<or> d s = d u" unfolding s using dickson_gradingD1[OF assms] by auto
          thus ?thesis
          proof
            assume "d s = d (t - lp g)"
            also from assms \<open>lp g adds t\<close> have "... \<le> d t" by (rule dickson_grading_minus)
            finally show ?thesis by blast
          next
            assume "d s = d u"
            moreover from \<open>u \<in> keys g\<close> have "u \<in> Keys (insert g (set gs))" by (simp add: Keys_insert)
            ultimately show ?thesis by auto
          qed
        qed
      qed
    qed
    thus "dgrad_set_le d (set (fst (sym_preproc_addnew gs ?ts ?fs t))) (insert t (Keys (insert g (set gs)) \<union> set ts))"
      by simp
  next
    from Cons show "dgrad_set_le d (set (fst (sym_preproc_addnew gs ts fs t))) (insert t (Keys (insert g (set gs)) \<union> set ts))"
    proof (rule dgrad_set_le_trans)
      show "dgrad_set_le d (Keys (set gs) \<union> insert t (set ts)) (insert t (Keys (insert g (set gs)) \<union> set ts))"
        by (rule dgrad_set_le_subset, auto simp add: Keys_def)
    qed
  qed
qed

lemma fst_sym_preproc_addnew_superset: "set ts \<subseteq> set (fst (sym_preproc_addnew gs ts fs t))"
proof (induct gs arbitrary: ts fs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    define f where "f = monom_mult 1 (t - lp g) g"
    have "set ts \<subseteq> set (merge_wrt op \<succ> ts (keys_to_list (tail f)))" by (auto simp add: set_merge_wrt)
    thus "set ts \<subseteq> set (fst (sym_preproc_addnew gs
                              (merge_wrt op \<succ> ts (keys_to_list (tail f))) (insert_list f fs) t))"
      using Cons by (rule subset_trans)
  next
    show "set ts \<subseteq> set (fst (sym_preproc_addnew gs ts fs t))" by (fact Cons)
  qed
qed

lemma snd_sym_preproc_addnew_superset: "set fs \<subseteq> set (snd (sym_preproc_addnew gs ts fs t))"
proof (induct gs arbitrary: ts fs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    define f where "f = monom_mult 1 (t - lp g) g"
    have "set fs \<subseteq> set (insert_list f fs)" by (auto simp add: set_insert_list)
    thus "set fs \<subseteq> set (snd (sym_preproc_addnew gs
                              (merge_wrt op \<succ> ts (keys_to_list (tail f))) (insert_list f fs) t))"
      using Cons by (rule subset_trans)
  next
    show "set fs \<subseteq> set (snd (sym_preproc_addnew gs ts fs t))" by (fact Cons)
  qed
qed

lemma in_snd_sym_preproc_addnewE:
  assumes "p \<in> set (snd (sym_preproc_addnew gs ts fs t))"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g s. g \<in> set gs \<Longrightarrow> p = monom_mult 1 s g \<Longrightarrow> thesis"
  shows thesis
  using assms
proof (induct gs arbitrary: ts fs thesis)
  case Nil
  from Nil(1) have "p \<in> set fs" by simp
  thus ?case by (rule Nil(2))
next
  case (Cons g gs)
  from Cons(2) show ?case
  proof (simp add: Let_def split: if_splits)
    define f where "f = monom_mult 1 (t - lp g) g"
    define ts' where "ts' = merge_wrt op \<succ> ts (keys_to_list (tail f))"
    define fs' where "fs' = insert_list f fs"
    assume "p \<in> set (snd (sym_preproc_addnew gs ts' fs' t))"
    thus ?thesis
    proof (rule Cons(1))
      assume "p \<in> set fs'"
      hence "p = f \<or> p \<in> set fs" by (simp add: fs'_def set_insert_list)
      thus ?thesis
      proof
        assume "p = f"
        have "g \<in> set (g # gs)" by simp
        from this \<open>p = f\<close> show ?thesis unfolding f_def by (rule Cons(4))
      next
        assume "p \<in> set fs"
        thus ?thesis by (rule Cons(3))
      qed
    next
      fix h s
      assume "h \<in> set gs"
      hence "h \<in> set (g # gs)" by simp
      moreover assume "p = monom_mult 1 s h"
      ultimately show thesis by (rule Cons(4))
    qed
  next
    assume "p \<in> set (snd (sym_preproc_addnew gs ts fs t))"
    moreover note Cons(3)
    moreover have "h \<in> set gs \<Longrightarrow> p = monom_mult 1 s h \<Longrightarrow> thesis" for h s
    proof -
      assume "h \<in> set gs"
      hence "h \<in> set (g # gs)" by simp
      moreover assume "p = monom_mult 1 s h"
      ultimately show thesis by (rule Cons(4))
    qed
    ultimately show ?thesis by (rule Cons(1))
  qed
qed

lemma sym_preproc_addnew_pideal:
  "pideal (set gs \<union> set (snd (sym_preproc_addnew gs ts fs t))) = pideal (set gs \<union> set fs)"
    (is "pideal (set gs \<union> ?l) = ?r")
proof
  have "set gs \<subseteq> set gs \<union> set fs" by simp
  also have "... \<subseteq> ?r" by (fact generator_subset_pideal)
  finally have "set gs \<subseteq> ?r" .
  moreover have "?l \<subseteq> ?r"
  proof
    fix p
    assume "p \<in> ?l"
    thus "p \<in> ?r"
    proof (rule in_snd_sym_preproc_addnewE)
      assume "p \<in> set fs"
      hence "p \<in> set gs \<union> set fs" by simp
      thus ?thesis by (rule generator_in_pideal)
    next
      fix g s
      assume "g \<in> set gs" and p: "p = monom_mult 1 s g"
      from this(1) \<open>set gs \<subseteq> ?r\<close> have "g \<in> ?r" ..
      thus ?thesis unfolding p by (rule pideal_closed_monom_mult)
    qed
  qed
  ultimately have "set gs \<union> ?l \<subseteq> ?r" by blast
  thus "pideal (set gs \<union> ?l) \<subseteq> ?r" by (rule pideal_subset_pidealI)
next
  from snd_sym_preproc_addnew_superset have "set gs \<union> set fs \<subseteq> set gs \<union> ?l" by blast
  thus "?r \<subseteq> pideal (set gs \<union> ?l)" by (rule pideal_mono)
qed

lemma Keys_snd_sym_preproc_addnew:
  "Keys (set (snd (sym_preproc_addnew gs ts fs t))) \<union> insert t (set ts) =
   Keys (set fs) \<union> insert t (set (fst (sym_preproc_addnew gs ts (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list) t)))"
proof (induct gs arbitrary: ts fs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  from Cons have eq: "insert t (Keys (set (snd (sym_preproc_addnew gs ts' fs' t))) \<union> set ts') =
                      insert t (Keys (set fs') \<union> set (fst (sym_preproc_addnew gs ts' fs' t)))"
    for ts' fs' by simp
  show ?case
  proof (simp add: Let_def eq, rule)
    assume "lp g adds t"
    define f where "f = monom_mult 1 (t - lp g) g"
    define ts' where "ts' = merge_wrt op \<succ> ts (keys_to_list (tail f))"
    define fs' where "fs' = insert_list f fs"
    have "keys (tail f) = keys f - {t}"
    proof (cases "g = 0")
      case True
      hence "f = 0" by (simp add: f_def monom_mult_right0)
      thus ?thesis by simp
    next
      case False
      hence "lp f = (t - lp g) + lp g" by (simp add: f_def lp_mult)
      also from \<open>lp g adds t\<close> have "... = t" by (rule adds_minus)
      finally show ?thesis by (simp add: keys_tail)
    qed
    hence ts': "set ts' = set ts \<union> (keys f - {t})"
      by (simp add: ts'_def set_merge_wrt set_keys_to_list)
    have fs': "set fs' = insert f (set fs)" by (simp add: fs'_def set_insert_list)
    hence "f \<in> set fs'" by simp
    from this snd_sym_preproc_addnew_superset have "f \<in> set (snd (sym_preproc_addnew gs ts' fs' t))" ..
    hence "keys f \<subseteq> Keys (set (snd (sym_preproc_addnew gs ts' fs' t)))" by (rule keys_subset_Keys)
    hence "insert t (Keys (set (snd (sym_preproc_addnew gs ts' fs' t))) \<union> set ts) =
          insert t (Keys (set (snd (sym_preproc_addnew gs ts' fs' t))) \<union> set ts')"
      by (auto simp add: ts')
    also have "... = insert t (Keys (set fs') \<union> set (fst (sym_preproc_addnew gs ts' fs' t)))"
      by (fact eq)
    also have "... = insert t (Keys (set fs) \<union> set (fst (sym_preproc_addnew gs ts' fs' t)))"
    proof -
      {
        fix s
        assume "s \<noteq> t" and "s \<in> keys f"
        hence "s \<in> set ts'" by (simp add: ts')
        from this fst_sym_preproc_addnew_superset have "s \<in> set (fst (sym_preproc_addnew gs ts' fs' t))" ..
      }
      thus ?thesis by (auto simp add: fs' Keys_insert)
    qed
    finally show "insert t (Keys (set (snd (sym_preproc_addnew gs ts' fs' t))) \<union> set ts) =
                  insert t (Keys (set fs) \<union> set (fst (sym_preproc_addnew gs ts' fs' t)))" .
  qed
qed

lemma sym_preproc_addnew_complete:
  assumes "g \<in> set gs" and "lp g adds t"
  shows "monom_mult 1 (t - lp g) g \<in> set (snd (sym_preproc_addnew gs ts fs t))"
  using assms(1)
proof (induct gs arbitrary: ts fs)
  case Nil
  thus ?case by simp
next
  case (Cons h gs)
  show ?case
  proof (cases "h = g")
    case True
    show ?thesis
    proof (simp add: True assms(2) Let_def)
      define f where "f = monom_mult 1 (t - lp g) g"
      define ts' where "ts' = merge_wrt op \<succ> ts (keys_to_list (tail (monom_mult 1 (t - lp g) g)))"
      have "f \<in> set (insert_list f fs)" by (simp add: set_insert_list)
      with snd_sym_preproc_addnew_superset show "f \<in> set (snd (sym_preproc_addnew gs ts' (insert_list f fs) t))" ..
    qed
  next
    case False
    with Cons(2) have "g \<in> set gs" by simp
    hence *: "monom_mult 1 (t - lp g) g \<in> set (snd (sym_preproc_addnew gs ts' fs' t))" for ts' fs'
      by (rule Cons(1))
    show ?thesis by (simp add: Let_def *)
  qed
qed

function sym_preproc_aux :: "('a \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> ('a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list" where
  "sym_preproc_aux gs (ts, fs) =
    (if ts = [] then
      fs
    else
      let t = ordered_powerprod_lin.Max (set ts); ts' = removeAll t ts in
        sym_preproc_aux gs (sym_preproc_addnew gs ts' fs t)
    )"
  by pat_completeness auto
termination proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (op +) d" ..
  let ?R = "(sym_preproc_aux_term d)::((('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                        ('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) set"
  show ?thesis
  proof
    from dg show "wf ?R" by (rule sym_preproc_aux_term_wf)
  next
    fix gs::"('a \<Rightarrow>\<^sub>0 'b) list" and ts fs t ts'
    assume "ts \<noteq> []" and t: "t = ordered_powerprod_lin.Max (set ts)" and ts': "ts' = removeAll t ts"
    obtain ts0 fs0 where eq: "sym_preproc_addnew gs ts' fs t = (ts0, fs0)" by fastforce
    show "((gs, sym_preproc_addnew gs ts' fs t), (gs, ts, fs)) \<in> ?R"
    proof (simp add: eq sym_preproc_aux_term_def sym_preproc_aux_term1_def sym_preproc_aux_term2_def,
           intro conjI bexI ballI)
      fix s
      assume "s \<in> set ts0"
      show "s \<prec> t"
      proof (rule fst_sym_preproc_addnew_less)
        fix u
        assume "u \<in> set ts'"
        thus "u \<prec> t" unfolding ts' t set_removeAll using ordered_powerprod_lin.antisym_conv1
          by fastforce
      next
        from \<open>s \<in> set ts0\<close> show "s \<in> set (fst (sym_preproc_addnew gs ts' fs t))" by (simp add: eq)
      qed
    next
      from \<open>ts \<noteq> []\<close> show "t \<in> set ts" by (simp add: t)
    next
      from dg have "dgrad_set_le d (set (fst (sym_preproc_addnew gs ts' fs t))) (Keys (set gs) \<union> insert t (set ts'))"
        by (rule fst_sym_preproc_addnew_dgrad_set_le)
      moreover have "insert t (set ts') = set ts" by (auto simp add: ts' t \<open>ts \<noteq> []\<close>)
      ultimately show "dgrad_set_le d (set ts0) (Keys (set gs) \<union> set ts)" by (simp add: eq)
    qed
  qed
qed

lemma sym_preproc_aux_Nil: "sym_preproc_aux gs ([], fs) = fs"
  by simp

lemma sym_preproc_aux_sorted:
  assumes "sorted_wrt (op \<succ>) (t # ts)"
  shows "sym_preproc_aux gs (t # ts, fs) = sym_preproc_aux gs (sym_preproc_addnew gs ts fs t)"
proof -
  have "transp (op \<succ>)" using transp_def by fastforce
  from assms have *: "s \<in> set ts \<Longrightarrow> s \<prec> t" for s by (simp add: sorted_wrt_Cons[OF \<open>transp (op \<succ>)\<close>])
  have eq1: "ordered_powerprod_lin.Max (set (t # ts)) = t"
  proof (rule ordered_powerprod_lin.Max_eqI)
    fix s
    assume "s \<in> set (t # ts)"
    hence "s = t \<or> s \<in> set ts" by simp
    thus "s \<preceq> t"
    proof
      assume "s = t"
      thus ?thesis by simp
    next
      assume "s \<in> set ts"
      hence "s \<prec> t" by (rule *)
      thus ?thesis by simp
    qed
  next
    show "t \<in> set (t # ts)" by simp
  qed rule
  have eq2: "removeAll t (t # ts) = ts"
  proof (simp, rule removeAll_id, rule)
    assume "t \<in> set ts"
    hence "t \<prec> t" by (rule *)
    thus False ..
  qed
  show ?thesis by (simp only: sym_preproc_aux.simps eq1 eq2 Let_def, simp)
qed

lemma sym_preproc_aux_induct [consumes 0, case_names base rec]:
  assumes base: "\<And>fs. P [] fs fs"
    and rec: "\<And>ts fs t ts'. ts \<noteq> [] \<Longrightarrow> t = ordered_powerprod_lin.Max (set ts) \<Longrightarrow> ts' = removeAll t ts \<Longrightarrow>
                P (fst (sym_preproc_addnew gs ts' fs t)) (snd (sym_preproc_addnew gs ts' fs t))
                    (sym_preproc_aux gs (sym_preproc_addnew gs ts' fs t)) \<Longrightarrow>
                P ts fs (sym_preproc_aux gs (sym_preproc_addnew gs ts' fs t))"
  shows "P ts fs (sym_preproc_aux gs (ts, fs))"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (op +) d" ..
  let ?R = "(sym_preproc_aux_term d)::((('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                        ('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) set"
  define args where "args = (gs, ts, fs)"
  from dg have "wf ?R" by (rule sym_preproc_aux_term_wf)
  hence "fst args = gs \<Longrightarrow> P (fst (snd args)) (snd (snd args)) (sym_preproc_aux gs (snd args))"
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> sym_preproc_aux_term d \<Longrightarrow> fst y = gs \<Longrightarrow>
                    P (fst (snd y)) (snd (snd y)) (sym_preproc_aux gs (snd y))"
    assume "fst x = gs"
    then obtain x0 where x: "x = (gs, x0)" by (meson eq_fst_iff)
    obtain ts fs where x0: "x0 = (ts, fs)" by (meson case_prodE case_prodI2)
    from IH' have IH: "\<And>n. ((gs, n), (gs, ts, fs)) \<in> sym_preproc_aux_term d \<Longrightarrow>
                            P (fst n) (snd n) (sym_preproc_aux gs n)" unfolding x x0 by fastforce
    show "P (fst (snd x)) (snd (snd x)) (sym_preproc_aux gs (snd x))"
    proof (simp add: x x0 Let_def, intro conjI impI)
      show "P [] fs fs" by (fact base)
    next
      assume "ts \<noteq> []"
      define t where "t = ordered_powerprod_lin.Max (set ts)"
      define ts' where "ts' = removeAll t ts"
      show "P ts fs (sym_preproc_aux gs (sym_preproc_addnew gs ts' fs t))"
      proof (rule rec, fact \<open>ts \<noteq> []\<close>, fact t_def, fact ts'_def)
        let ?n = "sym_preproc_addnew gs ts' fs t"
        obtain ts0 fs0 where eq: "?n = (ts0, fs0)" by fastforce
        show "P (fst ?n) (snd ?n) (sym_preproc_aux gs ?n)"
        proof (rule IH,
              simp add: eq sym_preproc_aux_term_def sym_preproc_aux_term1_def sym_preproc_aux_term2_def,
              intro conjI bexI ballI)
          fix s
          assume "s \<in> set ts0"
          show "s \<prec> t"
          proof (rule fst_sym_preproc_addnew_less)
            fix u
            assume "u \<in> set ts'"
            thus "u \<prec> t" unfolding ts'_def t_def set_removeAll using ordered_powerprod_lin.antisym_conv1
              by fastforce
          next
            from \<open>s \<in> set ts0\<close> show "s \<in> set (fst (sym_preproc_addnew gs ts' fs t))" by (simp add: eq)
          qed
        next
          from \<open>ts \<noteq> []\<close> show "t \<in> set ts" by (simp add: t_def)
        next
          from dg have "dgrad_set_le d (set (fst (sym_preproc_addnew gs ts' fs t))) (Keys (set gs) \<union> insert t (set ts'))"
            by (rule fst_sym_preproc_addnew_dgrad_set_le)
          moreover have "insert t (set ts') = set ts" by (auto simp add: ts'_def t_def \<open>ts \<noteq> []\<close>)
          ultimately show "dgrad_set_le d (set ts0) (Keys (set gs) \<union> set ts)" by (simp add: eq)
        qed
      qed
    qed
  qed
  thus ?thesis by (simp add: args_def)
qed

lemma sym_preproc_aux_superset: "set fs \<subseteq> set (sym_preproc_aux gs (ts, fs))"
proof (induct rule: sym_preproc_aux_induct)
  case (base fs)
  show ?case ..
next
  case (rec ts fs t ts')
  from snd_sym_preproc_addnew_superset rec(4) show ?case by (rule subset_trans)
qed


lemma in_sym_preproc_auxE:
  assumes "p \<in> set (sym_preproc_aux gs (ts, fs))"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g t. g \<in> set gs \<Longrightarrow> p = monom_mult 1 t g \<Longrightarrow> thesis"
  shows thesis
  using assms
proof (induct gs ts fs arbitrary: thesis rule: sym_preproc_aux_induct)
case (base fs)
  from base(1) show ?case by (rule base(2))
next
  case (rec ts fs t ts')
  from rec(5) show ?case
  proof (rule rec(4))
    assume "p \<in> set (snd (sym_preproc_addnew gs ts' fs t))"
    thus ?thesis
    proof (rule in_snd_sym_preproc_addnewE)
      assume "p \<in> set fs"
      thus ?thesis by (rule rec(6))
    next
      fix g s
      assume "g \<in> set gs" and "p = monom_mult 1 s g"
      thus ?thesis by (rule rec(7))
    qed
  next
    fix g t
    assume "g \<in> set gs" and "p = monom_mult 1 t g"
    thus ?thesis by (rule rec(7))
  qed
qed

lemma sym_preproc_aux_pideal:
  "pideal (set gs \<union> set (sym_preproc_aux gs (ts, fs))) = pideal (set gs \<union> set fs)"
proof (induct rule: sym_preproc_aux_induct)
case (base fs)
  show ?case ..
next
  case (rec ts fs t ts')
  from rec(4) sym_preproc_addnew_pideal show ?case by (rule trans)
qed

lemma sym_preproc_aux_dgrad_set_le:
  assumes "dickson_grading (op +) d" and "set ts \<subseteq> Keys (set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  shows "dgrad_set_le d (Keys (set (sym_preproc_aux gs (ts, fs)))) (Keys (set gs \<union> set fs))"
  using assms(2)
proof (induct rule: sym_preproc_aux_induct)
  case (base fs)
  show ?case by (rule dgrad_set_le_subset, simp add: Keys_Un)
next
  case (rec ts fs t ts')
  let ?n = "sym_preproc_addnew gs ts' fs t"
  from rec(1) have "t \<in> set ts" by (simp add: rec(2))
  hence set_ts: "insert t (set ts') = set ts" by (auto simp add: rec(3))
  from rec(5) have eq: "Keys (set fs) \<union> (Keys (set gs) \<union> set ts) = Keys (set gs) \<union> Keys (set fs)"
    by blast
  have "dgrad_set_le d (Keys (set (sym_preproc_aux gs ?n))) (Keys (set gs \<union> set (snd ?n)))"
  proof (rule rec(4))
    have "set (fst ?n) \<subseteq> Keys (set (snd ?n)) \<union> insert t (set ts')"
      by (simp only: Keys_snd_sym_preproc_addnew, blast)
    also have "... = Keys (set (snd ?n)) \<union> (set ts)" by (simp only: set_ts)
    also have "... \<subseteq> Keys (set (snd ?n))"
    proof -
      {
        fix s
        assume "s \<in> set ts"
        with rec(5) have "s \<in> Keys (set fs)" ..
        then obtain f where "f \<in> set fs" and "s \<in> keys f" by (rule in_KeysE)
        from this(1) snd_sym_preproc_addnew_superset have "f \<in> set (snd ?n)" ..
        with \<open>s \<in> keys f\<close> have "s \<in> Keys (set (snd ?n))" by (rule in_KeysI)
      }
      thus ?thesis by auto
    qed
    finally show "set (fst ?n) \<subseteq> Keys (set (snd ?n))" .
  qed
  also have "dgrad_set_le d ... (Keys (set gs \<union> set fs))"
  proof (simp only: Keys_Un dgrad_set_le_Un, rule)
    show "dgrad_set_le d (Keys (set gs)) (Keys (set gs) \<union> Keys (set fs))"
      by (rule dgrad_set_le_subset, simp)
  next
    have "dgrad_set_le d (Keys (set (snd ?n))) (Keys (set fs) \<union> insert t (set (fst ?n)))"
      by (rule dgrad_set_le_subset, auto simp only: Keys_snd_sym_preproc_addnew[symmetric])
    also have "dgrad_set_le d ... (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))"
    proof (simp only: dgrad_set_le_Un, rule)
      show "dgrad_set_le d (Keys (set fs)) (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))"
        by (rule dgrad_set_le_subset, blast)
    next
      have "dgrad_set_le d {t} (Keys (set gs) \<union> insert t (set ts'))"
        by (rule dgrad_set_le_subset, simp)
      moreover from assms(1) have "dgrad_set_le d (set (fst ?n)) (Keys (set gs) \<union> insert t (set ts'))"
        by (rule fst_sym_preproc_addnew_dgrad_set_le)
      ultimately have "dgrad_set_le d ({t} \<union> set (fst ?n)) (Keys (set gs) \<union> insert t (set ts'))"
        by (simp only: dgrad_set_le_Un)
      also have "dgrad_set_le d (Keys (set gs) \<union> insert t (set ts'))
                                (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))"
        by (rule dgrad_set_le_subset, blast)
      finally show "dgrad_set_le d (insert t (set (fst ?n)))
                                   (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))" by simp
    qed
    finally show "dgrad_set_le d (Keys (set (snd ?n))) (Keys (set gs) \<union> Keys (set fs))"
      by (simp only: set_ts eq)
  qed
  finally show ?case .
qed

(*
lemma sym_preproc_aux_dgrad_p_set_le:
  assumes "dickson_grading (op +) d" and "set ts \<subseteq> Keys (set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  shows "dgrad_p_set_le d (set (sym_preproc_aux gs (ts, fs))) (set gs \<union> set fs)"
  using assms(2)
proof (induct rule: sym_preproc_aux_induct)
  case (base fs)
  show ?case by (rule dgrad_p_set_le_subset, simp)
next
  case (rec ts fs t ts')
  let ?n = "sym_preproc_addnew gs ts' fs t"
  from rec(1) have "t \<in> set ts" by (simp add: rec(2))
  hence set_ts: "insert t (set ts') = set ts" by (auto simp add: rec(3))
  from rec(5) have eq: "Keys (set fs) \<union> (Keys (set gs) \<union> set ts) = Keys (set gs) \<union> Keys (set fs)"
    by blast
  have "dgrad_p_set_le d (set (sym_preproc_aux gs ?n)) (set gs \<union> set (snd ?n))"
  proof (rule rec(4))
    have "set (fst ?n) \<subseteq> Keys (set (snd ?n)) \<union> insert t (set ts')"
      by (simp only: Keys_snd_sym_preproc_addnew, blast)
    also have "... = Keys (set (snd ?n)) \<union> (set ts)" by (simp only: set_ts)
    also have "... \<subseteq> Keys (set (snd ?n))"
    proof -
      {
        fix s
        assume "s \<in> set ts"
        with rec(5) have "s \<in> Keys (set fs)" ..
        then obtain f where "f \<in> set fs" and "s \<in> keys f" by (rule in_KeysE)
        from this(1) snd_sym_preproc_addnew_superset have "f \<in> set (snd ?n)" ..
        with \<open>s \<in> keys f\<close> have "s \<in> Keys (set (snd ?n))" by (rule in_KeysI)
      }
      thus ?thesis by auto
    qed
    finally show "set (fst ?n) \<subseteq> Keys (set (snd ?n))" .
  qed
  also have "dgrad_p_set_le d ... (set gs \<union> set fs)"
  proof (cases "set gs \<union> set fs = {}")
    case True
    hence "gs = []" and "set fs = {}" by simp_all
    show ?thesis by (simp add: \<open>gs = []\<close> \<open>set fs = {}\<close>, rule dgrad_p_set_le_subset, fact subset_refl)
  next
    case False
    show ?thesis
    proof (rule dgrad_set_le_imp_dgrad_p_set_le[OF False], simp only: Keys_Un dgrad_set_le_Un, rule)
      show "dgrad_set_le d (Keys (set gs)) (Keys (set gs) \<union> Keys (set fs))"
        by (rule dgrad_set_le_subset, simp)
    next
      have "dgrad_set_le d (Keys (set (snd ?n))) (Keys (set fs) \<union> insert t (set (fst ?n)))"
        by (rule dgrad_set_le_subset, auto simp only: Keys_snd_sym_preproc_addnew[symmetric])
      also have "dgrad_set_le d ... (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))"
      proof (simp only: dgrad_set_le_Un, rule)
        show "dgrad_set_le d (Keys (set fs)) (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))"
          by (rule dgrad_set_le_subset, blast)
      next
        have "dgrad_set_le d {t} (Keys (set gs) \<union> insert t (set ts'))"
          by (rule dgrad_set_le_subset, simp)
        moreover from assms(1) have "dgrad_set_le d (set (fst ?n)) (Keys (set gs) \<union> insert t (set ts'))"
          by (rule fst_sym_preproc_addnew_dgrad_set_le)
        ultimately have "dgrad_set_le d ({t} \<union> set (fst ?n)) (Keys (set gs) \<union> insert t (set ts'))"
          by (simp only: dgrad_set_le_Un)
        also have "dgrad_set_le d (Keys (set gs) \<union> insert t (set ts'))
                                  (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))"
          by (rule dgrad_set_le_subset, blast)
        finally show "dgrad_set_le d (insert t (set (fst ?n)))
                                     (Keys (set fs) \<union> (Keys (set gs) \<union> insert t (set ts')))" by simp
      qed
      finally show "dgrad_set_le d (Keys (set (snd ?n))) (Keys (set gs) \<union> Keys (set fs))"
        by (simp only: set_ts eq)
    qed
  qed
  finally show ?case .
qed
*)

lemma sym_preproc_aux_complete:
  assumes "\<And>s' g'. s' \<in> Keys (set fs) \<Longrightarrow> s' \<notin> set ts \<Longrightarrow> g' \<in> set gs \<Longrightarrow> lp g' adds s' \<Longrightarrow>
            monom_mult 1 (s' - lp g') g' \<in> set fs"
  assumes "s \<in> Keys (set (sym_preproc_aux gs (ts, fs)))" and "g \<in> set gs" and "lp g adds s"
  shows "monom_mult (1::'b::semiring_1_no_zero_divisors) (s - lp g) g \<in> set (sym_preproc_aux gs (ts, fs))"
  using assms
proof (induct rule: sym_preproc_aux_induct)
  case (base fs)
  from base(2) _ base(3, 4) show ?case
  proof (rule base(1))
    show "s \<notin> set []" by simp
  qed
next
  case (rec ts fs t ts')
  from rec(1) have "t \<in> set ts" by (simp add: rec(2))
  hence set_ts: "set ts = insert t (set ts')" by (auto simp add: rec(3))

  let ?n = "sym_preproc_addnew gs ts' fs t"
  from _ rec(6, 7, 8) show ?case
  proof (rule rec(4))
    fix t' g'
    assume "t' \<in> Keys (set (snd ?n))" and "t' \<notin> set (fst ?n)" and "g' \<in> set gs" and "lp g' adds t'"
    from this(1) Keys_snd_sym_preproc_addnew have "t' \<in> Keys (set fs) \<union> insert t (set (fst ?n))"
      by blast
    with \<open>t' \<notin> set (fst ?n)\<close> have disj: "t' \<in> Keys (set fs) \<or> t' = t" by blast
    show "monom_mult 1 (t' - lp g') g' \<in> set (snd ?n)"
    proof (cases "t' = t")
      case True
      from \<open>g' \<in> set gs\<close> \<open>lp g' adds t'\<close> show ?thesis
        unfolding True by (rule sym_preproc_addnew_complete)
    next
      case False
      with disj have "t' \<in> Keys (set fs)" by simp
      moreover have "t' \<notin> set ts"
      proof
        assume "t' \<in> set ts"
        hence "t' \<in> set ts'" using False by (simp add: rec(3))
        with fst_sym_preproc_addnew_superset have "t' \<in> set (fst ?n)" ..
        with \<open>t' \<notin> set (fst ?n)\<close> show False ..
      qed
      ultimately have "monom_mult 1 (t' - lp g') g' \<in> set fs" using \<open>g' \<in> set gs\<close> \<open>lp g' adds t'\<close>
        by (rule rec(5))
      with snd_sym_preproc_addnew_superset show ?thesis ..
    qed
  qed
qed

definition sym_preproc :: "('a \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list"
  where "sym_preproc gs fs = sym_preproc_aux gs (Keys_to_list fs, fs)"

lemma sym_preproc_Nil [simp]: "sym_preproc gs [] = []"
  by (simp add: sym_preproc_def)

lemma sym_preproc_superset: "set fs \<subseteq> set (sym_preproc gs fs)"
  unfolding sym_preproc_def by (fact sym_preproc_aux_superset)

lemma in_sym_preprocE:
  assumes "p \<in> set (sym_preproc gs fs)"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g t. g \<in> set gs \<Longrightarrow> p = monom_mult 1 t g \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding sym_preproc_def by (rule in_sym_preproc_auxE)

lemma sym_preproc_pideal: "pideal (set gs \<union> set (sym_preproc gs fs)) = pideal (set gs \<union> set fs)"
  unfolding sym_preproc_def by (fact sym_preproc_aux_pideal)

lemma sym_preproc_dgrad_set_le:
  assumes "dickson_grading (op +) d"
  shows "dgrad_set_le d (Keys (set (sym_preproc gs fs))) (Keys (set gs \<union> set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list)))"
  unfolding sym_preproc_def using assms
proof (rule sym_preproc_aux_dgrad_set_le)
  show "set (Keys_to_list fs) \<subseteq> Keys (set fs)" by (simp add: set_Keys_to_list)
qed

corollary sym_preproc_dgrad_p_set_le:
  assumes "dickson_grading (op +) d"
  shows "dgrad_p_set_le d (set (sym_preproc gs fs)) (set gs \<union> set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
proof (cases "set gs \<union> set fs = {}")
  case True
  hence "set gs = {}" and "fs = []" by simp_all
  show ?thesis by (simp add: \<open>set gs = {}\<close> \<open>fs = []\<close>, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case False
  thus ?thesis
  proof (rule dgrad_set_le_imp_dgrad_p_set_le)
    from assms show "dgrad_set_le d (Keys (set (sym_preproc gs fs))) (Keys (set gs \<union> set fs))"
      by (rule sym_preproc_dgrad_set_le)
  qed
qed

lemma sym_preproc_complete:
  assumes "t \<in> Keys (set (sym_preproc gs fs))" and "g \<in> set gs" and "lp g adds t"
  shows "monom_mult (1::'b::semiring_1_no_zero_divisors) (t - lp g) g \<in> set (sym_preproc gs fs)"
  using _ assms unfolding sym_preproc_def
proof (rule sym_preproc_aux_complete)
  fix s' and g'::"'a \<Rightarrow>\<^sub>0 'b"
  assume "s' \<in> Keys (set fs)" and "s' \<notin> set (Keys_to_list fs)"
  thus "monom_mult 1 (s' - lp g') g' \<in> set fs" by (simp add: set_Keys_to_list)
qed

end (* gd_powerprod *)

subsection \<open>@{term lin_red}\<close>

context ordered_powerprod
begin

definition lin_red::"('a \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "lin_red F p q \<equiv> (\<exists>f\<in>F. red_single p q f 0)"

text \<open>@{const lin_red} is a restriction of @{const red}, where the reductor (@{term f}) may only be
  multiplied by a scalar factor, i.\,e. where the power-product is @{term 0}.\<close>

lemma lin_redI:
  assumes "f \<in> F" and "red_single p q f 0"
  shows "lin_red F p q"
  unfolding lin_red_def using assms ..

lemma lin_redE:
  assumes "lin_red F p q"
  obtains f::"'a \<Rightarrow>\<^sub>0 'b::field" where "f \<in> F" and "red_single p q f 0"
proof -
  from assms obtain f where "f \<in> F" and t: "red_single p q f 0" unfolding lin_red_def by blast
  thus "?thesis" ..
qed

lemma lin_red_imp_red:
  assumes "lin_red F p q"
  shows "red F p q"
proof -
  from assms obtain f where "f \<in> F" and "red_single p q f 0" by (rule lin_redE)
  thus ?thesis by (rule red_setI)
qed

lemma lin_red_Un: "lin_red (F \<union> G) p q = (lin_red F p q \<or> lin_red G p q)"
proof
  assume "lin_red (F \<union> G) p q"
  then obtain f where "f \<in> F \<union> G" and r: "red_single p q f 0" by (rule lin_redE)
  from this(1) show "lin_red F p q \<or> lin_red G p q"
  proof
    assume "f \<in> F"
    from this r have "lin_red F p q" by (rule lin_redI)
    thus ?thesis ..
  next
    assume "f \<in> G" 
    from this r have "lin_red G p q" by (rule lin_redI)
    thus ?thesis ..
  qed
next
  assume "lin_red F p q \<or> lin_red G p q"
  thus "lin_red (F \<union> G) p q"
  proof
    assume "lin_red F p q"
    then obtain f where "f \<in> F" and r: "red_single p q f 0" by (rule lin_redE)
    from this(1) have "f \<in> F \<union> G" by simp
    from this r show ?thesis by (rule lin_redI)
  next
    assume "lin_red G p q"
    then obtain g where "g \<in> G" and r: "red_single p q g 0" by (rule lin_redE)
    from this(1) have "g \<in> F \<union> G" by simp
    from this r show ?thesis by (rule lin_redI)
  qed
qed

lemma lin_red_imp_red_rtrancl:
  assumes "(lin_red F)\<^sup>*\<^sup>* p q"
  shows "(red F)\<^sup>*\<^sup>* p q"
  using assms
proof induct
  case base
  show ?case ..
next
  case (step y z)
  from step(2) have "red F y z" by (rule lin_red_imp_red)
  with step(3) show ?case ..
qed

(*
lemma lin_red_srtc_in_phull:
  assumes "relation.srtc (lin_red F) p q"
  shows "p - q \<in> phull F"
  using assms unfolding relation.srtc_def
proof (induct rule: rtranclp.induct)
  fix p
  show "p - p \<in> phull F" by (simp add: zero_in_phull)
next
  fix p r q
  assume pr_in: "p - r \<in> phull F" and red: "lin_red F r q \<or> lin_red F q r"
  from red obtain f c where "f \<in> F" and "q = r - monom_mult c 0 f"
  proof
    assume "lin_red F r q"
    then obtain f where "f \<in> F" and "red_single r q f 0" by (rule lin_redE)
    hence "q = r - monom_mult (lookup r (lp f) / lc f) 0 f" by (simp add: red_single_def)
    show thesis by (rule, fact, fact)
  next
    assume "lin_red F q r"
    then obtain f where "f \<in> F" and "red_single q r f 0" by (rule lin_redE)
    hence "r = q - monom_mult (lookup q (lp f) / lc f) 0 f" by (simp add: red_single_def)
    hence "q = r + monom_mult (lookup q (lp f) / lc f) 0 f" by simp
    hence "q = r - monom_mult (-(lookup q (lp f) / lc f)) 0 f"
      using monom_mult_uminus_left[of _ 0 f] by simp
    show thesis by (rule, fact, fact)
  qed
  hence eq: "p - q = (p - r) + monom_mult c 0 f" by simp
  show "p - q \<in> phull F" unfolding eq
    by (rule phull_closed_plus, fact, rule monom_mult_in_phull, fact)
qed

lemma lin_red_rtrancl_diff_in_phull:
  assumes "(lin_red F)\<^sup>*\<^sup>* p q"
  shows "p - q \<in> phull F"
proof -
  from assms have "relation.srtc (lin_red F) p q"
    by (simp add: r_into_rtranclp relation.rtc_implies_srtc)
  thus ?thesis by (rule lin_red_srtc_in_phull)
qed
*)

lemma phull_closed_lin_red:
  assumes "phull B \<subseteq> phull A" and "p \<in> phull A" and "lin_red B p q"
  shows "q \<in> phull A"
proof -
  from assms(3) obtain f where "f \<in> B" and "red_single p q f 0" by (rule lin_redE)
  hence q: "q = p - monom_mult (lookup p (lp f) / lc f) 0 f" by (simp add: red_single_def)
  have "q - p \<in> phull B"
    by (simp add: q, rule phull_closed_uminus, rule phull_closed_monom_mult, rule generator_in_phull,
        fact \<open>f \<in> B\<close>)
  with assms(1) have "q - p \<in> phull A" ..
  from this assms(2) have "(q - p) + p \<in> phull A" by (rule phull_closed_plus)
  thus ?thesis by simp
qed

subsection \<open>Reduction\<close>

definition Macaulay_red :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "Macaulay_red ps =
     (let lps = map lp (filter (\<lambda>p. p \<noteq> 0) ps) in
      filter (\<lambda>p. p \<noteq> 0 \<and> lp p \<notin> set lps) (mat_to_polys (pps_to_list (Keys (set ps))) (row_echelon (Macaulay_mat ps)))
     )"

text \<open>@{term "Macaulay_red ps"} auto-reduces (w.\,r.\,t. @{const lin_red}) the given list @{term ps}
  and returns those non-zero polynomials whose leading power-products are not in @{term "lp_set (set ps)"}.\<close>

lemma Macaulay_red_alt: "Macaulay_red ps = filter (\<lambda>p. lp p \<notin> lp_set (set ps)) (Macaulay_list ps)"
proof -
  have "{x \<in> set ps. x \<noteq> 0} = set ps - {0}" by blast
  thus ?thesis by (simp add: Macaulay_red_def Macaulay_list_def lp_set_def)
qed

lemma set_Macaulay_red: "set (Macaulay_red ps) = set (Macaulay_list ps) - {p. lp p \<in> lp_set (set ps)}"
  by (auto simp add: Macaulay_red_alt)

lemma Keys_Macaulay_red: "Keys (set (Macaulay_red ps)) \<subseteq> Keys (set ps)"
proof -
  have "Keys (set (Macaulay_red ps)) \<subseteq> Keys (set (Macaulay_list ps))" unfolding set_Macaulay_red
    by (fact Keys_minus)
  also have "... \<subseteq> Keys (set ps)" by (fact Keys_Macaulay_list)
  finally show ?thesis .
qed

end (* ordered_powerprod *)

context gd_powerprod
begin

lemma Macaulay_red_reducible:
  assumes "f \<in> phull (set ps)" and "F \<subseteq> set ps" and "lp_set F = lp_set (set ps)"
  shows "(lin_red (F \<union> set (Macaulay_red ps)))\<^sup>*\<^sup>* f 0"
proof -
  define A where "A = F \<union> set (Macaulay_red ps)"

  have phull_A: "phull A \<subseteq> phull (set ps)"
  proof (rule phull_subset_phullI, simp add: A_def, rule)
    have "F \<subseteq> phull F" by (rule generator_subset_phull)
    also from assms(2) have "... \<subseteq> phull (set ps)" by (rule phull_mono)
    finally show "F \<subseteq> phull (set ps)" .
  next
    have "set (Macaulay_red ps) \<subseteq> set (Macaulay_list ps)" by (auto simp add: set_Macaulay_red)
    also have "... \<subseteq> phull (set (Macaulay_list ps))" by (rule generator_subset_phull)
    also have "... = phull (set ps)" by (rule phull_Macaulay_list)
    finally show "set (Macaulay_red ps) \<subseteq> phull (set ps)" .
  qed

  have lp_A: "p \<in> phull (set ps) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> (\<And>g. g \<in> A \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> lp g = lp p \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    for p thesis
  proof -
    assume "p \<in> phull (set ps)" and "p \<noteq> 0"
    then obtain g where g_in: "g \<in> set (Macaulay_list ps)" and "g \<noteq> 0" and "lp p = lp g"
      by (rule Macaulay_list_lp)
    assume *: "\<And>g. g \<in> A \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> lp g = lp p \<Longrightarrow> thesis"
    show ?thesis
    proof (cases "g \<in> set (Macaulay_red ps)")
      case True
      hence "g \<in> A" by (simp add: A_def)
      from this \<open>g \<noteq> 0\<close> \<open>lp p = lp g\<close>[symmetric] show ?thesis by (rule *)
    next
      case False
      with g_in have "lp g \<in> lp_set (set ps)" by (simp add: set_Macaulay_red)
      also have "... = lp_set F" by (simp only: assms(3))
      finally obtain g' where "g' \<in> F" and "g' \<noteq> 0" and "lp g' = lp g" by (rule lp_setE)
      from this(1) have "g' \<in> A" by (simp add: A_def)
      moreover note \<open>g' \<noteq> 0\<close>
      moreover have "lp g' = lp p" by (simp only: \<open>lp p = lp g\<close> \<open>lp g' = lp g\<close>)
      ultimately show ?thesis by (rule *)
    qed
  qed

  from assms(2) finite_set have "finite F" by (rule finite_subset)
  from this finite_set have fin_A: "finite A" unfolding A_def by (rule finite_UnI)

  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (op +) d" ..
  from fin_A have "finite (insert f A)" ..
  then obtain m where "insert f A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  hence A_sub: "A \<subseteq> dgrad_p_set d m" and "f \<in> dgrad_p_set d m" by simp_all
  from dg have "wfP (dickson_less_p d m)" by (rule dickson_less_p_wf)
  from this assms(1) \<open>f \<in> dgrad_p_set d m\<close> show "(lin_red A)\<^sup>*\<^sup>* f 0"
  proof (induct f)
    fix p
    assume IH: "\<And>q. dickson_less_p d m q p \<Longrightarrow> q \<in> phull (set ps) \<Longrightarrow> q \<in> dgrad_p_set d m \<Longrightarrow>
                    (lin_red A)\<^sup>*\<^sup>* q 0"
      and "p \<in> phull (set ps)" and "p \<in> dgrad_p_set d m"
    show "(lin_red A)\<^sup>*\<^sup>* p 0"
    proof (cases "p = 0")
      case True
      thus ?thesis by simp
    next
      case False
      with \<open>p \<in> phull (set ps)\<close> obtain g where "g \<in> A" and "g \<noteq> 0" and "lp g = lp p" by (rule lp_A)
      define q where "q = p - monom_mult (lc p / lc g) 0 g"
      from \<open>g \<in> A\<close> have lr: "lin_red A p q"
      proof (rule lin_redI)
        show "red_single p q g 0"
          by (simp add: red_single_def \<open>lp g = lp p\<close> lc_def[symmetric] q_def \<open>g \<noteq> 0\<close> lc_not_0[OF False])
      qed
      moreover have "(lin_red A)\<^sup>*\<^sup>* q 0"
      proof -
        from lr have red: "red A p q" by (rule lin_red_imp_red)
        with dg A_sub \<open>p \<in> dgrad_p_set d m\<close> have "q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red)
        moreover from red have "q \<prec>p p" by (rule red_ord)
        ultimately have "dickson_less_p d m q p" using \<open>p \<in> dgrad_p_set d m\<close>
          by (simp add: dickson_less_p_def)
        moreover from phull_A \<open>p \<in> phull (set ps)\<close> lr have "q \<in> phull (set ps)"
          by (rule phull_closed_lin_red)
        ultimately show ?thesis using \<open>q \<in> dgrad_p_set d m\<close> by (rule IH)
      qed
      ultimately show ?thesis by fastforce
    qed
  qed
qed

primrec pdata_pairs_to_list :: "('a, 'b::field, 'c) pdata_pair list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list" where
  "pdata_pairs_to_list [] = []"|
  "pdata_pairs_to_list (p # ps) =
    (let f = fst (fst p); g = fst (snd p); l = lcs (lp f) (lp g) in
      (monom_mult (1 / lc f) (l - (lp f)) f) # (monom_mult (1 / lc g) (l - (lp g)) g) #
      (pdata_pairs_to_list ps)
    )"

lemma in_pdata_pairs_to_listI1:
  assumes "(f, g) \<in> set ps"
  shows "monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f) \<in>
          set (pdata_pairs_to_list ps)" (is "?m \<in> _")
  using assms
proof (induct ps)
  case Nil
  thus ?case by simp
next
  case (Cons p ps)
  from Cons(2) have "p = (f, g) \<or> (f, g) \<in> set ps" by auto
  thus ?case
  proof
    assume "p = (f, g)"
    show ?thesis by (simp add: \<open>p = (f, g)\<close> Let_def)
  next
    assume "(f, g) \<in> set ps"
    hence "?m \<in> set (pdata_pairs_to_list ps)" by (rule Cons(1))
    thus ?thesis by (simp add: Let_def)
  qed
qed

lemma in_pdata_pairs_to_listI2:
  assumes "(f, g) \<in> set ps"
  shows "monom_mult (1 / lc (fst g)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst g))) (fst g) \<in>
          set (pdata_pairs_to_list ps)" (is "?m \<in> _")
  using assms
proof (induct ps)
  case Nil
  thus ?case by simp
next
  case (Cons p ps)
  from Cons(2) have "p = (f, g) \<or> (f, g) \<in> set ps" by auto
  thus ?case
  proof
    assume "p = (f, g)"
    show ?thesis by (simp add: \<open>p = (f, g)\<close> Let_def)
  next
    assume "(f, g) \<in> set ps"
    hence "?m \<in> set (pdata_pairs_to_list ps)" by (rule Cons(1))
    thus ?thesis by (simp add: Let_def)
  qed
qed

lemma in_pdata_pairs_to_listE:
  assumes "h \<in> set (pdata_pairs_to_list ps)"
  obtains f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
    and "h = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
  using assms
proof (induct ps arbitrary: thesis)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons p ps)
  let ?f = "fst (fst p)"
  let ?g = "fst (snd p)"
  let ?l = "lcs (lp ?f) (lp ?g)"
  from Cons(3) have "h = monom_mult (1 / lc ?f) (?l - lp ?f) ?f \<or> h = monom_mult (1 / lc ?g) (?l - lp ?g) ?g \<or>
                     h \<in> set (pdata_pairs_to_list ps)"
    by (simp add: Let_def)
  thus ?case
  proof (elim disjE)
    assume h: "h = monom_mult (1 / lc ?f) (?l - lp ?f) ?f"
    have "(fst p, snd p) \<in> set (p # ps)" by simp
    hence "(fst p, snd p) \<in> set (p # ps) \<or> (snd p, fst p) \<in> set (p # ps)" ..
    from this h show ?thesis by (rule Cons(2))
  next
    assume h: "h = monom_mult (1 / lc ?g) (?l - lp ?g) ?g"
    have "(fst p, snd p) \<in> set (p # ps)" by simp
    hence "(snd p, fst p) \<in> set (p # ps) \<or> (fst p, snd p) \<in> set (p # ps)" ..
    moreover from h have "h = monom_mult (1 / lc ?g) ((lcs (lp ?g) (lp ?f)) - lp ?g) ?g"
      by (simp only: lcs_comm)
    ultimately show ?thesis by (rule Cons(2))
  next
    assume h_in: "h \<in> set (pdata_pairs_to_list ps)"
    obtain f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
      and h: "h = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
      by (rule Cons(1), assumption, intro h_in)
    from this(1) have "(f, g) \<in> set (p # ps) \<or> (g, f) \<in> set (p # ps)" by auto
    from this h show ?thesis by (rule Cons(2))
  qed
qed

definition f4_red_aux :: "('a, 'b::field, 'c::default) pdata list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                          ('a \<Rightarrow>\<^sub>0 'b) list"
  where "f4_red_aux bs ps = Macaulay_red (sym_preproc (map fst bs) (pdata_pairs_to_list ps))"

text \<open>@{const f4_red_aux} only takes two arguments, since it does not distinguish between those
  elements of the current basis that is known to be a Gr\"obner basis (called ``gs'' in
  @{theory Algorithm_Schema}) and the remaining ones.\<close>

lemma f4_red_aux_not_zero: "0 \<notin> set (f4_red_aux bs ps)"
  by (simp add: f4_red_aux_def set_Macaulay_red set_Macaulay_list)

lemma f4_red_aux_irredudible:
  assumes "h \<in> set (f4_red_aux bs ps)" and "b \<in> set bs" and "fst b \<noteq> 0"
  shows "\<not> lp (fst b) adds lp h"
proof
  from assms(1) have h_in: "h \<in> set (f4_red_aux bs ps)" by simp
  from this f4_red_aux_not_zero have "h \<noteq> 0" by metis
  hence "lp h \<in> keys h" by (rule lp_in_keys)
  also from h_in have "... \<subseteq> Keys (set (f4_red_aux bs ps))" by (rule keys_subset_Keys)
  also have "... \<subseteq> Keys (set (sym_preproc (map fst bs) (pdata_pairs_to_list ps)))"
    (is "_ \<subseteq> Keys (set ?s)") unfolding f4_red_aux_def by (fact Keys_Macaulay_red)
  finally have "lp h \<in> Keys (set ?s)" .
  moreover from assms(2) have "fst b \<in> set (map fst bs)" by auto
  moreover assume a: "lp (fst b) adds lp h"
  ultimately have "monom_mult 1 (lp h - lp (fst b)) (fst b) \<in> set ?s" (is "?m \<in> _")
    by (rule sym_preproc_complete)
  from assms(3) have "?m \<noteq> 0" by (simp add: monom_mult_0_iff)
  with \<open>?m \<in> set ?s\<close> have "lp ?m \<in> lp_set (set ?s)" by (rule lp_setI)
  moreover from assms(3) a have "lp ?m = lp h" by (simp add: lp_mult adds_minus)
  ultimately have "lp h \<in> lp_set (set ?s)" by simp
  moreover from h_in have "lp h \<notin> lp_set (set ?s)"
    by (simp add: f4_red_aux_def set_Macaulay_red)
  ultimately show False by simp
qed

lemma f4_red_aux_dgrad_p_set_le:
  assumes "dickson_grading (op +) d"
  shows "dgrad_p_set_le d (set (f4_red_aux bs ps)) (args_to_set ([], bs, ps))"
proof (cases "args_to_set ([], bs, ps) = {}")
  case True
  hence "bs = []" and "ps = []" by (simp_all add: args_to_set_def)
  hence eq: "f4_red_aux bs ps = []" by (simp add: f4_red_aux_def Macaulay_red_alt)
  show ?thesis by (simp add: eq True, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case False
  thus ?thesis
  proof (rule dgrad_set_le_imp_dgrad_p_set_le)
    show "dgrad_set_le d (Keys (set (f4_red_aux bs ps))) (Keys (args_to_set ([], bs, ps)))"
      unfolding dgrad_set_le_def
    proof
      fix s
      assume "s \<in> Keys (set (f4_red_aux bs ps))"
      also have "... \<subseteq> Keys (set (sym_preproc (map fst bs) (pdata_pairs_to_list ps)))"
        (is "_ \<subseteq> Keys (set ?s)") unfolding f4_red_aux_def by (fact Keys_Macaulay_red)
      finally have "s \<in> Keys (set ?s)" .
      with sym_preproc_dgrad_set_le[OF assms] obtain t
        where "t \<in> Keys (set (map fst bs) \<union> set (pdata_pairs_to_list ps))" and "d s \<le> d t"
        by (rule dgrad_set_leE)
      from this(1) have "t \<in> Keys (fst ` set bs) \<or> t \<in> Keys (set (pdata_pairs_to_list ps))"
        by (simp add: Keys_Un image_Un)
      thus "\<exists>t\<in>Keys (args_to_set ([], bs, ps)). d s \<le> d t"
      proof
        assume "t \<in> Keys (fst `  set bs)"
        also have "... \<subseteq> Keys (args_to_set ([], bs, ps))"
          by (rule Keys_mono, auto simp add: args_to_set_alt)
        finally have "t \<in> Keys (args_to_set ([], bs, ps))" .
        with \<open>d s \<le> d t\<close> show ?thesis ..
      next
        assume "t \<in> Keys (set (pdata_pairs_to_list ps))"
        then obtain p where "p \<in> set (pdata_pairs_to_list ps)" and "t \<in> keys p" by (rule in_KeysE)
        from this(1) obtain f g where disj: "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
          and p: "p = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
          by (rule in_pdata_pairs_to_listE)
        from disj have "fst f \<in> args_to_set ([], bs, ps) \<and> fst g \<in> args_to_set ([], bs, ps)"
        proof
          assume "(f, g) \<in> set ps"
          hence "f \<in> fst ` set ps" and "g \<in> snd ` set ps" by force+
          hence "fst f \<in> fst ` fst ` set ps" and "fst g \<in> fst ` snd ` set ps" by simp_all
          thus ?thesis by (simp add: args_to_set_def image_Un)
        next
          assume "(g, f) \<in> set ps"
          hence "f \<in> snd ` set ps" and "g \<in> fst ` set ps" by force+
          hence "fst f \<in> fst ` snd ` set ps" and "fst g \<in> fst ` fst ` set ps" by simp_all
          thus ?thesis by (simp add: args_to_set_def image_Un)
        qed
        hence "fst f \<in> args_to_set ([], bs, ps)" and "fst g \<in> args_to_set ([], bs, ps)" by simp_all
        hence keys_f: "keys (fst f) \<subseteq> Keys (args_to_set ([], bs, ps))"
          and keys_g: "keys (fst g) \<subseteq> Keys (args_to_set ([], bs, ps))"
          by (auto intro!: keys_subset_Keys)
        define l where "l = lcs (lp (fst f)) (lp (fst g))"
        from \<open>t \<in> keys p\<close> obtain t' where "t' \<in> keys (fst f)" and t: "t = (l - lp (fst f)) + t'"
          unfolding p l_def using keys_monom_mult_subset by blast
        from this(1) have "fst f \<noteq> 0" by auto
        show ?thesis
        proof (cases "fst g = 0")
          case True
          hence "lp (fst g) = 0" by (simp add: lp_def)
          hence "l = lp (fst f)" by (simp add: l_def lcs_zero lcs_comm)
          hence "t = t'" by (simp add: t)
          with \<open>d s \<le> d t\<close> have "d s \<le> d t'" by simp
          moreover from \<open>t' \<in> keys (fst f)\<close> keys_f have "t' \<in> Keys (args_to_set ([], bs, ps))" ..
          ultimately show ?thesis ..
        next
          case False
          have "d t = d (l - lp (fst f)) \<or> d t = d t'"
            by (auto simp add: t dickson_gradingD1[OF assms])
          thus ?thesis
          proof
            assume "d t = d (l - lp (fst f))"
            also from assms have "... \<le> ord_class.max (d (lp (fst f))) (d (lp (fst g)))"
              unfolding l_def by (rule dickson_grading_lcs_minus)
            finally have "d s \<le> d (lp (fst f)) \<or> d s \<le> d (lp (fst g))" using \<open>d s \<le> d t\<close> by auto
            thus ?thesis
            proof
              assume "d s \<le> d (lp (fst f))"
              moreover have "lp (fst f) \<in> Keys (args_to_set ([], bs, ps))"
                by (rule, rule lp_in_keys, fact+)
              ultimately show ?thesis ..
            next
              assume "d s \<le> d (lp (fst g))"
              moreover have "lp (fst g) \<in> Keys (args_to_set ([], bs, ps))"
                by (rule, rule lp_in_keys, fact+)
              ultimately show ?thesis ..
            qed
          next
            assume "d t = d t'"
            with \<open>d s \<le> d t\<close> have "d s \<le> d t'" by simp
            moreover from \<open>t' \<in> keys (fst f)\<close> keys_f have "t' \<in> Keys (args_to_set ([], bs, ps))" ..
            ultimately show ?thesis ..
          qed
        qed
      qed
    qed
  qed
qed

lemma pideal_f4_red_aux: "set (f4_red_aux bs ps) \<subseteq> pideal (args_to_set ([], bs, ps))"
proof -
  have "set (f4_red_aux bs ps) \<subseteq>
          set (Macaulay_list (sym_preproc (map fst bs) (pdata_pairs_to_list ps)))"
    by (auto simp add: f4_red_aux_def set_Macaulay_red)
  also have "... \<subseteq> pideal (set (Macaulay_list (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (fact generator_subset_pideal)
  also have "... = pideal (set (sym_preproc (map fst bs) (pdata_pairs_to_list ps)))"
    by (fact pideal_Macaulay_list)
  also have "... \<subseteq> pideal (set (map fst bs) \<union>
                        set (sym_preproc (map fst bs) (pdata_pairs_to_list ps)))"
    by (rule pideal_mono, blast)
  also have "... = pideal (set (map fst bs) \<union> set (pdata_pairs_to_list ps))"
    by (fact sym_preproc_pideal)
  also have "... \<subseteq> pideal (args_to_set ([], bs, ps))"
  proof (rule pideal_subset_pidealI, simp only: Un_subset_iff, rule conjI)
    have "set (map fst bs) \<subseteq> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_def)
    also have "... \<subseteq> pideal (args_to_set ([], bs, ps))" by (rule generator_subset_pideal)
    finally show "set (map fst bs) \<subseteq> pideal (args_to_set ([], bs, ps))" .
  next
    show "set (pdata_pairs_to_list ps) \<subseteq> pideal (args_to_set ([], bs, ps))"
    proof
      fix p
      assume "p \<in> set (pdata_pairs_to_list ps)"
      then obtain f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
        and p: "p = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
        by (rule in_pdata_pairs_to_listE)
      from this(1) have "f \<in> fst ` set ps \<union> snd ` set ps" by force
      hence "fst f \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
      hence "fst f \<in> pideal (args_to_set ([], bs, ps))" by (rule generator_in_pideal)
      thus "p \<in> pideal (args_to_set ([], bs, ps))" unfolding p by (rule pideal_closed_monom_mult)
    qed
  qed
  finally show ?thesis .
qed

lemma f4_red_aux_phull_reducible:
  assumes "set ps \<subseteq> set bs \<times> set bs"
    and "f \<in> phull (set (pdata_pairs_to_list ps))"
  shows "(red (fst ` set bs \<union> set (f4_red_aux bs ps)))\<^sup>*\<^sup>* f 0"
proof -
  define s where "s = sym_preproc (map fst bs) (pdata_pairs_to_list ps)"
  from assms(2) have f_in: "f \<in> phull (set s)"
  proof
    have "set (pdata_pairs_to_list ps) \<subseteq> set s" unfolding s_def by (fact sym_preproc_superset)
    thus "phull (set (pdata_pairs_to_list ps)) \<subseteq> phull (set s)" by (rule phull_mono)
  qed
  have eq: "(set s) \<union> set (f4_red_aux bs ps) = (set s) \<union> set (Macaulay_red s)"
    by (simp add: f4_red_aux_def s_def)

  have "(lin_red ((set s) \<union> set (f4_red_aux bs ps)))\<^sup>*\<^sup>* f 0"
    by (simp only: eq, rule Macaulay_red_reducible, fact f_in, fact subset_refl, fact refl)
  thus ?thesis
  proof induct
    case base
    show ?case ..
  next
    case (step y z)
    from step(2) have "red (fst ` set bs \<union> set (f4_red_aux bs ps)) y z" unfolding lin_red_Un
    proof
      assume "lin_red (set s) y z"
      then obtain a where "a \<in> set s" and r: "red_single y z a 0" by (rule lin_redE)
      from this(1) obtain b c t where "b \<in> fst ` set bs" and a: "a = monom_mult c t b" unfolding s_def
      proof (rule in_sym_preprocE)
        assume *: "\<And>b c t. b \<in> fst ` set bs \<Longrightarrow> a = monom_mult c t b \<Longrightarrow> thesis"
        assume "a \<in> set (pdata_pairs_to_list ps)"
        then obtain f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
          and a: "a = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
          by (rule in_pdata_pairs_to_listE)
        from this(1) have "f \<in> fst ` set ps \<union> snd ` set ps" by force
        with assms(1) have "f \<in> set bs" by fastforce
        hence "fst f \<in> fst ` set bs" by simp
        from this a show ?thesis by (rule *)
      next
        fix g s
        assume *: "\<And>b c t. b \<in> fst ` set bs \<Longrightarrow> a = monom_mult c t b \<Longrightarrow> thesis"
        assume "g \<in> set (map fst bs)"
        hence "g \<in> fst ` set bs" by simp
        moreover assume "a = monom_mult 1 s g"
        ultimately show ?thesis by (rule *)
      qed
      from r have "c \<noteq> 0" and "b \<noteq> 0" by (simp_all add: a red_single_def monom_mult_0_iff)
      from r have "red_single y z b t"
        by (simp add: a red_single_def monom_mult_0_iff lp_mult[OF \<open>c \<noteq> 0\<close> \<open>b \<noteq> 0\<close>]
                      lc_mult monom_mult_assoc)
      with \<open>b \<in> fst ` set bs\<close> have "red (fst ` set bs) y z" by (rule red_setI)
      thus ?thesis by (rule red_unionI1)
    next
      assume "lin_red (set (f4_red_aux bs ps)) y z"
      hence "red (set (f4_red_aux bs ps)) y z" by (rule lin_red_imp_red)
      thus ?thesis by (rule red_unionI2)
    qed
    with step(3) show ?case ..
  qed
qed

corollary f4_red_aux_spoly_reducible:
  assumes "set ps \<subseteq> set bs \<times> set bs" and "(p, q) \<in> set ps"
  shows "(red (fst ` set bs \<union> set (f4_red_aux bs ps)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
  using assms(1)
proof (rule f4_red_aux_phull_reducible)
  let ?l = "lcs (lp (fst p)) (lp (fst q))"
  let ?p = "monom_mult (1 / lc (fst p)) (?l - (lp (fst p))) (fst p)"
  let ?q = "monom_mult (1 / lc (fst q)) (?l - (lp (fst q))) (fst q)"
  from assms(2) have "?p \<in> set (pdata_pairs_to_list ps)" and "?q \<in> set (pdata_pairs_to_list ps)"
    by (rule in_pdata_pairs_to_listI1, rule in_pdata_pairs_to_listI2)
  hence "?p \<in> phull (set (pdata_pairs_to_list ps))" and "?q \<in> phull (set (pdata_pairs_to_list ps))"
    by (auto intro: generator_in_phull)
  hence "?p - ?q \<in> phull (set (pdata_pairs_to_list ps))" by (rule phull_closed_minus)
  thus "spoly (fst p) (fst q) \<in> phull (set (pdata_pairs_to_list ps))" by (simp only: spoly_def)
qed

definition f4_red :: "('a, 'b::field, 'c::default) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                        ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata list"
  where "f4_red gs bs ps = map (\<lambda>h. (h, default)) (f4_red_aux (gs @ bs) ps)"

end (* gd_powerprod *)

end (* theory *)