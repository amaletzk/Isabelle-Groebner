(* Author: Alexander Maletzky *)

section \<open>Faug\`ere's F4 Algorithm\<close>

theory F4
  imports Macaulay_Matrix Groebner_Bases.Algorithm_Schema
begin

text \<open>This theory implements Faug\`ere's F4 algorithm based on @{const gd_powerprod.gb_schema_direct}.\<close>

subsection \<open>Symbolic Preprocessing\<close>

context gd_powerprod
begin

definition sym_preproc_aux_term1 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)) set"
  where "sym_preproc_aux_term1 d =
            {((gs1, ks1, ts1, fs1), (gs2::('a \<Rightarrow>\<^sub>0 'b) list, ks2, ts2, fs2)). \<exists>t2\<in>set ts2. \<forall>t1\<in>set ts1. t1 \<prec> t2}"

definition sym_preproc_aux_term2 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b::zero) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)) set"
  where "sym_preproc_aux_term2 d =
            {((gs1, ks1, ts1, fs1), (gs2::('a \<Rightarrow>\<^sub>0 'b) list, ks2, ts2, fs2)). gs1 = gs2 \<and>
                                              dgrad_set_le d (set ts1) (Keys (set gs2) \<union> set ts2)}"

definition sym_preproc_aux_term
  where "sym_preproc_aux_term d = sym_preproc_aux_term1 d \<inter> sym_preproc_aux_term2 d"

lemma wfP_on_ord_strict:
  assumes "dickson_grading (+) d"
  shows "wfP_on (dgrad_set d m) (\<prec>)"
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
  assumes "dickson_grading (+) d"
  shows "wfP_on {x. set (fst (snd (snd x))) \<subseteq> dgrad_set d m} (\<lambda>x y. (x, y) \<in> sym_preproc_aux_term1 d)"
proof (rule wfP_onI_min)
  let ?B = "dgrad_set d m"
  let ?A = "{x::(('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list). set (fst (snd (snd x))) \<subseteq> ?B}"
  have A_sub_Pow: "set ` fst ` snd ` snd ` ?A \<subseteq> Pow ?B" by auto
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  let ?Q = "{ordered_powerprod_lin.Max (set (fst (snd (snd q)))) | q. q \<in> Q \<and> fst (snd (snd q)) \<noteq> []}"
  show "\<exists>z\<in>Q. \<forall>y\<in>{x. set (fst (snd (snd x))) \<subseteq> dgrad_set d m}. (y, z) \<in> sym_preproc_aux_term1 d \<longrightarrow> y \<notin> Q"
  proof (cases "\<exists>z\<in>Q. fst (snd (snd z)) = []")
    case True
    then obtain z where "z \<in> Q" and "fst (snd (snd z)) = []" ..
    show ?thesis
    proof (intro bexI ballI impI)
      fix y
      assume "(y, z) \<in> sym_preproc_aux_term1 d"
      then obtain t where "t \<in> set (fst (snd (snd z)))" unfolding sym_preproc_aux_term1_def by auto
      with \<open>fst (snd (snd z)) = []\<close> show "y \<notin> Q" by simp
    qed fact
  next
    case False
    hence *: "q \<in> Q \<Longrightarrow> fst (snd (snd q)) \<noteq> []" for q by blast
    with \<open>x \<in> Q\<close> have "fst (snd (snd x)) \<noteq> []" by simp
    from assms have "wfP_on ?B (\<prec>)" by (rule wfP_on_ord_strict)
    moreover from \<open>x \<in> Q\<close> \<open>fst (snd (snd x)) \<noteq> []\<close>
    have "ordered_powerprod_lin.Max (set (fst (snd (snd x)))) \<in> ?Q" by blast
    moreover have "?Q \<subseteq> ?B"
    proof (rule, simp, elim exE conjE, simp)
      fix a b c d
      assume "(a, b, c, d) \<in> Q" and "c \<noteq> []"
      from this(1) \<open>Q \<subseteq> ?A\<close> have "(a, b, c, d) \<in> ?A" ..
      hence "set c \<subseteq> ?B" by simp
      moreover from \<open>c \<noteq> []\<close> have "ordered_powerprod_lin.Max (set c) \<in> set c" by simp
      ultimately show "ordered_powerprod_lin.Max (set c) \<in> ?B" ..
    qed
    ultimately obtain t where "t \<in> ?Q" and min: "\<And>s. s \<prec> t \<Longrightarrow> s \<notin> ?Q" by (rule wfP_onE_min, blast)
    from this(1) obtain z where "z \<in> Q" and "fst (snd (snd z)) \<noteq> []"
      and t: "t = ordered_powerprod_lin.Max (set (fst (snd (snd z))))" by blast
    show ?thesis
    proof (intro bexI ballI impI, rule)
      fix y
      assume "y \<in> ?A" and "(y, z) \<in> sym_preproc_aux_term1 d" and "y \<in> Q"
      from this(2) obtain t' where "t' \<in> set (fst (snd (snd z)))"
        and **: "\<And>s. s \<in> set (fst (snd (snd y))) \<Longrightarrow> s \<prec> t'"
        unfolding sym_preproc_aux_term1_def by auto
      from \<open>y \<in> Q\<close> have "fst (snd (snd y)) \<noteq> []" by (rule *)
      with \<open>y \<in> Q\<close> have "ordered_powerprod_lin.Max (set (fst (snd (snd y)))) \<in> ?Q" (is "?s \<in> _")
        by blast
      from \<open>fst (snd (snd y)) \<noteq> []\<close> have "?s \<in> set (fst (snd (snd y)))" by simp
      hence "?s \<prec> t'" by (rule **)
      also from \<open>t' \<in> set (fst (snd (snd z)))\<close> have "t' \<preceq> t" unfolding t
        using \<open>fst (snd (snd z)) \<noteq> []\<close> by simp
      finally have "?s \<notin> ?Q" by (rule min)
      from this \<open>?s \<in> ?Q\<close> show False ..
    qed fact
  qed
qed

lemma sym_preproc_aux_term_wf:
  assumes "dickson_grading (+) d"
  shows "wf (sym_preproc_aux_term d)"
proof (rule wfI_min)
  fix x::"(('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)" and Q
  assume "x \<in> Q"
  let ?A = "Keys (set (fst x)) \<union> set (fst (snd (snd x)))"
  have "finite ?A" by (simp add: finite_Keys)
  then obtain m where A: "?A \<subseteq> dgrad_set d m" by (rule dgrad_set_exhaust)
  let ?B = "dgrad_set d m"
  let ?Q = "{q \<in> Q. Keys (set (fst q)) \<union> set (fst (snd (snd q))) \<subseteq> ?B}"
  from assms have "wfP_on {x. set (fst (snd (snd x))) \<subseteq> ?B} (\<lambda>x y. (x, y) \<in> sym_preproc_aux_term1 d)"
    by (rule sym_preproc_aux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by simp
  moreover have "?Q \<subseteq> {x. set (fst (snd (snd x))) \<subseteq> ?B}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> sym_preproc_aux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "Keys (set (fst z)) \<union> set (fst (snd (snd z))) \<subseteq> ?B" by simp_all
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> sym_preproc_aux_term d \<longrightarrow> y \<notin> Q"
  proof (intro bexI allI impI)
    fix y
    assume "(y, z) \<in> sym_preproc_aux_term d"
    hence "(y, z) \<in> sym_preproc_aux_term1 d" and "(y, z) \<in> sym_preproc_aux_term2 d"
      by (simp_all add: sym_preproc_aux_term_def)
    from this(2) have "fst y = fst z"
      and "dgrad_set_le d (set (fst (snd (snd y)))) (Keys (set (fst z)) \<union> set (fst (snd (snd z))))"
      by (auto simp add: sym_preproc_aux_term2_def)
    from this(2) a have "set (fst (snd (snd y))) \<subseteq> ?B" by (rule dgrad_set_le_dgrad_set)
    hence "Keys (set (fst y)) \<union> set (fst (snd (snd y))) \<subseteq> ?B"
      using a by (auto simp add: \<open>fst y = fst z\<close>)
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
        sym_preproc_addnew gs (merge_wrt (\<succ>) ts (keys_to_list (tail f))) (insert_list f fs) t
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
    assume "s \<in> set (fst (sym_preproc_addnew gs (merge_wrt (\<succ>) ts (keys_to_list (tail (monom_mult 1 (t - lp g) g))))
                    (insert_list (monom_mult 1 (t - lp g) g) fs) t))"
    with _ show ?thesis
    proof (rule Cons(1))
      fix u
      assume "u \<in> set (merge_wrt (\<succ>) ts (keys_to_list (tail (monom_mult 1 (t - lp g) g))))"
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
  assumes "dickson_grading (+) d"
  shows "dgrad_set_le d (set (fst (sym_preproc_addnew gs ts fs t))) (Keys (set gs) \<union> insert t (set ts))"
proof (induct gs arbitrary: fs ts)
  case Nil
  show ?case by (auto intro: dgrad_set_le_subset)
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    assume "lp g adds t"
    let ?ts = "merge_wrt (\<succ>) ts (keys_to_list (tail (monom_mult 1 (t - lp g) g)))"
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
          from this keys_monom_mult_subset have "s \<in> plus (t - lp g) ` keys g" ..
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
    have "set ts \<subseteq> set (merge_wrt (\<succ>) ts (keys_to_list (tail f)))" by (auto simp add: set_merge_wrt)
    thus "set ts \<subseteq> set (fst (sym_preproc_addnew gs
                              (merge_wrt (\<succ>) ts (keys_to_list (tail f))) (insert_list f fs) t))"
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
                              (merge_wrt (\<succ>) ts (keys_to_list (tail f))) (insert_list f fs) t))"
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
    define ts' where "ts' = merge_wrt (\<succ>) ts (keys_to_list (tail f))"
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
  also have "... \<subseteq> ?r" by (fact ideal.generator_subset_module)
  finally have "set gs \<subseteq> ?r" .
  moreover have "?l \<subseteq> ?r"
  proof
    fix p
    assume "p \<in> ?l"
    thus "p \<in> ?r"
    proof (rule in_snd_sym_preproc_addnewE)
      assume "p \<in> set fs"
      hence "p \<in> set gs \<union> set fs" by simp
      thus ?thesis by (rule ideal.generator_in_module)
    next
      fix g s
      assume "g \<in> set gs" and p: "p = monom_mult 1 s g"
      from this(1) \<open>set gs \<subseteq> ?r\<close> have "g \<in> ?r" ..
      thus ?thesis unfolding p by (rule pideal_closed_monom_mult)
    qed
  qed
  ultimately have "set gs \<union> ?l \<subseteq> ?r" by blast
  thus "pideal (set gs \<union> ?l) \<subseteq> ?r" by (rule ideal.module_subset_moduleI)
next
  from snd_sym_preproc_addnew_superset have "set gs \<union> set fs \<subseteq> set gs \<union> ?l" by blast
  thus "?r \<subseteq> pideal (set gs \<union> ?l)" by (rule ideal.module_mono)
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
    define ts' where "ts' = merge_wrt (\<succ>) ts (keys_to_list (tail f))"
    define fs' where "fs' = insert_list f fs"
    have "keys (tail f) = keys f - {t}"
    proof (cases "g = 0")
      case True
      hence "f = 0" by (simp add: f_def monom_mult_right0)
      thus ?thesis by simp
    next
      case False
      hence "lp f = (t - lp g) + lp g" by (simp add: f_def lp_monom_mult)
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
      define ts' where "ts' = merge_wrt (\<succ>) ts (keys_to_list (tail (monom_mult 1 (t - lp g) g)))"
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

function sym_preproc_aux :: "('a \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<Rightarrow>
                              ('a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)" where
  "sym_preproc_aux gs ks (ts, fs) =
    (if ts = [] then
      (ks, fs)
    else
      let t = ordered_powerprod_lin.max_list ts; ts' = removeAll t ts in
        sym_preproc_aux gs (ks @ [t]) (sym_preproc_addnew gs ts' fs t)
    )"
  by pat_completeness auto
termination proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "(sym_preproc_aux_term d)::((('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                        ('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) set"
  show ?thesis
  proof
    from dg show "wf ?R" by (rule sym_preproc_aux_term_wf)
  next
    fix gs::"('a \<Rightarrow>\<^sub>0 'b) list" and ks ts fs t ts'
    assume "ts \<noteq> []" and "t = ordered_powerprod_lin.max_list ts" and ts': "ts' = removeAll t ts"
    from this(1, 2) have t: "t = ordered_powerprod_lin.Max (set ts)"
      by (simp add: ordered_powerprod_lin.max_list_Max)
    obtain ts0 fs0 where eq: "sym_preproc_addnew gs ts' fs t = (ts0, fs0)" by fastforce
    show "((gs, ks @ [t], sym_preproc_addnew gs ts' fs t), (gs, ks, ts, fs)) \<in> ?R"
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

lemma sym_preproc_aux_Nil: "sym_preproc_aux gs ks ([], fs) = (ks, fs)"
  by simp

lemma sym_preproc_aux_sorted:
  assumes "sorted_wrt (\<succ>) (t # ts)"
  shows "sym_preproc_aux gs ks (t # ts, fs) = sym_preproc_aux gs (ks @ [t]) (sym_preproc_addnew gs ts fs t)"
proof -
  have "transp (\<succ>)" using transp_def by fastforce
  from assms have *: "s \<in> set ts \<Longrightarrow> s \<prec> t" for s by (simp add: sorted_wrt_Cons[OF \<open>transp (\<succ>)\<close>])
  have "ordered_powerprod_lin.max_list (t # ts) = ordered_powerprod_lin.Max (set (t # ts))"
    by (simp add: ordered_powerprod_lin.max_list_Max del: ordered_powerprod_lin.max_list.simps)
  also have "... = t"
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
  finally have eq1: "ordered_powerprod_lin.max_list (t # ts) = t" .
  have eq2: "removeAll t (t # ts) = ts"
  proof (simp, rule removeAll_id, rule)
    assume "t \<in> set ts"
    hence "t \<prec> t" by (rule *)
    thus False ..
  qed
  show ?thesis by (simp only: sym_preproc_aux.simps eq1 eq2 Let_def, simp)
qed

lemma sym_preproc_aux_induct [consumes 0, case_names base rec]:
  assumes base: "\<And>ks fs. P ks [] fs (ks, fs)"
    and rec: "\<And>ks ts fs t ts'. ts \<noteq> [] \<Longrightarrow> t = ordered_powerprod_lin.Max (set ts) \<Longrightarrow> ts' = removeAll t ts \<Longrightarrow>
                P (ks @ [t]) (fst (sym_preproc_addnew gs ts' fs t)) (snd (sym_preproc_addnew gs ts' fs t))
                    (sym_preproc_aux gs (ks @ [t]) (sym_preproc_addnew gs ts' fs t)) \<Longrightarrow>
                P ks ts fs (sym_preproc_aux gs (ks @ [t]) (sym_preproc_addnew gs ts' fs t))"
  shows "P ks ts fs (sym_preproc_aux gs ks (ts, fs))"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "(sym_preproc_aux_term d)::((('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) \<times>
                                        ('a \<Rightarrow>\<^sub>0 'b) list \<times> 'a list \<times> 'a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list) set"
  define args where "args = (gs, ks, ts, fs)"
  from dg have "wf ?R" by (rule sym_preproc_aux_term_wf)
  hence "fst args = gs \<Longrightarrow> P (fst (snd args)) (fst (snd (snd args))) (snd (snd (snd args)))
                              (sym_preproc_aux gs (fst (snd args)) (snd (snd args)))"
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> sym_preproc_aux_term d \<Longrightarrow> fst y = gs \<Longrightarrow>
                    P (fst (snd y)) (fst (snd (snd y))) (snd (snd (snd y)))
                      (sym_preproc_aux gs (fst (snd y)) (snd (snd y)))"
    assume "fst x = gs"
    then obtain x0 where x: "x = (gs, x0)" by (meson eq_fst_iff)
    obtain ks x1 where x0: "x0 = (ks, x1)" by (meson case_prodE case_prodI2)
    obtain ts fs where x1: "x1 = (ts, fs)" by (meson case_prodE case_prodI2)
    from IH' have IH: "\<And>ks' n. ((gs, ks', n), (gs, ks, ts, fs)) \<in> sym_preproc_aux_term d \<Longrightarrow>
                            P ks' (fst n) (snd n) (sym_preproc_aux gs ks' n)"
      unfolding x x0 x1 by fastforce
    show "P (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x)))
            (sym_preproc_aux gs (fst (snd x)) (snd (snd x)))"
    proof (simp add: x x0 x1 Let_def, intro conjI impI)
      show "P ks [] fs (ks, fs)" by (fact base)
    next
      assume "ts \<noteq> []"
      define t where "t = ordered_powerprod_lin.max_list ts"
      from \<open>ts \<noteq> []\<close> have t_alt: "t = ordered_powerprod_lin.Max (set ts)" unfolding t_def
        by (rule ordered_powerprod_lin.max_list_Max)
      define ts' where "ts' = removeAll t ts"
      show "P ks ts fs (sym_preproc_aux gs (ks @ [t]) (sym_preproc_addnew gs ts' fs t))"
      proof (rule rec, fact \<open>ts \<noteq> []\<close>, fact t_alt, fact ts'_def)
        let ?n = "sym_preproc_addnew gs ts' fs t"
        obtain ts0 fs0 where eq: "?n = (ts0, fs0)" by fastforce
        show "P (ks @ [t]) (fst ?n) (snd ?n) (sym_preproc_aux gs (ks @ [t]) ?n)"
        proof (rule IH,
              simp add: eq sym_preproc_aux_term_def sym_preproc_aux_term1_def sym_preproc_aux_term2_def,
              intro conjI bexI ballI)
          fix s
          assume "s \<in> set ts0"
          show "s \<prec> t"
          proof (rule fst_sym_preproc_addnew_less)
            fix u
            assume "u \<in> set ts'"
            thus "u \<prec> t" unfolding ts'_def t_alt set_removeAll using ordered_powerprod_lin.antisym_conv1
              by fastforce
          next
            from \<open>s \<in> set ts0\<close> show "s \<in> set (fst (sym_preproc_addnew gs ts' fs t))" by (simp add: eq)
          qed
        next
          from \<open>ts \<noteq> []\<close> show "t \<in> set ts" by (simp add: t_alt)
        next
          from dg have "dgrad_set_le d (set (fst (sym_preproc_addnew gs ts' fs t))) (Keys (set gs) \<union> insert t (set ts'))"
            by (rule fst_sym_preproc_addnew_dgrad_set_le)
          moreover have "insert t (set ts') = set ts" by (auto simp add: ts'_def t_alt \<open>ts \<noteq> []\<close>)
          ultimately show "dgrad_set_le d (set ts0) (Keys (set gs) \<union> set ts)" by (simp add: eq)
        qed
      qed
    qed
  qed
  thus ?thesis by (simp add: args_def)
qed

lemma fst_sym_preproc_aux_sorted_wrt:
  assumes "sorted_wrt (\<succ>) ks" and "\<And>k t. k \<in> set ks \<Longrightarrow> t \<in> set ts \<Longrightarrow> t \<prec> k"
  shows "sorted_wrt (\<succ>) (fst (sym_preproc_aux gs ks (ts, fs)))"
  using assms
proof (induct gs ks ts fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  from base(1) show ?case by simp
next
  case (rec ks ts fs t ts')
  from rec(1) have "t \<in> set ts" by (simp add: rec(2))
  from rec(1) have *: "\<And>u. u \<in> set ts' \<Longrightarrow> u \<prec> t" unfolding rec(2, 3) set_removeAll
    using ordered_powerprod_lin.antisym_conv3 by force
  show ?case
  proof (rule rec(4))
    have tr: "transp (\<succ>)" unfolding transp_def by fastforce
    show "sorted_wrt (\<succ>) (ks @ [t])"
    proof (simp add: sorted_wrt_append[OF tr] rec(5), rule)
      fix k
      assume "k \<in> set ks"
      from this \<open>t \<in> set ts\<close> show "t \<prec> k" by (rule rec(6))
    qed
  next
    fix k s
    assume "k \<in> set (ks @ [t])" and "s \<in> set (fst (sym_preproc_addnew gs ts' fs t))"
    from * this(2) have "s \<prec> t" by (rule fst_sym_preproc_addnew_less)
    from \<open>k \<in> set (ks @ [t])\<close> have "k \<in> set ks \<or> k = t" by auto
    thus "s \<prec> k"
    proof
      assume "k \<in> set ks"
      from this \<open>t \<in> set ts\<close> have "t \<prec> k" by (rule rec(6))
      with \<open>s \<prec> t\<close> show ?thesis by simp
    next
      assume "k = t"
      with \<open>s \<prec> t\<close> show ?thesis by simp
    qed
  qed
qed

lemma fst_sym_preproc_aux_complete:
  assumes "Keys (set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list)) = set ks \<union> set ts"
  shows "set (fst (sym_preproc_aux gs ks (ts, fs))) = Keys (set (snd (sym_preproc_aux gs ks (ts, fs))))"
  using assms
proof (induct gs ks ts fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  thus ?case by simp
next
  case (rec ks ts fs t ts')
  from rec(1) have "t \<in> set ts" by (simp add: rec(2))
  hence eq: "insert t (set ts') = set ts" by (auto simp add: rec(3))
  also from rec(5) have "... \<subseteq> Keys (set fs)" by simp
  also from snd_sym_preproc_addnew_superset have "... \<subseteq> Keys (set (snd (sym_preproc_addnew gs ts' fs t)))"
    by (rule Keys_mono)
  finally have "... = ... \<union> (insert t (set ts'))" by blast
  also have "... = Keys (set fs) \<union> insert t (set (fst (sym_preproc_addnew gs ts' fs t)))"
    by (fact Keys_snd_sym_preproc_addnew)
  also have "... = (set ks \<union> (insert t (set ts'))) \<union> (insert t (set (fst (sym_preproc_addnew gs ts' fs t))))"
    by (simp only: rec(5) eq)
  also have "... = set (ks @ [t]) \<union> (set ts' \<union> set (fst (sym_preproc_addnew gs ts' fs t)))" by auto
  also from fst_sym_preproc_addnew_superset have "... = set (ks @ [t]) \<union> set (fst (sym_preproc_addnew gs ts' fs t))"
    by blast
  finally show ?case by (rule rec(4))
qed

lemma snd_sym_preproc_aux_superset: "set fs \<subseteq> set (snd (sym_preproc_aux gs ks (ts, fs)))"
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  show ?case by simp
next
  case (rec ks ts fs t ts')
  from snd_sym_preproc_addnew_superset rec(4) show ?case by (rule subset_trans)
qed

lemma in_snd_sym_preproc_auxE:
  assumes "p \<in> set (snd (sym_preproc_aux gs ks (ts, fs)))"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g t. g \<in> set gs \<Longrightarrow> p = monom_mult 1 t g \<Longrightarrow> thesis"
  shows thesis
  using assms
proof (induct gs ks ts fs arbitrary: thesis rule: sym_preproc_aux_induct)
  case (base ks fs)
  from base(1) have "p \<in> set fs" by simp
  thus ?case by (rule base(2))
next
  case (rec ks ts fs t ts')
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

lemma snd_sym_preproc_aux_pideal:
  "pideal (set gs \<union> set (snd (sym_preproc_aux gs ks (ts, fs)))) = pideal (set gs \<union> set fs)"
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  show ?case by simp
next
  case (rec ks ts fs t ts')
  from rec(4) sym_preproc_addnew_pideal show ?case by (rule trans)
qed

lemma snd_sym_preproc_aux_dgrad_set_le:
  assumes "dickson_grading (+) d" and "set ts \<subseteq> Keys (set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  shows "dgrad_set_le d (Keys (set (snd (sym_preproc_aux gs ks (ts, fs))))) (Keys (set gs \<union> set fs))"
  using assms(2)
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  show ?case by (rule dgrad_set_le_subset, simp add: Keys_Un)
next
  case (rec ks ts fs t ts')
  let ?n = "sym_preproc_addnew gs ts' fs t"
  from rec(1) have "t \<in> set ts" by (simp add: rec(2))
  hence set_ts: "insert t (set ts') = set ts" by (auto simp add: rec(3))
  from rec(5) have eq: "Keys (set fs) \<union> (Keys (set gs) \<union> set ts) = Keys (set gs) \<union> Keys (set fs)"
    by blast
  have "dgrad_set_le d (Keys (set (snd (sym_preproc_aux gs (ks @ [t]) ?n)))) (Keys (set gs \<union> set (snd ?n)))"
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

lemma snd_sym_preproc_aux_complete:
  assumes "\<And>s' g'. s' \<in> Keys (set fs) \<Longrightarrow> s' \<notin> set ts \<Longrightarrow> g' \<in> set gs \<Longrightarrow> lp g' adds s' \<Longrightarrow>
            monom_mult 1 (s' - lp g') g' \<in> set fs"
  assumes "s \<in> Keys (set (snd (sym_preproc_aux gs ks (ts, fs))))" and "g \<in> set gs" and "lp g adds s"
  shows "monom_mult (1::'b::semiring_1_no_zero_divisors) (s - lp g) g \<in> set (snd (sym_preproc_aux gs ks (ts, fs)))"
  using assms
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  from base(2) have "s \<in> Keys (set fs)" by simp
  from this _ base(3, 4) have "monom_mult 1 (s - lp g) g \<in> set fs"
  proof (rule base(1))
    show "s \<notin> set []" by simp
  qed
  thus ?case by simp
next
  case (rec ks ts fs t ts')
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

definition sym_preproc :: "('a \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a list \<times> ('a \<Rightarrow>\<^sub>0 'b) list)"
  where "sym_preproc gs fs = sym_preproc_aux gs [] (Keys_to_list fs, fs)"

lemma sym_preproc_Nil [simp]: "sym_preproc gs [] = ([], [])"
  by (simp add: sym_preproc_def)

lemma fst_sym_preproc:
  "fst (sym_preproc gs fs) = Keys_to_list (snd (sym_preproc gs (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list)))"
proof -
  let ?a = "fst (sym_preproc gs fs)"
  let ?b = "Keys_to_list (snd (sym_preproc gs fs))"
  have "antisymp (\<succ>)" unfolding antisymp_def by fastforce
  have "irreflp (\<succ>)" by (simp add: irreflp_def)
  moreover have "transp (\<succ>)" unfolding transp_def by fastforce
  moreover have s1: "sorted_wrt (\<succ>) ?a" unfolding sym_preproc_def
    by (rule fst_sym_preproc_aux_sorted_wrt, simp_all)
  ultimately have d1: "distinct ?a" by (rule distinct_sorted_wrt_irrefl)
  have s2: "sorted_wrt (\<succ>) ?b" by (fact Keys_to_list_sorted_wrt)
  with \<open>irreflp (\<succ>)\<close> \<open>transp (\<succ>)\<close> have d2: "distinct ?b" by (rule distinct_sorted_wrt_irrefl)
  from \<open>transp (\<succ>)\<close> \<open>antisymp (\<succ>)\<close> s1 d1 s2 d2 show ?thesis
  proof (rule sorted_wrt_distinct_set_unique)
    show "set ?a = set ?b" unfolding set_Keys_to_list sym_preproc_def
      by (rule fst_sym_preproc_aux_complete, simp add: set_Keys_to_list)
  qed
qed

lemma snd_sym_preproc_superset: "set fs \<subseteq> set (snd (sym_preproc gs fs))"
  by (simp only: sym_preproc_def snd_conv, fact snd_sym_preproc_aux_superset)

lemma in_snd_sym_preprocE:
  assumes "p \<in> set (snd (sym_preproc gs fs))"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g t. g \<in> set gs \<Longrightarrow> p = monom_mult 1 t g \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding sym_preproc_def snd_conv by (rule in_snd_sym_preproc_auxE)

lemma snd_sym_preproc_pideal: "pideal (set gs \<union> set (snd (sym_preproc gs fs))) = pideal (set gs \<union> set fs)"
  unfolding sym_preproc_def snd_conv by (fact snd_sym_preproc_aux_pideal)

lemma snd_sym_preproc_dgrad_set_le:
  assumes "dickson_grading (+) d"
  shows "dgrad_set_le d (Keys (set (snd (sym_preproc gs fs))))
                        (Keys (set gs \<union> set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list)))"
  unfolding sym_preproc_def snd_conv using assms
proof (rule snd_sym_preproc_aux_dgrad_set_le)
  show "set (Keys_to_list fs) \<subseteq> Keys (set fs)" by (simp add: set_Keys_to_list)
qed

corollary snd_sym_preproc_dgrad_p_set_le:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d (set (snd (sym_preproc gs fs))) (set gs \<union> set (fs::('a \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  unfolding dgrad_p_set_le_def
proof -
  from assms show "dgrad_set_le d (Keys (set (snd (sym_preproc gs fs)))) (Keys (set gs \<union> set fs))"
    by (rule snd_sym_preproc_dgrad_set_le)
qed

lemma snd_sym_preproc_complete:
  assumes "t \<in> Keys (set (snd (sym_preproc gs fs)))" and "g \<in> set gs" and "lp g adds t"
  shows "monom_mult (1::'b::semiring_1_no_zero_divisors) (t - lp g) g \<in> set (snd (sym_preproc gs fs))"
  using _ assms unfolding sym_preproc_def snd_conv
proof (rule snd_sym_preproc_aux_complete)
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

lemma phull_closed_lin_red:
  assumes "phull B \<subseteq> phull A" and "p \<in> phull A" and "lin_red B p q"
  shows "q \<in> phull A"
proof -
  from assms(3) obtain f where "f \<in> B" and "red_single p q f 0" by (rule lin_redE)
  hence q: "q = p - monom_mult (lookup p (lp f) / lc f) 0 f" by (simp add: red_single_def)
  have "q - p \<in> phull B"
    by (simp add: q, rule phull.module_closed_uminus, rule phull.module_closed_smult, rule phull.generator_in_module,
        fact \<open>f \<in> B\<close>)
  with assms(1) have "q - p \<in> phull A" ..
  from this assms(2) have "(q - p) + p \<in> phull A" by (rule phull.module_closed_plus)
  thus ?thesis by simp
qed

subsection \<open>Reduction\<close>

definition Macaulay_red :: "'a list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "Macaulay_red ts fs =
     (let lps = map lp (filter (\<lambda>p. p \<noteq> 0) fs) in
       filter (\<lambda>p. p \<noteq> 0 \<and> lp p \<notin> set lps) (mat_to_polys ts (row_echelon (polys_to_mat ts fs)))
     )"

text \<open>@{term "Macaulay_red ts fs"} auto-reduces (w.\,r.\,t. @{const lin_red}) the given list @{term fs}
  and returns those non-zero polynomials whose leading power-products are not in @{term "lp_set (set fs)"}.
  Argument @{term ts} is expected to be @{term "Keys_to_list fs"}; this list is passed as an argument
  to @{const Macaulay_red}, because it can be efficiently computed by symbolic preprocessing.\<close>

lemma Macaulay_red_alt:
  "Macaulay_red (Keys_to_list fs) fs = filter (\<lambda>p. lp p \<notin> lp_set (set fs)) (Macaulay_list fs)"
proof -
  have "{x \<in> set fs. x \<noteq> 0} = set fs - {0}" by blast
  thus ?thesis by (simp add: Macaulay_red_def Macaulay_list_def Macaulay_mat_def lp_set_def Let_def)
qed

lemma set_Macaulay_red:
  "set (Macaulay_red (Keys_to_list fs) fs) = set (Macaulay_list fs) - {p. lp p \<in> lp_set (set fs)}"
  by (auto simp add: Macaulay_red_alt)

lemma Keys_Macaulay_red: "Keys (set (Macaulay_red (Keys_to_list fs) fs)) \<subseteq> Keys (set fs)"
proof -
  have "Keys (set (Macaulay_red (Keys_to_list fs) fs)) \<subseteq> Keys (set (Macaulay_list fs))"
    unfolding set_Macaulay_red by (fact Keys_minus)
  also have "... \<subseteq> Keys (set fs)" by (fact Keys_Macaulay_list)
  finally show ?thesis .
qed

end (* ordered_powerprod *)

context gd_powerprod
begin

lemma Macaulay_red_reducible:
  assumes "f \<in> phull (set fs)" and "F \<subseteq> set fs" and "lp_set F = lp_set (set fs)"
  shows "(lin_red (F \<union> set (Macaulay_red (Keys_to_list fs) fs)))\<^sup>*\<^sup>* f 0"
proof -
  define A where "A = F \<union> set (Macaulay_red (Keys_to_list fs) fs)"

  have phull_A: "phull A \<subseteq> phull (set fs)"
  proof (rule phull.module_subset_moduleI, simp add: A_def, rule)
    have "F \<subseteq> phull F" by (rule phull.generator_subset_module)
    also from assms(2) have "... \<subseteq> phull (set fs)" by (rule phull.module_mono)
    finally show "F \<subseteq> phull (set fs)" .
  next
    have "set (Macaulay_red (Keys_to_list fs) fs) \<subseteq> set (Macaulay_list fs)"
      by (auto simp add: set_Macaulay_red)
    also have "... \<subseteq> phull (set (Macaulay_list fs))" by (rule phull.generator_subset_module)
    also have "... = phull (set fs)" by (rule phull_Macaulay_list)
    finally show "set (Macaulay_red (Keys_to_list fs) fs) \<subseteq> phull (set fs)" .
  qed

  have lp_A: "p \<in> phull (set fs) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> (\<And>g. g \<in> A \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> lp g = lp p \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    for p thesis
  proof -
    assume "p \<in> phull (set fs)" and "p \<noteq> 0"
    then obtain g where g_in: "g \<in> set (Macaulay_list fs)" and "g \<noteq> 0" and "lp p = lp g"
      by (rule Macaulay_list_lp)
    assume *: "\<And>g. g \<in> A \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> lp g = lp p \<Longrightarrow> thesis"
    show ?thesis
    proof (cases "g \<in> set (Macaulay_red (Keys_to_list fs) fs)")
      case True
      hence "g \<in> A" by (simp add: A_def)
      from this \<open>g \<noteq> 0\<close> \<open>lp p = lp g\<close>[symmetric] show ?thesis by (rule *)
    next
      case False
      with g_in have "lp g \<in> lp_set (set fs)" by (simp add: set_Macaulay_red)
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

  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  from fin_A have "finite (insert f A)" ..
  then obtain m where "insert f A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  hence A_sub: "A \<subseteq> dgrad_p_set d m" and "f \<in> dgrad_p_set d m" by simp_all
  from dg have "wfP (dickson_less_p d m)" by (rule dickson_less_p_wf)
  from this assms(1) \<open>f \<in> dgrad_p_set d m\<close> show "(lin_red A)\<^sup>*\<^sup>* f 0"
  proof (induct f)
    fix p
    assume IH: "\<And>q. dickson_less_p d m q p \<Longrightarrow> q \<in> phull (set fs) \<Longrightarrow> q \<in> dgrad_p_set d m \<Longrightarrow>
                    (lin_red A)\<^sup>*\<^sup>* q 0"
      and "p \<in> phull (set fs)" and "p \<in> dgrad_p_set d m"
    show "(lin_red A)\<^sup>*\<^sup>* p 0"
    proof (cases "p = 0")
      case True
      thus ?thesis by simp
    next
      case False
      with \<open>p \<in> phull (set fs)\<close> obtain g where "g \<in> A" and "g \<noteq> 0" and "lp g = lp p" by (rule lp_A)
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
        moreover from phull_A \<open>p \<in> phull (set fs)\<close> lr have "q \<in> phull (set fs)"
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

definition f4_red_aux :: "('a, 'b::field, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                          ('a \<Rightarrow>\<^sub>0 'b) list"
  where "f4_red_aux bs ps =
            (let aux = sym_preproc (map fst bs) (pdata_pairs_to_list ps) in Macaulay_red (fst aux) (snd aux))"

text \<open>@{const f4_red_aux} only takes two arguments, since it does not distinguish between those
  elements of the current basis that are known to be a Gr\"obner basis (called ``gs'' in
  @{theory Algorithm_Schema}) and the remaining ones.\<close>

lemma f4_red_aux_not_zero: "0 \<notin> set (f4_red_aux bs ps)"
  by (simp add: f4_red_aux_def Let_def fst_sym_preproc set_Macaulay_red set_Macaulay_list)

lemma f4_red_aux_irredudible:
  assumes "h \<in> set (f4_red_aux bs ps)" and "b \<in> set bs" and "fst b \<noteq> 0"
  shows "\<not> lp (fst b) adds lp h"
proof
  from assms(1) f4_red_aux_not_zero have "h \<noteq> 0" by metis
  hence "lp h \<in> keys h" by (rule lp_in_keys)
  also from assms(1) have "... \<subseteq> Keys (set (f4_red_aux bs ps))" by (rule keys_subset_Keys)
  also have "... \<subseteq> Keys (set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    (is "_ \<subseteq> Keys (set ?s)") by (simp only: f4_red_aux_def Let_def fst_sym_preproc Keys_Macaulay_red)
  finally have "lp h \<in> Keys (set ?s)" .
  moreover from assms(2) have "fst b \<in> set (map fst bs)" by auto
  moreover assume a: "lp (fst b) adds lp h"
  ultimately have "monom_mult 1 (lp h - lp (fst b)) (fst b) \<in> set ?s" (is "?m \<in> _")
    by (rule snd_sym_preproc_complete)
  from assms(3) have "?m \<noteq> 0" by (simp add: monom_mult_0_iff)
  with \<open>?m \<in> set ?s\<close> have "lp ?m \<in> lp_set (set ?s)" by (rule lp_setI)
  moreover from assms(3) a have "lp ?m = lp h" by (simp add: lp_monom_mult adds_minus)
  ultimately have "lp h \<in> lp_set (set ?s)" by simp
  moreover from assms(1) have "lp h \<notin> lp_set (set ?s)"
    by (simp add: f4_red_aux_def Let_def fst_sym_preproc set_Macaulay_red)
  ultimately show False by simp
qed

lemma f4_red_aux_dgrad_p_set_le:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d (set (f4_red_aux bs ps)) (args_to_set ([], bs, ps))"
  unfolding dgrad_p_set_le_def dgrad_set_le_def
proof
  fix s
  assume "s \<in> Keys (set (f4_red_aux bs ps))"
  also have "... \<subseteq> Keys (set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    (is "_ \<subseteq> Keys (set ?s)") by (simp only: f4_red_aux_def Let_def fst_sym_preproc Keys_Macaulay_red)
  finally have "s \<in> Keys (set ?s)" .
  with snd_sym_preproc_dgrad_set_le[OF assms] obtain t
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

lemma pideal_f4_red_aux: "set (f4_red_aux bs ps) \<subseteq> pideal (args_to_set ([], bs, ps))"
proof -
  have "set (f4_red_aux bs ps) \<subseteq>
          set (Macaulay_list (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (auto simp add: f4_red_aux_def Let_def fst_sym_preproc set_Macaulay_red)
  also have "... \<subseteq> pideal (set (Macaulay_list (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps)))))"
    by (fact ideal.generator_subset_module)
  also have "... = pideal (set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (fact pideal_Macaulay_list)
  also have "... \<subseteq> pideal (set (map fst bs) \<union>
                        set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (rule ideal.module_mono, blast)
  also have "... = pideal (set (map fst bs) \<union> set (pdata_pairs_to_list ps))"
    by (fact snd_sym_preproc_pideal)
  also have "... \<subseteq> pideal (args_to_set ([], bs, ps))"
  proof (rule ideal.module_subset_moduleI, simp only: Un_subset_iff, rule conjI)
    have "set (map fst bs) \<subseteq> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_def)
    also have "... \<subseteq> pideal (args_to_set ([], bs, ps))" by (rule ideal.generator_subset_module)
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
      hence "fst f \<in> pideal (args_to_set ([], bs, ps))" by (rule ideal.generator_in_module)
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
  define fs where "fs = snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))"
  have "set (pdata_pairs_to_list ps) \<subseteq> set fs" unfolding fs_def by (fact snd_sym_preproc_superset)
  hence "phull (set (pdata_pairs_to_list ps)) \<subseteq> phull (set fs)" by (rule phull.module_mono)
  with assms(2) have f_in: "f \<in> phull (set fs)" ..
  have eq: "(set fs) \<union> set (f4_red_aux bs ps) = (set fs) \<union> set (Macaulay_red (Keys_to_list fs) fs)"
    by (simp add: f4_red_aux_def fs_def Let_def fst_sym_preproc)

  have "(lin_red ((set fs) \<union> set (f4_red_aux bs ps)))\<^sup>*\<^sup>* f 0"
    by (simp only: eq, rule Macaulay_red_reducible, fact f_in, fact subset_refl, fact refl)
  thus ?thesis
  proof induct
    case base
    show ?case ..
  next
    case (step y z)
    from step(2) have "red (fst ` set bs \<union> set (f4_red_aux bs ps)) y z" unfolding lin_red_Un
    proof
      assume "lin_red (set fs) y z"
      then obtain a where "a \<in> set fs" and r: "red_single y z a 0" by (rule lin_redE)
      from this(1) obtain b c t where "b \<in> fst ` set bs" and a: "a = monom_mult c t b" unfolding fs_def
      proof (rule in_snd_sym_preprocE)
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
        by (simp add: a red_single_def monom_mult_0_iff lp_monom_mult[OF \<open>c \<noteq> 0\<close> \<open>b \<noteq> 0\<close>]
                      lc_monom_mult monom_mult_assoc)
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
    by (auto intro: phull.generator_in_module)
  hence "?p - ?q \<in> phull (set (pdata_pairs_to_list ps))" by (rule phull.module_closed_minus)
  thus "spoly (fst p) (fst q) \<in> phull (set (pdata_pairs_to_list ps))" by (simp only: spoly_def)
qed

definition f4_red :: "('a, 'b::field, 'c::default, 'd) rcpT"
  where "f4_red gs bs ps data = (map (\<lambda>h. (h, default)) (f4_red_aux (gs @ bs) ps), snd data)"

lemma fst_set_fst_f4_red: "fst ` set (fst (f4_red gs bs ps data)) = set (f4_red_aux (gs @ bs) ps)"
  by (simp add: f4_red_def, force)

lemma rcp_spec_f4_red: "rcp_spec f4_red"
proof (rule rcp_specI)
  fix gs bs::"('a, 'b, 'c) pdata list" and ps and data::"nat \<times> 'd"
  show "0 \<notin> fst ` set (fst (f4_red gs bs ps data))"
    by (simp add: fst_set_fst_f4_red f4_red_aux_not_zero)
next
  fix gs bs::"('a, 'b, 'c) pdata list" and ps h b and data::"nat \<times> 'd"
  assume "h \<in> set (fst (f4_red gs bs ps data))" and "b \<in> set bs"
  from this(1) have "fst h \<in> fst ` set (fst (f4_red gs bs ps data))" by simp
  hence "fst h \<in> set (f4_red_aux (gs @ bs) ps)" by (simp only: fst_set_fst_f4_red)
  moreover from \<open>b \<in> set bs\<close> have "b \<in> set (gs @ bs)" by simp
  moreover assume "fst b \<noteq> 0"
  ultimately show "\<not> lp (fst b) adds lp (fst h)" by (rule f4_red_aux_irredudible)
next
  fix gs bs::"('a, 'b, 'c) pdata list" and ps and d::"'a \<Rightarrow> nat" and data::"nat \<times> 'd"
  assume "dickson_grading (+) d"
  hence "dgrad_p_set_le d (set (f4_red_aux (gs @ bs) ps)) (args_to_set ([], gs @ bs, ps))"
    by (fact f4_red_aux_dgrad_p_set_le)
  also have "... = args_to_set (gs, bs, ps)" by (simp add: args_to_set_alt image_Un)
  finally show "dgrad_p_set_le d (fst ` set (fst (f4_red gs bs ps data))) (args_to_set (gs, bs, ps))"
    by (simp only: fst_set_fst_f4_red)
next
  fix gs bs::"('a, 'b, 'c) pdata list" and ps and data::"nat \<times> 'd"
  have "set (f4_red_aux (gs @ bs) ps) \<subseteq> pideal (args_to_set ([], gs @ bs, ps))"
    by (fact pideal_f4_red_aux)
  also have "... = pideal (args_to_set (gs, bs, ps))" by (simp add: args_to_set_alt image_Un)
  finally have "fst ` set (fst (f4_red gs bs ps data)) \<subseteq> pideal (args_to_set (gs, bs, ps))"
    by (simp only: fst_set_fst_f4_red)
  moreover {
    fix p q :: "('a, 'b, 'c) pdata"
    assume "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    hence "set ps \<subseteq> set (gs @ bs) \<times> set (gs @ bs)" by fastforce
    moreover assume "(p, q) \<in> set ps"
    ultimately have "(red (fst ` set (gs @ bs) \<union> set (f4_red_aux (gs @ bs) ps)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
      by (rule f4_red_aux_spoly_reducible)
  }
  ultimately show
    "fst ` set (fst (f4_red gs bs ps data)) \<subseteq> pideal (args_to_set (gs, bs, ps)) \<and>
     (\<forall>(p, q)\<in>set ps.
         set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
         (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (f4_red gs bs ps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0)"
    by (auto simp add: image_Un fst_set_fst_f4_red)
qed

subsection \<open>Pair Selection\<close>

primrec f4_sel_aux :: "'a \<Rightarrow> ('a, 'b::zero, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list" where
  "f4_sel_aux _ [] = []"|
  "f4_sel_aux t (p # ps) =
    (if (lcs (lp (fst (fst p))) (lp (fst (snd p)))) = t then
      p # (f4_sel_aux t ps)
    else
      []
    )"

lemma f4_sel_aux_subset: "set (f4_sel_aux t ps) \<subseteq> set ps"
  by (induct ps, auto)

primrec f4_sel :: "('a, 'b::zero, 'c, 'd) selT" where
  "f4_sel gs bs [] data = []"|
  "f4_sel gs bs (p # ps) data = p # (f4_sel_aux (lcs (lp (fst (fst p))) (lp (fst (snd p)))) ps)"

lemma sel_spec_f4_sel: "sel_spec f4_sel"
proof (rule sel_specI)
  fix gs bs :: "('a, 'b, 'c) pdata list" and ps::"('a, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "ps \<noteq> []"
  then obtain p ps' where ps: "ps = p # ps'" by (meson list.exhaust)
  show "f4_sel gs bs ps data \<noteq> [] \<and> set (f4_sel gs bs ps data) \<subseteq> set ps"
  proof
    show "f4_sel gs bs ps data \<noteq> []" by (simp add: ps)
  next
    from f4_sel_aux_subset show "set (f4_sel gs bs ps data) \<subseteq> set ps" by (auto simp add: ps)
  qed
qed

subsection \<open>The F4 Algorithm\<close>

text \<open>The F4 algorithm is just @{const gb_schema_direct} with parameters instantiated by suitable
  functions.\<close>

abbreviation "f4_ap \<equiv> add_pairs_sorted canon_pair_order"
abbreviation "f4_ab \<equiv> add_basis_sorted canon_basis_order"
abbreviation "f4_compl \<equiv> discard_red_cp pc_crit f4_red"

lemma struct_spec_f4: "struct_spec f4_sel f4_ap f4_ab f4_compl"
  using sel_spec_f4_sel ap_spec_add_pairs_sorted ab_spec_add_basis_sorted
proof (rule struct_specI)
  from rcp_spec_f4_red show "compl_struct f4_compl" by (rule compl_struct_discard_red_cp)
qed

lemmas compl_conn_f4_compl = compl_conn_discard_red_cp[OF crit_spec_pc_crit rcp_spec_f4_red]

lemmas compl_pideal_f4_compl = compl_pideal_discard_red_cp[OF rcp_spec_f4_red]

definition f4_aux :: "nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                   ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b::field, 'c::default) pdata list"
  where "f4_aux = gb_schema_aux f4_sel f4_ap f4_ab f4_compl"

lemmas f4_aux_simps [code] = gb_schema_aux_simp[OF struct_spec_f4, folded f4_aux_def]

definition f4 :: "('a, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('a, 'b::field, 'c::default) pdata' list"
  where "f4 = gb_schema_direct f4_sel f4_ap f4_ab f4_compl"

lemmas f4_simps [code] = gb_schema_direct_def[of "f4_sel" "f4_ap" "f4_ab" "f4_compl", folded f4_def f4_aux_def]

lemmas f4_isGB = gb_schema_direct_isGB[OF struct_spec_f4 compl_conn_f4_compl, folded f4_def]

lemmas f4_pideal = gb_schema_direct_pideal[OF struct_spec_f4 compl_pideal_f4_compl, folded f4_def]

end (* gd_powerprod *)

end (* theory *)
