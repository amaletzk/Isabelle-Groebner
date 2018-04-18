(* Author: Alexander Maletzky *)

section \<open>A General Algorithm Schema for Computing Gr\"obner Bases\<close>

theory Algorithm_Schema
  imports Groebner_Bases.General "Groebner_Bases"
begin

text \<open>This theory formalizes a general algorithm schema for computing Gr\"obner bases, generalizing
  Buchberger's original critical-pair/completion algorithm. The algorithm schema depends on several
  functional parameters that can be instantiated by a variety of concrete functions. Possible instances
  yield Buchberger's algorithm, Faug\`ere's F4 algorithm, and (as far as we can tell) even his F5
  algorithm.
  The fact that Buchberger's algorithm is an instance of the algorithm schema formalizes here implies
  that sooner or later theory "Groebner_Bases.Buchberger_Algorithm" might be superseded by this
  theory.\<close>

subsection \<open>@{term processed}\<close>

definition processed :: "('a \<times> 'a) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"
  where "processed p xs ps \<longleftrightarrow> fst p \<in> set xs \<and> snd p \<in> set xs \<and> p \<notin> set ps \<and> (snd p, fst p) \<notin> set ps"

lemma processed_alt:
  "processed (a, b) xs ps \<longleftrightarrow> ((a \<in> set xs) \<and> (b \<in> set xs) \<and> (a, b) \<notin> set ps \<and> (b, a) \<notin> set ps)"
  unfolding processed_def by auto

lemma processedI:
  assumes "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin> set ps" and "(b, a) \<notin> set ps"
  shows "processed (a, b) xs ps"
  unfolding processed_alt using assms by simp

lemma processedD1:
  assumes "processed (a, b) xs ps"
  shows "a \<in> set xs"
  using assms by (simp add: processed_alt)

lemma processedD2:
  assumes "processed (a, b) xs ps"
  shows "b \<in> set xs"
  using assms by (simp add: processed_alt)

lemma processedD3:
  assumes "processed (a, b) xs ps"
  shows "(a, b) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processedD4:
  assumes "processed (a, b) xs ps"
  shows "(b, a) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processed_Nil: "processed (a, b) xs [] \<longleftrightarrow> (a \<in> set xs \<and> b \<in> set xs)"
  by (simp add: processed_alt)

lemma processed_Cons:
  assumes "processed (a, b) xs ps"
    and a1: "a = p \<Longrightarrow> b = q \<Longrightarrow> thesis"
    and a2: "a = q \<Longrightarrow> b = p \<Longrightarrow> thesis"
    and a3: "processed (a, b) xs ((p, q) # ps) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin> set ps" and "(b, a) \<notin> set ps"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(a, b) = (p, q)")
    case True
    hence "a = p" and "b = q" by simp_all
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(a, b) \<notin> set ps\<close> have *: "(a, b) \<notin> set ((p, q) # ps)" by auto
    show ?thesis
    proof (cases "(b, a) = (p, q)")
      case True
      hence "a = q" and "b = p" by simp_all
      thus ?thesis by (rule a2)
    next
      case False
      with \<open>(b, a) \<notin> set ps\<close> have "(b, a) \<notin> set ((p, q) # ps)" by auto
      with \<open>a \<in> set xs\<close> \<open>b \<in> set xs\<close> * have "processed (a, b) xs ((p, q) # ps)"
        by (rule processedI)
      thus ?thesis by (rule a3)
    qed
  qed
qed

lemma processed_minus:
  assumes "processed (a, b) xs (ps -- qs)"
    and a1: "(a, b) \<in> set qs \<Longrightarrow> thesis"
    and a2: "(b, a) \<in> set qs \<Longrightarrow> thesis"
    and a3: "processed (a, b) xs ps \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin> set (ps -- qs)"
    and "(b, a) \<notin> set (ps -- qs)"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(a, b) \<in> set qs")
    case True
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(a, b) \<notin> set (ps -- qs)\<close> have *: "(a, b) \<notin> set ps" by (auto simp add: set_diff_list)
    show ?thesis
    proof (cases "(b, a) \<in> set qs")
      case True
      thus ?thesis by (rule a2)
    next
      case False
      with \<open>(b, a) \<notin> set (ps -- qs)\<close> have "(b, a) \<notin> set ps" by (auto simp add: set_diff_list)
      with \<open>a \<in> set xs\<close> \<open>b \<in> set xs\<close> * have "processed (a, b) xs ps"
        by (rule processedI)
      thus ?thesis by (rule a3)
    qed
  qed
qed

subsection \<open>Algorithm Schema\<close>

subsubsection \<open>\<open>const_lt_component\<close>\<close>

context ordered_term
begin

definition const_lt_component :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'k option"
  where "const_lt_component p =
                      (let v = lt p in if pp_of_term v = 0 then Some (component_of_term v) else None)"

lemma const_lt_component_SomeI:
  assumes "lp p = 0" and "component_of_term (lt p) = cmp"
  shows "const_lt_component p = Some cmp"
  using assms by (simp add: const_lt_component_def)

lemma const_lt_component_SomeD1:
  assumes "const_lt_component p = Some cmp"
  shows "lp p = 0"
  using assms by (simp add: const_lt_component_def Let_def split: if_split_asm)

lemma const_lt_component_SomeD2:
  assumes "const_lt_component p = Some cmp"
  shows "component_of_term (lt p) = cmp"
  using assms by (simp add: const_lt_component_def Let_def split: if_split_asm)

lemma const_lt_component_subset:
  "const_lt_component ` (B - {0}) - {None} \<subseteq> Some ` component_of_term ` Keys B"
proof
  fix k
  assume "k \<in> const_lt_component ` (B - {0}) - {None}"
  hence "k \<in> const_lt_component ` (B - {0})" and "k \<noteq> None" by simp_all
  from this(1) obtain p where "p \<in> B - {0}" and "k = const_lt_component p" ..
  moreover from \<open>k \<noteq> None\<close> obtain k' where "k = Some k'" by blast
  ultimately have "const_lt_component p = Some k'" and "p \<in> B" and "p \<noteq> 0" by simp_all
  from this(1) have "component_of_term (lt p) = k'" by (rule const_lt_component_SomeD2)
  moreover have "lt p \<in> Keys B" by (rule in_KeysI, rule lt_in_keys, fact+)
  ultimately have "k' \<in> component_of_term ` Keys B" by fastforce
  thus "k \<in> Some ` component_of_term ` Keys B" by (simp add: \<open>k = Some k'\<close>)
qed

corollary card_const_lt_component_le:
  assumes "finite B"
  shows "card (const_lt_component ` (B - {0}) - {None}) \<le> card (component_of_term ` Keys B)"
proof (rule surj_card_le)
  show "finite (component_of_term ` Keys B)"
    by (intro finite_imageI finite_Keys, fact)
next
  show "const_lt_component ` (B - {0}) - {None} \<subseteq> Some ` component_of_term ` Keys B"
    by (fact const_lt_component_subset)
qed

end (* ordered_term *)

subsubsection \<open>Type synonyms\<close>

type_synonym ('a, 'b, 'c) pdata' = "('a \<Rightarrow>\<^sub>0 'b) \<times> 'c"
type_synonym ('a, 'b, 'c) pdata = "('a \<Rightarrow>\<^sub>0 'b) \<times> nat \<times> 'c"
type_synonym ('a, 'b, 'c) pdata_pair = "('a, 'b, 'c) pdata \<times> ('a, 'b, 'c) pdata"
type_synonym ('a, 'b, 'c, 'd) selT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c, 'd) complT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                    nat \<times> 'd \<Rightarrow> (('a, 'b, 'c) pdata' list \<times> 'd)"
type_synonym ('a, 'b, 'c, 'd) apT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c, 'd) abT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata list"

subsubsection \<open>Specification of the @{emph \<open>selector\<close>} parameter\<close>

definition sel_spec :: "('a, 'b, 'c, 'd) selT \<Rightarrow> bool"
  where "sel_spec sel \<longleftrightarrow>
          (\<forall>gs bs ps data. ps \<noteq> [] \<longrightarrow> (sel gs bs ps data \<noteq> [] \<and> set (sel gs bs ps data) \<subseteq> set ps))"

lemma sel_specI:
  assumes "\<And>gs bs ps data. ps \<noteq> [] \<Longrightarrow> (sel gs bs ps data \<noteq> [] \<and> set (sel gs bs ps data) \<subseteq> set ps)"
  shows "sel_spec sel"
  unfolding sel_spec_def using assms by blast

lemma sel_specD1:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "sel gs bs ps data \<noteq> []"
  using assms unfolding sel_spec_def by blast

lemma sel_specD2:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "set (sel gs bs ps data) \<subseteq> set ps"
  using assms unfolding sel_spec_def by blast

subsubsection \<open>Specification of the @{emph \<open>add-basis\<close>} parameter\<close>

definition ab_spec :: "('a, 'b, 'c, 'd) abT \<Rightarrow> bool"
  where "ab_spec ab \<longleftrightarrow>
              (\<forall>gs bs ns data. ns \<noteq> [] \<longrightarrow> set (ab gs bs ns data) = set bs \<union> set ns) \<and>
              (\<forall>gs bs data. ab gs bs [] data = bs)"

lemma ab_specI:
  assumes "\<And>gs bs ns data. ns \<noteq> [] \<Longrightarrow> set (ab gs bs ns data) = set bs \<union> set ns"
    and "\<And>gs bs data. ab gs bs [] data = bs"
  shows "ab_spec ab"
  unfolding ab_spec_def using assms by blast

lemma ab_specD1:
  assumes "ab_spec ab"
  shows "set (ab gs bs ns data) = set bs \<union> set ns"
  using assms unfolding ab_spec_def by (metis empty_set sup_bot.right_neutral)

lemma ab_specD2:
  assumes "ab_spec ab"
  shows "ab gs bs [] data = bs"
  using assms unfolding ab_spec_def by blast

subsubsection \<open>Specification of the @{emph \<open>add-pairs\<close>} parameter\<close>

context ordered_term
begin

definition ap_spec :: "('t, 'b::zero, 'c, 'd) apT \<Rightarrow> bool"
  where "ap_spec ap \<longleftrightarrow> (\<forall>gs bs ps hs data.
      set (ap gs bs ps hs data) \<subseteq> set ps \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs)) \<and>
      set ps \<subseteq> set (ap gs bs ps hs data) \<and>
      (\<forall>h\<in>set hs. \<forall>g\<in>set gs \<union> set bs. component_of_term (lt (fst h)) = component_of_term (lt (fst g)) \<longrightarrow>
        (h, g) \<in> set (ap gs bs ps hs data)) \<and>
      (\<forall>h1\<in>set hs. \<forall>h2\<in> set hs. h1 \<noteq> h2 \<longrightarrow> component_of_term (lt (fst h1)) = component_of_term (lt (fst h2)) \<longrightarrow>
        ((h1, h2) \<in> set (ap gs bs ps hs data) \<or> (h2, h1) \<in> set (ap gs bs ps hs data))))"

lemma ap_specI:
  assumes "\<And>gs bs ps hs data.
                set (ap gs bs ps hs data) \<subseteq> set ps \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs))"
  assumes "\<And>gs bs ps hs data. set ps \<subseteq> set (ap gs bs ps hs data)"
  assumes "\<And>gs bs ps hs h g data. h \<in> set hs \<Longrightarrow> g \<in> set gs \<union> set bs \<Longrightarrow>
                   component_of_term (lt (fst h)) = component_of_term (lt (fst g)) \<Longrightarrow>
                   (h, g) \<in> set (ap gs bs ps hs data)"
  assumes "\<And>gs bs ps hs h1 h2 data. h1 \<in> set hs \<Longrightarrow> h2 \<in> set hs \<Longrightarrow> h1 \<noteq> h2 \<Longrightarrow>
                   component_of_term (lt (fst h1)) = component_of_term (lt (fst h2)) \<Longrightarrow>
                   ((h1, h2) \<in> set (ap gs bs ps hs data) \<or> (h2, h1) \<in> set (ap gs bs ps hs data))"
  shows "ap_spec ap"
  unfolding ap_spec_def using assms by auto

lemma ap_specD1:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps hs data) \<subseteq> set ps \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs))"
  using assms unfolding ap_spec_def by blast

lemma ap_specD2:
  assumes "ap_spec ap"
  shows "set ps \<subseteq> set (ap gs bs ps hs data)"
  using assms unfolding ap_spec_def by blast

lemma ap_specD3:
  assumes "ap_spec ap" and "h \<in> set hs" and "g \<in> set gs \<union> set bs"
    and "component_of_term (lt (fst h)) = component_of_term (lt (fst g))"
  shows "(h, g) \<in> set (ap gs bs ps hs data)"
  using assms unfolding ap_spec_def by blast

lemma ap_specE:
  assumes "ap_spec ap" and "h1 \<in> set hs" and "h2 \<in> set hs" and "h1 \<noteq> h2"
    and "component_of_term (lt (fst h1)) = component_of_term (lt (fst h2))"
  obtains "(h1, h2) \<in> set (ap gs bs ps hs data)"|"(h2, h1) \<in> set (ap gs bs ps hs data)"
  using assms unfolding ap_spec_def by blast

lemma ap_spec_Nil_new:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps [] data) = set ps"
proof
  from ap_specD1[OF assms] show "set (ap gs bs ps [] data) \<subseteq> set ps" by fastforce
next
  from ap_specD2[OF assms] show "set ps \<subseteq> set (ap gs bs ps [] data)" by blast
qed

lemma ap_spec_fst_subset:
  assumes "ap_spec ap"
  shows "fst ` set (ap gs bs ps hs data) \<subseteq> fst ` set ps \<union> set hs"
proof -
  from ap_specD1[OF assms]
  have "fst ` set (ap gs bs ps hs data) \<subseteq> fst ` (set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_snd_subset:
  assumes "ap_spec ap"
  shows "snd ` set (ap gs bs ps hs data) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set hs"
proof -
  from ap_specD1[OF assms]
  have "snd ` set (ap gs bs ps hs data) \<subseteq> snd ` (set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_inE:
  assumes "ap_spec ap" and "(p, q) \<in> set (ap gs bs ps hs data)"
  assumes 1: "(p, q) \<in> set ps \<Longrightarrow> thesis"
  assumes 2: "p \<in> set hs \<Longrightarrow> q \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(2) ap_specD1[OF assms(1)] have "(p, q) \<in> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)" ..
  thus ?thesis
  proof
    assume "(p, q) \<in> set ps"
    thus ?thesis by (rule 1)
  next
    assume "(p, q) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    hence "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" by blast+
    thus ?thesis by (rule 2)
  qed
qed

lemma subset_Times_ap:
  assumes "ap_spec ap" and "ab_spec ab" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "set (ap gs bs (ps -- sps) hs data) \<subseteq> set (ab gs bs hs data) \<times> (set gs \<union> set (ab gs bs hs data))"
proof
  fix p q
  assume "(p, q) \<in> set (ap gs bs (ps -- sps) hs data)"
  with assms(1) show "(p, q) \<in> set (ab gs bs hs data) \<times> (set gs \<union> set (ab gs bs hs data))"
  proof (rule ap_spec_inE)
    assume "(p, q) \<in> set (ps -- sps)"
    hence "(p, q) \<in> set ps" by (simp add: set_diff_list)
    from this assms(3) have "(p, q) \<in> set bs \<times> (set gs \<union> set bs)" ..
    hence "p \<in> set bs" and "q \<in> set gs \<union> set bs" by blast+
    thus ?thesis by (auto simp add: ab_specD1[OF assms(2)])
  next
    assume "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs"
    thus ?thesis by (simp add: ab_specD1[OF assms(2)])
  qed
qed

lemma processed_apE:
  assumes "ap_spec ap" and "ab_spec ab" and "processed (f, g) (gs @ (ab gs bs hs data)) (ap gs bs ps hs data)"
    and "component_of_term (lt (fst f)) = component_of_term (lt (fst g))"
  assumes 1: "processed (f, g) (gs @ bs) ps \<Longrightarrow> thesis"
  assumes 2: "f \<in> set hs \<Longrightarrow> g \<in> set hs \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(3) have d1: "f \<in> set gs \<union> set bs \<or> f \<in> set hs" and d2: "g \<in> set gs \<union> set bs \<or> g \<in> set hs"
    and a: "(f, g) \<notin> set (ap gs bs ps hs data)" and b: "(g, f) \<notin> set (ap gs bs ps hs data)"
    by (simp_all add: processed_def ab_specD1[OF assms(2)])
  from d1 show ?thesis
  proof
    assume "f \<in> set hs"
    from d2 show ?thesis
    proof
      assume "g \<in> set hs"
      with \<open>f \<in> set hs\<close> show ?thesis by (rule 2)
    next
      assume "g \<in> set gs \<union> set bs"
      from assms(1) \<open>f \<in> set hs\<close> this assms(4) have "(f, g) \<in> set (ap gs bs ps hs data)"
        by (rule ap_specD3)
      with a show ?thesis ..
    qed
  next
    assume "f \<in> set gs \<union> set bs"
    hence "f \<in> set (gs @ bs)" by simp
    from d2 show ?thesis
    proof
      assume "g \<in> set hs"
      from assms(1) this \<open>f \<in> set gs \<union> set bs\<close> assms(4)[symmetric] have "(g, f) \<in> set (ap gs bs ps hs data)"
        by (rule ap_specD3)
      with b show ?thesis ..
    next
      assume "g \<in> set gs \<union> set bs"
      hence "g \<in> set (gs @ bs)" by simp
      from \<open>f \<in> set (gs @ bs)\<close> this have "processed (f, g) (gs @ bs) ps"
      proof (rule processedI)
        show "(f, g) \<notin> set ps"
        proof
          assume "(f, g) \<in> set ps"
          also from assms(1) have "... \<subseteq> set (ap gs bs ps hs data)" by (rule ap_specD2)
          finally have "(f, g) \<in> set (ap gs bs ps hs data)" .
          with a show False ..
        qed
      next
        show "(g, f) \<notin> set ps"
        proof
          assume "(g, f) \<in> set ps"
          also from assms(1) have "... \<subseteq> set (ap gs bs ps hs data)" by (rule ap_specD2)
          finally have "(g, f) \<in> set (ap gs bs ps hs data)" .
          with b show False ..
        qed
      qed
      thus ?thesis by (rule 1)
    qed
  qed
qed

subsubsection \<open>Function \<open>args_to_set\<close>\<close>

definition args_to_set :: "('t, 'b::field, 'c) pdata list \<times> ('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set"
  where "args_to_set x = fst ` (set (fst x) \<union> set (fst (snd x)) \<union> fst ` set (snd (snd x)) \<union> snd ` set (snd (snd x)))"

lemma args_to_set_alt:
  "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs \<union> fst ` fst ` set ps \<union> fst ` snd ` set ps"
  by (simp add: args_to_set_def image_Un)

lemma args_to_set_subset_Times:
  assumes "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs"
  unfolding args_to_set_alt using assms by auto

lemma args_to_set_alt2:
  assumes "ap_spec ap" and "ab_spec ab"
  shows "args_to_set (gs, ab gs bs ns data, ap gs bs ps ns data) = fst ` (set gs \<union> set bs \<union>
              fst ` set ps \<union> snd ` set ps \<union> set ns)" (is "?l = fst ` ?r")
proof
  show "?l \<subseteq> fst ` ?r"
  proof (simp only: args_to_set_alt Un_subset_iff, intro conjI image_mono)
    show "set (ab gs bs ns data) \<subseteq> ?r" by (auto simp add: ab_specD1[OF assms(2)])
  next
    from assms(1) have "fst ` set (ap gs bs ps ns data) \<subseteq> fst ` set ps \<union> set ns"
      by (rule ap_spec_fst_subset)
    thus "fst ` set (ap gs bs ps ns data) \<subseteq> ?r" by blast
  next
    from assms(1) have "snd ` set (ap gs bs ps ns data) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set ns"
      by (rule ap_spec_snd_subset)
    thus "snd ` set (ap gs bs ps ns data) \<subseteq> ?r" by blast
  qed blast
next
  let ?u = "set gs \<union> set (ab gs bs ns data) \<union> fst ` set (ap gs bs ps ns data) \<union> snd ` set (ap gs bs ps ns data)"
  show "fst ` ?r \<subseteq> ?l"
  proof (simp only: args_to_set_alt image_Un[symmetric], rule image_mono, simp only: Un_subset_iff, intro conjI)
    show "set gs \<subseteq> ?u" by blast
  next
    from assms(2) have "set bs \<subseteq> set (ab gs bs ns data)" by (simp add: ab_specD1)
    thus "set bs \<subseteq> ?u" by blast
  next
    from assms(1) have "set ps \<subseteq> set (ap gs bs ps ns data)" by (rule ap_specD2)
    thus "fst ` set ps \<subseteq> ?u" by blast
  next
    from assms(1) have "set ps \<subseteq> set (ap gs bs ps ns data)" by (rule ap_specD2)
    thus "snd ` set ps \<subseteq> ?u" by blast
  next
    from assms(2) have "set ns \<subseteq> set (ab gs bs ns data)" by (simp add: ab_specD1)
    thus "set ns \<subseteq> ?u" by blast
  qed
qed

lemma args_to_set_subset1:
  assumes "set gs1 \<subseteq> set gs2"
  shows "args_to_set (gs1, bs, ps) \<subseteq> args_to_set (gs2, bs, ps)"
  using assms by (auto simp add: args_to_set_alt)

lemma args_to_set_subset2:
  assumes "set bs1 \<subseteq> set bs2"
  shows "args_to_set (gs, bs1, ps) \<subseteq> args_to_set (gs, bs2, ps)"
  using assms by (auto simp add: args_to_set_alt)

lemma args_to_set_subset3:
  assumes "set ps1 \<subseteq> set ps2"
  shows "args_to_set (gs, bs, ps1) \<subseteq> args_to_set (gs, bs, ps2)"
  using assms unfolding args_to_set_alt by blast

subsubsection \<open>Functions \<open>count_const_lt_components\<close>, \<open>count_rem_comps\<close> and \<open>full_gb\<close>\<close>

definition rem_comps_spec :: "('t, 'b::zero, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow> bool"
  where "rem_comps_spec bs data \<longleftrightarrow> (card (component_of_term ` Keys (fst ` set bs)) =
                                  fst data + card (const_lt_component ` (fst ` set bs - {0}) - {None}))"

definition count_const_lt_components :: "('t, 'b::zero, 'c) pdata' list \<Rightarrow> nat"
  where "count_const_lt_components hs = length (remdups (filter (\<lambda>x. x \<noteq> None) (map (const_lt_component \<circ> fst) hs)))"

definition count_rem_components :: "('t, 'b::zero, 'c) pdata' list \<Rightarrow> nat"
  where "count_rem_components bs = length (remdups (map component_of_term (Keys_to_list (map fst bs)))) -
                                    count_const_lt_components [b\<leftarrow>bs . fst b \<noteq> 0]"

lemma count_const_lt_components_alt:
  "count_const_lt_components hs = card (const_lt_component ` fst ` set hs - {None})"
  by (simp add: count_const_lt_components_def card_set[symmetric] set_diff_eq image_comp del: not_None_eq)

lemma count_rem_components_alt:
  "count_rem_components bs + card (const_lt_component ` (fst ` set bs - {0}) - {None}) =
    card (component_of_term ` Keys (fst ` set bs))"
proof -
  have eq: "fst ` {x \<in> set bs. fst x \<noteq> 0} = fst ` set bs - {0}" by fastforce
  have "card (const_lt_component ` (fst ` set bs - {0}) - {None}) \<le> card (component_of_term ` Keys (fst ` set bs))"
    by (rule card_const_lt_component_le, rule finite_imageI, fact finite_set)
  thus ?thesis
    by (simp add: count_rem_components_def card_set[symmetric] set_Keys_to_list count_const_lt_components_alt eq)
qed

lemma rem_comps_spec_count_rem_components: "rem_comps_spec bs (count_rem_components bs, data)"
  by (simp only: rem_comps_spec_def fst_conv count_rem_components_alt)

definition full_gb :: "('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b::zero_neq_one, 'c::default) pdata list"
  where "full_gb bs = map (\<lambda>k. (monomial 1 (term_of_pair (0, k)), 0, default))
                          (remdups (map component_of_term (Keys_to_list (map fst bs))))"

lemma fst_set_full_gb:
  "fst ` set (full_gb bs) = (\<lambda>v. monomial 1 (term_of_pair (0, component_of_term v))) ` Keys (fst ` set bs)"
  by (simp add: full_gb_def set_Keys_to_list image_comp, rule image_cong, fact refl, simp)

lemma Keys_full_gb:
  "Keys (fst ` set (full_gb bs)) = (\<lambda>v. term_of_pair (0, component_of_term v)) ` Keys (fst ` set bs)"
  by (simp add: fst_set_full_gb Keys_def image_UN, blast)

lemma pps_full_gb: "pp_of_term ` Keys (fst ` set (full_gb bs)) \<subseteq> {0}"
  by (simp add: Keys_full_gb image_comp image_subset_iff term_simps)

lemma components_full_gb:
  "component_of_term ` Keys (fst ` set (full_gb bs)) = component_of_term ` Keys (fst ` set bs)"
  by (simp add: Keys_full_gb image_comp, rule image_cong, fact refl, simp add: term_simps)

end (* ordered_term *)

context gd_term
begin

lemma full_gb_is_full_pmdl: "is_full_pmdl (fst ` set (full_gb bs))"
    for bs::"('t, 'b::field, 'c::default) pdata list"
proof (rule is_full_pmdlI_lt_finite)
  from finite_set show "finite (fst ` set (full_gb bs))" by (rule finite_imageI)
next
  fix k
  assume "k \<in> component_of_term ` Keys (fst ` set (full_gb bs))"
  then obtain v where "v \<in> Keys (fst ` set (full_gb bs))" and k: "k = component_of_term v" ..
  from this(1) obtain b where "b \<in> fst ` set (full_gb bs)" and "v \<in> keys b" by (rule in_KeysE)
  from this(1) obtain u where "u \<in> Keys (fst ` set bs)" and b: "b = monomial 1 (term_of_pair (0, component_of_term u))"
    unfolding fst_set_full_gb ..
  have lt: "lt b = term_of_pair (0, component_of_term u)" by (simp add: b lt_monomial)
  from \<open>v \<in> keys b\<close> have v: "v = term_of_pair (0, component_of_term u)" by (simp add: b)
  show "\<exists>b\<in>fst ` set (full_gb bs). b \<noteq> 0 \<and> component_of_term (lt b) = k \<and> lp b = 0"
  proof (intro bexI conjI)
    show "b \<noteq> 0" by (simp add: b monomial_0_iff)
  next
    show "component_of_term (lt b) = k" by (simp add: lt term_simps k v)
  next
    show "lp b = 0" by (simp add: lt term_simps)
  qed fact
qed

text \<open>In fact, @{thm full_gb_is_full_pmdl} also holds if @{typ 'b} is no field.\<close>

lemma full_gb_isGB: "is_Groebner_basis (fst ` set (full_gb bs))"
proof (rule Buchberger_criterion_finite)
  from finite_set show "finite (fst ` set (full_gb bs))" by (rule finite_imageI)
next
  fix p q :: "'t \<Rightarrow>\<^sub>0 'b"
  assume "p \<in> fst ` set (full_gb bs)"
  then obtain v where p: "p = monomial 1 (term_of_pair (0, component_of_term v))"
    unfolding fst_set_full_gb ..
  hence lt: "component_of_term (lt p) = component_of_term v" by (simp add: lt_monomial term_simps)
  assume "q \<in> fst ` set (full_gb bs)"
  then obtain u where q: "q = monomial 1 (term_of_pair (0, component_of_term u))"
    unfolding fst_set_full_gb ..
  hence lq: "component_of_term (lt q) = component_of_term u" by (simp add: lt_monomial term_simps)
  assume "component_of_term (lt p) = component_of_term (lt q)"
  hence "component_of_term v = component_of_term u" by (simp only: lt lq)
  hence "p = q" by (simp only: p q)
  moreover assume "p \<noteq> q"
  ultimately show "(red (fst ` set (full_gb bs)))\<^sup>*\<^sup>* (spoly p q) 0" by (simp only:)
qed

subsubsection \<open>Specification of the @{emph \<open>completion\<close>} parameter\<close>

definition compl_struct :: "('t, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_struct compl \<longleftrightarrow>
          (\<forall>gs bs ps sps data. sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              (\<forall>d. dickson_grading (+) d \<longrightarrow>
                  dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))) \<and>
              component_of_term ` Keys (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, ps)) \<and>
              0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data)) \<and>
              (\<forall>h\<in>set (fst (compl gs bs (ps -- sps) sps data)). \<forall>b\<in>set gs \<union> set bs. fst b \<noteq> 0 \<longrightarrow> \<not> lt (fst b) adds\<^sub>t lt (fst h)))"

lemma compl_structI:
  assumes "\<And>d gs bs ps sps data. dickson_grading (+) d \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps sps data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              component_of_term ` Keys (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps sps data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow> 0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
  assumes "\<And>gs bs ps sps h b data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow> h \<in> set (fst (compl gs bs (ps -- sps) sps data)) \<Longrightarrow>
              b \<in> set gs \<union> set bs \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> \<not> lt (fst b) adds\<^sub>t lt (fst h)"
  shows "compl_struct compl"
  unfolding compl_struct_def using assms by auto

lemma compl_structD1:
  assumes "compl_struct compl" and "dickson_grading (+) d" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD2:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "component_of_term ` Keys (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) \<subseteq>
           component_of_term ` Keys (args_to_set (gs, bs, ps))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD3:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD4:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
    and "h \<in> set (fst (compl gs bs (ps -- sps) sps data))" and "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0"
  shows "\<not> lt (fst b) adds\<^sub>t lt (fst h)"
  using assms unfolding compl_struct_def by blast

definition struct_spec :: "('t, 'b::field, 'c, 'd) selT \<Rightarrow> ('t, 'b, 'c, 'd) apT \<Rightarrow> ('t, 'b, 'c, 'd) abT \<Rightarrow>
                            ('t, 'b, 'c, 'd) complT \<Rightarrow> bool"
  where "struct_spec sel ap ab compl \<longleftrightarrow> (sel_spec sel \<and> ap_spec ap \<and> ab_spec ab \<and> compl_struct compl)"

lemma struct_specI:
  assumes "sel_spec sel" and "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  shows "struct_spec sel ap ab compl"
  unfolding struct_spec_def using assms by (intro conjI)

lemma struct_specD1:
  assumes "struct_spec sel ap ab compl"
  shows "sel_spec sel"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD2:
  assumes "struct_spec sel ap ab compl"
  shows "ap_spec ap"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD3:
  assumes "struct_spec sel ap ab compl"
  shows "ab_spec ab"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD4:
  assumes "struct_spec sel ap ab compl"
  shows "compl_struct compl"
  using assms unfolding struct_spec_def by (elim conjE)

lemmas struct_specD = struct_specD1 struct_specD2 struct_specD3 struct_specD4

definition unique_idx :: "('t, 'b, 'c) pdata list \<Rightarrow> (nat \<times> 'd) \<Rightarrow> bool"
  where "unique_idx bs data \<longleftrightarrow>
                         (\<forall>f\<in>set bs. \<forall>g\<in>set bs. fst (snd f) = fst (snd g) \<longrightarrow> f = g) \<and>
                         (\<forall>f\<in>set bs. fst (snd f) < fst data)"

lemma unique_idxI:
  assumes "\<And>f g. f \<in> set bs \<Longrightarrow> g \<in> set bs \<Longrightarrow> fst (snd f) = fst (snd g) \<Longrightarrow> f = g"
    and "\<And>f. f \<in> set bs \<Longrightarrow> fst (snd f) < fst data"
  shows "unique_idx bs data"
  unfolding unique_idx_def using assms by blast

lemma unique_idxD1:
  assumes "unique_idx bs data" and "f \<in> set bs" and "g \<in> set bs" and "fst (snd f) = fst (snd g)"
  shows "f = g"
  using assms unfolding unique_idx_def by blast

lemma unique_idxD2:
  assumes "unique_idx bs data" and "f \<in> set bs"
  shows "fst (snd f) < fst data"
  using assms unfolding unique_idx_def by blast

lemma unique_idx_Nil: "unique_idx [] data"
  by (simp add: unique_idx_def)

definition compl_pmdl :: "('t, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_pmdl compl \<longleftrightarrow>
          (\<forall>gs bs ps sps data. is_Groebner_basis (fst ` set gs) \<longrightarrow> sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              unique_idx (gs @ bs) data \<longrightarrow>
              fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pmdl (args_to_set (gs, bs, ps)))"

lemma compl_pmdlI:
  assumes "\<And>gs bs ps sps data. is_Groebner_basis (fst ` set gs) \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              unique_idx (gs @ bs) data \<Longrightarrow>
              fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pmdl (args_to_set (gs, bs, ps))"
  shows "compl_pmdl compl"
  unfolding compl_pmdl_def using assms by blast

lemma compl_pmdlD:
  assumes "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "sps \<noteq> []" and "set sps \<subseteq> set ps" and "unique_idx (gs @ bs) data"
  shows "fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pmdl (args_to_set (gs, bs, ps))"
  using assms unfolding compl_pmdl_def by blast

definition compl_conn :: "('t, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_conn compl \<longleftrightarrow>
            (\<forall>d m gs bs ps sps p q data. dickson_grading (+) d \<longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<longrightarrow>
              is_Groebner_basis (fst ` set gs) \<longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
              set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              unique_idx (gs @ bs) data \<longrightarrow>
              (\<forall>p' q'. processed (p', q') (gs @ bs) ps \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                  crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')) \<longrightarrow>
              (p, q) \<in> set sps \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q))"

text \<open>Informally, \<open>compl_conn compl\<close> means that, for suitable arguments \<open>gs\<close>, \<open>bs\<close>, \<open>ps\<close> and \<open>sps\<close>,
  the value of \<open>compl gs bs ps sps\<close> is a list \<open>hs\<close> such that the critical pairs of all elements in
  \<open>sps\<close> can be connected modulo \<open>set gs \<union> set bs \<union> set hs\<close>, provided that the critical pairs of all
  elements that have been processed already can be connected modulo the smaller set \<open>set gs \<union> set bs\<close>.\<close>

lemma compl_connI:
  assumes "\<And>d m gs bs ps sps p q data. dickson_grading (+) d \<Longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<Longrightarrow>
            is_Groebner_basis (fst ` set gs) \<Longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<Longrightarrow>
            set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
            unique_idx (gs @ bs) data \<Longrightarrow>
            (\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                      crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')) \<Longrightarrow>
            (p, q) \<in> set sps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q)"
  shows "compl_conn compl"
  unfolding compl_conn_def using assms by presburger

lemma compl_connD:
  assumes "compl_conn compl" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
    and "unique_idx (gs @ bs) data"
    and "\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                 crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
    and "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q)"
  using assms unfolding compl_conn_def Un_assoc by blast

subsubsection \<open>Function \<open>gb_schema_aux\<close>\<close>

definition (in -) add_indices :: "(('a, 'b, 'c) pdata' list \<times> 'd) \<Rightarrow> (nat \<times> 'd) \<Rightarrow> (('a, 'b, 'c) pdata list \<times> nat \<times> 'd)"
  where [code del]: "add_indices ns data =
        (map_idx (\<lambda>h i. (fst h, i, snd h)) (fst ns) (fst data), fst data + length (fst ns), snd ns)"

lemma (in -) add_indices_code [code]:
  "add_indices (ns, data) (n, data') = (map_idx (\<lambda>(h, d) i. (h, i, d)) ns n, n + length ns, data)"
  by (simp add: add_indices_def case_prod_beta')

lemma fst_add_indices: "map fst (fst (add_indices ns data')) = map fst (fst ns)"
  by (simp add: add_indices_def map_map_idx map_idx_no_idx)

corollary fst_set_add_indices: "fst ` set (fst (add_indices ns data')) = fst ` set (fst ns)"
  using fst_add_indices by (metis set_map)

lemma in_set_add_indicesE:
  assumes "f \<in> set (fst (add_indices aux data))"
  obtains i where "i < length (fst aux)" and "f = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))"
proof -
  let ?hs = "fst (add_indices aux data)"
  from assms obtain i where "i < length ?hs" and "f = ?hs ! i" by (metis in_set_conv_nth)
  from this(1) have "i < length (fst aux)" by (simp add: add_indices_def)
  hence "?hs ! i = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))"
    unfolding add_indices_def fst_conv by (rule map_idx_nth)
  hence "f = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))" by (simp add: \<open>f = ?hs ! i\<close>)
  with \<open>i < length (fst aux)\<close> show ?thesis ..
qed

definition gb_schema_aux_term1 ::
    "('a \<Rightarrow> nat) \<Rightarrow> ((('t, 'b::field, 'c) pdata list \<times> ('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list) \<times>
                    (('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term1 d = (measure length) <*lex*>
                              {(a, b::('t, 'b, 'c) pdata list). (fst ` set a) \<sqsupset>p (fst ` set b)} <*lex*>
                              (measure (card \<circ> set))"

definition gb_schema_aux_term2 ::
    "('a \<Rightarrow> nat) \<Rightarrow> ((('t, 'b::field, 'c) pdata list \<times> ('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list) \<times>
                    (('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term2 d = {(a, b). dgrad_p_set_le d (args_to_set a) (args_to_set b) \<and>
                          component_of_term ` Keys (args_to_set a) \<subseteq> component_of_term ` Keys (args_to_set b)}"

definition gb_schema_aux_term where "gb_schema_aux_term d = gb_schema_aux_term1 d \<inter> gb_schema_aux_term2 d"

text \<open>@{const gb_schema_aux_term} is needed for proving termination of function @{term gb_schema_aux}.\<close>

lemma gb_schema_aux_term1_wf_on:
  assumes "dickson_grading (+) d" and "finite K"
  shows "wfP_on {x::(('t, 'b, 'c) pdata list) \<times> ('t, 'b, 'c) pdata list \<times> ((('t, 'b::field, 'c) pdata_pair list)).
                    args_to_set x \<subseteq> dgrad_p_set d m \<and> component_of_term ` Keys (args_to_set x) \<subseteq> K}
                (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1 d)"
proof (rule wfP_onI_min)
  let ?B = "dgrad_p_set d m"
  let ?A = "{x::(('t, 'b, 'c) pdata list) \<times> ('t, 'b, 'c) pdata list \<times> ((('t, 'b, 'c) pdata_pair list)).
              args_to_set x \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set x) \<subseteq> K}"
  let ?C = "Pow ?B \<inter> {F. component_of_term ` Keys F \<subseteq> K}"
  have A_sub_Pow: "(image fst) ` set ` fst ` snd ` ?A \<subseteq> ?C"
  proof
    fix x
    assume "x \<in> (image fst) ` set ` fst ` snd ` ?A"
    then obtain x1 where "x1 \<in> set ` fst ` snd ` ?A" and x: "x = fst ` x1" by auto
    from this(1) obtain x2 where "x2 \<in> fst ` snd ` ?A" and x1: "x1 = set x2" by auto
    from this(1) obtain x3 where "x3 \<in> snd ` ?A" and x2: "x2 = fst x3" by auto
    from this(1) obtain x4 where "x4 \<in> ?A" and x3: "x3 = snd x4" by auto
    from this(1) have "args_to_set x4 \<subseteq> ?B" and "component_of_term ` Keys (args_to_set x4) \<subseteq> K"
      by simp_all
    thus "x \<in> ?C" by (simp add: args_to_set_def x x1 x2 x3 image_Un Keys_Un)
  qed

  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  have "fst x \<in> fst ` Q" by (rule, fact refl, fact)
  with wf_measure obtain z0 where "z0 \<in> fst ` Q"
    and 1: "\<And>y. (y, z0) \<in> measure length \<Longrightarrow> y \<notin> fst ` Q" by (rule wfE_min, blast)
  from this(1) obtain x0 where "x0 \<in> Q" and z0: "z0 = fst x0" ..

  let ?Q1 = "{q \<in> Q. fst q = z0}"
  have "?Q1 \<subseteq> Q" by blast
  have "(image fst) ` set ` fst ` snd ` ?Q1 \<subseteq> (image fst) ` set ` fst ` snd ` Q"
    by ((rule image_mono)+, fact)
  also have "... \<subseteq> (image fst) ` set ` fst ` snd ` ?A"
    by ((rule image_mono)+, fact)
  finally have Q_sub_A: "(image fst) ` set ` fst ` snd ` ?Q1 \<subseteq> (image fst) ` set ` fst ` snd ` ?A" .
  from assms have "wfP_on ?C (\<sqsupset>p)" by (rule red_supset_wf_on)
  moreover have "fst ` set (fst (snd x0)) \<in> (image fst) ` set ` fst ` snd ` ?Q1"
    by (rule, fact refl, rule, fact refl, rule, fact refl, rule, fact refl, simp add: \<open>x0 \<in> Q\<close> z0)
  moreover from Q_sub_A A_sub_Pow have "(image fst) ` set ` fst ` snd ` ?Q1 \<subseteq> ?C" by (rule subset_trans)
  ultimately obtain z1 where "z1 \<in> (image fst) ` set ` fst ` snd ` ?Q1"
    and 2: "\<And>y. y \<sqsupset>p z1 \<Longrightarrow> y \<notin> (image fst) ` set ` fst ` snd ` ?Q1" by (rule wfP_onE_min, auto)
  from this(1) obtain x1 where "x1 \<in> ?Q1" and z1: "z1 = fst ` set (fst (snd x1))" by auto
  from this(1) have "x1 \<in> Q" and x1: "fst x1 = z0" by simp_all

  let ?Q2 = "{q \<in> ?Q1. fst ` set (fst (snd q)) = z1}"
  have "snd (snd x1) \<in> snd ` snd ` ?Q2"
    by (rule, fact refl, rule, fact refl, simp add: \<open>x1 \<in> ?Q1\<close> \<open>x1 \<in> Q\<close> z1 x1)
  with wf_measure obtain z2 where "z2 \<in> snd ` snd ` ?Q2"
    and 3: "\<And>y. (y, z2) \<in> measure (card \<circ> set) \<Longrightarrow> y \<notin> snd ` snd ` ?Q2"
    by (rule wfE_min, blast)
  from this(1) obtain z3 where "z3 \<in> snd ` ?Q2" and z2: "z2 = snd z3" ..
  from this(1) obtain z where "z \<in> ?Q2" and z3: "z3 = snd z" by auto
  from this(1) have "z \<in> ?Q1" and eq1: "fst ` set (fst (snd z)) = z1" by blast+
  from this(1) have "z \<in> Q" and eq2: "fst z = z0" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>?A. (y, z) \<in> gb_schema_aux_term1 d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>?A. (y, z) \<in> gb_schema_aux_term1 d \<longrightarrow> y \<notin> Q"
    proof (intro ballI impI)
      fix y
      assume "y \<in> ?A"
      assume "(y, z) \<in> gb_schema_aux_term1 d"
      hence "(fst y, z0) \<in> measure length \<or>
              (fst y = z0 \<and> (fst ` set (fst (snd y)) \<sqsupset>p z1 \<or>
                (fst (snd y) = fst z3 \<and> (snd (snd y), z2) \<in> measure (card \<circ> set))))"
        by (simp add: gb_schema_aux_term1_def eq1[symmetric] eq2[symmetric] z2 z3 in_lex_prod_alt)
      thus "y \<notin> Q"
      proof (elim disjE conjE)
        assume "(fst y, z0) \<in> measure length"
        hence "fst y \<notin> fst ` Q" by (rule 1)
        thus ?thesis by blast
      next
        assume "fst ` set (fst (snd y)) \<sqsupset>p z1"
        hence "fst ` set (fst (snd y)) \<notin> (image fst) ` set ` fst ` snd ` ?Q1" by (rule 2)
        moreover assume "fst y = z0"
        ultimately show ?thesis by auto
      next
        assume "(snd (snd y), z2) \<in> measure (card \<circ> set)"
        hence "snd (snd y) \<notin> snd ` snd ` ?Q2" by (rule 3)
        hence "y \<notin> ?Q2" by blast
        moreover assume "fst y = z0" and "fst (snd y) = fst z3"
        ultimately show ?thesis by (simp add: eq1 z3)
      qed
    qed
  qed
qed

lemma gb_schema_aux_term_wf:
  assumes "dickson_grading (+) d"
  shows "wf (gb_schema_aux_term d)"
proof (rule wfI_min)
  fix x::"(('t, 'b, 'c) pdata list) \<times> ('t, 'b, 'c) pdata list \<times> (('t, 'b, 'c) pdata_pair list)" and Q
  assume "x \<in> Q"
  let ?A = "args_to_set x"
  have "finite ?A" by (simp add: args_to_set_def)
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  define K where "K = component_of_term ` Keys ?A"
  from \<open>finite ?A\<close> have "finite K" unfolding K_def by (rule finite_imp_finite_component_Keys)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. args_to_set q \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set q) \<subseteq> K}"
  from assms \<open>finite K\<close> have "wfP_on {x. args_to_set x \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set x) \<subseteq> K}
                          (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1 d)"
    by (rule gb_schema_aux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by (simp add: K_def)
  moreover have "?Q \<subseteq> {x. args_to_set x \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set x) \<subseteq> K}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> gb_schema_aux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "args_to_set z \<subseteq> ?B" and b: "component_of_term ` Keys (args_to_set z) \<subseteq> K"
    by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> gb_schema_aux_term d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> gb_schema_aux_term d \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> gb_schema_aux_term d"
      hence "(y, z) \<in> gb_schema_aux_term1 d" and "(y, z) \<in> gb_schema_aux_term2 d"
        by (simp_all add: gb_schema_aux_term_def)
      from this(2) have "dgrad_p_set_le d (args_to_set y) (args_to_set z)"
        and comp_sub: "component_of_term ` Keys (args_to_set y) \<subseteq> component_of_term ` Keys (args_to_set z)"
        by (simp_all add: gb_schema_aux_term2_def)
      from this(1) \<open>args_to_set z \<subseteq> ?B\<close> have "args_to_set y \<subseteq> ?B" by (rule dgrad_p_set_le_dgrad_p_set)
      moreover from comp_sub b have "component_of_term ` Keys (args_to_set y) \<subseteq> K" by (rule subset_trans)
      moreover from \<open>(y, z) \<in> gb_schema_aux_term1 d\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

lemma dgrad_p_set_le_args_to_set_ab:
  assumes "dickson_grading (+) d" and "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  assumes "sps \<noteq> []" and "set sps \<subseteq> set ps" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
  unfolding args_to_set_alt2[OF assms(2, 3)] image_Un
proof (intro dgrad_p_set_leI_Un)
  show "dgrad_p_set_le d (fst ` set gs) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
next
  show "dgrad_p_set_le d (fst ` set bs) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
next
  show "dgrad_p_set_le d (fst ` fst ` set (ps -- sps)) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_diff_list)
next
  show "dgrad_p_set_le d (fst ` snd ` set (ps -- sps)) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_diff_list)
next
  from assms(4, 1, 5, 6) show "dgrad_p_set_le d (fst ` set hs) (args_to_set (gs, bs, ps))"
    unfolding assms(7) fst_set_add_indices by (rule compl_structD1)
qed

corollary dgrad_p_set_le_args_to_set_struct:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl" and "ps \<noteq> []"
  assumes "sps = sel gs bs ps data" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
proof -
  from assms(2) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(3) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding assms(4) by (rule sel_specD1, rule sel_specD2)
  from assms(1) ap ab compl this assms(5) show ?thesis by (rule dgrad_p_set_le_args_to_set_ab)
qed

lemma components_subset_ab:
  assumes "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  assumes "sps \<noteq> []" and "set sps \<subseteq> set ps" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
          component_of_term ` Keys (args_to_set (gs, bs, ps))"
  unfolding args_to_set_alt2[OF assms(1, 2)] image_Un Keys_Un Un_subset_iff
proof (intro conjI)
  show "component_of_term ` Keys (fst ` set gs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_def)
next
  show "component_of_term ` Keys (fst ` set bs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_def)
next
  show "component_of_term ` Keys (fst ` fst ` set (ps -- sps)) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_def set_diff_list)
next
  show "component_of_term ` Keys (fst ` snd ` set (ps -- sps)) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_def set_diff_list)
next
  from assms(3, 4, 5) show "component_of_term ` Keys (fst ` set hs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
    unfolding assms(6) fst_set_add_indices by (rule compl_structD2)
qed

corollary components_subset_struct:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []"
  assumes "sps = sel gs bs ps data" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
          component_of_term ` Keys (args_to_set (gs, bs, ps))"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(2) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding assms(3) by (rule sel_specD1, rule sel_specD2)
  from ap ab compl this assms(4) show ?thesis by (rule components_subset_ab)
qed

corollary components_struct:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  assumes "sps = sel gs bs ps data" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) =
          component_of_term ` Keys (args_to_set (gs, bs, ps))" (is "?l = ?r")
proof
  from assms(1, 2, 4, 5) show "?l \<subseteq> ?r" by (rule components_subset_struct)
next
  from assms(1) have ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD)+
  from ap ab assms(3)
  have sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  show "?r \<subseteq> ?l"
    by (simp add: args_to_set_subset_Times[OF sub] args_to_set_subset_Times[OF assms(3)] ab_specD1[OF ab],
        rule image_mono, rule Keys_mono, blast)
qed

lemma struct_spec_red_supset:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []" and "sps = sel gs bs ps data"
    and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)" and "hs \<noteq> []"
  shows "(fst ` set (ab gs bs hs data')) \<sqsupset>p (fst ` set bs)"
proof -
  from assms(5) have "set hs \<noteq> {}" by simp
  then obtain h' where "h' \<in> set hs" by fastforce
  let ?h = "fst h'"
  let ?m = "monomial (lc ?h) (lt ?h)"
  from \<open>h' \<in> set hs\<close> have h_in: "?h \<in> fst ` set hs" by simp
  hence "?h \<in> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
    by (simp only: assms(4) fst_set_add_indices)
  then obtain h'' where h''_in: "h'' \<in> set (fst (compl gs bs (ps -- sps) sps data))"
    and "?h = fst h''" ..
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(2) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding assms(3)
    by (rule sel_specD1, rule sel_specD2)
  from h_in compl_structD3[OF compl this] have "?h \<noteq> 0" unfolding assms(4) fst_set_add_indices
    by metis
  show ?thesis
  proof (simp add: ab_specD1[OF ab] image_Un, rule)
    fix q
    assume "is_red (fst ` set bs) q"
    moreover have "fst ` set bs \<subseteq> fst ` set bs \<union> fst ` set hs" by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set hs) q" by (rule is_red_subset)
  next
    from \<open>?h \<noteq> 0\<close> have "lc ?h \<noteq> 0" by (rule lc_not_0)
    moreover have "?h \<in> {?h}" ..
    ultimately have "is_red {?h} ?m" using \<open>?h \<noteq> 0\<close> adds_term_refl by (rule is_red_monomialI)
    moreover have "{?h} \<subseteq> fst ` set bs \<union> fst ` set hs" using h_in by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set hs) ?m" by (rule is_red_subset)
  next
    show "\<not> is_red (fst ` set bs) ?m"
    proof
      assume "is_red (fst ` set bs) ?m"
      then obtain b' where "b' \<in> fst ` set bs" and "b' \<noteq> 0" and "lt b' adds\<^sub>t lt ?h"
        by (rule is_red_monomialE)
      from this(1) obtain b where "b \<in> set bs" and b': "b' = fst b" ..
      from this(1) have "b \<in> set gs \<union> set bs" by simp
      from \<open>b' \<noteq> 0\<close> have "fst b \<noteq> 0" by (simp add: b')
      with compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> h''_in \<open>b \<in> set gs \<union> set bs\<close> have "\<not> lt (fst b) adds\<^sub>t lt ?h"
        unfolding \<open>?h = fst h''\<close> by (rule compl_structD4)
      from this \<open>lt b' adds\<^sub>t lt ?h\<close> show False by (simp add: b')
    qed
  qed
qed

lemma unique_idx_append:
  assumes "unique_idx gs data" and "(hs, data') = add_indices aux data"
  shows "unique_idx (gs @ hs) data'"
proof -
  from assms(2) have hs: "hs = fst (add_indices aux data)" and data': "data' = snd (add_indices aux data)"
    by (metis fst_conv, metis snd_conv)
  have len: "length hs = length (fst aux)" by (simp add: hs add_indices_def)
  have eq: "fst data' = fst data + length hs" by (simp add: data' add_indices_def hs)
  show ?thesis
  proof (rule unique_idxI)
    fix f g
    assume "f \<in> set (gs @ hs)" and "g \<in> set (gs @ hs)"
    hence d1: "f \<in> set gs \<union> set hs" and d2: "g \<in> set gs \<union> set hs" by simp_all
    assume id_eq: "fst (snd f) = fst (snd g)"
    from d1 show "f = g"
    proof
      assume "f \<in> set gs"
      from d2 show ?thesis
      proof
        assume "g \<in> set gs"
        from assms(1) \<open>f \<in> set gs\<close> this id_eq show ?thesis by (rule unique_idxD1)
      next
        assume "g \<in> set hs"
        then obtain j where "g = (fst (fst aux ! j), fst data + j, snd (fst aux ! j))" unfolding hs
          by (rule in_set_add_indicesE)
        hence "fst (snd g) = fst data + j" by simp
        moreover from assms(1) \<open>f \<in> set gs\<close> have "fst (snd f) < fst data"
          by (rule unique_idxD2)
        ultimately show ?thesis by (simp add: id_eq)
      qed
    next
      assume "f \<in> set hs"
      then obtain i where f: "f = (fst (fst aux ! i), fst data + i, snd (fst aux ! i))" unfolding hs
        by (rule in_set_add_indicesE)
      hence *: "fst (snd f) = fst data + i" by simp
      from d2 show ?thesis
      proof
        assume "g \<in> set gs"
        with assms(1) have "fst (snd g) < fst data" by (rule unique_idxD2)
        with * show ?thesis by (simp add: id_eq)
      next
        assume "g \<in> set hs"
        then obtain j where g: "g = (fst (fst aux ! j), fst data + j, snd (fst aux ! j))" unfolding hs
          by (rule in_set_add_indicesE)
        hence "fst (snd g) = fst data + j" by simp
        with * have "i = j" by (simp add: id_eq)
        thus ?thesis by (simp add: f g)
      qed
    qed
  next
    fix f
    assume "f \<in> set (gs @ hs)"
    hence "f \<in> set gs \<union> set hs" by simp
    thus "fst (snd f) < fst data'"
    proof
      assume "f \<in> set gs"
      with assms(1) have "fst (snd f) < fst data" by (rule unique_idxD2)
      also have "... \<le> fst data'" by (simp add: eq)
      finally show ?thesis .
    next
      assume "f \<in> set hs"
      then obtain i where "i < length (fst aux)"
        and "f = (fst (fst aux ! i), fst data + i, snd (fst aux ! i))" unfolding hs
        by (rule in_set_add_indicesE)
      from this(2) have "fst (snd f) = fst data + i" by simp
      also from \<open>i < length (fst aux)\<close> have "... < fst data + length (fst aux)" by simp
      finally show ?thesis by (simp only: eq len)
    qed
  qed
qed

corollary unique_idx_ab:
  assumes "ab_spec ab" and "unique_idx (gs @ bs) data" and "(hs, data') = add_indices aux data"
  shows "unique_idx (gs @ ab gs bs hs data') data'"
proof -
  from assms(2, 3) have "unique_idx ((gs @ bs) @ hs) data'" by (rule unique_idx_append)
  thus ?thesis by (simp add: unique_idx_def ab_specD1[OF assms(1)])
qed

lemma rem_comps_spec_struct:
  assumes "struct_spec sel ap ab compl" and "rem_comps_spec (gs @ bs) data" and "ps \<noteq> []"
    and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)" and "sps = sel gs bs ps (snd data)"
    and "aux = compl gs bs (ps -- sps) sps (snd data)" and "(hs, data') = add_indices aux (snd data)"
  shows "rem_comps_spec (gs @ ab gs bs hs data') (fst data - count_const_lt_components (fst aux), data')"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD)+
  from ap ab assms(4)
  have sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  have hs: "hs = fst (add_indices aux (snd data))" by (simp add: assms(7)[symmetric])
  from sel assms(3) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding assms(5)
    by (rule sel_specD1, rule sel_specD2)
  have eq0: "fst ` set (fst aux) - {0} = fst ` set (fst aux)"
    by (rule Diff_triv, simp add: Int_insert_right assms(6), rule compl_structD3, fact+)
  have "component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')) =
        component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data'))"
    by (simp add: args_to_set_subset_Times[OF sub] image_Un)
  also from assms(1, 3, 4, 5) hs
  have "... = component_of_term ` Keys (args_to_set (gs, bs, ps))" unfolding assms(6)
    by (rule components_struct)
  also have "... = component_of_term ` Keys (fst ` set (gs @ bs))"
    by (simp add: args_to_set_subset_Times[OF assms(4)] image_Un)
  finally have eq: "component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')) =
                      component_of_term ` Keys (fst ` set (gs @ bs))" .
  from assms(2)
  have eq2: "card (component_of_term ` Keys (fst ` set (gs @ bs))) =
             fst data + card (const_lt_component ` (fst ` set (gs @ bs) - {0}) - {None})" (is "?a = _ + ?b")
    by (simp only: rem_comps_spec_def)
  have eq3: "card (const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0}) - {None}) =
              ?b + count_const_lt_components (fst aux)" (is "?c = _")
  proof (simp add: ab_specD1[OF ab] image_Un Un_assoc[symmetric] Un_Diff count_const_lt_components_alt
        hs fst_set_add_indices eq0, rule card_Un_disjoint)
    show "finite (const_lt_component ` (fst ` set gs - {0}) - {None} \<union> (const_lt_component ` (fst ` set bs - {0}) - {None}))"
      by (intro finite_UnI finite_Diff finite_imageI finite_set)
  next
    show "finite (const_lt_component ` fst ` set (fst aux) - {None})"
      by (rule finite_Diff, intro finite_imageI, fact finite_set)
  next
    have "(const_lt_component ` (fst ` (set gs \<union> set bs) - {0}) - {None}) \<inter>
          (const_lt_component ` fst ` set (fst aux) - {None}) =
          (const_lt_component ` (fst ` (set gs \<union> set bs) - {0}) \<inter>
          const_lt_component ` fst ` set (fst aux)) - {None}" by blast
    also have "... = {}"
    proof (simp, rule, simp, elim conjE)
      fix k
      assume "k \<in> const_lt_component ` (fst ` (set gs \<union> set bs) - {0})"
      then obtain b where "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0" and k1: "k = const_lt_component (fst b)"
        by blast
      assume "k \<in> const_lt_component ` fst ` set (fst aux)"
      then obtain h where "h \<in> set (fst aux)" and k2: "k = const_lt_component (fst h)" by blast
      show "k = None"
      proof (rule ccontr, simp, elim exE)
        fix k'
        assume "k = Some k'"
        hence "lp (fst b) = 0" and "component_of_term (lt (fst b)) = k'" unfolding k1
          by (rule const_lt_component_SomeD1, rule const_lt_component_SomeD2)
        moreover from \<open>k = Some k'\<close> have "lp (fst h) = 0" and "component_of_term (lt (fst h)) = k'"
          unfolding k2 by (rule const_lt_component_SomeD1, rule const_lt_component_SomeD2)
        ultimately have "lt (fst b) adds\<^sub>t lt (fst h)" by (simp add: adds_term_def)
        moreover from compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> \<open>h \<in> set (fst aux)\<close> \<open>b \<in> set gs \<union> set bs\<close> \<open>fst b \<noteq> 0\<close>
        have "\<not> lt (fst b) adds\<^sub>t lt (fst h)" unfolding assms(6) by (rule compl_structD4)
        ultimately show False by simp
      qed
    qed
    finally show "(const_lt_component ` (fst ` set gs - {0}) - {None} \<union> (const_lt_component ` (fst ` set bs - {0}) - {None})) \<inter>
          (const_lt_component ` fst ` set (fst aux) - {None}) = {}" by (simp only: Un_Diff image_Un)
  qed
  have "?c \<le> ?a" unfolding eq[symmetric]
    by (rule card_const_lt_component_le, rule finite_imageI, fact finite_set)
  hence le: "count_const_lt_components (fst aux) \<le> fst data" by (simp only: eq2 eq3)
  show ?thesis by (simp only: rem_comps_spec_def eq eq2 eq3, simp add: le)
qed

lemma pmdl_struct:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "ps \<noteq> []" and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) (snd data)"
    and "sps = sel gs bs ps (snd data)" and "aux = compl gs bs (ps -- sps) sps (snd data)"
    and "(hs, data') = add_indices aux (snd data)"
  shows "pmdl (fst ` set (gs @ ab gs bs hs data')) = pmdl (fst ` set (gs @ bs))"
proof -
  have hs: "hs = fst (add_indices aux (snd data))" by (simp add: assms(9)[symmetric])
  from assms(1) have sel: "sel_spec sel" and ab: "ab_spec ab" by (rule struct_specD)+
  have eq: "fst ` (set gs \<union> set (ab gs bs hs data')) = fst ` (set gs \<union> set bs) \<union> fst ` set hs"
    by (auto simp add: ab_specD1[OF ab])
  show ?thesis
  proof (simp add: eq, rule)
    show "pmdl (fst ` (set gs \<union> set bs) \<union> fst ` set hs) \<subseteq> pmdl (fst ` (set gs \<union> set bs))"
    proof (rule pmdl.module_subset_moduleI, simp only: Un_subset_iff, rule)
      show "fst ` (set gs \<union> set bs) \<subseteq> pmdl (fst ` (set gs \<union> set bs))"
        by (fact pmdl.generator_subset_module)
    next
      from sel assms(4) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
        unfolding assms(7) by (rule sel_specD1, rule sel_specD2)
      with assms(2, 3) have "fst ` set hs \<subseteq> pmdl (args_to_set (gs, bs, ps))"
        unfolding hs assms(8) fst_set_add_indices using assms(6) by (rule compl_pmdlD)
      thus "fst ` set hs \<subseteq> pmdl (fst ` (set gs \<union> set bs))"
        by (simp only: args_to_set_subset_Times[OF assms(5)] image_Un)
    qed
  next
    show "pmdl (fst ` (set gs \<union> set bs)) \<subseteq> pmdl (fst ` (set gs \<union> set bs) \<union> fst ` set hs)"
      by (rule pmdl.module_mono, blast)
  qed
qed

function (domintros) gb_schema_aux :: "('t, 'b, 'c, 'd) selT \<Rightarrow> ('t, 'b, 'c, 'd) apT \<Rightarrow> ('t, 'b, 'c, 'd) abT \<Rightarrow>
                        ('t, 'b, 'c, 'd) complT \<Rightarrow> nat \<times> nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                        ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b::zero_neq_one, 'c::default) pdata list"
  where
    "gb_schema_aux sel ap ab compl data gs bs ps =
        (if ps = [] then
          gs @ bs
        else
          (let sps = sel gs bs ps (snd data); ps0 = ps -- sps; aux = compl gs bs ps0 sps (snd data);
               remcomps = fst (data) - count_const_lt_components (fst aux) in
            (if remcomps = 0 then
              full_gb (gs @ bs)
            else
              let (hs, data') = add_indices aux (snd data) in
                gb_schema_aux sel ap ab compl (remcomps, data') gs (ab gs bs hs data') (ap gs bs ps0 hs data')
            )
          )
        )"
  by pat_completeness auto

text \<open>The \<open>data\<close> parameter of @{const gb_schema_aux} is a triple \<open>(c, i, d)\<close>, where \<open>c\<close> is the
  number of components \<open>cmp\<close> of the input list for which the current basis \<open>gs @ bs\<close> does @{emph \<open>not\<close>}
  yet contain an element whose leading power-product is \<open>0\<close> and has component \<open>cmp\<close>. As soon as \<open>c\<close>
  gets \<open>0\<close>, the function can return a trivial Gr\"obner basis, since then the submodule generated by
  the input list is just the full module. This idea generalizes the well-known fact that if a set of
  scalar polynomials contains a non-zero constant, the ideal generated by that set is the whole ring.
  \<open>i\<close> is the total number of polynomials generated during the execution of the function so far; it
  is used to attach unique indices to the polynomials for fast equality tests.
  \<open>d\<close>, finally, is some arbitrary data-field that may be used by concrete instances of
  @{const gb_schema_aux} for storing information.\<close>

lemma gb_schema_aux_domI1: "gb_schema_aux_dom (sel, ap, ab, compl, data, gs, bs, [])"
  by (rule gb_schema_aux.domintros, simp)

lemma gb_schema_aux_domI2:
  assumes "struct_spec sel ap ab compl"
  shows "gb_schema_aux_dom (sel, ap, ab, compl, data, args)"
proof -
  from assms have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gb_schema_aux_term d"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  thus ?thesis
  proof (induct args arbitrary: data rule: wf_induct_rule)
    fix x data
    assume IH: "\<And>y data'. (y, x) \<in> ?R \<Longrightarrow> gb_schema_aux_dom (sel, ap, ab, compl, data', y)"
    obtain gs bs0 where x: "x = (gs, bs0)" by (meson case_prodE case_prodI2)
    obtain bs ps where bs0: "bs0 = (bs, ps)" by (meson case_prodE case_prodI2)
    show "gb_schema_aux_dom (sel, ap, ab, compl, data, x)" unfolding x bs0
    proof (rule gb_schema_aux.domintros)
      fix rc0 n0 data0 hs n1 data1
      assume "ps \<noteq> []"
        and hs_data': "(hs, n1, data1) = add_indices (compl gs bs (ps -- sel gs bs ps (n0, data0))
                                               (sel gs bs ps (n0, data0)) (n0, data0)) (n0, data0)"
        and data: "data = (rc0, n0, data0)"
      define sps where "sps = sel gs bs ps (n0, data0)"
      define data' where "data' = (n1, data1)"
      define rc where "rc = rc0 - count_const_lt_components (fst (compl gs bs (ps -- sel gs bs ps (n0, data0))
                                                                  (sel gs bs ps (n0, data0)) (n0, data0)))"
      from hs_data' have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps (snd data)) (snd data))"
        unfolding sps_def data snd_conv by (metis fstI)
      show "gb_schema_aux_dom (sel, ap, ab, compl, (rc, data'), gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')"
      proof (rule IH, simp add: x bs0 gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, intro conjI)
        show "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs \<or>
                ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
        proof (cases "hs = []")
          case True
          have "ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
          proof (simp only: True ap_spec_Nil_new[OF ap], rule)
            from ab show "ab gs bs [] data' = bs" by (rule ab_specD2)
          next
            from sel \<open>ps \<noteq> []\<close> have "sps \<noteq> []" and "set sps \<subseteq> set ps"
              unfolding sps_def by (rule sel_specD1, rule sel_specD2)
            moreover from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
            ultimately have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
            hence "set (ps -- sps) \<subset> set ps" unfolding set_diff_list by fastforce
            thus "card (set (ps -- sps)) < card (set ps)" by (simp add: psubset_card_mono)
          qed
          thus ?thesis ..
        next
          case False
          with assms \<open>ps \<noteq> []\<close> sps_def hs have "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs"
            unfolding data snd_conv by (rule struct_spec_red_supset)
          thus ?thesis ..
        qed
      next
        from dg assms \<open>ps \<noteq> []\<close> sps_def hs
        show "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
          unfolding data snd_conv by (rule dgrad_p_set_le_args_to_set_struct)
      next
        from assms \<open>ps \<noteq> []\<close> sps_def hs
        show "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
              component_of_term ` Keys (args_to_set (gs, bs, ps))"
          unfolding data snd_conv by (rule components_subset_struct)
      qed
    qed
  qed
qed

lemmas gb_schema_aux_simp = gb_schema_aux.psimps[OF gb_schema_aux_domI2]

lemma gb_schema_aux_Nil [simp, code]: "gb_schema_aux sel ap ab compl data gs bs [] = gs @ bs"
  by (simp add: gb_schema_aux.psimps[OF gb_schema_aux_domI1])

lemma gb_schema_aux_not_Nil:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []"
  shows "gb_schema_aux sel ap ab compl data gs bs ps =
          (let sps = sel gs bs ps (snd data); ps0 = ps -- sps; aux = compl gs bs ps0 sps (snd data);
               remcomps = fst (data) - count_const_lt_components (fst aux) in
            (if remcomps = 0 then
              full_gb (gs @ bs)
            else
              let (hs, data') = add_indices aux (snd data) in
                gb_schema_aux sel ap ab compl (remcomps, data') gs (ab gs bs hs data') (ap gs bs ps0 hs data')
            )
          )"
  by (simp add: gb_schema_aux_simp[OF assms(1)] assms(2))

text \<open>In order to prove the following lemma we again have to employ well-founded induction, since
  @{thm gb_schema_aux.pinduct} does not treat the first arguments of @{const gb_schema_aux} in the proper way.\<close>
lemma gb_schema_aux_induct [consumes 1, case_names base rec1 rec2]:
  assumes "struct_spec sel ap ab compl"
  assumes base: "\<And>bs data. P data bs [] (gs @ bs)"
    and rec1: "\<And>bs ps sps data. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                fst (data) \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data))) \<Longrightarrow>
                P data bs ps (full_gb (gs @ bs))"
    and rec2: "\<And>bs ps sps aux hs rc data data'. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                aux = compl gs bs (ps -- sps) sps (snd data) \<Longrightarrow> (hs, data') = add_indices aux (snd data) \<Longrightarrow>
                rc = fst data - count_const_lt_components (fst aux) \<Longrightarrow> 0 < rc \<Longrightarrow>
                P (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_aux sel ap ab compl (rc, data') gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')) \<Longrightarrow>
                P data bs ps (gb_schema_aux sel ap ab compl (rc, data') gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
  shows "P data bs ps (gb_schema_aux sel ap ab compl data gs bs ps)"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    by (rule struct_specD)+
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gb_schema_aux_term d"
  define args where "args = (gs, bs, ps)"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  hence "fst args = gs \<Longrightarrow> P data (fst (snd args)) (snd (snd args))
              (gb_schema_aux sel ap ab compl data gs (fst (snd args)) (snd (snd args)))"
  proof (induct arbitrary: data)
    fix x data
    assume IH': "\<And>y data'. (y, x) \<in> gb_schema_aux_term d \<Longrightarrow> fst y = gs \<Longrightarrow>
                   P data' (fst (snd y)) (snd (snd y)) (gb_schema_aux sel ap ab compl data' gs (fst (snd y)) (snd (snd y)))"
    assume "fst x = gs"
    then obtain bs0 where x: "x = (gs, bs0)" by (meson eq_fst_iff)
    obtain bs ps where bs0: "bs0 = (bs, ps)" by (meson case_prodE case_prodI2)
    from IH' have IH: "\<And>bs' ps' data'. ((gs, bs', ps'), (gs, bs, ps)) \<in> gb_schema_aux_term d \<Longrightarrow>
                   P data' bs' ps' (gb_schema_aux sel ap ab compl data' gs bs' ps')" unfolding x bs0 by auto
    show "P data (fst (snd x)) (snd (snd x))
              (gb_schema_aux sel ap ab compl data gs (fst (snd x)) (snd (snd x)))"
    proof (simp add: x bs0, cases "ps = []")
      case True
      from base show "P data bs ps (gb_schema_aux sel ap ab compl data gs bs ps)" by (simp add: True)
    next
      case False
      show "P data bs ps (gb_schema_aux sel ap ab compl data gs bs ps)"
      proof (simp add: gb_schema_aux_not_Nil[OF assms(1) False] Let_def case_prod_beta, intro conjI impI)
        define sps where "sps = sel gs bs ps (snd data)"
        assume "fst data \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data)))"
        from False sps_def this show "P data bs ps (full_gb (gs @ bs))"
          by (rule rec1)
      next
        define sps where "sps = sel gs bs ps (snd data)"
        define aux where "aux = compl gs bs (ps -- sps) sps (snd data)"
        define hs where "hs = fst (add_indices aux (snd data))"
        define data' where "data' = snd (add_indices aux (snd data))"
        define rc where "rc = fst data - count_const_lt_components (fst aux)"
        assume a: "\<not> fst data \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data)))"
        hence "0 < rc" by (simp add: rc_def aux_def)
        have "(hs, data') = add_indices aux (snd data)" by (simp add: hs_def data'_def)
        from False sps_def aux_def this rc_def \<open>0 < rc\<close>
        show "P data bs ps (gb_schema_aux sel ap ab compl (rc, data') gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
        proof (rule rec2)
          show "P (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                    (gb_schema_aux sel ap ab compl (rc, data') gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
          proof (rule IH, simp add: x bs0 gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, intro conjI)
            show "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs \<or>
                      ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
            proof (cases "hs = []")
              case True
              have "ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
              proof (simp only: True ap_spec_Nil_new[OF ap], rule)
                from ab show "ab gs bs [] data' = bs" by (rule ab_specD2)
              next
                from sel False have "sps \<noteq> []" and "set sps \<subseteq> set ps"
                  unfolding sps_def by (rule sel_specD1, rule sel_specD2)
                moreover from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
                ultimately have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
                hence "set (ps -- sps) \<subset> set ps" unfolding set_diff_list by fastforce
                thus "card (set (ps -- sps)) < card (set ps)" by (simp add: psubset_card_mono)
              qed
              thus ?thesis ..
            next
              case False
              with assms(1) \<open>ps \<noteq> []\<close> sps_def hs_def have "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs"
                unfolding aux_def by (rule struct_spec_red_supset)
              thus ?thesis ..
            qed
          next
            from dg assms(1) False sps_def hs_def
            show "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
              unfolding aux_def by (rule dgrad_p_set_le_args_to_set_struct)
          next
            from assms(1) False sps_def hs_def
            show "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
                  component_of_term ` Keys (args_to_set (gs, bs, ps))"
              unfolding aux_def by (rule components_subset_struct)
          qed
        qed
      qed
    qed
  qed
  thus ?thesis by (simp add: args_def)
qed

lemma gb_schema_aux_dgrad_p_set_le:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_aux sel ap ab compl data gs bs ps)) (args_to_set (gs, bs, ps))"
  using assms(2)
proof (induct rule: gb_schema_aux_induct)
  case (base bs data)
  show ?case by (simp add: args_to_set_def, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (rec1 bs ps sps data)
  show ?case
  proof (cases "fst ` set gs \<union> fst ` set bs \<subseteq> {0}")
    case True
    hence "Keys (fst ` set (gs @ bs)) = {}" by (auto simp add: image_Un Keys_def)
    hence "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) = {}"
      by (simp add: components_full_gb)
    hence "Keys (fst ` set (full_gb (gs @ bs))) = {}" by simp
    thus ?thesis by (simp add: dgrad_p_set_le_def dgrad_set_le_def)
  next
    case False
    from pps_full_gb have "dgrad_set_le d (pp_of_term ` Keys (fst ` set (full_gb (gs @ bs)))) {0}"
      by (rule dgrad_set_le_subset)
    also have "dgrad_set_le d ... (pp_of_term ` Keys (args_to_set (gs, bs, ps)))"
    proof (rule dgrad_set_leI, simp)
      from False have "Keys (args_to_set (gs, bs, ps)) \<noteq> {}"
        by (simp add: args_to_set_alt Keys_Un, metis Keys_not_empty singletonI subsetI)
      then obtain v where "v \<in> Keys (args_to_set (gs, bs, ps))" by blast
      moreover have "d 0 \<le> d (pp_of_term v)" by (simp add: assms(1) dickson_grading_adds_imp_le)
      ultimately show "\<exists>t\<in>Keys (args_to_set (gs, bs, ps)). d 0 \<le> d (pp_of_term t)" ..
    qed
    finally show ?thesis by (simp add: dgrad_p_set_le_def)
  qed
next
  case (rec2 bs ps sps aux hs rc data data')
  from rec2(4) have "hs = fst (add_indices (compl gs bs (ps -- sps) sps (snd data)) (snd data))"
    unfolding rec2(3) by (metis fstI)
  with assms rec2(1, 2)
  have "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_args_to_set_struct)
  with rec2(7) show ?case by (rule dgrad_p_set_le_trans)
qed

lemma gb_schema_aux_components:
  assumes "struct_spec sel ap ab compl" and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)"
  shows "component_of_term ` Keys (fst ` set (gb_schema_aux sel ap ab compl data gs bs ps)) =
          component_of_term ` Keys (args_to_set (gs, bs, ps))"
  using assms
proof (induct rule: gb_schema_aux_induct)
  case (base bs data)
  show ?case by (simp add: args_to_set_def)
next
  case (rec1 bs ps sps data)
  have "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) =
        component_of_term ` Keys (fst ` set (gs @ bs))" by (fact components_full_gb)
  also have "... = component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (simp add: args_to_set_subset_Times[OF rec1.prems] image_Un)
  finally show ?case .
next
  case (rec2 bs ps sps aux hs rc data data')
  from assms(1) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from this rec2.prems
  have sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  from rec2(4) have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps (snd data)) (snd data))"
    unfolding rec2(3) by (metis fstI)
  have "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) =
        component_of_term ` Keys (args_to_set (gs, bs, ps))" (is "?l = ?r")
  proof
    from assms(1) rec2(1, 2) hs show "?l \<subseteq> ?r" by (rule components_subset_struct)
  next
    show "?r \<subseteq> ?l"
      by (simp add: args_to_set_subset_Times[OF rec2.prems] args_to_set_alt2[OF ap ab] image_Un,
          rule image_mono, rule Keys_mono, blast)
  qed
  with rec2.hyps(7)[OF sub] show ?case by (rule trans)
qed

lemma gb_schema_aux_pmdl:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) (snd data)"
    and "rem_comps_spec (gs @ bs) data"
  shows "pmdl (fst ` set (gb_schema_aux sel ap ab compl data gs bs ps)) = pmdl (fst ` set (gs @ bs))"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD)+
  from assms(1, 4, 5, 6) show ?thesis
  proof (induct bs ps rule: gb_schema_aux_induct)
    case (base bs data)
    show ?case ..
  next
    case (rec1 bs ps sps data)
    define aux where "aux = compl gs bs (ps -- sps) sps (snd data)"
    define data' where "data' = snd (add_indices aux (snd data))"
    define hs where "hs = fst (add_indices aux (snd data))"
    have hs_data': "(hs, data') = add_indices aux (snd data)" by (simp add: hs_def data'_def)
    have eq: "set (gs @ ab gs bs hs data') = set (gs @ bs @ hs)" by (simp add: ab_specD1[OF ab])
    from sel rec1(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding rec1(2)
      by (rule sel_specD1, rule sel_specD2)
    from full_gb_is_full_pmdl have "pmdl (fst ` set (full_gb (gs @ bs))) = pmdl (fst ` set (gs @ ab gs bs hs data'))"
    proof (rule is_full_pmdl_eq)
      show "is_full_pmdl (fst ` set (gs @ ab gs bs hs data'))"
      proof (rule is_full_pmdlI_lt_finite)
        from finite_set show "finite (fst ` set (gs @ ab gs bs hs data'))" by (rule finite_imageI)
      next
        fix k
        assume "k \<in> component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data'))"
        hence "Some k \<in> Some ` component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data'))" by simp
        also have "... = const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0}) - {None}" (is "?A = ?B")
        proof (rule card_seteq[symmetric])
          show "finite ?A" by (intro finite_imageI finite_Keys, fact finite_set)
        next
          have "rem_comps_spec (gs @ ab gs bs hs data') (fst data - count_const_lt_components (fst aux), data')"
            using assms(1) rec1.prems(3) rec1.hyps(1) rec1.prems(1) rec1.hyps(2) aux_def hs_data'
            by (rule rem_comps_spec_struct)
          also have "... = (0, data')" by (simp add: aux_def rec1.hyps(3))
          finally have "card (const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0}) - {None}) =
                        card (component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')))"
            by (simp add: rem_comps_spec_def)
          also have "... = card (Some ` component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')))"
            by (rule card_image[symmetric], simp)
          finally show "card ?A \<le> card ?B" by simp
        qed (fact const_lt_component_subset)
        finally have "Some k \<in> const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0})"
          by simp
        then obtain b where "b \<in> fst ` set (gs @ ab gs bs hs data')" and "b \<noteq> 0"
          and *: "const_lt_component b = Some k" by fastforce
        show "\<exists>b\<in>fst ` set (gs @ ab gs bs hs data'). b \<noteq> 0 \<and> component_of_term (lt b) = k \<and> lp b = 0"
        proof (intro bexI conjI)
          from * show "component_of_term (lt b) = k" by (rule const_lt_component_SomeD2)
        next
          from * show "lp b = 0" by (rule const_lt_component_SomeD1)
        qed fact+
      qed
    next
      from compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close>
      have "component_of_term ` Keys (fst ` set hs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
        unfolding hs_def aux_def fst_set_add_indices by (rule compl_structD2)
      hence sub: "component_of_term ` Keys (fst ` set hs) \<subseteq> component_of_term ` Keys (fst ` set (gs @ bs))"
        by (simp add: args_to_set_subset_Times[OF rec1.prems(1)] image_Un)
      have "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) =
            component_of_term ` Keys (fst ` set (gs @ bs))" by (fact components_full_gb)
      also have "... = component_of_term ` Keys (fst ` set ((gs @ bs) @ hs))"
        by (simp only: set_append[of _ hs] image_Un Keys_Un Un_absorb2 sub)
      finally show "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) =
                    component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data'))"
        by (simp only: eq append_assoc)
    qed
    also have "... = pmdl (fst ` set (gs @ bs))"
      using assms(1, 2, 3) rec1.hyps(1) rec1.prems(1, 2) rec1.hyps(2) aux_def hs_data'
      by (rule pmdl_struct)
    finally show ?case .
  next
    case (rec2 bs ps sps aux hs rc data data')
    from rec2(4) have hs: "hs = fst (add_indices aux (snd data))" by (metis fstI)
    have "pmdl (fst ` set (gb_schema_aux sel ap ab compl (rc, data') gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))) =
          pmdl (fst ` set (gs @ ab gs bs hs data'))"
    proof (rule rec2(7))
      from ap ab rec2(8) show "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
        by (rule subset_Times_ap)
    next
      from ab rec2.prems(2) rec2(4) show "unique_idx (gs @ ab gs bs hs data') (snd (rc, data'))"
        unfolding snd_conv by (rule unique_idx_ab)
    next
      show "rem_comps_spec (gs @ ab gs bs hs data') (rc, data')" unfolding rec2.hyps(5)
        using assms(1) rec2.prems(3) rec2.hyps(1) rec2.prems(1) rec2.hyps(2, 3, 4)
        by (rule rem_comps_spec_struct)
    qed
    also have "... = pmdl (fst ` set (gs @ bs))"
      using assms(1, 2, 3) rec2.hyps(1) rec2.prems(1, 2) rec2.hyps(2, 3, 4) by (rule pmdl_struct)
    finally show ?case .
  qed
qed

lemma gb_schema_aux_connectible:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "dickson_grading (+) d"
    and "fst ` set gs \<subseteq> dgrad_p_set d m" and "is_Groebner_basis (fst ` set gs)"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)"
    and "unique_idx (gs @ bs) (snd data)"
    and "\<And>p q. processed (p, q) (gs @ bs) ps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)"
  assumes "f \<in> set (gb_schema_aux sel ap ab compl data gs bs ps)"
    and "g \<in> set (gb_schema_aux sel ap ab compl data gs bs ps)" and "fst f \<noteq> 0" and "fst g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` set (gb_schema_aux sel ap ab compl data gs bs ps)) (fst f) (fst g)"
  using assms(1, 6, 7, 8, 9, 10, 11)
proof (induct rule: gb_schema_aux_induct)
  case (base bs data)
  show ?case
  proof (cases "f \<in> set gs")
    case True
    show ?thesis
    proof (cases "g \<in> set gs")
      case True
      note assms(3, 4, 5)
      moreover from \<open>f \<in> set gs\<close> have "fst f \<in> fst ` set gs" by simp
      moreover from \<open>g \<in> set gs\<close> have "fst g \<in> fst ` set gs" by simp
      ultimately have "crit_pair_cbelow_on d m (fst ` set gs) (fst f) (fst g)"
        using assms(12, 13) by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
      moreover have "fst ` set gs \<subseteq> fst ` set (gs @ bs)" by auto
      ultimately show ?thesis by (rule crit_pair_cbelow_mono)
    next
      case False
      from this base(5, 6) have "processed (g, f) (gs @ bs) []" by (simp add: processed_Nil)
      from this \<open>fst g \<noteq> 0\<close> \<open>fst f \<noteq> 0\<close> have "crit_pair_cbelow_on d m (fst ` set (gs @ bs)) (fst g) (fst f)"
        unfolding set_append by (rule base(4))
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
  next
    case False
    from this base(5, 6) have "processed (f, g) (gs @ bs) []" by (simp add: processed_Nil)
    from this \<open>fst f \<noteq> 0\<close> \<open>fst g \<noteq> 0\<close> show ?thesis unfolding set_append by (rule base(4))
  qed
next
  case (rec1 bs ps sps data)
  note assms(3)
  moreover have "fst ` set (full_gb (gs @ bs)) \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    have eq: "full_gb (gs @ bs) = gb_schema_aux sel ap ab compl data gs bs ps"
      by (simp add: gb_schema_aux_not_Nil[OF assms(1) \<open>ps \<noteq> []\<close>] rec1.hyps(3) rec1.hyps(2)[symmetric])
    have "dgrad_p_set_le d (fst ` set (full_gb (gs @ bs))) (args_to_set (gs, bs, ps))"
      unfolding eq using assms(3, 1) by (rule gb_schema_aux_dgrad_p_set_le)
    also from rec1.prems(2) have "... = fst ` set gs \<union> fst ` set bs" by (rule args_to_set_subset_Times)
    finally show "dgrad_p_set_le d (fst ` set (full_gb (gs @ bs))) (fst ` set gs \<union> fst ` set bs)" .
  next
    from assms(4) rec1.prems(1) show "fst ` set gs \<union> fst ` set bs \<subseteq> dgrad_p_set d m" by blast
  qed
  moreover note full_gb_isGB
  moreover from rec1.prems(5) have "fst f \<in> fst ` set (full_gb (gs @ bs))" by simp
  moreover from rec1.prems(6) have "fst g \<in> fst ` set (full_gb (gs @ bs))" by simp
  ultimately show ?case using assms(12, 13) by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
next
  case (rec2 bs ps sps aux hs rc data data')
  from rec2(4) have hs: "hs = fst (add_indices aux (snd data))" by (metis fstI)
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3, rule struct_specD4)
  from sel rec2(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding rec2(2) by (rule sel_specD1, rule sel_specD2)
  from ap ab rec2(9) have ap_sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq>
                                    set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  have ns_sub: "fst ` set hs \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from compl assms(3) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close>
    show "dgrad_p_set_le d (fst ` set hs) (args_to_set (gs, bs, ps))"
      unfolding hs rec2.hyps(3) fst_set_add_indices by (rule compl_structD1)
  next
    from assms(4) rec2(8) show "args_to_set (gs, bs, ps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF rec2(9)])
  qed
  with rec2(8) have ab_sub: "fst ` set (ab gs bs hs data') \<subseteq> dgrad_p_set d m"
    by (auto simp add: ab_specD1[OF ab])

  have cpq: "(p, q) \<in> set sps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)" for p q
  proof -
    assume "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    with assms(2, 3, 4, 5) rec2(8, 9) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> rec2.prems(3) _
    have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps (snd data))))
            (fst p) (fst q)"
    proof (rule compl_connD)
      fix p' q'
      assume "processed (p', q') (gs @ bs) ps" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
        by (rule rec2(11))
    qed
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)"
      by (simp add: ab_specD1[OF ab] hs rec2.hyps(3) fst_set_add_indices image_Un Un_assoc)
  qed

  from ab_sub ap_sub _ _ rec2(12, 13) show ?case
  proof (rule rec2(7))
    from ab rec2.prems(3) rec2(4) show "unique_idx (gs @ ab gs bs hs data') (snd (rc, data'))"
      unfolding snd_conv by (rule unique_idx_ab)
  next
    fix p q :: "('t, 'b, 'c) pdata"
    assume "fst p \<noteq> 0" and "fst q \<noteq> 0"
    assume proc: "processed (p, q) (gs @ ab gs bs hs data') (ap gs bs (ps -- sps) hs data')"
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)"
    proof (cases "component_of_term (lt (fst p)) = component_of_term (lt (fst q))")
      case True
      with ap ab proc show ?thesis
      proof (rule processed_apE)
        assume "processed (p, q) (gs @ bs) (ps -- sps)"
        thus ?thesis
        proof (rule processed_minus)
          assume "(p, q) \<in> set sps"
          from this \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> show ?thesis by (rule cpq)
        next
          assume "(q, p) \<in> set sps"
          from this \<open>fst q \<noteq> 0\<close> \<open>fst p \<noteq> 0\<close>
          have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst q) (fst p)"
            by (rule cpq)
          thus ?thesis by (rule crit_pair_cbelow_sym)
        next
          assume "processed (p, q) (gs @ bs) ps"
          from this \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
          have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)" by (rule rec2(11))
          moreover have "fst ` (set gs \<union> set bs) \<subseteq> fst ` (set gs \<union> set (ab gs bs hs data'))"
            by (auto simp add: ab_specD1[OF ab])
          ultimately show ?thesis by (rule crit_pair_cbelow_mono)
        qed
      next
        assume "p \<in> set hs" and "q \<in> set hs"
        show ?thesis
        proof (cases "p = q")
          case True
          from \<open>q \<in> set hs\<close> have "fst q \<in> fst ` set hs" by simp
          from this ns_sub have "fst q \<in> dgrad_p_set d m" ..
          with assms(3) show ?thesis unfolding True by (rule crit_pair_cbelow_same)
        next
          case False
          with ap \<open>p \<in> set hs\<close> \<open>q \<in> set hs\<close>
          have "\<not> processed (p, q) (gs @ (ab gs bs hs data')) (ap gs bs (ps -- sps) hs data')"
          proof (rule ap_specE)
            assume "(p, q) \<in> set (ap gs bs (ps -- sps) hs data')"
            thus ?thesis by (simp add: processed_def)
          next
            assume "(q, p) \<in> set (ap gs bs (ps -- sps) hs data')"
            thus ?thesis by (simp add: processed_def)
          qed fact
          from this proc show ?thesis ..
        qed
      qed
    next
      case False
      thus ?thesis by (rule crit_pair_cbelow_distinct_component)
    qed
  qed
qed

lemma gb_schema_aux_dgrad_p_set_le_init:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_aux sel ap ab compl data gs (ab gs [] bs (snd data)) (ap gs [] [] bs (snd data))))
                          (fst ` (set gs \<union> set bs))"
proof -
  let ?bs = "ab gs [] bs (snd data)"
  from assms(2) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ap_specD1[OF ap, of gs "[]" "[]" bs]
  have *: "set (ap gs [] [] bs (snd data)) \<subseteq> set ?bs \<times> (set gs \<union> set ?bs)"
    by (simp add: ab_specD1[OF ab])
  from assms
  have "dgrad_p_set_le d
         (fst ` set (gb_schema_aux sel ap ab compl data gs ?bs (ap gs [] [] bs (snd data))))
         (args_to_set (gs, ?bs, (ap gs [] [] bs (snd data))))"
    by (rule gb_schema_aux_dgrad_p_set_le)
  also have "... = fst ` (set gs \<union> set bs)"
    by (simp add: args_to_set_subset_Times[OF *] image_Un ab_specD1[OF ab])
  finally show ?thesis .
qed

corollary gb_schema_aux_dgrad_p_set_init:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
    and "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_aux sel ap ab compl (rc, data) gs (ab gs [] bs data) (ap gs [] [] bs data)) \<subseteq> dgrad_p_set d m"
proof (rule dgrad_p_set_le_dgrad_p_set)
  let ?data = "(rc, data)"
  from assms(1, 2)
  have "dgrad_p_set_le d
          (fst ` set (gb_schema_aux sel ap ab compl ?data gs (ab gs [] bs (snd ?data)) (ap gs [] [] bs (snd ?data))))
          (fst ` (set gs \<union> set bs))"
    by (rule gb_schema_aux_dgrad_p_set_le_init)
  thus "dgrad_p_set_le d
          (fst ` set (gb_schema_aux sel ap ab compl ?data gs (ab gs [] bs data) (ap gs [] [] bs data)))
          (fst ` (set gs \<union> set bs))"
    by (simp only: snd_conv)
qed fact

lemma gb_schema_aux_components_init:
  fixes ap ab gs bs data
  defines "bs0 \<equiv> ab gs [] bs data"
  defines "ps0 \<equiv> ap gs [] [] bs data"
  assumes "struct_spec sel ap ab compl"
  shows "component_of_term ` Keys (fst ` set (gb_schema_aux sel ap ab compl (rc, data) gs bs0 ps0)) =
          component_of_term ` Keys (fst ` set (gs @ bs))" (is "?l = ?r")
proof -
  from assms(3) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ap_specD1[OF ap, of gs "[]" "[]" bs]
  have *: "set ps0 \<subseteq> set bs0 \<times> (set gs \<union> set bs0)" by (simp add: ps0_def bs0_def ab_specD1[OF ab])
  with assms(3) have "?l = component_of_term ` Keys (args_to_set (gs, bs0, ps0))"
    by (rule gb_schema_aux_components)
  also have "... = ?r"
    by (simp only: args_to_set_subset_Times[OF *], simp add: ab_specD1[OF ab] bs0_def image_Un)
  finally show ?thesis .
qed

lemma gb_schema_aux_pmdl_init:
  fixes ap ab gs bs data
  defines "bs0 \<equiv> ab gs [] bs data"
  defines "ps0 \<equiv> ap gs [] [] bs data"
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ bs0) data" and "rem_comps_spec (gs @ bs0) (rc, data)"
  shows "pmdl (fst ` set (gb_schema_aux sel ap ab compl (rc, data) gs bs0 ps0)) =
          pmdl (fst ` (set (gs @ bs)))" (is "?l = ?r")
proof -
  from assms(3) have ab: "ab_spec ab" by (rule struct_specD3)
  let ?data = "(rc, data)"
  from assms(6) have "unique_idx (gs @ bs0) (snd ?data)" by (simp only: snd_conv)
  from assms(3, 4, 5) _ this assms(7) have "?l = pmdl (fst ` (set (gs @ bs0)))"
  proof (rule gb_schema_aux_pmdl)
    from assms(3) have "ap_spec ap" by (rule struct_specD2)
    from ap_specD1[OF this, of gs "[]" "[]" bs]
    show "set ps0 \<subseteq> set bs0 \<times> (set gs \<union> set bs0)" by (simp add: ps0_def bs0_def ab_specD1[OF ab])
  qed
  also have "... = ?r" by (simp add: bs0_def ab_specD1[OF ab])
  finally show ?thesis .
qed

lemma gb_schema_aux_isGB_init:
  fixes ap ab gs bs data
  defines "bs0 \<equiv> ab gs [] bs data"
  defines "ps0 \<equiv> ap gs [] [] bs data"
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ bs0) data" and "rem_comps_spec (gs @ bs0) (rc, data)"
  shows "is_Groebner_basis (fst ` set (gb_schema_aux sel ap ab compl (rc, data) gs bs0 ps0))"
proof -
  let ?data = "(rc, data)"
  let ?res = "gb_schema_aux sel ap ab compl ?data gs bs0 ps0"
  from assms(3) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD2, rule struct_specD3)
  have set_bs0: "set bs0 = set bs" by (simp add: bs0_def ab_specD1[OF ab])
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  have "finite (fst ` (set gs \<union> set bs))" by (rule, rule finite_UnI, fact finite_set, fact finite_set)
  then obtain m where "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  with dg assms(3) have "fst ` set ?res \<subseteq> dgrad_p_set d m" unfolding bs0_def ps0_def
    by (rule gb_schema_aux_dgrad_p_set_init)
  with dg show ?thesis
  proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
    fix p0 q0
    assume p0_in: "p0 \<in> fst ` set ?res" and q0_in: "q0 \<in> fst ` set ?res"
    assume "p0 \<noteq> 0" and "q0 \<noteq> 0"
    from \<open>fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m\<close>
    have "fst ` set gs \<subseteq> dgrad_p_set d m" and "fst ` set bs \<subseteq> dgrad_p_set d m"
      by (simp_all add: image_Un)
    from p0_in obtain p where p_in: "p \<in> set ?res" and p0: "p0 = fst p" ..
    from q0_in obtain q where q_in: "q \<in> set ?res" and q0: "q0 = fst q" ..
    from assms(6) have "unique_idx (gs @ bs0) (snd ?data)" by (simp only: snd_conv)
    from assms(3, 4) dg \<open>fst ` set gs \<subseteq> dgrad_p_set d m\<close> assms(5) _ _ this _ p_in q_in \<open>p0 \<noteq> 0\<close> \<open>q0 \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` set ?res) p0 q0" unfolding p0 q0
    proof (rule gb_schema_aux_connectible)
      from \<open>fst ` set bs \<subseteq> dgrad_p_set d m\<close> show "fst ` set bs0 \<subseteq> dgrad_p_set d m"
        by (simp only: set_bs0)
    next
      from ap_specD1[OF ap, of gs "[]" "[]" bs]
      show "set ps0 \<subseteq> set bs0 \<times> (set gs \<union> set bs0)" by (simp add: ps0_def set_bs0)
    next
      fix p' q'
      assume "processed (p', q') (gs @ bs0) ps0"
      hence proc: "processed (p', q') (gs @ bs) ps0"
        by (simp add: set_bs0 processed_alt)
      hence "p' \<in> set gs \<union> set bs" and "q' \<in> set gs \<union> set bs" by (auto dest: processedD1 processedD2)
      assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
      proof (cases "p' = q'")
        case True
        from dg show ?thesis unfolding True
        proof (rule crit_pair_cbelow_same)
          from \<open>q' \<in> set gs \<union> set bs\<close> have "fst q' \<in> fst ` (set gs \<union> set bs)" by simp
          from this \<open>fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m\<close> show "fst q' \<in> dgrad_p_set d m" ..
        qed
      next
        case False
        show ?thesis
        proof (cases "component_of_term (lt (fst p')) = component_of_term (lt (fst q'))")
          case True
          from \<open>p' \<in> set gs \<union> set bs\<close> show ?thesis
          proof
            assume "p' \<in> set gs"
            from \<open>q' \<in> set gs \<union> set bs\<close> show ?thesis
            proof
              assume "q' \<in> set gs"
              note dg \<open>fst ` set gs \<subseteq> dgrad_p_set d m\<close> assms(5)
              moreover from \<open>p' \<in> set gs\<close> have "fst p' \<in> fst ` set gs" by simp
              moreover from \<open>q' \<in> set gs\<close> have "fst q' \<in> fst ` set gs" by simp
              ultimately have "crit_pair_cbelow_on d m (fst ` set gs) (fst p') (fst q')"
                using \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
              moreover have "fst ` set gs \<subseteq> fst ` (set gs \<union> set bs)" by blast
              ultimately show ?thesis by (rule crit_pair_cbelow_mono)
            next
              assume "q' \<in> set bs"
              from \<open>p' \<in> set gs\<close> have "p' \<in> set gs \<union> set []" by simp
              from ap \<open>q' \<in> set bs\<close> this True[symmetric] have "(q', p') \<in> set ps0"
                unfolding ps0_def by (rule ap_specD3)
              hence "\<not> processed (p', q') (gs @ bs) ps0"
                by (simp add: processed_alt)
              from this proc show ?thesis ..
            qed
          next
            assume "p' \<in> set bs"
            from \<open>q' \<in> set gs \<union> set bs\<close> show ?thesis
            proof
              assume "q' \<in> set gs"
              hence "q' \<in> set gs \<union> set []" by simp
              from ap \<open>p' \<in> set bs\<close> this True have "(p', q') \<in> set ps0"
                unfolding ps0_def by (rule ap_specD3)
              hence "\<not> processed (p', q') (gs @ bs) ps0"
                by (simp add: processed_alt)
              from this proc show ?thesis ..
            next
              assume "q' \<in> set bs"
              from ap \<open>p' \<in> set bs\<close> this \<open>p' \<noteq> q'\<close>
              have "\<not> processed (p', q') (gs @ bs) ps0"
              proof (rule ap_specE)
                assume "(p', q') \<in> set (ap gs [] [] bs data)"
                thus ?thesis by (simp add: ps0_def processed_alt)
              next
                assume "(q', p') \<in> set (ap gs [] [] bs data)"
                thus ?thesis by (simp add: ps0_def processed_alt)
              qed fact
              from this proc show ?thesis ..
            qed
          qed
        next
          case False
          thus ?thesis by (rule crit_pair_cbelow_distinct_component)
        qed
      qed
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs0)) (fst p') (fst q')"
        by (simp only: set_bs0)
    qed
  qed
qed

subsubsection \<open>Functions \<open>gb_schema_direct\<close> and \<open>term gb_schema_incr\<close>\<close>

definition gb_schema_direct :: "('t, 'b, 'c, 'd) selT \<Rightarrow> ('t, 'b, 'c, 'd) apT \<Rightarrow> ('t, 'b, 'c, 'd) abT \<Rightarrow>
                                ('t, 'b, 'c, 'd) complT \<Rightarrow> ('t, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow>
                                ('t, 'b::field, 'c::default) pdata' list"
  where "gb_schema_direct sel ap ab compl bs0 data0 =
            (let data = (length bs0, data0); bs1 = fst (add_indices (bs0, data0) (0, data0));
                 bs = ab [] [] bs1 data in
              map (\<lambda>(f, _, d). (f, d))
                    (gb_schema_aux sel ap ab compl (count_rem_components bs, data) [] bs (ap [] [] [] bs1 data))
            )"

primrec gb_schema_incr :: "('t, 'b, 'c, 'd) selT \<Rightarrow> ('t, 'b, 'c, 'd) apT \<Rightarrow> ('t, 'b, 'c, 'd) abT \<Rightarrow>
                                ('t, 'b, 'c, 'd) complT \<Rightarrow>
                                (('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
                                ('t, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('t, 'b::field, 'c::default) pdata' list"
  where
    "gb_schema_incr _ _ _ _ _ [] _ = []"|
    "gb_schema_incr sel ap ab compl upd (b0 # bs) data =
      (let (gs, n, data') = add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data);
           b = (fst b0, n, snd b0); data'' = upd gs b data' in
        map (\<lambda>(f, _, d). (f, d))
          (gb_schema_aux sel ap ab compl (count_rem_components (b # gs), Suc n, data'') gs
                        (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))
      )"

lemma (in -) fst_set_drop_indices:
  "fst ` (\<lambda>(f, _, d). (f, d)) ` A = fst ` A" for A::"('x \<times> 'y \<times> 'z) set"
  by (simp add: image_image, rule image_cong, fact refl, simp add: prod.case_eq_if)

lemma fst_gb_schema_direct:
  "fst ` set (gb_schema_direct sel ap ab compl bs0 data0) =
      (let data = (length bs0, data0); bs1 = fst (add_indices (bs0, data0) (0, data0)); bs = ab [] [] bs1 data in
        fst ` set (gb_schema_aux sel ap ab compl (count_rem_components bs, data) []
                                bs (ap [] [] [] bs1 data))
      )"
  by (simp add: gb_schema_direct_def Let_def fst_set_drop_indices)

lemma gb_schema_direct_dgrad_p_set:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl" and "fst ` set bs \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_direct sel ap ab compl bs data) \<subseteq> dgrad_p_set d m"
  unfolding fst_gb_schema_direct Let_def using assms(1, 2)
proof (rule gb_schema_aux_dgrad_p_set_init)
  show "fst ` (set [] \<union> set (fst (add_indices (bs, data) (0, data)))) \<subseteq> dgrad_p_set d m"
    using assms(3) by (simp add: image_Un fst_set_add_indices)
qed

theorem gb_schema_direct_isGB:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl"
  shows "is_Groebner_basis (fst ` set (gb_schema_direct sel ap ab compl bs data))"
  unfolding fst_gb_schema_direct Let_def using assms
proof (rule gb_schema_aux_isGB_init)
  from is_Groebner_basis_empty show "is_Groebner_basis (fst ` set [])" by simp
next
  let ?data = "(length bs, data)"
  from assms(1) have "ab_spec ab" by (rule struct_specD)
  moreover have "unique_idx ([] @ []) (0, data)" by (simp add: unique_idx_Nil)
  ultimately show "unique_idx ([] @ ab [] [] (fst (add_indices (bs, data) (0, data))) ?data) ?data"
  proof (rule unique_idx_ab)
    show "(fst (add_indices (bs, data) (0, data)), length bs, data) = add_indices (bs, data) (0, data)"
      by (simp add: add_indices_def)
  qed
qed (simp add: rem_comps_spec_count_rem_components)

theorem gb_schema_direct_pmdl:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl"
  shows "pmdl (fst ` set (gb_schema_direct sel ap ab compl bs data)) = pmdl (fst ` set bs)"
proof -
  have "pmdl (fst ` set (gb_schema_direct sel ap ab compl bs data)) =
          pmdl (fst ` set ([] @ (fst (add_indices (bs, data) (0, data)))))"
    unfolding fst_gb_schema_direct Let_def using assms
  proof (rule gb_schema_aux_pmdl_init)
    from is_Groebner_basis_empty show "is_Groebner_basis (fst ` set [])" by simp
  next
    let ?data = "(length bs, data)"
    from assms(1) have "ab_spec ab" by (rule struct_specD)
    moreover have "unique_idx ([] @ []) (0, data)" by (simp add: unique_idx_Nil)
    ultimately show "unique_idx ([] @ ab [] [] (fst (add_indices (bs, data) (0, data))) ?data) ?data"
    proof (rule unique_idx_ab)
      show "(fst (add_indices (bs, data) (0, data)), length bs, data) = add_indices (bs, data) (0, data)"
        by (simp add: add_indices_def)
    qed
  qed (simp add: rem_comps_spec_count_rem_components)
  thus ?thesis by (simp add: fst_set_add_indices)
qed

lemma fst_gb_schema_incr:
  "fst ` set (gb_schema_incr sel ap ab compl upd (b0 # bs) data) =
      (let (gs, n, data') = add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data);
            b = (fst b0, n, snd b0); data'' = upd gs b data' in
        fst ` set (gb_schema_aux sel ap ab compl (count_rem_components (b # gs), Suc n, data'') gs
                                (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))
      )"
  by (simp only: gb_schema_incr.simps Let_def prod.case_distrib[of set]
        prod.case_distrib[of "image fst"] set_map fst_set_drop_indices)

lemma gb_schema_incr_dgrad_p_set:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_incr sel ap ab compl upd bs data) \<subseteq> dgrad_p_set d m"
  using assms(3)
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons b0 bs)
  from Cons(2) have 1: "fst b0 \<in> dgrad_p_set d m" and 2: "fst ` set bs \<subseteq> dgrad_p_set d m" by simp_all
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1, 2)
    show "fst ` set (gb_schema_aux sel ap ab compl (count_rem_components (b # gs), Suc n, data'') gs
                (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data''))) \<subseteq> dgrad_p_set d m"
    proof (rule gb_schema_aux_dgrad_p_set_init)
      from 1 Cons(1)[OF 2] show "fst ` (set gs \<union> set [b]) \<subseteq> dgrad_p_set d m"
        by (simp add: gs fst_set_add_indices b_def)
    qed
  qed
qed

theorem gb_schema_incr_dgrad_p_set_isGB:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl"
  shows "is_Groebner_basis (fst ` set (gb_schema_incr sel ap ab compl upd bs data))"
proof (induct bs)
  case Nil
  from is_Groebner_basis_empty show ?case by simp
next
  case (Cons b0 bs)
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume *: "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1) have ab: "ab_spec ab" by (rule struct_specD3)
    from Cons have "is_Groebner_basis (fst ` set gs)" by (simp add: gs fst_set_add_indices)
    with assms
    show "is_Groebner_basis (fst ` set (gb_schema_aux sel ap ab compl (count_rem_components (b # gs), Suc n, data'') gs
                                (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data''))))"
    proof (rule gb_schema_aux_isGB_init)
      from ab show "unique_idx (gs @ ab gs [] [b] (Suc n, data'')) (Suc n, data'')"
      proof (rule unique_idx_ab)
        from unique_idx_Nil *[symmetric] have "unique_idx ([] @ gs) (n, data')"
          by (rule unique_idx_append)
        thus "unique_idx (gs @ []) (n, data')" by simp
      next
        show "([b], Suc n, data'') = add_indices ([b0], data'') (n, data')"
          by (simp add: add_indices_def b_def)
      qed
    next
      have "rem_comps_spec (b # gs) (count_rem_components (b # gs), Suc n, data'')"
        by (fact rem_comps_spec_count_rem_components)
      moreover have "set (b # gs) = set (gs @ ab gs [] [b] (Suc n, data''))"
        by (simp add: ab_specD1[OF ab])
      ultimately show "rem_comps_spec (gs @ ab gs [] [b] (Suc n, data''))
                                      (count_rem_components (b # gs), Suc n, data'')"
        by (simp only: rem_comps_spec_def)
    qed
  qed
qed

theorem gb_schema_incr_pmdl:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" "compl_pmdl compl"
  shows "pmdl (fst ` set (gb_schema_incr sel ap ab compl upd bs data)) = pmdl (fst ` set bs)"
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons b0 bs)
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume *: "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1) have ab: "ab_spec ab" by (rule struct_specD3)
    from assms(1, 2) have "is_Groebner_basis (fst ` set gs)" unfolding gs fst_conv fst_set_add_indices
      by (rule gb_schema_incr_dgrad_p_set_isGB)
    with assms(1, 3)
    have eq: "pmdl (fst ` set (gb_schema_aux sel ap ab compl (count_rem_components (b # gs), Suc n, data'') gs
                          (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))) =
              pmdl (fst ` set (gs @ [b]))"
    proof (rule gb_schema_aux_pmdl_init)
      from ab show "unique_idx (gs @ ab gs [] [b] (Suc n, data'')) (Suc n, data'')"
      proof (rule unique_idx_ab)
        from unique_idx_Nil *[symmetric] have "unique_idx ([] @ gs) (n, data')"
          by (rule unique_idx_append)
        thus "unique_idx (gs @ []) (n, data')" by simp
      next
        show "([b], Suc n, data'') = add_indices ([b0], data'') (n, data')"
          by (simp add: add_indices_def b_def)
      qed
    next
      have "rem_comps_spec (b # gs) (count_rem_components (b # gs), Suc n, data'')"
        by (fact rem_comps_spec_count_rem_components)
      moreover have "set (b # gs) = set (gs @ ab gs [] [b] (Suc n, data''))"
        by (simp add: ab_specD1[OF ab])
      ultimately show "rem_comps_spec (gs @ ab gs [] [b] (Suc n, data''))
                                      (count_rem_components (b # gs), Suc n, data'')"
        by (simp only: rem_comps_spec_def)
    qed
    also have "... = pmdl (insert (fst b) (fst ` set gs))" by simp
    also from Cons have "... = pmdl (insert (fst b) (fst ` set bs))"
      unfolding gs fst_conv fst_set_add_indices by (rule pmdl.module_insert_cong)
    finally show "pmdl (fst ` set (gb_schema_aux sel ap ab compl (count_rem_components (b # gs), Suc n, data'') gs
                              (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))) =
                  pmdl (insert (fst b0) (fst ` set bs))" by (simp add: b_def)
  qed
qed

subsection \<open>Suitable Instances of the @{emph \<open>completion\<close>} Parameter\<close>

subsubsection \<open>Specification of the @{emph \<open>crit\<close>} parameter\<close>

type_synonym (in -) ('t, 'b, 'c, 'd) critT = "('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                          ('t, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow>
                                          ('t, 'b, 'c) pdata \<Rightarrow> bool"

definition crit_spec :: "('t, 'b::field, 'c, 'd) critT \<Rightarrow> bool"
  where "crit_spec crit \<longleftrightarrow>
            (\<forall>d m gs bs ps F data p q. dickson_grading (+) d \<longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<longrightarrow>
              is_Groebner_basis (fst ` set gs) \<longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
              F \<subseteq> dgrad_p_set d m \<longrightarrow> set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> unique_idx (gs @ bs) data \<longrightarrow>
              (\<forall>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                  crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')) \<longrightarrow>
              p \<in> set bs \<longrightarrow> q \<in> set gs \<union> set bs \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow> crit gs bs ps data p q \<longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q))"

text \<open>Informally, \<open>crit_spec crit\<close> expresses that \<open>crit\<close> is a predicate such that whenever
  \<open>crit gs bs ps p q\<close> holds (for suitable arguments \<open>gs\<close>, \<open>bs\<close>, \<open>ps\<close>, \<open>p\<close> and \<open>q\<close>), then the critical
  pair of polynomials \<open>p\<close> and \<open>q\<close> is connectible modulo any superset \<open>G\<close> of \<open>set gs \<union> set bs\<close>,
  provided that the critical pairs of all polynomials that have been processed already are connectible
  modulo \<open>G\<close>.\<close>

lemma crit_specI:
  assumes "\<And>d m gs bs ps F data p q. dickson_grading (+) d \<Longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<Longrightarrow>
              is_Groebner_basis (fst ` set gs) \<Longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<Longrightarrow>
              F \<subseteq> dgrad_p_set d m \<Longrightarrow> set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow> unique_idx (gs @ bs) data \<Longrightarrow>
              (\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')) \<Longrightarrow>
              p \<in> set bs \<Longrightarrow> q \<in> set gs \<union> set bs \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow> crit gs bs ps data p q \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  shows "crit_spec crit"
  unfolding crit_spec_def using assms by meson

lemma crit_specD:
  assumes "crit_spec crit" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) data"
    and "\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                 crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "p \<in> set bs" and "q \<in> set gs \<union> set bs" and "fst p \<noteq> 0" and "fst q \<noteq> 0" and "crit gs bs ps data p q"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  using assms unfolding crit_spec_def by blast

subsubsection \<open>Suitable Instances of the @{emph \<open>crit\<close>} parameter: chain criterion and product criterion\<close>

text \<open>The product criterion is only applicable to scalar polynomials.\<close>

definition product_crit :: "('a, 'b::zero, 'c, 'd) critT"
  where "product_crit gs bs ps data p q \<longleftrightarrow> (gcs (punit.lt (fst p)) (punit.lt (fst q)) = 0)"

lemma (in gd_term) crit_spec_product_crit: "punit.crit_spec product_crit"
proof (rule punit.crit_specI)
  fix d m gs bs ps and F::"('a \<Rightarrow>\<^sub>0 'b) set" and data::"nat \<times> 'd" and p q::"('a, 'b, 'c) pdata"
  assume "product_crit gs bs ps data p q"
  hence *: "gcs (punit.lt (fst p)) (punit.lt (fst q)) = 0" by (simp only: product_crit_def)
  assume gs: "fst ` set gs \<subseteq> punit.dgrad_p_set d m" and bs: "fst ` set bs \<subseteq> punit.dgrad_p_set d m"
    and F: "F \<subseteq> punit.dgrad_p_set d m" and "p \<in> set bs" and "q \<in> set gs \<union> set bs"
  assume "dickson_grading (+) d"
  moreover from gs bs F have "fst ` (set gs \<union> set bs) \<union> F \<subseteq> punit.dgrad_p_set d m" (is "?F \<subseteq> _")
    by (simp add: image_Un)
  moreover from \<open>p \<in> set bs\<close> have "fst p \<in> ?F" by simp
  moreover from \<open>q \<in> set gs \<union> set bs\<close> have "fst q \<in> ?F" by simp
  moreover assume "fst p \<noteq> 0" and "fst q \<noteq> 0"
  ultimately show "punit.crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
    using * by (rule product_criterion)
qed

fun (in -) pairs_not_in_list :: "('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "pairs_not_in_list [] _ _ _ = True"|
  "pairs_not_in_list (((_, (a, _)), (_, (b, _))) # ps) i j k =
    (if a = k then
      if b = i \<or> b = j then False else pairs_not_in_list ps i j k
    else if b = k then
      if a = i \<or> a = j then False else pairs_not_in_list ps i j k
    else
      pairs_not_in_list ps i j k
    )"

lemma (in -) pairs_not_in_listD:
  assumes "pairs_not_in_list ps i j k" and "(p, q) \<in> set ps"
  shows "(fst (snd p), fst (snd q)) \<noteq> (i, k) \<and> (fst (snd p), fst (snd q)) \<noteq> (k, i) \<and>
         (fst (snd p), fst (snd q)) \<noteq> (j, k) \<and> (fst (snd p), fst (snd q)) \<noteq> (k, j)"
  using assms
proof (induct i j k rule: pairs_not_in_list.induct)
  case (1 uu uv uw)
  from 1(2) show ?case by simp
next
  case (2 ux a uy uz b va ps i j k)
  from 2(4) have a: "a = k \<Longrightarrow> \<not> (b = i \<or> b = j)" and b: "a \<noteq> k \<Longrightarrow> b = k \<Longrightarrow> \<not> (a = i \<or> a = j)"
    and *: "pairs_not_in_list ps i j k" by (simp_all split: if_split_asm)
  from 2(5) have "(p, q) = ((ux, a, uy), (uz, b, va)) \<or> (p, q) \<in> set ps" by simp
  thus ?case
  proof
    assume "(p, q) = ((ux, a, uy), (uz, b, va))"
    hence p: "fst (snd p) = a" and q: "fst (snd q) = b" by auto
    from a b show ?thesis unfolding p q by blast
  next
    assume "(p, q) \<in> set ps"
    show ?thesis
    proof (cases "a = k")
      case True
      moreover from True have "\<not> (b = i \<or> b = j)" by (rule a)
      ultimately show ?thesis using * \<open>(p, q) \<in> set ps\<close> by (rule 2(1))
    next
      case False
      show ?thesis
      proof (cases "b = k")
        note False
        moreover assume "b = k"
        moreover from False this have "\<not> (a = i \<or> a = j)" by (rule b)
        ultimately show ?thesis using * \<open>(p, q) \<in> set ps\<close> by (rule 2(2))
      next
        note False
        moreover assume "b \<noteq> k"
        ultimately show ?thesis using * \<open>(p, q) \<in> set ps\<close> by (rule 2(3))
      qed
    qed
  qed
qed

definition chain_crit :: "('t, 'b::zero, 'c, 'd) critT"
  where "chain_crit gs bs ps data p q \<longleftrightarrow>
          (let v = lt (fst p); l = term_of_pair (lcs (pp_of_term v) (lp (fst q)), component_of_term v);
               i = fst (snd p); j = fst (snd q) in
            (\<exists>r\<in>set (gs @ bs). let k = fst (snd r) in
                  k \<noteq> i \<and> k \<noteq> j \<and> lt (fst r) adds\<^sub>t l \<and> pairs_not_in_list ps i j k \<and> fst r \<noteq> 0)
          )"

text \<open>@{const product_crit} and @{const chain_crit} ignore the \<open>data\<close> parameter.\<close>

lemma chain_critE:
  assumes "chain_crit gs bs ps data p q" and "p \<in> set bs" and "q \<in> set gs \<union> set bs"
  obtains r where "r \<in> set (gs @ bs)" and "fst r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and "lt (fst r) adds\<^sub>t term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
    and "processed (p, r) (gs @ bs) ps" and "processed (r, q) (gs @ bs) ps"
proof -
  let ?l = "term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
  from assms(1) obtain r where "r \<in> set (gs @ bs)" and "fst r \<noteq> 0" and rp: "fst (snd r) \<noteq> fst (snd p)"
    and rq: "fst (snd r) \<noteq> fst (snd q)" and "lt (fst r) adds\<^sub>t ?l"
    and *: "pairs_not_in_list ps (fst (snd p)) (fst (snd q)) (fst (snd r))"
    unfolding chain_crit_def Let_def by blast
  from rp have "r \<noteq> p" by auto
  from rq have "r \<noteq> q" by auto
  from \<open>r \<in> set (gs @ bs)\<close> \<open>fst r \<noteq> 0\<close> \<open>r \<noteq> p\<close> \<open>r \<noteq> q\<close> \<open>lt (fst r) adds\<^sub>t ?l\<close> show ?thesis
  proof
    from assms(2) have "p \<in> set (gs @ bs)" by simp
    moreover note \<open>r \<in> set (gs @ bs)\<close>
    moreover have "(p, r) \<notin> set ps"
    proof
      assume "(p, r) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    moreover have "(r, p) \<notin> set ps"
    proof
      assume "(r, p) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    ultimately show "processed (p, r) (gs @ bs) ps" by (rule processedI)
  next
    note \<open>r \<in> set (gs @ bs)\<close>
    moreover from assms(3) have "q \<in> set (gs @ bs)" by simp
    moreover have "(r, q) \<notin> set ps"
    proof
      assume "(r, q) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    moreover have "(q, r) \<notin> set ps"
    proof
      assume "(q, r) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    ultimately show "processed (r, q) (gs @ bs) ps" by (rule processedI)
  qed
qed

text \<open>For proving the following lemma, @{const unique_idx} is not needed at all.\<close>

lemma crit_spec_chain_crit: "crit_spec chain_crit"
proof (rule crit_specI)
  fix d m gs bs ps F and data::"nat \<times> 'd" and p q::"('t, 'b, 'c) pdata"
  assume dg: "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "fst ` set bs \<subseteq> dgrad_p_set d m" and "F \<subseteq> dgrad_p_set d m"
    and *: "\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
           crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  let ?l = "term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
  assume "chain_crit gs bs ps data p q" and "p \<in> set bs" and "q \<in> set gs \<union> set bs"
  then obtain r where "fst r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and adds: "lt (fst r) adds\<^sub>t ?l"
    and "processed (p, r) (gs @ bs) ps" and "processed (r, q) (gs @ bs) ps" by (rule chain_critE)
  define G where "G = fst ` (set gs \<union> set bs) \<union> F"
  note dg
  moreover have "G \<subseteq> dgrad_p_set d m" unfolding G_def image_Un by (intro Un_least, fact+)
  moreover from \<open>p \<in> set bs\<close> \<open>q \<in> set gs \<union> set bs\<close> have "fst p \<in> G" and "fst q \<in> G"
    by (simp_all add: G_def)
  moreover note \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
  moreover from adds have "lp (fst r) adds lcs (lp (fst p)) (lp (fst q))"
    by (simp add: adds_term_def term_simps)
  moreover from adds have "component_of_term (lt (fst r)) = component_of_term (lt (fst p))"
    by (simp add: adds_term_def term_simps)
  ultimately show "crit_pair_cbelow_on d m G (fst p) (fst q)"
  proof (rule chain_criterion)
    from \<open>processed (p, r) (gs @ bs) ps\<close> have "processed (p, r) (gs @ bs) ((p, q) # ps)"
    proof (rule processed_Cons)
      assume "r = q"
      with \<open>r \<noteq> q\<close> show ?thesis ..
    next
      assume "r = p"
      with \<open>r \<noteq> p\<close> show ?thesis ..
    qed
    from this \<open>fst p \<noteq> 0\<close> \<open>fst r \<noteq> 0\<close> show "crit_pair_cbelow_on d m G (fst p) (fst r)"
      unfolding G_def by (rule *)
  next
    from \<open>processed (r, q) (gs @ bs) ps\<close> have "processed (r, q) (gs @ bs) ((p, q) # ps)"
    proof (rule processed_Cons)
      assume "r = p"
      with \<open>r \<noteq> p\<close> show ?thesis ..
    next
      assume "r = q"
      with \<open>r \<noteq> q\<close> show ?thesis ..
    qed
    from this \<open>fst r \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> show "crit_pair_cbelow_on d m G (fst r) (fst q)"
      unfolding G_def by (rule *)
  qed
qed

definition comb_crit :: "('t, 'b::zero, 'c, 'd) critT \<Rightarrow> ('t, 'b, 'c, 'd) critT \<Rightarrow> ('t, 'b, 'c, 'd) critT"
  where "comb_crit c1 c2 gs bs ps data p q \<longleftrightarrow> (c1 gs bs ps data p q \<or> c2 gs bs ps data p q)"

lemma crit_spec_comb_crit:
  assumes "crit_spec c1" and "crit_spec c2"
  shows "crit_spec (comb_crit c1 c2)"
proof (rule crit_specI)
  fix d m gs bs ps and F::"('t \<Rightarrow>\<^sub>0 'b) set" and data::"nat \<times> 'd" and p q::"('t, 'b, 'c) pdata"
  assume 1: "dickson_grading (+) d" and 2: "fst ` set gs \<subseteq> dgrad_p_set d m"
    and 3: "is_Groebner_basis (fst ` set gs)" and 4: "fst ` set bs \<subseteq> dgrad_p_set d m"
    and 5: "F \<subseteq> dgrad_p_set d m" and 6: "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and 7: "unique_idx (gs @ bs) data"
    and 8: "\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and 9: "p \<in> set bs" and 10: "q \<in> set gs \<union> set bs" and 11: "fst p \<noteq> 0" and 12: "fst q \<noteq> 0"
  assume "comb_crit c1 c2 gs bs ps data p q"
  hence "c1 gs bs ps data p q \<or> c2 gs bs ps data p q" by (simp only: comb_crit_def)
  thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  proof
    assume "c1 gs bs ps data p q"
    with assms(1) 1 2 3 4 5 6 7 8 9 10 11 12 show ?thesis by (rule crit_specD)
  next
    assume "c2 gs bs ps data p q"
    with assms(2) 1 2 3 4 5 6 7 8 9 10 11 12 show ?thesis by (rule crit_specD)
  qed
qed

definition (in gd_term) pc_crit :: "('a, 'b::zero, 'c, 'd) critT"
  where "pc_crit = punit.comb_crit product_crit punit.chain_crit"

corollary crit_spec_pc_crit: "punit.crit_spec pc_crit"
  by (simp only: pc_crit_def, rule punit.crit_spec_comb_crit, fact crit_spec_product_crit, fact punit.crit_spec_chain_crit)

subsubsection \<open>Function @{term discard_crit_pairs}\<close>

primrec discard_crit_pairs_dummy :: "('t, 'b, 'c, 'd) critT \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                      ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                      ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow>
                                      ((('t, 'b, 'c) pdata_pair list) \<times> (('t, 'b, 'c) pdata_pair list))"
  where
    "discard_crit_pairs_dummy _ _ _ _ [] _ ks ds = (ks, ds)"|
    "discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds =
      (if crit gs bs (sps @ ps) data (fst p) (snd p) then
        discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds)
      else
        discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds
      )"

text \<open>The last argument of @{const discard_crit_pairs_dummy} is a ``dummy'' argument that is only
  needed for proving properties of the function, but that does not contribute to the final result
  we are interested in.\<close>

lemma set_discard_crit_pairs_dummy_partition:
  "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) \<union>
    set (snd (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) =
  set sps \<union> set ks \<union> set ds"
  by (induct sps arbitrary: ks ds, simp_all)

lemma fst_discard_crit_pairs_dummy_subset:
  "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) \<subseteq> set sps \<union> set ks"
proof (induct sps arbitrary: ks ds)
  case Nil
  show ?case by simp
next
  case (Cons p sps)
  show ?case
  proof (simp, intro conjI impI)
    have "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds))) \<subseteq> set sps \<union> set ks"
      by (rule Cons)
    also have "... \<subseteq> insert p (set sps \<union> set ks)" by blast
    finally show "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds))) \<subseteq>
                    insert p (set sps \<union> set ks)" .
  next
    have "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds)) \<subseteq> set sps \<union> set (p # ks)"
      by (rule Cons)
    thus "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds)) \<subseteq>
            insert p (set sps \<union> set ks)" by simp
  qed
qed

lemma fst_discard_crit_pairs_dummy_sublist:
  obtains ks' where "fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds) = ks' @ ks"
proof (induct sps arbitrary: thesis ks ds)
  case Nil
  show ?case
  proof (rule Nil)
    show "fst (discard_crit_pairs_dummy crit gs bs ps [] data ks ds) = [] @ ks" by simp
  qed
next
  case (Cons p sps)
  show ?case
  proof (cases "crit gs bs (sps @ ps) data (fst p) (snd p)")
    case True
    obtain ks' where *: "fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds)) = ks' @ ks"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from True * show "fst (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = ks' @ ks"
        by simp
    qed
  next
    case False
    obtain ks' where *: "fst (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds) = ks' @ (p # ks)"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from False * show "fst (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = (ks' @ [p]) @ ks"
        by simp
    qed
  qed
qed

lemma snd_discard_crit_pairs_dummy_sublist:
  obtains ds' where "snd (discard_crit_pairs_dummy crit gs bs ps sps data ks ds) = ds' @ ds"
proof (induct sps arbitrary: thesis ks ds)
  case Nil
  show ?case
  proof (rule Nil)
    show "snd (discard_crit_pairs_dummy crit gs bs ps [] data ks ds) = [] @ ds" by simp
  qed
next
  case (Cons p sps)
  show ?case
  proof (cases "crit gs bs (sps @ ps) data (fst p) (snd p)")
    case True
    obtain ds' where *: "snd (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds)) = ds' @ (p # ds)"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from True * show "snd (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = (ds' @ [p]) @ ds"
        by simp
    qed
  next
    case False
    obtain ds' where *: "snd (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds) = ds' @ ds"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from False * show "snd (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = ds' @ ds"
        by simp
    qed
  qed
qed

lemma discard_crit_pairs_dummy_connectible:
  assumes "crit_spec crit" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) data"
    and "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "\<And>p' q'. processed (p', q') (gs @ bs) (sps @ ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set ds \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) \<Longrightarrow>
            fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
  assumes "(p, q) \<in> set (snd (discard_crit_pairs_dummy crit gs bs ps sps data ks ds))"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  using assms(9, 10, 11, 12, 13)
proof (induct sps arbitrary: ks ds)
  case Nil
  from Nil(5) have "(p, q) \<in> set ds" by simp
  from this assms(14, 15) show ?case by (rule Nil(3))
next
  case (Cons s sps)
  from Cons(2) have "s \<in> set bs \<times> (set gs \<union> set bs)" and sps_sub: "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    by simp_all
  from this(1) have "fst s \<in> set bs" and "snd s \<in> set gs \<union> set bs" by auto
  let ?res = "discard_crit_pairs_dummy crit gs bs ps (s # sps) data ks ds"

  have *: "fst (fst s) \<noteq> 0 \<Longrightarrow> fst (snd s) \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
  proof -
    assume "fst (fst s) \<noteq> 0" and "fst (snd s) \<noteq> 0"
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
    proof (cases "crit gs bs (sps @ ps) data (fst s) (snd s)")
      case True
      with assms(1, 2, 3, 4, 5, 6) _ assms(8) _ \<open>fst s \<in> set bs\<close> \<open>snd s \<in> set gs \<union> set bs\<close>
          \<open>fst (fst s) \<noteq> 0\<close> \<open>fst (snd s) \<noteq> 0\<close>
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
      proof (rule crit_specD)
        from sps_sub assms(7) show "set (sps @ ps) \<subseteq> set bs \<times> (set gs \<union> set bs)" by auto
      next
        fix p' q'
        assume "processed (p', q') (gs @ bs) ((fst s, snd s) # sps @ ps)"
        hence "processed (p', q') (gs @ bs) ((s # sps) @ ps)" by simp
        moreover assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
        ultimately show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
          by (rule Cons(3))
      qed
      thus ?thesis by simp
    next
      case False
      show ?thesis
      proof (rule Cons(5), simp add: False)
        obtain ks' where "fst (discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds) = ks' @ (s # ks)"
          by (rule fst_discard_crit_pairs_dummy_sublist)
        thus "s \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds))" by simp
      qed fact+
    qed
  qed

  have **: "processed (p', q') (gs @ bs) (sps @ ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" for p' q'
  proof -
    assume proc: "processed (p', q') (gs @ bs) (sps @ ps)"
    assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    proof (cases "s = (p', q')")
      case True
      hence p': "p' = fst s" and q': "q' = snd s" by simp_all
      from \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis unfolding p' q' by (rule *)
    next
      case False
      show ?thesis
      proof (cases "s = (q', p')")
        case True
        hence p': "p' = snd s" and q': "q' = fst s" by simp_all
        from \<open>fst q' \<noteq> 0\<close> \<open>fst p' \<noteq> 0\<close>
        have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst q') (fst p')"
          unfolding p' q' by (rule *)
        thus ?thesis by (rule crit_pair_cbelow_sym)
      next
        case False
        from _ \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis
        proof (rule Cons(3))
          from proc have "processed (p', q') (gs @ bs) (s # (sps @ ps))"
          proof (rule processed_Cons)
            assume "p' = fst s" and "q' = snd s"
            hence "s = (p', q')" by simp
            with \<open>s \<noteq> (p', q')\<close> show ?thesis ..
          next
            assume "p' = snd s" and "q' = fst s"
            hence "s = (q', p')" by simp
            with \<open>s \<noteq> (q', p')\<close> show ?thesis ..
          qed simp
          thus "processed (p', q') (gs @ bs) ((s # sps) @ ps)" by simp
        qed
      qed
    qed
  qed

  from Cons(6) show ?case
  proof (simp split: if_splits)
    let ?a = "discard_crit_pairs_dummy crit gs bs ps sps data ks (s # ds)"
    assume crit: "crit gs bs (sps @ ps) data (fst s) (snd s)"
    hence "?res = ?a" by simp
    assume "(p, q) \<in> set (snd ?a)"
    with sps_sub _ _ _ show ?thesis
    proof (rule Cons(1))
      fix p' q'
      assume "processed (p', q') (gs @ bs) (sps @ ps)" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule **)
    next
      fix p' q'
      assume "(p', q') \<in> set (s # ds)"
      hence disj: "s = (p', q') \<or> (p', q') \<in> set ds" by auto
      assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      from disj show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
      proof
        assume "s = (p', q')"
        hence p': "p' = fst s" and q': "q' = snd s" by simp_all
        from \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis unfolding p' q' by (rule *)
      next
        assume "(p', q') \<in> set ds"
        from this \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis by (rule Cons(4))
      qed
    next
      fix p' q'
      assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (s # ds)))"
        and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
        by (rule Cons(5), simp only: \<open>?res = ?a\<close>, fact+)
    qed
  next
    let ?a = "discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds"
    assume "\<not> crit gs bs (sps @ ps) data (fst s) (snd s)"
    hence "?res = ?a" by simp
    assume "(p, q) \<in> set (snd ?a)"
    with sps_sub _ _ _ show ?thesis
    proof (rule Cons(1))
      fix p' q'
      assume "processed (p', q') (gs @ bs) (sps @ ps)" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule **)
    next
      fix p' q'
      assume "(p', q') \<in> set ds" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule Cons(4))
    next
      fix p' q'
      assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds))"
        and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
        by (rule Cons(5), simp only: \<open>?res = ?a\<close>, fact+)
    qed
  qed
qed

primrec discard_crit_pairs_aux :: "('t, 'b, 'c, 'd) critT \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                      ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                      ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list"
  where
    "discard_crit_pairs_aux _ _ _ _ [] _ ks = ks"|
    "discard_crit_pairs_aux crit gs bs ps (p # sps) data ks =
      (if crit gs bs (sps @ ps) data (fst p) (snd p) then
        discard_crit_pairs_aux crit gs bs ps sps data ks
      else
        discard_crit_pairs_aux crit gs bs ps sps data (p # ks)
      )"

text \<open>Function @{const discard_crit_pairs_aux} is like @{const discard_crit_pairs_dummy}, but lacks
  the dummy argument. Therefore, it is the method of choice for doing actual computations.\<close>

lemma discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy':
  "discard_crit_pairs_aux crit gs bs ps sps data ks =
              fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)"
  by (induct sps arbitrary: ks ds, simp_all)

lemmas discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy =
          discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy'[where ds="[]"]

definition discard_crit_pairs :: "('t, 'b, 'c, 'd) critT \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                      ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                      ('t, 'b, 'c) pdata_pair list"
  where "discard_crit_pairs crit gs bs ps sps data = discard_crit_pairs_aux crit gs bs ps sps data []"

lemma discard_crit_pairs_alt:
  "discard_crit_pairs crit gs bs ps sps data = fst (discard_crit_pairs_dummy crit gs bs ps sps data [] [])"
  by (simp only: discard_crit_pairs_def discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy)

lemma set_discard_crit_pairs_partition:
  "set sps = set (discard_crit_pairs crit gs bs ps sps data) \<union>
              set (snd (discard_crit_pairs_dummy crit gs bs ps sps data [] []))"
  by (simp add: discard_crit_pairs_alt set_discard_crit_pairs_dummy_partition)

corollary discard_crit_pairs_subset: "set (discard_crit_pairs crit gs bs ps sps data) \<subseteq> set sps"
  using set_discard_crit_pairs_partition by fastforce

lemma discard_crit_pairs_connectible:
  assumes "crit_spec crit" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "unique_idx (gs @ bs) data" and "set sps \<subseteq> set ps"
    and "\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set (discard_crit_pairs crit gs bs (ps -- sps) sps data) \<Longrightarrow>
            fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
  assumes "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
proof (cases "(p, q) \<in> set (discard_crit_pairs crit gs bs (ps -- sps) sps data)")
  case True
  from this assms(13, 14) show ?thesis by (rule assms(11))
next
  case False
  note assms(1, 2, 3, 4, 5, 6)
  moreover from assms(7) have "set (ps -- sps) \<subseteq> set bs \<times> (set gs \<union> set bs)" by (auto simp add: set_diff_list)
  moreover note assms(8)
  moreover from assms(9, 7) have "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)" by (rule subset_trans)
  moreover note _ _ _
  moreover from False assms(12) have "(p, q) \<in> set (snd (discard_crit_pairs_dummy crit gs bs (ps -- sps) sps data [] []))"
    using set_discard_crit_pairs_partition[of sps crit gs bs "ps -- sps"] by blast
  ultimately show ?thesis using assms(13, 14)
  proof (rule discard_crit_pairs_dummy_connectible)
    fix p' q'
    assume "processed (p', q') (gs @ bs) (sps @ (ps -- sps))"
    hence "processed (p', q') (gs @ bs) ps"
      by (simp only: processed_alt subset_append_diff_cancel[OF assms(9)], simp)
    moreover assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    ultimately show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
      by (rule assms(10))
  next
    fix p' q' :: "('t, 'b, 'c) pdata"
    assume "(p', q') \<in> set []"
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by simp
  next
    fix p' q'
    assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs (ps -- sps) sps data [] []))"
      and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
      unfolding discard_crit_pairs_alt[symmetric] by (rule assms(11))
  qed
qed

subsubsection \<open>Specification of the @{emph \<open>reduce-critical-pairs\<close>} parameter\<close>

type_synonym (in -) ('t, 'b, 'c, 'd) rcpT = "('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                          ('t, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                          (('t, 'b, 'c) pdata' list \<times> 'd)"

definition rcp_spec :: "('t, 'b::field, 'c, 'd) rcpT \<Rightarrow> bool"
  where "rcp_spec rcp \<longleftrightarrow>
            (\<forall>gs bs ps data.
              0 \<notin> fst ` set (fst (rcp gs bs ps data)) \<and>
              (\<forall>h b. h \<in> set (fst (rcp gs bs ps data)) \<longrightarrow> b \<in> set gs \<union> set bs \<longrightarrow> fst b \<noteq> 0 \<longrightarrow>
                     \<not> lt (fst b) adds\<^sub>t lt (fst h)) \<and>
              (\<forall>d. dickson_grading (+) d \<longrightarrow>
                     dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps data))) (args_to_set (gs, bs, ps))) \<and>
              component_of_term ` Keys (fst ` (set (fst (rcp gs bs ps data)))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, ps)) \<and>
              (is_Groebner_basis (fst ` set gs) \<longrightarrow> unique_idx (gs @ bs) data \<longrightarrow>
                (fst ` set (fst (rcp gs bs ps data)) \<subseteq> pmdl (args_to_set (gs, bs, ps)) \<and>
                (\<forall>(p, q)\<in>set ps.  set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
                  (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0))))"

text \<open>Informally, \<open>rcp_spec rcp\<close> expresses that, for suitable \<open>gs\<close>, \<open>bs\<close> and \<open>ps\<close>, the value of
  \<open>rcp gs bs ps\<close>
  \begin{itemize}
    \item is a list consisting exclusively of non-zero polynomials contained in the module generated
      by \<open>set bs \<union> set gs\<close>, whose leading terms are not divisible by the leading
      term of any non-zero @{prop "b \<in> set bs"}, and
    \item contains sufficiently many new polynomials such that all S-polynomials originating from
      \<open>ps\<close> can be reduced to \<open>0\<close> modulo the enlarged list of polynomials.
  \end{itemize}\<close>

lemma rcp_specI:
  assumes "\<And>gs bs ps data. 0 \<notin> fst ` set (fst (rcp gs bs ps data))"
  assumes "\<And>gs bs ps h b data. h \<in> set (fst (rcp gs bs ps data)) \<Longrightarrow> b \<in> set gs \<union> set bs \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
                          \<not> lt (fst b) adds\<^sub>t lt (fst h)"
  assumes "\<And>gs bs ps d data. dickson_grading (+) d \<Longrightarrow>
                         dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps data))) (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps data. component_of_term ` Keys (fst ` (set (fst (rcp gs bs ps data)))) \<subseteq>
                            component_of_term ` Keys (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps data. is_Groebner_basis (fst ` set gs) \<Longrightarrow> unique_idx (gs @ bs) data \<Longrightarrow>
                (fst ` set (fst (rcp gs bs ps data)) \<subseteq> pmdl (args_to_set (gs, bs, ps)) \<and>
                (\<forall>(p, q)\<in>set ps.  set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
                  (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0))"
  shows "rcp_spec rcp"
  unfolding rcp_spec_def using assms by auto

lemma rcp_specD1:
  assumes "rcp_spec rcp"
  shows "0 \<notin> fst ` set (fst (rcp gs bs ps data))"
  using assms unfolding rcp_spec_def by (elim allE conjE)

lemma rcp_specD2:
  assumes "rcp_spec rcp"
    and "h \<in> set (fst (rcp gs bs ps data))" and "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0"
  shows "\<not> lt (fst b) adds\<^sub>t lt (fst h)"
  using assms unfolding rcp_spec_def by (elim allE conjE, blast)

lemma rcp_specD3:
  assumes "rcp_spec rcp" and "dickson_grading (+) d"
  shows "dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps data))) (args_to_set (gs, bs, ps))"
  using assms unfolding rcp_spec_def by (elim allE conjE, blast)

lemma rcp_specD4:
  assumes "rcp_spec rcp"
  shows "component_of_term ` Keys (fst ` (set (fst (rcp gs bs ps data)))) \<subseteq>
          component_of_term ` Keys (args_to_set (gs, bs, ps))"
  using assms unfolding rcp_spec_def by (elim allE conjE)

lemma rcp_specD5:
  assumes "rcp_spec rcp" and "is_Groebner_basis (fst ` set gs)" and "unique_idx (gs @ bs) data"
  shows "fst ` set (fst (rcp gs bs ps data)) \<subseteq> pmdl (args_to_set (gs, bs, ps))"
  using assms unfolding rcp_spec_def by blast

lemma rcp_specD6:
  assumes "rcp_spec rcp" and "is_Groebner_basis (fst ` set gs)" and "unique_idx (gs @ bs) data"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "(p, q) \<in> set ps"
  shows "(red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
  using assms unfolding rcp_spec_def by blast

subsubsection \<open>Function \<open>discard_red_cp\<close>\<close>

definition discard_red_cp :: "('t, 'b, 'c, 'd) critT \<Rightarrow> ('t, 'b, 'c, 'd) rcpT \<Rightarrow> ('t, 'b::field, 'c, 'd) complT"
  where "discard_red_cp crit rcp gs bs ps sps data =
                rcp gs bs (discard_crit_pairs crit gs bs ps sps data) data"

lemma discard_red_cp_dgrad_p_set_le:
  assumes "rcp_spec rcp" and "dickson_grading (+) d" and "set sps \<subseteq> set ps"
  shows "dgrad_p_set_le d (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)))
                          (args_to_set (gs, bs, ps))"
proof -
  from assms(1, 2)
  have "dgrad_p_set_le d (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)))
                          (args_to_set (gs, bs, discard_crit_pairs crit gs bs (ps -- sps) sps data))"
    unfolding discard_red_cp_def by (rule rcp_specD3)
  also have "dgrad_p_set_le d ... (args_to_set (gs, bs, ps))"
  proof (rule dgrad_p_set_le_subset, rule args_to_set_subset3)
    from discard_crit_pairs_subset \<open>set sps \<subseteq> set ps\<close>
    show "set (discard_crit_pairs crit gs bs (ps -- sps) sps data) \<subseteq> set ps" by (rule subset_trans)
  qed
  finally show ?thesis .
qed

lemma compl_struct_discard_red_cp:
  assumes "rcp_spec rcp"
  shows "compl_struct (discard_red_cp crit rcp)"
proof (rule compl_structI)
  fix d::"'a \<Rightarrow> nat" and gs bs ps and sps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "dickson_grading (+) d" and "set sps \<subseteq> set ps"
  with assms show "dgrad_p_set_le d (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)))
                                    (args_to_set (gs, bs, ps))"
    by (rule discard_red_cp_dgrad_p_set_le)
next
  fix gs bs ps and sps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  from assms show "0 \<notin> fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data))"
    unfolding discard_red_cp_def by (rule rcp_specD1)
next
  fix gs bs ps sps h b data
  assume "h \<in> set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data))"
    and "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0"
  with assms show "\<not> lt (fst b) adds\<^sub>t lt (fst h)" unfolding discard_red_cp_def by (rule rcp_specD2)
next
  fix gs bs ps and sps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "set sps \<subseteq> set ps"
  from assms
  have "component_of_term ` Keys (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data))) \<subseteq>
        component_of_term ` Keys (args_to_set (gs, bs, discard_crit_pairs crit gs bs (ps -- sps) sps data))"
    unfolding discard_red_cp_def by (rule rcp_specD4)
  also have "... \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (rule image_mono, rule Keys_mono, rule args_to_set_subset3, rule subset_trans,
        fact discard_crit_pairs_subset, fact)
  finally show "component_of_term ` Keys (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, ps))" .
qed

lemma compl_pmdl_discard_red_cp:
  assumes "rcp_spec rcp"
  shows "compl_pmdl (discard_red_cp crit rcp)"
proof (rule compl_pmdlI)
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps sps :: "('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume gb: "is_Groebner_basis (fst ` set gs)" and "set sps \<subseteq> set ps"
    and un: "unique_idx (gs @ bs) data"
  let ?res = "fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)"
  let ?ks = "discard_crit_pairs crit gs bs (ps -- sps) sps data"
  from assms gb un have "fst ` set ?res \<subseteq> pmdl (args_to_set (gs, bs, ?ks))"
    unfolding discard_red_cp_def by (rule rcp_specD5)
  also have "... \<subseteq> pmdl (args_to_set (gs, bs, ps))"
  proof (rule pmdl.module_mono)
    from discard_crit_pairs_subset \<open>set sps \<subseteq> set ps\<close> have "set ?ks \<subseteq> set ps"
      by (rule subset_trans)
    thus "args_to_set (gs, bs, ?ks) \<subseteq> args_to_set (gs, bs, ps)" by (rule args_to_set_subset3)
  qed
  finally show "fst ` set ?res \<subseteq> pmdl (args_to_set (gs, bs, ps))" .
qed

lemma compl_conn_discard_red_cp:
  assumes "crit_spec crit" and "rcp_spec rcp"
  shows "compl_conn (discard_red_cp crit rcp)"
proof (rule compl_connI)
  fix d::"'a \<Rightarrow> nat" and m gs bs ps sps p and q::"('t, 'b, 'c) pdata" and data::"nat \<times> 'd"
  assume dg: "dickson_grading (+) d" and gs_sub: "fst ` set gs \<subseteq> dgrad_p_set d m"
    and gb: "is_Groebner_basis (fst ` set gs)" and bs_sub: "fst ` set bs \<subseteq> dgrad_p_set d m"
    and ps_sub: "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "set sps \<subseteq> set ps"
    and un: "unique_idx (gs @ bs) data"
    and *: "\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
    and "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"

  let ?res = "fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)"
  have res_sub: "fst ` set ?res \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set, rule discard_red_cp_dgrad_p_set_le, fact+)
    show "args_to_set (gs, bs, ps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF ps_sub], rule, fact+)
  qed

  have gs_bs_sub: "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m" by (simp add: image_Un, rule, fact+)

  from assms(1) dg gs_sub gb bs_sub res_sub ps_sub un \<open>set sps \<subseteq> set ps\<close> _ _ \<open>(p, q) \<in> set sps\<close>
      \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
  show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set ?res) (fst p) (fst q)"
  proof (rule discard_crit_pairs_connectible)
    fix p' q'
    assume "processed (p', q') (gs @ bs) ps" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    hence "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')" by (rule *)
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set ?res) (fst p') (fst q')"
      by (rule crit_pair_cbelow_mono, simp)
  next
    fix p' q'
    assume p'q'_in: "(p', q') \<in> set (discard_crit_pairs crit gs bs (ps -- sps) sps data)" (is "_ \<in> set ?ks")
      and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    
    have "set ?ks \<subseteq> set sps" by (fact discard_crit_pairs_subset)
    also have "... \<subseteq> set ps" by fact
    also have "... \<subseteq> set bs \<times> (set gs \<union> set bs)" by fact
    finally have ks_sub: "set ?ks \<subseteq> set bs \<times> (set gs \<union> set bs)" .
    hence "fst ` set ?ks \<subseteq> set bs" by fastforce
    from this bs_sub have "fst ` fst ` set ?ks \<subseteq> dgrad_p_set d m" by blast
    with p'q'_in have "fst p' \<in> dgrad_p_set d m"
      by (meson bs_sub contra_subsetD imageI ks_sub mem_Sigma_iff)
    from ks_sub have "snd ` set ?ks \<subseteq> set gs \<union> set bs" by fastforce
    from this gs_bs_sub have "fst ` snd ` set ?ks \<subseteq> dgrad_p_set d m" by blast
    with p'q'_in have "fst q' \<in> dgrad_p_set d m"
      by (metis (no_types, lifting) contra_subsetD imageI snd_conv)

    from assms(2) gb un ks_sub p'q'_in have "(red (fst ` (set gs \<union> set bs) \<union> fst ` set ?res))\<^sup>*\<^sup>*
                                            (spoly (fst p') (fst q')) 0"
      unfolding discard_red_cp_def by (rule rcp_specD6)
    hence "(red (fst ` (set gs \<union> set bs) \<union> fst ` set ?res))\<^sup>*\<^sup>* (spoly (fst p') (fst q')) 0"
      by (simp only: image_Un)
    with dg _ \<open>fst p' \<in> dgrad_p_set d m\<close> \<open>fst q' \<in> dgrad_p_set d m\<close> \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set ?res) (fst p') (fst q')"
    proof (rule spoly_red_zero_imp_crit_pair_cbelow_on)
      from gs_bs_sub res_sub show "fst ` (set gs \<union> set bs) \<union> fst ` set ?res \<subseteq> dgrad_p_set d m"
        by simp
    qed
  qed
qed

end (* gd_term *)

subsection \<open>Suitable Instances of the @{emph \<open>add-pairs\<close>} Parameter\<close>

type_synonym ('t, 'b, 'c, 'd) apsT = "('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                    ('t, 'b, 'c) pdata \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow>
                                    ('t, 'b, 'c) pdata_pair list"

context ordered_term
begin

definition add_pairs_single_naive :: "'d \<Rightarrow> ('t, 'b::zero, 'c, 'd) apsT"
  where "add_pairs_single_naive data gs bs h ps =
            (let k = component_of_term (lt (fst h)) in
              ps @ (map (Pair h) (filter (\<lambda>g. component_of_term (lt (fst g)) = k) gs)) @
                   (map (Pair h) (filter (\<lambda>b. component_of_term (lt (fst b)) = k) bs)))"

lemma set_add_pairs_single_naive:
  "set (add_pairs_single_naive data gs bs h ps) =
    set ps \<union> {h} \<times> ((set gs \<union> set bs) \<inter> {b. component_of_term (lt (fst b)) = component_of_term (lt (fst h))})"
  by (auto simp add: add_pairs_single_naive_def Let_def)

fun add_pairs_single_sorted_aux :: "'k \<Rightarrow> (('t, 'b, 'c) pdata_pair \<Rightarrow> ('t, 'b, 'c) pdata_pair \<Rightarrow> bool) \<Rightarrow>
                                    ('t, 'b::zero, 'c, 'd) apsT"
    where
  "add_pairs_single_sorted_aux _ _ [] [] _ ps = ps"|
  "add_pairs_single_sorted_aux k rel [] (b # bs) h ps =
    (if component_of_term (lt (fst b)) = k then
      add_pairs_single_sorted_aux k rel [] bs h (insort_wrt rel (h, b) ps)
    else
      add_pairs_single_sorted_aux k rel [] bs h ps)"|
  "add_pairs_single_sorted_aux k rel (g # gs) bs h ps =
    (if component_of_term (lt (fst g)) = k then
      add_pairs_single_sorted_aux k rel gs bs h (insort_wrt rel (h, g) ps)
    else
      add_pairs_single_sorted_aux k rel gs bs h ps)"

definition add_pairs_single_sorted :: "(('t, 'b, 'c) pdata_pair \<Rightarrow> ('t, 'b, 'c) pdata_pair \<Rightarrow> bool) \<Rightarrow>
                                        ('t, 'b::zero, 'c, 'd) apsT"
  where "add_pairs_single_sorted rel gs bs h ps =
                        add_pairs_single_sorted_aux (component_of_term (lt (fst h))) rel gs bs h ps"

lemma set_add_pairs_single_sorted_aux:
  "set (add_pairs_single_sorted_aux k rel gs bs h ps) =
    set ps \<union> {h} \<times> ((set gs \<union> set bs) \<inter> {b. component_of_term (lt (fst b)) = k})"
proof (induct gs arbitrary: ps)
  case Nil
  show ?case
  proof (induct bs arbitrary: ps)
    case Nil
    show ?case by simp
  next
    case (Cons b bs)
    show ?case by (simp add: Cons)
  qed
next
  case (Cons g gs)
  show ?case by (simp add: Cons)
qed

corollary set_add_pairs_single_sorted:
  "set (add_pairs_single_sorted rel gs bs h ps) =
    set ps \<union> {h} \<times> ((set gs \<union> set bs) \<inter> {b. component_of_term (lt (fst b)) = component_of_term (lt (fst h))})"
  by (simp only: add_pairs_single_sorted_def set_add_pairs_single_sorted_aux)

primrec (in -) pairs :: "('t, 'b, 'c, 'd) apsT \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata_pair list"
  where
  "pairs _ [] = []"|
  "pairs aps (x # xs) = aps [] xs x (pairs aps xs)"

lemma pairs_subset:
  assumes "\<And>gs bs h ps. set (aps gs bs h ps) = set ps \<union> {h} \<times> ((set gs \<union> set bs) \<inter>
                                {b. component_of_term (lt (fst b)) = component_of_term (lt (fst h))})"
  shows "set (pairs aps xs) \<subseteq> (set xs \<times> set xs)"
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons have "set (pairs aps xs) \<subseteq> set (x # xs) \<times> set (x # xs)" by fastforce
  moreover have "{x} \<times> set xs \<subseteq> set (x # xs) \<times> set (x # xs)" by fastforce
  ultimately show ?case by (auto simp add: assms)
qed

lemma in_pairsI:
  assumes "\<And>gs bs h ps. set (aps gs bs h ps) = set ps \<union> {h} \<times> ((set gs \<union> set bs) \<inter>
                                {b. component_of_term (lt (fst b)) = component_of_term (lt (fst h))})"
    and "a \<noteq> b" and "component_of_term (lt (fst a)) = component_of_term (lt (fst b))"
    and "a \<in> set xs" and "b \<in> set xs"
  shows "(a, b) \<in> set (pairs aps xs) \<or> (b, a) \<in> set (pairs aps xs)"
  using assms(4, 5)
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons(3) have d: "b = x \<or> b \<in> set xs" by simp
  from Cons(2) have "a = x \<or> a \<in> set xs" by simp
  thus ?case
  proof
    assume "a = x"
    with assms(2) have "b \<noteq> x" by simp
    with d have "b \<in> set xs" by simp
    hence "(a, b) \<in> set (pairs aps (x # xs))" by (simp add: \<open>a = x\<close> assms(1) assms(3)[symmetric])
    thus ?thesis ..
  next
    assume "a \<in> set xs"
    from d show ?thesis
    proof
      assume "b = x"
      from \<open>a \<in> set xs\<close> have "(b, a) \<in> set (pairs aps (x # xs))" by (simp add: \<open>b = x\<close> assms(1, 3))
      thus ?thesis ..
    next
      assume "b \<in> set xs"
      with \<open>a \<in> set xs\<close> have "(a, b) \<in> set (pairs aps xs) \<or> (b, a) \<in> set (pairs aps xs)"
        by (rule Cons(1))
      thus ?thesis
      proof
        assume "(a, b) \<in> set (pairs aps xs)"
        hence "(a, b) \<in> set (pairs aps (x # xs))" by (simp add: assms(1))
        thus ?thesis ..
      next
        assume "(b, a) \<in> set (pairs aps xs)"
        hence "(b, a) \<in> set (pairs aps (x # xs))" by (simp add: assms(1))
        thus ?thesis ..
      qed
    qed
  qed
qed

definition add_pairs_naive :: "('t, 'b::zero, 'c, 'd) apT"
  where "add_pairs_naive gs bs ps hs data =
          fold (add_pairs_single_naive data gs bs) hs (ps @ (pairs (add_pairs_single_naive data) hs))"

definition add_pairs_sorted :: "(nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata_pair \<Rightarrow> ('t, 'b, 'c) pdata_pair \<Rightarrow> bool) \<Rightarrow>
                                ('t, 'b::zero, 'c, 'd) apT"
  where "add_pairs_sorted rel gs bs ps hs data =
          fold (add_pairs_single_sorted (rel data) gs bs) hs
                (merge_wrt (rel data) ps (pairs (add_pairs_single_sorted (rel data)) hs))"

lemma set_fold_aps:
  assumes "\<And>gs bs h ps. set (aps gs bs h ps) = set ps \<union> {h} \<times> ((set gs \<union> set bs) \<inter>
                                {b. component_of_term (lt (fst b)) = component_of_term (lt (fst h))})"
  shows "set (fold (aps gs bs) hs ps) = ((set hs \<times> (set gs \<union> set bs)) \<inter>
           {x. component_of_term (lt (fst (fst x))) = component_of_term (lt (fst (snd x)))}) \<union> set ps"
proof (induct hs arbitrary: ps)
  case Nil
  show ?case by simp
next
  case (Cons h hs)
  show ?case by (auto simp add: Cons assms)
qed

lemma set_add_pairs_naive:
  "set (add_pairs_naive gs bs ps hs data) =
    set ps \<union> ((set hs \<times> (set gs \<union> set bs)) \<inter> {x. component_of_term (lt (fst (fst x))) = component_of_term (lt (fst (snd x)))}) \<union>
    set (pairs (add_pairs_single_naive data) hs)"
proof -
  have "set (add_pairs_naive gs bs ps hs data) =
          ((set hs \<times> (set gs \<union> set bs)) \<inter> {x. component_of_term (lt (fst (fst x))) = component_of_term (lt (fst (snd x)))}) \<union>
             set (ps @ (pairs (add_pairs_single_naive data) hs))"
    unfolding add_pairs_naive_def by (rule set_fold_aps, fact set_add_pairs_single_naive)
  thus ?thesis by (simp add: ac_simps)
qed

lemma (in gd_term) ap_spec_add_pairs_naive: "ap_spec add_pairs_naive"
proof (rule ap_specI)
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps hs and data::"nat \<times> 'd"
  show "set (add_pairs_naive gs bs ps hs data) \<subseteq> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"
  proof (simp add: set_add_pairs_naive, rule, blast)
    have "set (pairs (add_pairs_single_naive data) hs) \<subseteq> set hs \<times> set hs"
      by (rule pairs_subset, fact set_add_pairs_single_naive)
    thus "set (pairs (add_pairs_single_naive data) hs) \<subseteq>
          set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)" by blast
  qed
next
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps hs and h1 h2 :: "('t, 'b, 'c) pdata" and data::"nat \<times> 'd"
  assume "h1 \<noteq> h2" and "component_of_term (lt (fst h1)) = component_of_term (lt (fst h2))"
    and "h1 \<in> set hs" and "h2 \<in> set hs"
  with set_add_pairs_single_naive
  have "(h1, h2) \<in> set (pairs (add_pairs_single_naive data) hs) \<or>
        (h2, h1) \<in> set (pairs (add_pairs_single_naive data) hs)" by (rule in_pairsI)
  thus "(h1, h2) \<in> set (add_pairs_naive gs bs ps hs data) \<or>
        (h2, h1) \<in> set (add_pairs_naive gs bs ps hs data)"
    by (auto simp add: set_add_pairs_naive)
qed (auto simp add: set_add_pairs_naive)

lemma set_add_pairs_sorted:
  "set (add_pairs_sorted rel gs bs ps hs data) =
    set ps \<union> ((set hs \<times> (set gs \<union> set bs)) \<inter> {x. component_of_term (lt (fst (fst x))) = component_of_term (lt (fst (snd x)))}) \<union>
    set (pairs (add_pairs_single_sorted (rel data)) hs)"
proof -
  have "set (add_pairs_sorted rel gs bs ps hs data) =
          ((set hs \<times> (set gs \<union> set bs)) \<inter> {x. component_of_term (lt (fst (fst x))) = component_of_term (lt (fst (snd x)))}) \<union>
             set (merge_wrt (rel data) ps (pairs (add_pairs_single_sorted (rel data)) hs))"
    unfolding add_pairs_sorted_def by (rule set_fold_aps, fact set_add_pairs_single_sorted)
  thus ?thesis by (simp add: set_merge_wrt ac_simps)
qed

lemma (in gd_term) ap_spec_add_pairs_sorted: "ap_spec (add_pairs_sorted rel)"
proof (rule ap_specI)
  fix gs bs ps hs data
  show "set (add_pairs_sorted rel gs bs ps hs data) \<subseteq> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"
  proof (simp add: set_add_pairs_sorted, rule, blast)
    have "set (pairs (add_pairs_single_sorted (rel data)) hs) \<subseteq> set hs \<times> set hs"
      by (rule pairs_subset, fact set_add_pairs_single_sorted)
    thus "set (pairs (add_pairs_single_sorted (rel data)) hs) \<subseteq>
          set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)" by blast
  qed
next
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps hs and h1 h2 :: "('t, 'b, 'c) pdata" and data::"nat \<times> 'd"
  assume "h1 \<noteq> h2" and "component_of_term (lt (fst h1)) = component_of_term (lt (fst h2))"
    and "h1 \<in> set hs" and "h2 \<in> set hs"
  with set_add_pairs_single_sorted
  have "(h1, h2) \<in> set (pairs (add_pairs_single_sorted (rel data)) hs) \<or>
        (h2, h1) \<in> set (pairs (add_pairs_single_sorted (rel data)) hs)" by (rule in_pairsI)
  thus "(h1, h2) \<in> set (add_pairs_sorted rel gs bs ps hs data) \<or>
        (h2, h1) \<in> set (add_pairs_sorted rel gs bs ps hs data)"
    by (auto simp add: set_add_pairs_sorted)
qed (auto simp add: set_add_pairs_sorted)

end (* ordered_term *)

definition (in gd_term) canon_pair_order :: "'d \<Rightarrow> ('t, 'b::zero, 'c) pdata_pair \<Rightarrow> ('t, 'b, 'c) pdata_pair \<Rightarrow> bool"
  where "canon_pair_order data p q \<longleftrightarrow>
          (lcs (lp (fst (fst p))) (lp (fst (snd p))) \<preceq>
            lcs (lp (fst (fst q))) (lp (fst (snd q))))"

subsection \<open>Suitable Instances of the @{emph \<open>add-basis\<close>} Parameter\<close>

definition add_basis_naive :: "('a, 'b, 'c, 'd) abT"
  where "add_basis_naive gs bs ns data = bs @ ns"

lemma ab_spec_add_basis_naive: "ab_spec add_basis_naive"
  by (rule ab_specI, simp_all add: add_basis_naive_def)

definition add_basis_sorted :: "(nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd) abT"
  where "add_basis_sorted rel gs bs ns data = merge_wrt (rel data) bs ns"

lemma ab_spec_add_basis_sorted: "ab_spec (add_basis_sorted rel)"
  by (rule ab_specI, simp_all add: add_basis_sorted_def set_merge_wrt)

definition card_keys :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> nat"
  where "card_keys = card \<circ> keys"

definition (in ordered_term) canon_basis_order :: "'d \<Rightarrow> ('t, 'b::zero, 'c) pdata \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow> bool"
  where "canon_basis_order data p q \<longleftrightarrow>
          (let cp = card_keys (fst p); cq = card_keys (fst q) in
            cp < cq \<or> (cp = cq \<and> lt (fst p) \<prec>\<^sub>t lt (fst q)))"

subsection \<open>Special Case: Scalar Polynomials\<close>

context ordered_powerprod
begin

lemma remdups_map_component_of_term_punit:
  "remdups (map (\<lambda>_. ()) (punit.Keys_to_list (map fst bs))) =
    (if (\<forall>b\<in>set bs. fst b = 0) then [] else [()])"
proof (split if_split, intro conjI impI)
  assume "\<forall>b\<in>set bs. fst b = 0"
  hence "fst ` set bs \<subseteq> {0}" by blast
  hence "Keys (fst ` set bs) = {}" by (metis Keys_empty Keys_zero subset_singleton_iff)
  hence "punit.Keys_to_list (map fst bs) = []"
    by (simp add: set_empty[symmetric] punit.set_Keys_to_list del: set_empty)
  thus "remdups (map (\<lambda>_. ()) (punit.Keys_to_list (map fst bs))) = []" by simp
next
  assume "\<not> (\<forall>b\<in>set bs. fst b = 0)"
  hence "\<exists>b\<in>set bs. fst b \<noteq> 0" by simp
  then obtain b where "b \<in> set bs" and "fst b \<noteq> 0" ..
  hence "Keys (fst ` set bs) \<noteq> {}" by (meson Keys_not_empty \<open>fst b \<noteq> 0\<close> imageI)
  hence "set (punit.Keys_to_list (map fst bs)) \<noteq> {}" by (simp add: punit.set_Keys_to_list)
  hence "punit.Keys_to_list (map fst bs) \<noteq> []" by simp
  thus "remdups (map (\<lambda>_. ()) (punit.Keys_to_list (map fst bs))) = [()]"
    by (metis (full_types) Nil_is_map_conv distinct_length_2_or_more distinct_remdups
        old.unit.exhaust remdups_eq_nil_right_iff sorted.cases)
qed

lemma count_const_lt_components_punit [code]:
  "punit.count_const_lt_components hs =
    (if (\<exists>h\<in>set hs. punit.const_lt_component (fst h) = Some ()) then 1 else 0)"
proof (simp add: punit.count_const_lt_components_def, simp add: card_set[symmetric], rule)
  assume "\<exists>h\<in>set hs. punit.const_lt_component (fst h) = Some ()"
  then obtain h where "h \<in> set hs" and "punit.const_lt_component (fst h) = Some ()" ..
  from this(2) have "(punit.const_lt_component \<circ> fst) h = Some ()" by simp
  with \<open>h \<in> set hs\<close> have "Some () \<in> (punit.const_lt_component \<circ> fst) ` set hs"
    by (metis rev_image_eqI)
  hence "{x. x = Some () \<and> x \<in> (punit.const_lt_component \<circ> fst) ` set hs} = {Some ()}" by auto
  thus "card {x. x = Some () \<and> x \<in> (punit.const_lt_component \<circ> fst) ` set hs} = Suc 0" by simp
qed

lemma count_rem_components_punit [code]:
  "punit.count_rem_components bs =
    (if (\<forall>b\<in>set bs. fst b = 0) then 0
    else
      if (\<exists>b\<in>set bs. fst b \<noteq> 0 \<and> punit.const_lt_component (fst b) = Some ()) then 0 else 1)"
proof (cases "\<forall>b\<in>set bs. fst b = 0")
  case True
  thus ?thesis by (simp add: punit.count_rem_components_def remdups_map_component_of_term_punit)
next
  case False
  have eq: "(\<exists>b\<in>set [b\<leftarrow>bs . fst b \<noteq> 0]. punit.const_lt_component (fst b) = Some ()) =
            (\<exists>b\<in>set bs. fst b \<noteq> 0 \<and> punit.const_lt_component (fst b) = Some ())"
    by (metis (mono_tags, lifting) filter_set member_filter)
  show ?thesis
    by (simp only: False punit.count_rem_components_def eq if_False
        remdups_map_component_of_term_punit count_const_lt_components_punit punit_component_of_term, simp)
qed

lemma full_gb_punit [code]:
  "punit.full_gb bs = (if (\<forall>b\<in>set bs. fst b = 0) then [] else [(1, 0, default)])"
  by (simp add: punit.full_gb_def remdups_map_component_of_term_punit)

lemma add_pairs_single_naive_punit [code]:
  "punit.add_pairs_single_naive data gs bs h ps = ps @ (map (Pair h) gs) @ (map (Pair h) bs)"
  by (simp add: punit.add_pairs_single_naive_def)

lemma add_pairs_single_sorted_aux_punit [code]:
  "punit.add_pairs_single_sorted_aux k rel [] [] h ps = ps"
  "punit.add_pairs_single_sorted_aux k rel [] (b # bs) h ps =
      punit.add_pairs_single_sorted_aux k rel [] bs h (insort_wrt rel (h, b) ps)"
  "punit.add_pairs_single_sorted_aux k rel (g # gs) bs h ps =
      punit.add_pairs_single_sorted_aux k rel gs bs h (insort_wrt rel (h, g) ps)"
  by simp_all

lemma add_pairs_single_sorted_punit [code]:
  "punit.add_pairs_single_sorted = punit.add_pairs_single_sorted_aux ()"
  by (intro ext, simp add: punit.add_pairs_single_sorted_def)

end (* ordered_powerprod *)

end (* theory *)
