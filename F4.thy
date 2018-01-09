section \<open>Faug\'ere's F4 Algorithm\<close>

theory F4
  imports Groebner_Bases.Groebner_Bases
begin

subsection \<open>Lists\<close>

(* TODO: Don't instantiate type class, but introduce new function with infix notation. *)
instantiation list :: (type) minus
begin

definition minus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "minus_list xs ys = fold removeAll ys xs"

instance ..

end

lemma set_minus_list: "set (xs - ys) = set xs - set ys"
  sorry

(* TODO: Replace "processed" in "Groebner_Bases" by this more general definition. *)
definition processed' :: "('a \<times> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"
  where "processed' p xs ys ps \<longleftrightarrow> fst p \<in> set ys \<and> snd p \<in> (set xs \<union> set ys) \<and> p \<notin> set ps \<and> (snd p, fst p) \<notin> set ps"

lemma processed'_alt:
  "processed' (a, b) xs ys ps \<longleftrightarrow> ((a \<in> set ys) \<and> (b \<in> (set xs \<union> set ys)) \<and> (a, b) \<notin> set ps \<and> (b, a) \<notin> set ps)"
  unfolding processed'_def by auto

lemma processed'I:
  assumes "a \<in> set ys" and "b \<in> set xs \<union> set ys" and "(a, b) \<notin> set ps" and "(b, a) \<notin> set ps"
  shows "processed' (a, b) xs ys ps"
  unfolding processed'_alt using assms by simp

lemma processed'D1:
  assumes "processed' (a, b) xs ys ps"
  shows "a \<in> set ys"
  using assms by (simp add: processed'_alt)

lemma processed'D2:
  assumes "processed' (a, b) xs ys ps"
  shows "b \<in> set xs \<union> set ys"
  using assms by (simp add: processed'_alt)

lemma processed'D3:
  assumes "processed' (a, b) xs ys ps"
  shows "(a, b) \<notin> set ps"
  using assms by (simp add: processed'_alt)

lemma processed'D4:
  assumes "processed' (a, b) xs ys ps"
  shows "(b, a) \<notin> set ps"
  using assms by (simp add: processed'_alt)

lemma processed'_Nil: "processed' (a, b) xs ys [] \<longleftrightarrow> (a \<in> set ys \<and> b \<in> (set xs \<union> set ys))"
  by (simp add: processed'_alt)

lemma processed'_Cons:
  assumes "processed' (a, b) xs ys ps"
    and a1: "a = p \<Longrightarrow> b = q \<Longrightarrow> thesis"
    and a2: "a = q \<Longrightarrow> b = p \<Longrightarrow> thesis"
    and a3: "processed' (a, b) xs ys ((p, q) # ps) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "a \<in> set ys" and "b \<in> set xs \<union> set ys" and "(a, b) \<notin> set ps" and "(b, a) \<notin> set ps"
    by (simp_all add: processed'_alt)
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
      with \<open>a \<in> set ys\<close> \<open>b \<in> set xs \<union> set ys\<close> * have "processed' (a, b) xs ys ((p, q) # ps)"
        by (rule processed'I)
      thus ?thesis by (rule a3)
    qed
  qed
qed

lemma processed'_minus:
  assumes "processed' (a, b) xs ys (ps - qs)"
    and a1: "(a, b) \<in> set qs \<Longrightarrow> thesis"
    and a2: "(b, a) \<in> set qs \<Longrightarrow> thesis"
    and a3: "processed' (a, b) xs ys ps \<Longrightarrow> thesis"
  shows thesis
  sorry

subsection \<open>Algorithm Schema\<close>

subsubsection \<open>Type synonyms\<close>

type_synonym ('a, 'b, 'c) pdata = "('a \<Rightarrow>\<^sub>0 'b) \<times> 'c"
type_synonym ('a, 'b, 'c) pdata_pair = "('a, 'b, 'c) pdata \<times> ('a, 'b, 'c) pdata"
type_synonym ('a, 'b, 'c) selT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c) complT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                    ('a, 'b, 'c) pdata list"
type_synonym ('a, 'b, 'c) apT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c) abT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list"

subsubsection \<open>Specification of the @{emph \<open>selector\<close>} parameter\<close>

definition sel_spec :: "('a, 'b, 'c) selT \<Rightarrow> bool"
  where "sel_spec sel \<longleftrightarrow> (\<forall>gs bs ps. ps \<noteq> [] \<longrightarrow> (sel gs bs ps \<noteq> [] \<and> set (sel gs bs ps) \<subseteq> set ps))"

lemma sel_specD1:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "sel gs bs ps \<noteq> []"
  sorry

lemma sel_specD2:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "set (sel gs bs ps) \<subseteq> set ps"
  sorry

subsubsection \<open>Specification of the @{emph \<open>add-pairs\<close>} parameter\<close>

definition ap_spec :: "('a, 'b, 'c) apT \<Rightarrow> bool"
  where "ap_spec ap \<longleftrightarrow> (\<forall>gs bs ps ns.
      set (ap gs bs ps ns) \<subseteq> set ps \<union> (set ns \<times> (set gs \<union> set bs \<union> set ns)) \<and>
      set ps \<union> (set ns \<times> (set gs \<union> set bs)) \<subseteq> set (ap gs bs ps ns) \<and>
      (\<forall>h1\<in>set ns. \<forall>h2\<in> set ns. h1 \<noteq> h2 \<longrightarrow> ((h1, h2) \<in> set (ap gs bs ps ns) \<or> (h2, h1) \<in> set (ap gs bs ps ns))))"

lemma ap_specI:
  assumes "\<And>gs bs ps ns.
        set (ap gs bs ps ns) \<subseteq> set ps \<union> (set ns \<times> (set gs \<union> set bs \<union> set ns)) \<and>
        set ps \<union> (set ns \<times> (set gs \<union> set bs)) \<subseteq> set (ap gs bs ps ns) \<and>
        (\<forall>h1\<in>set ns. \<forall>h2\<in> set ns. h1 \<noteq> h2 \<longrightarrow> ((h1, h2) \<in> set (ap gs bs ps ns) \<or> (h2, h1) \<in> set (ap gs bs ps ns)))"
  shows "ap_spec ap"
  unfolding ap_spec_def using assms by blast

lemma ap_specD1:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps ns) \<subseteq> set ps \<union> (set ns \<times> (set gs \<union> set bs \<union> set ns))"
  using assms unfolding ap_spec_def by blast

lemma ap_specD2:
  assumes "ap_spec ap"
  shows "set ps \<union> (set ns \<times> (set gs \<union> set bs)) \<subseteq> set (ap gs bs ps ns)"
  using assms unfolding ap_spec_def by blast

lemma ap_specE:
  assumes "ap_spec ap" and "h1 \<in> set ns" and "h2 \<in> set ns" and "h1 \<noteq> h2"
  obtains "(h1, h2) \<in> set (ap gs bs ps ns)"|"(h2, h1) \<in> set (ap gs bs ps ns)"
  using assms unfolding ap_spec_def by blast

lemma ap_spec_empty_new:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps []) = set ps"
proof
  from ap_specD1[OF assms] show "set (ap gs bs ps []) \<subseteq> set ps" by fastforce
next
  from ap_specD2[OF assms] show "set ps \<subseteq> set (ap gs bs ps [])" by blast
qed

lemma ap_spec_inI1:
  assumes "ap_spec ap" and "p \<in> set ps"
  shows "p \<in> set (ap gs bs ps ns)"
  using ap_specD2[OF assms(1)] assms(2) by blast

lemma ap_spec_inI2:
  assumes "ap_spec ap" and "h \<in> set ns" and "g \<in> set gs \<union> set bs"
  shows "(h, g) \<in> set (ap gs bs ps ns)"
  using ap_specD2[OF assms(1)] assms(2, 3) by blast

lemma ap_spec_fst_subset:
  assumes "ap_spec ap"
  shows "fst ` set (ap gs bs ps ns) \<subseteq> fst ` set ps \<union> set ns"
proof -
  from ap_specD1[OF assms]
  have "fst ` set (ap gs bs ps ns) \<subseteq> fst ` (set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_snd_subset:
  assumes "ap_spec ap"
  shows "snd ` set (ap gs bs ps ns) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set ns"
proof -
  from ap_specD1[OF assms]
  have "snd ` set (ap gs bs ps ns) \<subseteq> snd ` (set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_fst_superset:
  assumes "ap_spec ap"
  shows "fst ` set ps \<subseteq> fst ` set (ap gs bs ps ns)"
proof -
  from ap_specD2[OF assms]
  have "fst ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> fst ` set (ap gs bs ps ns)"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_fst:
  assumes "ap_spec ap" and "set gs \<union> set bs \<noteq> {}"
  shows "fst ` set (ap gs bs ps ns) = fst ` set ps \<union> set ns"
proof
  from assms(1) show "fst ` set (ap gs bs ps ns) \<subseteq> fst ` set ps \<union> set ns" by (rule ap_spec_fst_subset)
next
  show "fst ` set ps \<union> set ns \<subseteq> fst ` set (ap gs bs ps ns)"
  proof (simp only: Un_subset_iff, rule conjI, rule ap_spec_fst_superset, fact)
    from ap_specD2[OF assms(1)]
    have "fst ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> fst ` set (ap gs bs ps ns)"
      by (rule image_mono)
    hence "fst ` (set ns \<times> (set gs \<union> set bs)) \<subseteq> fst ` set (ap gs bs ps ns)" by blast
    with assms(2) show "set ns \<subseteq> fst ` set (ap gs bs ps ns)" by auto
  qed
qed

lemma ap_spec_snd_superset1:
  assumes "ap_spec ap"
  shows "snd ` set ps \<subseteq> snd ` set (ap gs bs ps ns)"
proof -
  from ap_specD2[OF assms]
  have "snd ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> snd ` set (ap gs bs ps ns)"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_snd_superset2:
  assumes "ap_spec ap" and "ns \<noteq> []"
  shows "snd ` set ps \<union> set gs \<union> set bs \<subseteq> snd ` set (ap gs bs ps ns)"
proof -
  from ap_specD2[OF assms(1)]
  have "snd ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> snd ` set (ap gs bs ps ns)"
    by (rule image_mono)
  with assms(2) show ?thesis by (simp add: image_Un)
qed

lemma ap_spec_inE:
  assumes "ap_spec ap" and "(p, q) \<in> set (ap gs bs ps ns)"
  assumes 1: "(p, q) \<in> set ps \<Longrightarrow> thesis"
  assumes 2: "p \<in> set ns \<Longrightarrow> q \<in> set gs \<union> set bs \<union> set ns \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(2) ap_specD1[OF assms(1)] have "(p, q) \<in> set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns)" ..
  thus ?thesis
  proof
    assume "(p, q) \<in> set ps"
    thus ?thesis by (rule 1)
  next
    assume "(p, q) \<in> set ns \<times> (set gs \<union> set bs \<union> set ns)"
    hence "p \<in> set ns" and "q \<in> set gs \<union> set bs \<union> set ns" by blast+
    thus ?thesis by (rule 2)
  qed
qed

subsubsection \<open>Specification of the @{emph \<open>add-basis\<close>} parameter\<close>

definition ab_spec :: "('a, 'b, 'c) abT \<Rightarrow> bool"
  where "ab_spec ab \<longleftrightarrow> (\<forall>gs bs ns. ns \<noteq> [] \<longrightarrow> set (ab gs bs ns) = set bs \<union> set ns) \<and> (\<forall>gs bs. ab gs bs [] = bs)"

lemma ab_specD1:
  assumes "ab_spec ab"
  shows "set (ab gs bs ns) = set bs \<union> set ns"
  sorry

lemma ab_specD2:
  assumes "ab_spec ab"
  shows "ab gs bs [] = bs"
  sorry

lemma subset_Times_ap:
  assumes "ap_spec ap" and "ab_spec ab" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "set (ap gs bs (ps - sps) ns) \<subseteq> set (ab gs bs ns) \<times> (set gs \<union> set (ab gs bs ns))"
proof
  fix p q
  assume "(p, q) \<in> set (ap gs bs (ps - sps) ns)"
  with assms(1) show "(p, q) \<in> set (ab gs bs ns) \<times> (set gs \<union> set (ab gs bs ns))"
  proof (rule ap_spec_inE)
    assume "(p, q) \<in> set (ps - sps)"
    hence "(p, q) \<in> set ps" by (simp add: set_minus_list)
    from this assms(3) have "(p, q) \<in> set bs \<times> (set gs \<union> set bs)" ..
    hence "p \<in> set bs" and "q \<in> set gs \<union> set bs" by blast+
    thus ?thesis by (auto simp add: ab_specD1[OF assms(2)])
  next
    assume "p \<in> set ns" and "q \<in> set gs \<union> set bs \<union> set ns"
    thus ?thesis by (simp add: ab_specD1[OF assms(2)])
  qed
qed

lemma processed'_apE:
  assumes "ap_spec ap" and "ab_spec ab" and "processed' (f, g) gs (ab gs bs ns) (ap gs bs ps ns)"
  assumes 1: "processed' (f, g) gs bs ps \<Longrightarrow> thesis"
  assumes 2: "f \<in> set ns \<Longrightarrow> g \<in> set ns \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(3) have d1: "f \<in> set bs \<or> f \<in> set ns" and d2: "g \<in> set gs \<union> set bs \<or> g \<in> set ns"
    and a: "(f, g) \<notin> set (ap gs bs ps ns)" and b: "(g, f) \<notin> set (ap gs bs ps ns)"
    by (simp_all add: processed'_def ab_specD1[OF assms(2)])
  from d1 show ?thesis
  proof
    assume "f \<in> set ns"
    from d2 show ?thesis
    proof
      assume "g \<in> set ns"
      with \<open>f \<in> set ns\<close> show ?thesis by (rule 2)
    next
      assume "g \<in> set gs \<union> set bs"
      with assms(1) \<open>f \<in> set ns\<close> have "(f, g) \<in> set (ap gs bs ps ns)" by (rule ap_spec_inI2)
      with a show ?thesis ..
    qed
  next
    assume "f \<in> set bs"
    hence "f \<in> set gs \<union> set bs" by simp
    from d2 show ?thesis
    proof
      assume "g \<in> set ns"
      from assms(1) this \<open>f \<in> set gs \<union> set bs\<close> have "(g, f) \<in> set (ap gs bs ps ns)"
        by (rule ap_spec_inI2)
      with b show ?thesis ..
    next
      assume "g \<in> set gs \<union> set bs"
      from \<open>f \<in> set bs\<close> this have "processed' (f, g) gs bs ps"
      proof (rule processed'I)
        show "(f, g) \<notin> set ps"
        proof
          assume "(f, g) \<in> set ps"
          with assms(1) have "(f, g) \<in> set (ap gs bs ps ns)" by (rule ap_spec_inI1)
          with a show False ..
        qed
      next
        show "(g, f) \<notin> set ps"
        proof
          assume "(g, f) \<in> set ps"
          with assms(1) have "(g, f) \<in> set (ap gs bs ps ns)" by (rule ap_spec_inI1)
          with b show False ..
        qed
      qed
      thus ?thesis by (rule 1)
    qed
  qed
qed

subsubsection \<open>Function @{term args_to_set}\<close>

context gd_powerprod
begin

definition args_to_set :: "('a, 'b::field, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) set"
  where "args_to_set x = fst ` (set (fst x) \<union> set (fst (snd x)) \<union> fst ` set (snd (snd x)) \<union> snd ` set (snd (snd x)))"

lemma args_to_set_alt:
  "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs \<union> fst ` fst ` set ps \<union> fst ` snd ` set ps"
  by (simp add: args_to_set_def image_Un)

lemma args_to_set_subset_Times:
  assumes "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs"
  unfolding args_to_set_alt using assms by auto

subsubsection \<open>Specification of the @{emph \<open>completion\<close>} parameter\<close>

definition compl_struct :: "('a, 'b::field, 'c) complT \<Rightarrow> bool"
  where "compl_struct compl \<longleftrightarrow> (\<forall>d gs bs ps sps. dickson_grading (op +) d \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
                          dgrad_p_set_le d (fst ` (set (compl gs bs ps sps))) (args_to_set (gs, bs, ps))) \<and>
                       (\<forall>gs bs ps sps h. set sps \<subseteq> set ps \<longrightarrow> h \<in> set (compl gs bs ps sps) \<longrightarrow>
                          (fst h \<noteq> 0 \<and> \<not> is_red (fst ` set bs) (fst h)))"

lemma compl_structD1:
  assumes "compl_struct compl" and "dickson_grading (op +) d" and "set sps \<subseteq> set ps"
  shows "dgrad_p_set_le d (fst ` (set (compl gs bs ps sps))) (args_to_set (gs, bs, ps))"
  sorry

lemma compl_structD2:
  assumes "compl_struct compl" and "set sps \<subseteq> set ps"
  shows "0 \<notin> fst ` set (compl gs bs ps sps)"
  sorry

lemma compl_structD3:
  assumes "compl_struct compl" and "set sps \<subseteq> set ps" and "h \<in> set (compl gs bs ps sps)"
  shows "\<not> is_red (fst ` set bs) (fst h)"
  sorry

lemma args_to_set_alt2:
  assumes "ap_spec ap" and "ab_spec ab"
  shows "args_to_set (gs, ab gs bs ns, ap gs bs ps ns) = fst ` (set gs \<union> set bs \<union>
              fst ` set ps \<union> snd ` set ps \<union> set ns)" (is "?l = fst ` ?r")
proof
  show "?l \<subseteq> fst ` ?r"
  proof (simp only: args_to_set_alt Un_subset_iff, intro conjI image_mono)
    show "set (ab gs bs ns) \<subseteq> ?r" by (auto simp add: ab_specD1[OF assms(2)])
  next
    from assms(1) have "fst ` set (ap gs bs ps ns) \<subseteq> fst ` set ps \<union> set ns"
      by (rule ap_spec_fst_subset)
    thus "fst ` set (ap gs bs ps ns) \<subseteq> ?r" by blast
  next
    from assms(1) have "snd ` set (ap gs bs ps ns) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set ns"
      by (rule ap_spec_snd_subset)
    thus "snd ` set (ap gs bs ps ns) \<subseteq> ?r" by blast
  qed blast
next
  let ?u = "set gs \<union> set (ab gs bs ns) \<union> fst ` set (ap gs bs ps ns) \<union> snd ` set (ap gs bs ps ns)"
  show "fst ` ?r \<subseteq> ?l"
  proof (simp only: args_to_set_alt image_Un[symmetric], rule image_mono, simp only: Un_subset_iff, intro conjI)
    show "set gs \<subseteq> ?u" by blast
  next
    from assms(2) have "set bs \<subseteq> set (ab gs bs ns)" by (simp add: ab_specD1)
    thus "set bs \<subseteq> ?u" by blast
  next
    from assms(1) have "fst ` set ps \<subseteq> fst ` set (ap gs bs ps ns)"
      by (rule ap_spec_fst_superset)
    thus "fst ` set ps \<subseteq> ?u" by blast
  next
    from assms(1) have "snd ` set ps \<subseteq> snd ` set (ap gs bs ps ns)"
      by (rule ap_spec_snd_superset1)
    thus "snd ` set ps \<subseteq> ?u" by blast
  next
    from assms(2) have "set ns \<subseteq> set (ab gs bs ns)" by (simp add: ab_specD1)
    thus "set ns \<subseteq> ?u" by blast
  qed
qed

definition struct_spec :: "('a, 'b::field, 'c) selT \<Rightarrow> ('a, 'b, 'c) apT \<Rightarrow> ('a, 'b, 'c) abT \<Rightarrow> ('a, 'b, 'c) complT \<Rightarrow> bool"
  where "struct_spec sel ap ab compl \<longleftrightarrow> (sel_spec sel \<and> ap_spec ap \<and> ab_spec ab \<and> compl_struct compl)"

lemma struct_specD1:
  assumes "struct_spec sel ap ab compl"
  shows "sel_spec sel"
  sorry

lemma struct_specD2:
  assumes "struct_spec sel ap ab compl"
  shows "ap_spec ap"
  sorry

lemma struct_specD3:
  assumes "struct_spec sel ap ab compl"
  shows "ab_spec ab"
  sorry

lemma struct_specD4:
  assumes "struct_spec sel ap ab compl"
  shows "compl_struct compl"
  sorry

definition compl_pideal :: "('a, 'b::field, 'c) complT \<Rightarrow> bool"
  where "compl_pideal compl \<longleftrightarrow> (\<forall>gs bs ps sps. ps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
                          fst ` (set (compl gs bs ps sps)) \<subseteq> pideal (args_to_set (gs, bs, ps)))"

lemma compl_pidealD:
  assumes "compl_pideal compl" and "ps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "fst ` (set (compl gs bs ps sps)) \<subseteq> pideal (args_to_set (gs, bs, ps))"
  using assms unfolding compl_pideal_def by blast

definition compl_conn :: "('a, 'b::field, 'c) complT \<Rightarrow> bool"
  where "compl_conn compl \<longleftrightarrow> (\<forall>d m gs bs ps sps p q. dickson_grading (op +) d \<longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<longrightarrow>
                                is_Groebner_basis (fst ` set gs) \<longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
                                set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
                                (\<forall>p' q'. processed' (p', q') gs bs ps \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                                    crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')) \<longrightarrow>
                                (p, q) \<in> set sps \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow>
                                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set (compl gs bs ps sps))) (fst p) (fst q))"

lemma compl_connD:
  assumes "compl_conn compl" and "dickson_grading (op +) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "set sps \<subseteq> set ps"
    and "\<And>p' q'. processed' (p', q') gs bs ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                 crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
    and "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> (set bs \<union> set (compl gs bs ps sps)))) (fst p) (fst q)"
  using assms unfolding compl_conn_def Un_assoc by blast

subsubsection \<open>More facts about Gr\"obner bases\<close>

(* TODO: Move to "Groebner_Bases"? *)

lemma lcs_red_single_fst_crit_pair:
  assumes "p \<noteq> 0"
  shows "red_single (monomial (-1) (lcs (lp p) (lp q))) (fst (crit_pair p q)) p (lcs (lp p) (lp q) - lp p)"
proof -
  let ?l = "lcs (lp p) (lp q)"
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  have "lp p adds ?l" by (rule adds_lcs)
  hence eq1: "?l - lp p + lp p = ?l" by (rule adds_minus)
  with assms show ?thesis
  proof (simp add: crit_pair_def red_single_def)
    have eq2: "monomial (-1) ?l = monom_mult (- (1 / lc p)) (?l - lp p) (monomial (lc p) (lp p))"
      by (simp add: monom_mult_monomial eq1 \<open>lc p \<noteq> 0\<close>)
    show "monom_mult (1 / lc p) (?l - lp p) (tail p) = monomial (-1) ?l - monom_mult (- (1 / lc p)) (?l - lp p) p"
      by (simp add: eq2 monom_mult_dist_right_minus[symmetric] tail_alt_2 monom_mult_uminus_left)
  qed
qed

corollary lcs_red_single_snd_crit_pair:
  assumes "q \<noteq> 0"
  shows "red_single (monomial (-1) (lcs (lp p) (lp q))) (snd (crit_pair p q)) q (lcs (lp p) (lp q) - lp q)"
  by (simp add: crit_pair_swap[of p q] lcs_comm[of "lp p"], rule lcs_red_single_fst_crit_pair, fact)

lemma GB_imp_crit_pair_cbelow_dgrad_p_set:
  assumes "dickson_grading (op +) d" and "F \<subseteq> dgrad_p_set d m" and "is_Groebner_basis F"
  assumes "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
  shows "crit_pair_cbelow_on d m F p q"
  using assms(1, 2)
proof (rule crit_pair_cs_imp_crit_pair_cbelow_on)
  from assms(4, 2) show "p \<in> dgrad_p_set d m" ..
next
  from assms(5, 2) show "q \<in> dgrad_p_set d m" ..
next
  let ?cp = "crit_pair p q"
  let ?l = "monomial (-1) (lcs (lp p) (lp q))"
  from assms(4) lcs_red_single_fst_crit_pair[OF assms(6)] have "red F ?l (fst ?cp)"
    by (rule red_setI)
  hence 1: "(red F)\<^sup>*\<^sup>* ?l (fst ?cp)" ..
  from assms(5) lcs_red_single_snd_crit_pair[OF assms(7)] have "red F ?l (snd ?cp)"
    by (rule red_setI)
  hence 2: "(red F)\<^sup>*\<^sup>* ?l (snd ?cp)" ..
  from assms(3) have "relation.is_confluent_on (red F) UNIV"
    by (simp only: is_Groebner_basis_def relation.confluence_equiv_ChurchRosser[symmetric]
        relation.is_confluent_def)
  from this 1 2 show "relation.cs (red F) (fst ?cp) (snd ?cp)"
    by (simp add: relation.is_confluent_on_def)
qed

subsubsection \<open>Function @{term gb_schema_aux}\<close>

definition gb_schema_aux_term1 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a, 'b::field, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list) \<times>
                                                (('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term1 d = (measure length) <*lex*>
                              {(a, b::('a, 'b, 'c) pdata list). (fst ` set a) \<sqsupset>p (fst ` set b)} <*lex*>
                              (measure (card \<circ> set))"

definition gb_schema_aux_term2 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a, 'b::field, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list) \<times>
                                                (('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term2 d = {(a, b). dgrad_p_set_le d (args_to_set a) (args_to_set b)}"

definition gb_schema_aux_term where "gb_schema_aux_term d = gb_schema_aux_term1 d \<inter> gb_schema_aux_term2 d"

text \<open>@{const gb_schema_aux_term} is needed for proving termination of function @{term gb_schema_aux}.\<close>

lemma gb_schema_aux_term1_wf_on:
  assumes "dickson_grading (op +) d"
  shows "wfP_on {x. args_to_set x \<subseteq> dgrad_p_set d m} (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1 d)"
proof (rule wfP_onI_min)
  let ?B = "dgrad_p_set d m"
  let ?A = "{x::(('a, 'b, 'c) pdata list) \<times> ('a, 'b, 'c) pdata list \<times> ((('a, 'b, 'c) pdata_pair list)). args_to_set x \<subseteq> ?B}"
  have A_sub_Pow: "(op ` fst) ` set ` fst ` snd ` ?A \<subseteq> Pow ?B"
  proof
    fix x
    assume "x \<in> (op ` fst) ` set ` fst ` snd ` ?A"
    then obtain x1 where "x1 \<in> set ` fst ` snd ` ?A" and x: "x = fst ` x1" by auto
    from this(1) obtain x2 where "x2 \<in> fst ` snd ` ?A" and x1: "x1 = set x2" by auto
    from this(1) obtain x3 where "x3 \<in> snd ` ?A" and x2: "x2 = fst x3" by auto
    from this(1) obtain x4 where "x4 \<in> ?A" and x3: "x3 = snd x4" by auto
    from this(1) have "args_to_set x4 \<subseteq> ?B" by simp
    thus "x \<in> Pow ?B" by (simp add: args_to_set_def x x1 x2 x3 image_Un)
  qed

  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  have "fst x \<in> fst ` Q" by (rule, fact refl, fact)
  with wf_measure obtain z0 where "z0 \<in> fst ` Q" and 1: "\<And>y. (y, z0) \<in> measure length \<Longrightarrow> y \<notin> fst ` Q"
    by (rule wfE_min, blast)
  from this(1) obtain x0 where "x0 \<in> Q" and z0: "z0 = fst x0" ..

  let ?Q1 = "{q \<in> Q. fst q = z0}"
  have "?Q1 \<subseteq> Q" by blast
  have "(op ` fst) ` set ` fst ` snd ` ?Q1 \<subseteq> (op ` fst) ` set ` fst ` snd ` Q"
    by ((rule image_mono)+, fact)
  also have "... \<subseteq> (op ` fst) ` set ` fst ` snd ` ?A"
    by ((rule image_mono)+, fact)
  finally have Q_sub_A: "(op ` fst) ` set ` fst ` snd ` ?Q1 \<subseteq> (op ` fst) ` set ` fst ` snd ` ?A" .
  from assms have "wfP_on (Pow ?B) (op \<sqsupset>p)" by (rule red_supset_wf_on)
  moreover have "fst ` set (fst (snd x0)) \<in> (op ` fst) ` set ` fst ` snd ` ?Q1"
    by (rule, fact refl, rule, fact refl, rule, fact refl, rule, fact refl, simp add: \<open>x0 \<in> Q\<close> z0)
  moreover from Q_sub_A A_sub_Pow have "(op ` fst) ` set ` fst ` snd ` ?Q1 \<subseteq> Pow ?B" by (rule subset_trans)
  ultimately obtain z1 where "z1 \<in> (op ` fst) ` set ` fst ` snd ` ?Q1"
    and 2: "\<And>y. y \<sqsupset>p z1 \<Longrightarrow> y \<notin> (op ` fst) ` set ` fst ` snd ` ?Q1" by (rule wfP_onE_min, auto)
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
  from this(1) have "z \<in> ?Q1" and eq1: "fst ` set (fst (snd z)) = z1" by simp_all
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
        hence "fst ` set (fst (snd y)) \<notin> (op ` fst) ` set ` fst ` snd ` ?Q1" by (rule 2)
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
  assumes "dickson_grading (op +) d"
  shows "wf (gb_schema_aux_term d)"
proof (rule wfI_min)
  fix x::"(('a, 'b, 'c) pdata list) \<times> ('a, 'b, 'c) pdata list \<times> (('a, 'b, 'c) pdata_pair list)" and Q
  assume "x \<in> Q"
  let ?A = "args_to_set x"
  have "finite ?A" by (simp add: args_to_set_def)
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. args_to_set q \<subseteq> ?B}"
  from assms have "wfP_on {x. args_to_set x \<subseteq> ?B} (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1 d)"
    by (rule gb_schema_aux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by simp
  moreover have "?Q \<subseteq> {x. args_to_set x \<subseteq> ?B}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> gb_schema_aux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "args_to_set z \<subseteq> ?B" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> gb_schema_aux_term d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> gb_schema_aux_term d \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> gb_schema_aux_term d"
      hence "(y, z) \<in> gb_schema_aux_term1 d" and "(y, z) \<in> gb_schema_aux_term2 d"
        by (simp_all add: gb_schema_aux_term_def)
      from this(2) have "dgrad_p_set_le d (args_to_set y) (args_to_set z)"
        by (simp add: gb_schema_aux_term2_def)
      from this \<open>args_to_set z \<subseteq> ?B\<close> have "args_to_set y \<subseteq> ?B" by (rule dgrad_p_set_le_dgrad_p_set)
      moreover from \<open>(y, z) \<in> gb_schema_aux_term1 d\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

lemma dgrad_p_set_leI_Un:
  assumes "dgrad_p_set_le d F1 G" and "dgrad_p_set_le d F2 G"
  shows "dgrad_p_set_le d (F1 \<union> F2) G"
  using assms by (auto simp: dgrad_p_set_le_def)

lemma dgrad_p_set_le_args_to_set_ab:
  assumes "dickson_grading (op +) d" and "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  assumes "set sps \<subseteq> set ps" and "ns = compl gs bs ps sps"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs ns, ap gs bs (ps - sps) ns)) (args_to_set (gs, bs, ps))"
  unfolding args_to_set_alt2[OF assms(2, 3)] image_Un
proof (intro dgrad_p_set_leI_Un)
  show "dgrad_p_set_le d (fst ` set gs) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
next
  show "dgrad_p_set_le d (fst ` set bs) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
next
  show "dgrad_p_set_le d (fst ` fst ` set (ps - sps)) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_minus_list)
next
  show "dgrad_p_set_le d (fst ` snd ` set (ps - sps)) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_minus_list)
next
  from assms(4, 1, 5) show "dgrad_p_set_le d (fst ` set ns) (args_to_set (gs, bs, ps))"
    unfolding assms(6) by (rule compl_structD1)
qed

corollary dgrad_p_set_le_args_to_set_struct:
  assumes "dickson_grading (op +) d" and "struct_spec sel ap ab compl" and "ps \<noteq> []"
  assumes "sps = sel gs bs ps" and "ns = compl gs bs ps sps"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs ns, ap gs bs (ps - sps) ns)) (args_to_set (gs, bs, ps))"
proof -
  from assms(2) have "sel_spec sel" by (rule struct_specD1)
  from this assms(3) have "set sps \<subseteq> set ps" unfolding assms(4) by (rule sel_specD2)
  from assms(2) have "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
    by (rule struct_specD2, rule struct_specD3, rule struct_specD4)
  from assms(1) this \<open>set sps \<subseteq> set ps\<close> assms(5) show ?thesis by (rule dgrad_p_set_le_args_to_set_ab)
qed

lemma red_supset_ab:
  assumes "ab_spec ab" and "compl_struct compl" and "set sps \<subseteq> set ps" and "ns = compl gs bs ps sps"
    and "ns \<noteq> []"
  shows "(fst ` set (ab gs bs ns)) \<sqsupset>p (fst ` set bs)"
proof -
  from assms(5) have "set ns \<noteq> {}" by simp
  then obtain h' where "h' \<in> set ns" by fastforce
  let ?h = "fst h'"
  from \<open>h' \<in> set ns\<close> have h_in: "?h \<in> fst ` set ns" by simp
  with compl_structD2[OF assms(2, 3), of gs bs] have "?h \<noteq> 0" unfolding assms(4) by metis
  show ?thesis
  proof (simp add: ab_specD1[OF assms(1)] image_Un, rule)
    fix q
    assume "is_red (fst ` set bs) q"
    moreover have "fst ` set bs \<subseteq> fst ` set bs \<union> fst ` set ns" by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set ns) q" by (rule is_red_subset)
  next
    from \<open>?h \<noteq> 0\<close> have "is_red {?h} ?h" using is_red_alt red_self by auto
    moreover have "{?h} \<subseteq> fst ` set bs \<union> fst ` set ns" using h_in by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set ns) ?h" by (rule is_red_subset)
  next
    thm compl_structD3
    from assms(2, 3) \<open>h' \<in> set ns\<close> show "\<not> is_red (fst ` set bs) ?h"
      unfolding assms(4) by (rule compl_structD3)
  qed
qed

(* TODO: Abort "gb_schema_aux" as soon as "is_nz_const_pdata" holds for some element of "ns".
  Actually, this could also be incorporated into the computation of reduced Groebner bases. *)
definition is_nz_const_pdata :: "('a, 'b::zero, 'c) pdata \<Rightarrow> bool"
  where "is_nz_const_pdata p \<longleftrightarrow> (fst p \<noteq> 0 \<and> lp (fst p) = 0)"

function (domintros) gb_schema_aux :: "('a, 'b, 'c) selT \<Rightarrow> ('a, 'b, 'c) apT \<Rightarrow> ('a, 'b, 'c) abT \<Rightarrow> ('a, 'b, 'c) complT \<Rightarrow>
                        ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                        ('a, 'b, 'c) pdata list"
  where
    "gb_schema_aux sel ap ab compl gs bs ps =
        (if ps = [] then
          gs @ bs
        else
          (let sps = sel gs bs ps; ns = compl gs bs ps sps in
            gb_schema_aux sel ap ab compl gs (ab gs bs ns) (ap gs bs (ps - sps) ns)
          )
        )"
  by pat_completeness auto

lemma gb_schema_aux_domI1: "gb_schema_aux_dom (sel, ap, ab, compl, gs, bs, [])"
  using gb_schema_aux.domintros by blast

lemma gb_schema_aux_domI2:
  assumes "struct_spec sel ap ab compl"
  shows "gb_schema_aux_dom (sel, ap, ab, compl, args)"
proof -
  from assms have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3, rule struct_specD4)
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (op +) d" ..
  let ?R = "gb_schema_aux_term d"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  thus ?thesis
  proof induct
    fix x
    assume IH: "\<And>y. (y, x) \<in> gb_schema_aux_term d \<Longrightarrow> gb_schema_aux_dom (sel, ap, ab, compl, y)"
    obtain gs bs0 where x: "x = (gs, bs0)" by (meson case_prodE case_prodI2)
    obtain bs ps where bs0: "bs0 = (bs, ps)" by (meson case_prodE case_prodI2)
    show "gb_schema_aux_dom (sel, ap, ab, compl, x)" unfolding x bs0
    proof (rule gb_schema_aux.domintros)
      assume "ps \<noteq> []"
      define sps where "sps = sel gs bs ps"
      from sel \<open>ps \<noteq> []\<close> have sub: "set sps \<subseteq> set ps" unfolding sps_def by (rule sel_specD2)
      define ns where "ns = compl gs bs ps sps"
      show "gb_schema_aux_dom (sel, ap, ab, compl, gs, ab gs bs ns, ap gs bs (ps - sps) ns)"
      proof (rule IH, simp add: x bs0 gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, rule)
        show "fst ` set (ab gs bs ns) \<sqsupset>p fst ` set bs \<or> ab gs bs ns = bs \<and> card (set (ap gs bs (ps - sps) ns)) < card (set ps)"
        proof (cases "ns = []")
          case True
          have "ab gs bs ns = bs \<and> card (set (ap gs bs (ps - sps) ns)) < card (set ps)"
          proof (simp only: True ap_spec_empty_new[OF ap], rule)
            from ab show "ab gs bs [] = bs" by (rule ab_specD2)
          next
            from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
            with sub have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
            hence "set (ps - sps) \<subset> set ps" unfolding set_minus_list by fastforce
            thus "card (set (ps - sps)) < card (set ps)" by (simp add: psubset_card_mono)
          qed
          thus ?thesis ..
        next
          case False
          with ab compl sub ns_def have "fst ` set (ab gs bs ns) \<sqsupset>p fst ` set bs" by (rule red_supset_ab)
          thus ?thesis ..
        qed
      next
        from dg assms \<open>ps \<noteq> []\<close> sps_def ns_def
        show "dgrad_p_set_le d (args_to_set (gs, ab gs bs ns, ap gs bs (ps - sps) ns)) (args_to_set (gs, bs, ps))"
          by (rule dgrad_p_set_le_args_to_set_struct)
      qed
    qed
  qed
qed

lemmas gb_schema_aux_simp = gb_schema_aux.psimps[OF gb_schema_aux_domI2]

lemma gb_schema_aux_empty [simp, code]: "gb_schema_aux sel ap ab compl gs bs [] = gs @ bs"
  by (simp add: gb_schema_aux.psimps[OF gb_schema_aux_domI1])

lemma gb_schema_aux_not_empty:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []"
  shows "gb_schema_aux sel ap ab compl gs bs ps =
          (let sps = sel gs bs ps; ns = compl gs bs ps sps in
            gb_schema_aux sel ap ab compl gs (ab gs bs ns) (ap gs bs (ps - sps) ns)
          )"
  by (simp add: gb_schema_aux_simp[OF assms(1)] assms(2))

text \<open>In order to prove the following lemma we again have to employ well-founded induction, since
  @{thm gb_schema_aux.pinduct} does not treat the first arguments of @{const gb_schema_aux} in the proper way.\<close>
lemma gb_schema_aux_induct [consumes 1, case_names base rec]:
  assumes "struct_spec sel ap ab compl"
  assumes base: "\<And>bs. P bs [] (gs @ bs)"
    and rec: "\<And>bs ps sps ns. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps \<Longrightarrow> ns = compl gs bs ps sps \<Longrightarrow>
                P (ab gs bs ns) (ap gs bs (ps - sps) ns) (gb_schema_aux sel ap ab compl gs (ab gs bs ns) (ap gs bs (ps - sps) ns)) \<Longrightarrow>
                P bs ps (gb_schema_aux sel ap ab compl gs (ab gs bs ns) (ap gs bs (ps - sps) ns))"
  shows "P bs ps (gb_schema_aux sel ap ab compl gs bs ps)"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3, rule struct_specD4)
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (op +) d" ..
  let ?R = "gb_schema_aux_term d"
  define args where "args = (gs, bs, ps)"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  hence "fst args = gs \<Longrightarrow> P (fst (snd args)) (snd (snd args))
              (gb_schema_aux sel ap ab compl gs (fst (snd args)) (snd (snd args)))"
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> gb_schema_aux_term d \<Longrightarrow> fst y = gs \<Longrightarrow>
                   P (fst (snd y)) (snd (snd y)) (gb_schema_aux sel ap ab compl gs (fst (snd y)) (snd (snd y)))"
    assume "fst x = gs"
    then obtain bs0 where x: "x = (gs, bs0)" by (meson eq_fst_iff)
    obtain bs ps where bs0: "bs0 = (bs, ps)" by (meson case_prodE case_prodI2)
    from IH' have IH: "\<And>bs' ps'. ((gs, bs', ps'), (gs, bs, ps)) \<in> gb_schema_aux_term d \<Longrightarrow>
                   P bs' ps' (gb_schema_aux sel ap ab compl gs bs' ps')" unfolding x bs0 by auto
    show "P (fst (snd x)) (snd (snd x))
              (gb_schema_aux sel ap ab compl gs (fst (snd x)) (snd (snd x)))"
    proof (simp add: x bs0, cases "ps = []")
      case True
      from base show "P bs ps (gb_schema_aux sel ap ab compl gs bs ps)" by (simp add: True)
    next
      case False
      show "P bs ps (gb_schema_aux sel ap ab compl gs bs ps)"
      proof (simp add: gb_schema_aux_not_empty[OF assms(1) False] Let_def)
        define sps where "sps = sel gs bs ps"
        from sel False have sub: "set sps \<subseteq> set ps" unfolding sps_def by (rule sel_specD2)
        define ns where "ns = compl gs bs ps sps"
        from False sps_def ns_def show "P bs ps (gb_schema_aux sel ap ab compl gs (ab gs bs ns) (ap gs bs (ps - sps) ns))"
        proof (rule rec)
          show "P (ab gs bs ns) (ap gs bs (ps - sps) ns)
                    (gb_schema_aux sel ap ab compl gs (ab gs bs ns) (ap gs bs (ps - sps) ns))"
          proof (rule IH, simp add: x bs0 gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, rule)
            show "fst ` set (ab gs bs ns) \<sqsupset>p fst ` set bs \<or>
                      ab gs bs ns = bs \<and> card (set (ap gs bs (ps - sps) ns)) < card (set ps)"
            proof (cases "ns = []")
              case True
              have "ab gs bs ns = bs \<and> card (set (ap gs bs (ps - sps) ns)) < card (set ps)"
              proof (simp only: True ap_spec_empty_new[OF ap], rule)
                from ab show "ab gs bs [] = bs" by (rule ab_specD2)
              next
                from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
                with sub have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
                hence "set (ps - sps) \<subset> set ps" unfolding set_minus_list by fastforce
                thus "card (set (ps - sps)) < card (set ps)" by (simp add: psubset_card_mono)
              qed
              thus ?thesis ..
            next
              case False
              with ab compl sub ns_def have "fst ` set (ab gs bs ns) \<sqsupset>p fst ` set bs" by (rule red_supset_ab)
              thus ?thesis ..
            qed
          next
            from dg assms(1) False sps_def ns_def
            show "dgrad_p_set_le d (args_to_set (gs, ab gs bs ns, ap gs bs (ps - sps) ns)) (args_to_set (gs, bs, ps))"
              by (rule dgrad_p_set_le_args_to_set_struct)
          qed
        qed
      qed
    qed
  qed
  thus ?thesis by (simp add: args_def)
qed

lemma gb_schema_aux_subset:
  assumes "struct_spec sel ap ab compl"
  shows "set (gs @ bs) \<subseteq> set (gb_schema_aux sel ap ab compl gs bs ps)"
  using assms
proof (induct rule: gb_schema_aux_induct)
  case (base bs)
  show ?case ..
next
  case (rec bs ps sps ns)
  from assms have "ab_spec ab" by (rule struct_specD3)
  hence "set (ab gs bs ns) = set bs \<union> set ns" by (rule ab_specD1)
  hence "set (gs @ bs) \<subseteq> set (gs @ ab gs bs ns)" by auto
  from this rec(4) show ?case by (rule subset_trans)
qed

lemma gb_schema_aux_dgrad_p_set_le:
  assumes "dickson_grading (op +) d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_aux sel ap ab compl gs bs ps)) (args_to_set (gs, bs, ps))"
  using assms(2)
proof (induct rule: gb_schema_aux_induct)
  case (base bs)
  thus ?case by (simp add: args_to_set_def, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (rec bs ps sps ns)
  from assms rec(1, 2, 3)
  have "dgrad_p_set_le d (args_to_set (gs, ab gs bs ns, ap gs bs (ps - sps) ns)) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_args_to_set_struct)
  with rec(4) show ?case by (rule dgrad_p_set_le_trans)
qed

lemma gb_schema_aux_pideal:
  assumes "struct_spec sel ap ab compl" and "compl_pideal compl" and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)"
  shows "pideal (fst ` set (gb_schema_aux sel ap ab compl gs bs ps)) = pideal (fst ` set (gs @ bs))"
    (is "?l = ?r")
proof
  from assms(1, 3) show "?l \<subseteq> ?r"
  proof (induction bs ps rule: gb_schema_aux_induct)
    case (base bs)
    show ?case ..
  next
    case (rec bs ps sps ns)
    from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
      by (rule struct_specD1, rule struct_specD2, rule struct_specD3)
    have "pideal (fst ` set (gb_schema_aux sel ap ab compl gs (ab gs bs ns) (ap gs bs (ps - sps) ns))) \<subseteq>
          pideal (fst ` set (gs @ ab gs bs ns))"
    proof (rule rec(4))
      from ap ab rec(5) show "set (ap gs bs (ps - sps) ns) \<subseteq> set (ab gs bs ns) \<times> (set gs \<union> set (ab gs bs ns))"
        by (rule subset_Times_ap)
    qed
    also have "... \<subseteq> pideal (fst ` set (gs @ bs))"
    proof (rule pideal_subset_pidealI, simp add: ab_specD1[OF ab] image_Un, intro conjI)
      have "fst ` set gs \<subseteq> pideal (fst ` set gs)" by (rule generator_subset_pideal)
      also have "... \<subseteq> pideal (fst ` set gs \<union> fst ` set bs)" by (rule pideal_mono, simp)
      finally show "fst ` set gs \<subseteq> pideal (fst ` set gs \<union> fst ` set bs)" .
    next
      have "fst ` set bs \<subseteq> pideal (fst ` set bs)" by (rule generator_subset_pideal)
      also have "... \<subseteq> pideal (fst ` set gs \<union> fst ` set bs)" by (rule pideal_mono, simp)
      finally show "fst ` set bs \<subseteq> pideal (fst ` set gs \<union> fst ` set bs)" .
    next
      from assms(2) rec(1) have "fst ` set ns \<subseteq> pideal (args_to_set (gs, bs, ps))" unfolding rec(3)
      proof (rule compl_pidealD)
        from sel rec(1) show "set sps \<subseteq> set ps" unfolding rec(2) by (rule sel_specD2)
      qed
      thus "fst ` set ns \<subseteq> pideal (fst ` set gs \<union> fst ` set bs)"
        by (simp only: args_to_set_subset_Times[OF rec(5)])
    qed
    finally show ?case .
  qed
next
  show "?r \<subseteq> ?l" by (rule pideal_mono, rule image_mono, rule gb_schema_aux_subset, fact assms(1))
qed

lemma gb_schema_aux_connectible:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "dickson_grading (op +) d"
    and "fst ` set gs \<subseteq> dgrad_p_set d m" and "is_Groebner_basis (fst ` set gs)"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)"
    and "\<And>p q. processed' (p, q) gs bs ps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)"
  assumes "f \<in> set (gb_schema_aux sel ap ab compl gs bs ps)" and "g \<in> set (gb_schema_aux sel ap ab compl gs bs ps)"
    and "fst f \<noteq> 0" and "fst g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` set (gb_schema_aux sel ap ab compl gs bs ps)) (fst f) (fst g)"
  using assms(1, 6, 7, 8, 9, 10)
proof (induct rule: gb_schema_aux_induct)
  case (base bs)
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
        using assms(11, 12) by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
      moreover have "fst ` set gs \<subseteq> fst ` set (gs @ bs)" by auto
      ultimately show ?thesis by (rule crit_pair_cbelow_mono)
    next
      case False
      from this base(4, 5) have "processed' (g, f) gs bs []" by (simp add: processed'_Nil)
      from this \<open>fst g \<noteq> 0\<close> \<open>fst f \<noteq> 0\<close> have "crit_pair_cbelow_on d m (fst ` set (gs @ bs)) (fst g) (fst f)"
        unfolding set_append by (rule base(3))
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
  next
    case False
    from this base(4, 5) have "processed' (f, g) gs bs []" by (simp add: processed'_Nil)
    from this \<open>fst f \<noteq> 0\<close> \<open>fst g \<noteq> 0\<close> show ?thesis unfolding set_append by (rule base(3))
  qed
next
  case (rec bs ps sps ns)
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3, rule struct_specD4)
  from sel rec(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding rec(2)
    by (rule sel_specD1, rule sel_specD2)
  from this(2) rec(6) have "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)" by (rule subset_trans)
  from ap ab rec(6) have ap_sub: "set (ap gs bs (ps - sps) ns) \<subseteq> set (ab gs bs ns) \<times> (set gs \<union> set (ab gs bs ns))"
    by (rule subset_Times_ap)
  have ns_sub: "fst ` set ns \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from compl assms(3) \<open>set sps \<subseteq> set ps\<close> show "dgrad_p_set_le d (fst ` set ns) (args_to_set (gs, bs, ps))"
      unfolding rec(3) by (rule compl_structD1)
  next
    from assms(4) rec(5) show "args_to_set (gs, bs, ps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF rec(6)])
  qed
  with rec(5) have ab_sub: "fst ` set (ab gs bs ns) \<subseteq> dgrad_p_set d m"
    by (auto simp add: ab_specD1[OF ab])

  have cpq: "(p, q) \<in> set sps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs ns))) (fst p) (fst q)" for p q
  proof -
    assume "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    with assms(2, 3, 4, 5) rec(5, 6) \<open>set sps \<subseteq> set ps\<close> _
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs ns))) (fst p) (fst q)"
      unfolding ab_specD1[OF ab] rec(3)
    proof (rule compl_connD)
      fix p' q'
      assume "processed' (p', q') gs bs ps" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')" by (rule rec(7))
    qed
  qed

  from ab_sub ap_sub _ rec(8, 9) show ?case
  proof (rule rec(4))
    fix p q :: "('a, 'b, 'c) pdata"
    assume "fst p \<noteq> 0" and "fst q \<noteq> 0"
    assume proc: "processed' (p, q) gs (ab gs bs ns) (ap gs bs (ps - sps) ns)"
    with ap ab show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs ns))) (fst p) (fst q)"
    proof (rule processed'_apE)
      assume "processed' (p, q) gs bs (ps - sps)"
      thus ?thesis
      proof (rule processed'_minus)
        assume "(p, q) \<in> set sps"
        from this \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> show ?thesis by (rule cpq)
      next
        assume "(q, p) \<in> set sps"
        from this \<open>fst q \<noteq> 0\<close> \<open>fst p \<noteq> 0\<close>
        have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs ns))) (fst q) (fst p)"
          by (rule cpq)
        thus ?thesis by (rule crit_pair_cbelow_sym)
      next
        assume "processed' (p, q) gs bs ps"
        from this \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
        have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)" by (rule rec(7))
        moreover have "fst ` (set gs \<union> set bs) \<subseteq> fst ` (set gs \<union> set (ab gs bs ns))"
          by (auto simp add: ab_specD1[OF ab])
        ultimately show ?thesis by (rule crit_pair_cbelow_mono)
      qed
    next
      assume "p \<in> set ns" and "q \<in> set ns"
      show ?thesis
      proof (cases "p = q")
        case True
        from \<open>q \<in> set ns\<close> have "fst q \<in> fst ` set ns" by simp
        from this ns_sub have "fst q \<in> dgrad_p_set d m" ..
        with assms(3) show ?thesis unfolding True by (rule crit_pair_cbelow_same)
      next
        case False
        with ap \<open>p \<in> set ns\<close> \<open>q \<in> set ns\<close>
        have "\<not> processed' (p, q) gs (ab gs bs ns) (ap gs bs (ps - sps) ns)"
        proof (rule ap_specE)
          assume "(p, q) \<in> set (ap gs bs (ps - sps) ns)"
          thus ?thesis by (simp add: processed'_def)
        next
          assume "(q, p) \<in> set (ap gs bs (ps - sps) ns)"
          thus ?thesis by (simp add: processed'_def)
        qed
        from this proc show ?thesis ..
      qed
    qed
  qed
qed

subsubsection \<open>Functions @{term gb_schema_direct} and @{term gb_schema_incr}\<close>

definition gb_schema_direct :: "('a, 'b, 'c) selT \<Rightarrow> ('a, 'b, 'c) apT \<Rightarrow> ('a, 'b, 'c) abT \<Rightarrow>
                                ('a, 'b, 'c) complT \<Rightarrow> ('a, 'b::field, 'c) pdata list \<Rightarrow>
                                ('a, 'b, 'c) pdata list"
  where "gb_schema_direct sel ap ab compl bs = gb_schema_aux sel ap ab compl [] bs (ap [] [] [] bs)"

fun gb_schema_incr :: "('a, 'b, 'c) selT \<Rightarrow> ('a, 'b, 'c) apT \<Rightarrow> ('a, 'b, 'c) abT \<Rightarrow>
                                ('a, 'b, 'c) complT \<Rightarrow> ('a, 'b::field, 'c) pdata list \<Rightarrow>
                                ('a, 'b, 'c) pdata list"
  where
    "gb_schema_incr _ _ _ _ [] = []"|
    "gb_schema_incr _ _ _ _ [b] = [b]"|
    "gb_schema_incr sel ap ab compl (b # bs) =
      (let gs = gb_schema_incr sel ap ab compl bs in
        gb_schema_aux sel ap ab compl gs [b] (ap gs [] [] [b])
      )"

lemma gb_schema_direct_dgrad_p_set_le:
  assumes "dickson_grading (op +) d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_direct sel ap ab compl bs)) (fst ` set bs)"
proof -
  from assms(2) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD2, rule struct_specD3)
  from ap_specD1[OF ap, of "[]" "[]" "[]" bs] have *: "set (ap [] [] [] bs) \<subseteq> set bs \<times> set bs" by simp
  from assms have "dgrad_p_set_le d (fst ` set (gb_schema_aux sel ap ab compl [] bs (ap [] [] [] bs)))
                                    (args_to_set ([], bs, (ap [] [] [] bs)))"
    by (rule gb_schema_aux_dgrad_p_set_le)
  also from * have "... = fst ` set bs" by (auto simp add: args_to_set_alt)
  finally show ?thesis unfolding gb_schema_direct_def .
qed

corollary gb_schema_direct_dgrad_p_set:
  assumes "dickson_grading (op +) d" and "struct_spec sel ap ab compl" and "fst ` set bs \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_direct sel ap ab compl bs) \<subseteq> dgrad_p_set d m"
  by (rule dgrad_p_set_le_dgrad_p_set, rule gb_schema_direct_dgrad_p_set_le, fact+)

theorem gb_schema_direct_isGB:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl"
  shows "is_Groebner_basis (fst ` set (gb_schema_direct sel ap ab compl bs))"
proof -
  from assms(1) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD2, rule struct_specD3)
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (op +) d" ..
  obtain m where "fst ` set bs \<subseteq> dgrad_p_set d m"
    by (rule dgrad_p_set_exhaust, rule finite_imageI, rule finite_set)
  with dg assms(1) have "fst ` set (gb_schema_direct sel ap ab compl bs) \<subseteq> dgrad_p_set d m"
    by (rule gb_schema_direct_dgrad_p_set)
  with dg show ?thesis
  proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
    fix p0 q0
    assume p0_in: "p0 \<in> fst ` set (gb_schema_direct sel ap ab compl bs)"
      and q0_in: "q0 \<in> fst ` set (gb_schema_direct sel ap ab compl bs)"
    assume "p0 \<noteq> 0" and "q0 \<noteq> 0"
    from p0_in obtain p where p_in: "p \<in> set (gb_schema_direct sel ap ab compl bs)" and p0: "p0 = fst p" ..
    from q0_in obtain q where q_in: "q \<in> set (gb_schema_direct sel ap ab compl bs)" and q0: "q0 = fst q" ..
    from assms dg _ _ \<open>fst ` set bs \<subseteq> dgrad_p_set d m\<close> _ _ p_in q_in \<open>p0 \<noteq> 0\<close> \<open>q0 \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` set (gb_schema_direct sel ap ab compl bs)) p0 q0"
      unfolding gb_schema_direct_def p0 q0
    proof (rule gb_schema_aux_connectible)
      show "fst ` set [] \<subseteq> dgrad_p_set d m" by simp
    next
      from is_Groebner_basis_empty show "is_Groebner_basis (fst ` set [])" by simp
    next
      from ap_specD1[OF ap, of "[]" "[]" "[]" bs] show "set (ap [] [] [] bs) \<subseteq> set bs \<times> (set [] \<union> set bs)"
        by simp
    next
      fix p' q'
      assume proc: "processed' (p', q') [] bs (ap [] [] [] bs)"
      hence "p' \<in> set bs" and "q' \<in> set bs" by (rule processed'D1, auto dest: processed'D2)
      show "crit_pair_cbelow_on d m (fst ` (set [] \<union> set bs)) (fst p') (fst q')"
      proof (cases "p' = q'")
        case True
        from dg show ?thesis unfolding True
        proof (rule crit_pair_cbelow_same)
          from \<open>q' \<in> set bs\<close> have "fst q' \<in> fst ` set bs" by simp
          from this \<open>fst ` set bs \<subseteq> dgrad_p_set d m\<close> show "fst q' \<in> dgrad_p_set d m" ..
        qed
      next
        case False
        with ap \<open>p' \<in> set bs\<close> \<open>q' \<in> set bs\<close> have "\<not> processed' (p', q') [] bs (ap [] [] [] bs)"
        proof (rule ap_specE)
          assume "(p', q') \<in> set (ap [] [] [] bs)"
          thus ?thesis by (simp add: processed'_alt)
        next
          assume "(q', p') \<in> set (ap [] [] [] bs)"
          thus ?thesis by (simp add: processed'_alt)
        qed
        from this proc show ?thesis ..
      qed
    qed
  qed
qed

theorem gb_schema_direct_pideal:
  assumes "struct_spec sel ap ab compl" and "compl_pideal compl"
  shows "pideal (fst ` set (gb_schema_direct sel ap ab compl bs)) = pideal (fst ` set bs)"
proof -
  have "pideal (fst ` set (gb_schema_direct sel ap ab compl bs)) = pideal (fst ` set ([] @ bs))"
    unfolding gb_schema_direct_def using assms
  proof (rule gb_schema_aux_pideal)
    from assms(1) have "ap_spec ap" by (rule struct_specD2)
    from ap_specD1[OF this, of "[]" "[]" "[]" bs] show "set (ap [] [] [] bs) \<subseteq> set bs \<times> (set [] \<union> set bs)"
      by simp
  qed
  thus ?thesis by simp
qed

subsection \<open>Suitable Instances of the @{emph \<open>completion\<close>} Parameter\<close>

subsubsection \<open>Specification of the @{emph \<open>crit\<close>} parameter\<close>

type_synonym (in -) ('a, 'b, 'c) critT' = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                          ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow>
                                          ('a, 'b, 'c) pdata \<Rightarrow> bool"

definition crit_spec :: "('a, 'b::field, 'c) critT' \<Rightarrow> bool"
  where "crit_spec crit \<longleftrightarrow> (\<forall>d m gs bs ps F p q. dickson_grading (op +) d \<longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<longrightarrow>
                                is_Groebner_basis (fst ` set gs) \<longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
                                F \<subseteq> dgrad_p_set d m \<longrightarrow> set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
                                (\<forall>p' q'. processed' (p', q') gs bs ((p, q) # ps) \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                                    crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')) \<longrightarrow>
                                p \<in> set bs \<longrightarrow> q \<in> set gs \<union> set bs \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow> crit gs bs ps p q \<longrightarrow>
                                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q))"

lemma crit_specI:
  assumes "\<And>d m gs bs ps F p q. dickson_grading (op +) d \<Longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<Longrightarrow>
              is_Groebner_basis (fst ` set gs) \<Longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<Longrightarrow>
              F \<subseteq> dgrad_p_set d m \<Longrightarrow> set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow>
              (\<And>p' q'. processed' (p', q') gs bs ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')) \<Longrightarrow>
              p \<in> set bs \<Longrightarrow> q \<in> set gs \<union> set bs \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow> crit gs bs ps p q \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  shows "crit_spec crit"
  unfolding crit_spec_def using assms by meson

lemma crit_specD:
  assumes "crit_spec crit" and "dickson_grading (op +) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "\<And>p' q'. processed' (p', q') gs bs ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                 crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "p \<in> set bs" and "q \<in> set gs \<union> set bs" and "fst p \<noteq> 0" and "fst q \<noteq> 0" and "crit gs bs ps p q"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  using assms unfolding crit_spec_def by blast

subsubsection \<open>Function @{term discard_crit_pairs}\<close>

(* TODO: Apply "compl" to "ps - sps". *)
primrec discard_crit_pairs_dummy :: "('a, 'b, 'c) critT' \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                      ((('a, 'b, 'c) pdata_pair list) \<times> (('a, 'b, 'c) pdata_pair list))"
  where
    "discard_crit_pairs_dummy _ _ _ _ [] ks ds = (ks, ds)"|
    "discard_crit_pairs_dummy crit gs bs ps (p # sps) ks ds =
      (if crit gs bs (sps @ ps) (fst p) (snd p) then
        discard_crit_pairs_dummy crit gs bs ps sps ks (p # ds)
      else
        discard_crit_pairs_dummy crit gs bs ps sps (p # ks) ds
      )"

text \<open>The last argument of @{const discard_crit_pairs_dummy} is a ``dummy'' argument that is only
  needed for proving properties of the function, but that does not contribute to the final result
  we are interested in.\<close>

lemma set_discard_crit_pairs_dummy_partition:
  "set (fst (discard_crit_pairs_dummy crit gs bs ps sps ks ds)) \<union>
    set (snd (discard_crit_pairs_dummy crit gs bs ps sps ks ds)) =
  set sps \<union> set ks \<union> set ds"
  by (induct sps arbitrary: ks ds, simp_all)

lemma fst_discard_crit_pairs_dummy_subset:
  "set (fst (discard_crit_pairs_dummy crit gs bs ps sps ks ds)) \<subseteq> set sps \<union> set ks"
proof (induct sps arbitrary: ks ds)
  case Nil
  show ?case by simp
next
  case (Cons p sps)
  show ?case
  proof (simp, intro conjI impI)
    have "set (fst (discard_crit_pairs_dummy crit gs bs ps sps ks (p # ds))) \<subseteq> set sps \<union> set ks"
      by (rule Cons)
    also have "... \<subseteq> insert p (set sps \<union> set ks)" by blast
    finally show "set (fst (discard_crit_pairs_dummy crit gs bs ps sps ks (p # ds))) \<subseteq>
                    insert p (set sps \<union> set ks)" .
  next
    have "set (fst (discard_crit_pairs_dummy crit gs bs ps sps (p # ks) ds)) \<subseteq> set sps \<union> set (p # ks)"
      by (rule Cons)
    thus "set (fst (discard_crit_pairs_dummy crit gs bs ps sps (p # ks) ds)) \<subseteq>
            insert p (set sps \<union> set ks)" by simp
  qed
qed

lemma fst_discard_crit_pairs_dummy_sublist:
  obtains ks' where "fst (discard_crit_pairs_dummy crit gs bs ps sps ks ds) = ks' @ ks"
proof (induct sps arbitrary: thesis ks ds)
  case Nil
  show ?case
  proof (rule Nil)
    show "fst (discard_crit_pairs_dummy crit gs bs ps [] ks ds) = [] @ ks" by simp
  qed
next
  case (Cons p sps)
  show ?case
  proof (cases "crit gs bs (sps @ ps) (fst p) (snd p)")
    case True
    obtain ks' where *: "fst (discard_crit_pairs_dummy crit gs bs ps sps ks (p # ds)) = ks' @ ks"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from True * show "fst (discard_crit_pairs_dummy crit gs bs ps (p # sps) ks ds) = ks' @ ks"
        by simp
    qed
  next
    case False
    obtain ks' where *: "fst (discard_crit_pairs_dummy crit gs bs ps sps (p # ks) ds) = ks' @ (p # ks)"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from False * show "fst (discard_crit_pairs_dummy crit gs bs ps (p # sps) ks ds) = (ks' @ [p]) @ ks"
        by simp
    qed
  qed
qed

lemma snd_discard_crit_pairs_dummy_sublist:
  obtains ds' where "snd (discard_crit_pairs_dummy crit gs bs ps sps ks ds) = ds' @ ds"
proof (induct sps arbitrary: thesis ks ds)
  case Nil
  show ?case
  proof (rule Nil)
    show "snd (discard_crit_pairs_dummy crit gs bs ps [] ks ds) = [] @ ds" by simp
  qed
next
  case (Cons p sps)
  show ?case
  proof (cases "crit gs bs (sps @ ps) (fst p) (snd p)")
    case True
    obtain ds' where *: "snd (discard_crit_pairs_dummy crit gs bs ps sps ks (p # ds)) = ds' @ (p # ds)"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from True * show "snd (discard_crit_pairs_dummy crit gs bs ps (p # sps) ks ds) = (ds' @ [p]) @ ds"
        by simp
    qed
  next
    case False
    obtain ds' where *: "snd (discard_crit_pairs_dummy crit gs bs ps sps (p # ks) ds) = ds' @ ds"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from False * show "snd (discard_crit_pairs_dummy crit gs bs ps (p # sps) ks ds) = ds' @ ds"
        by simp
    qed
  qed
qed

lemma discard_crit_pairs_dummy_connectible:
  assumes "crit_spec crit" and "dickson_grading (op +) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "\<And>p' q'. processed' (p', q') gs bs (sps @ ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set ds \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps ks ds)) \<Longrightarrow>
            fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
  assumes "(p, q) \<in> set (snd (discard_crit_pairs_dummy crit gs bs ps sps ks ds))"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  using assms(8, 9, 10, 11, 12)
proof (induct sps arbitrary: ks ds)
  case Nil
  from Nil(5) have "(p, q) \<in> set ds" by simp
  from this assms(13, 14) show ?case by (rule Nil(3))
next
  case (Cons s sps)
  from Cons(2) have "s \<in> set bs \<times> (set gs \<union> set bs)" and sps_sub: "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    by simp_all
  from this(1) have "fst s \<in> set bs" and "snd s \<in> set gs \<union> set bs" by auto
  let ?res = "discard_crit_pairs_dummy crit gs bs ps (s # sps) ks ds"

  have *: "fst (fst s) \<noteq> 0 \<Longrightarrow> fst (snd s) \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
  proof -
    assume "fst (fst s) \<noteq> 0" and "fst (snd s) \<noteq> 0"
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
    proof (cases "crit gs bs (sps @ ps) (fst s) (snd s)")
      case True
      with assms(1, 2, 3, 4, 5, 6) _ _ \<open>fst s \<in> set bs\<close> \<open>snd s \<in> set gs \<union> set bs\<close>
          \<open>fst (fst s) \<noteq> 0\<close> \<open>fst (snd s) \<noteq> 0\<close>
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
      proof (rule crit_specD)
        from sps_sub assms(7) show "set (sps @ ps) \<subseteq> set bs \<times> (set gs \<union> set bs)" by auto
      next
        fix p' q'
        assume "processed' (p', q') gs bs ((fst s, snd s) # sps @ ps)"
        hence "processed' (p', q') gs bs ((s # sps) @ ps)" by simp
        moreover assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
        ultimately show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
          by (rule Cons(3))
      qed
      thus ?thesis by simp
    next
      case False
      show ?thesis
      proof (rule Cons(5), simp add: False)
        obtain ks' where "fst (discard_crit_pairs_dummy crit gs bs ps sps (s # ks) ds) = ks' @ (s # ks)"
          by (rule fst_discard_crit_pairs_dummy_sublist)
        thus "s \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps (s # ks) ds))" by simp
      qed fact+
    qed
  qed

  have **: "processed' (p', q') gs bs (sps @ ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" for p' q'
  proof -
    assume proc: "processed' (p', q') gs bs (sps @ ps)"
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
          from proc have "processed' (p', q') gs bs (s # (sps @ ps))"
          proof (rule processed'_Cons)
            assume "p' = fst s" and "q' = snd s"
            hence "s = (p', q')" by simp
            with \<open>s \<noteq> (p', q')\<close> show ?thesis ..
          next
            assume "p' = snd s" and "q' = fst s"
            hence "s = (q', p')" by simp
            with \<open>s \<noteq> (q', p')\<close> show ?thesis ..
          qed simp
          thus "processed' (p', q') gs bs ((s # sps) @ ps)" by simp
        qed
      qed
    qed
  qed

  from Cons(6) show ?case
  proof (simp split: if_splits)
    let ?a = "discard_crit_pairs_dummy crit gs bs ps sps ks (s # ds)"
    assume crit: "crit gs bs (sps @ ps) (fst s) (snd s)"
    hence "?res = ?a" by simp
    assume "(p, q) \<in> set (snd ?a)"
    with sps_sub _ _ _ show ?thesis
    proof (rule Cons(1))
      fix p' q'
      assume "processed' (p', q') gs bs (sps @ ps)" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
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
      assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps ks (s # ds)))"
        and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
        by (rule Cons(5), simp only: \<open>?res = ?a\<close>, fact+)
    qed
  next
    let ?a = "discard_crit_pairs_dummy crit gs bs ps sps (s # ks) ds"
    assume "\<not> crit gs bs (sps @ ps) (fst s) (snd s)"
    hence "?res = ?a" by simp
    assume "(p, q) \<in> set (snd ?a)"
    with sps_sub _ _ _ show ?thesis
    proof (rule Cons(1))
      fix p' q'
      assume "processed' (p', q') gs bs (sps @ ps)" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule **)
    next
      fix p' q'
      assume "(p', q') \<in> set ds" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule Cons(4))
    next
      fix p' q'
      assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps (s # ks) ds))"
        and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
        by (rule Cons(5), simp only: \<open>?res = ?a\<close>, fact+)
    qed
  qed
qed

primrec discard_crit_pairs_aux :: "('a, 'b, 'c) critT' \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list"
  where
    "discard_crit_pairs_aux _ _ _ _ [] ks = ks"|
    "discard_crit_pairs_aux crit gs bs ps (p # sps) ks =
      (if crit gs bs (sps @ ps) (fst p) (snd p) then
        discard_crit_pairs_aux crit gs bs ps sps ks
      else
        discard_crit_pairs_aux crit gs bs ps sps (p # ks)
      )"

text \<open>Function @{const discard_crit_pairs_aux} is like @{const discard_crit_pairs_dummy}, but lacks
  the dummy argument. Therefore, it is the method of choice for doing actual computations.\<close>

lemma discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy':
  "discard_crit_pairs_aux crit gs bs ps sps ks = fst (discard_crit_pairs_dummy crit gs bs ps sps ks ds)"
  by (induct sps arbitrary: ks ds, simp_all)

lemmas discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy =
          discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy'[where ds="[]"]

definition discard_crit_pairs :: "('a, 'b, 'c) critT' \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list"
  where "discard_crit_pairs crit gs bs ps sps = discard_crit_pairs_aux crit gs bs ps sps []"

lemma discard_crit_pairs_alt:
  "discard_crit_pairs crit gs bs ps sps = fst (discard_crit_pairs_dummy crit gs bs ps sps [] [])"
  by (simp only: discard_crit_pairs_def discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy)

lemma set_discard_crit_pairs_partition:
  "set sps = set (discard_crit_pairs crit gs bs ps sps) \<union>
              set (snd (discard_crit_pairs_dummy crit gs bs ps sps [] []))"
  by (simp add: discard_crit_pairs_alt set_discard_crit_pairs_dummy_partition)

corollary discard_crit_pairs_subset: "set (discard_crit_pairs crit gs bs ps sps) \<subseteq> set sps"
  using set_discard_crit_pairs_partition by blast

lemma discard_crit_pairs_connectible:
  assumes "crit_spec crit" and "dickson_grading (op +) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "\<And>p' q'. processed' (p', q') gs bs (sps @ ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set (discard_crit_pairs crit gs bs ps sps) \<Longrightarrow>
            fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
  assumes "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
proof (cases "(p, q) \<in> set (discard_crit_pairs crit gs bs ps sps)")
  case True
  from this assms(12, 13) show ?thesis by (rule assms(10))
next
  case False
  with assms(11) have "(p, q) \<in> set (snd (discard_crit_pairs_dummy crit gs bs ps sps [] []))"
    using set_discard_crit_pairs_partition[of sps crit gs bs ps] by blast
  thm discard_crit_pairs_dummy_connectible
  from assms(1, 2, 3, 4, 5, 6, 7, 8) _ _ _ this assms(12, 13) show ?thesis
  proof (rule discard_crit_pairs_dummy_connectible)
    fix p' q'
    assume "processed' (p', q') gs bs (sps @ ps)" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule assms(9))
  next
    fix p' q' :: "('a, 'b, 'c) pdata"
    assume "(p', q') \<in> set []"
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by simp
  next
    fix p' q'
    assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps [] []))"
      and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
      unfolding discard_crit_pairs_alt[symmetric] by (rule assms(10))
  qed
qed

end (* gd_powerprod *)

end (* theory *)
