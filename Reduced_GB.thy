section \<open>Reduced Gr\"obner Bases\<close>

theory Reduced_GB
  imports Groebner_Bases.Groebner_Bases Auto_Reduction
begin

subsection \<open>Properties of Gr\"obner Bases\<close>

context gd_powerprod
begin

lemma monic_set_GB: "is_Groebner_basis (monic_set G) \<longleftrightarrow> is_Groebner_basis G"
  by (simp add: GB_alt_1)

end (* gd_powerprod *)
  
subsubsection \<open>Replacing Elements in Gr\"obner Bases\<close>

context ordered_powerprod
begin

lemma replace_lp_adds_stable_is_red:
  assumes red: "is_red F f" and "q \<noteq> 0" and "lp q adds lp p"
  shows "is_red (insert q (F - {p})) f"
proof -
  from red obtain g t where "g \<in> F" and "g \<noteq> 0" and "t \<in> keys f" and "lp g adds t" by (rule is_red_addsE)
  show ?thesis
  proof (cases "g = p")
    case True
    show ?thesis
    proof (rule is_red_addsI)
      show "q \<in> insert q (F - {p})" by simp
    next
      have "lp q adds lp p" by fact
      also have "... adds t" using \<open>lp g adds t\<close> unfolding True .
      finally show "lp q adds t" .
    qed (fact+)
  next
    case False
    with \<open>g \<in> F\<close> have "g \<in> insert q (F - {p})" by blast
    from this \<open>g \<noteq> 0\<close> \<open>t \<in> keys f\<close> \<open>lp g adds t\<close> show ?thesis by (rule is_red_addsI)
  qed
qed
  
lemma conversion_property:
  assumes "is_red {p} f" and "red {r} p q"
  shows "is_red {q} f \<or> is_red {r} f"
proof -
  from \<open>is_red {p} f\<close> obtain t where "t \<in> keys f" and "lp p adds t" and "p \<noteq> 0" by (rule is_red_addsE, simp)
  from red_indE[OF \<open>red {r} p q\<close>]
    have "(r \<noteq> 0 \<and> lp r adds lp p \<and> q = p - monom_mult (lc p / lc r) (lp p - lp r) r) \<or>
          red {r} (tail p) (q - monomial (lc p) (lp p))" by simp
  thus ?thesis
  proof
    assume "r \<noteq> 0 \<and> lp r adds lp p \<and> q = p - monom_mult (lc p / lc r) (lp p - lp r) r"
    hence "r \<noteq> 0" and "lp r adds lp p" by simp_all
    show ?thesis by (intro disjI2, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  next
    assume "red {r} (tail p) (q - monomial (lc p) (lp p))" (is "red _ ?p' ?q'")
    with red_ord have "?q' \<prec>p ?p'" .
    hence "?p' \<noteq> 0"
      and assm: "(?q' = 0 \<or> ((lp ?q') \<prec> (lp ?p') \<or> (lp ?q') = (lp ?p')))"
      unfolding ord_strict_p_rec[of ?q' ?p'] by (auto simp add: Let_def lc_def)
    have "lp ?p' \<prec> lp p" by (rule lp_tail, fact)
    let ?m = "monomial (lc p) (lp p)"
    from monomial_0D[of "lp p" "lc p"] lc_not_0[OF \<open>p \<noteq> 0\<close>] have "?m \<noteq> 0" by blast
    have "lp ?m = lp p" by (rule lp_monomial, rule lc_not_0, fact)
    have "q \<noteq> 0 \<and> lp q = lp p"
    proof (cases "?q' = 0")
      case True
      hence "q = ?m" by simp
      with \<open>?m \<noteq> 0\<close> \<open>lp ?m = lp p\<close> show ?thesis by simp
    next
      case False
      from assm show ?thesis
      proof
        assume "(lp ?q') \<prec> (lp ?p') \<or> (lp ?q') = (lp ?p')"
        hence "lp ?q' \<preceq> lp ?p'" by auto
        also have "... \<prec> lp p" by fact
        finally have "lp ?q' \<prec> lp p" .
        hence "lp ?q' \<prec> lp ?m" unfolding \<open>lp ?m = lp p\<close> .
        from lp_plus_eqI[OF this] \<open>lp ?m = lp p\<close> have "lp q = lp p" by simp
        show ?thesis
        proof (intro conjI, rule ccontr)
          assume "\<not> q \<noteq> 0"
          hence "q = 0" by simp
          hence "?q' = -?m" by simp
          hence "lp ?q' = lp (-?m)" by simp
          also have "... = lp ?m" using lp_uminus .
          finally have "lp ?q' = lp ?m" .
          with \<open>lp ?q' \<prec> lp ?m\<close> show False by simp
        qed (fact)
      next
        assume "?q' = 0"
        with False show ?thesis ..
      qed
    qed
    hence "q \<noteq> 0" and "lp q adds lp p" by simp_all
    show ?thesis by (intro disjI1, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  qed
qed
  
lemma replace_red_stable_is_red:
  assumes a1: "is_red F f" and a2: "red (F - {p}) p q"
  shows "is_red (insert q (F - {p})) f" (is "is_red ?F' f")
proof -
  from a1 obtain g where "g \<in> F" and "is_red {g} f" by (rule is_red_singletonI)
  show ?thesis
  proof (cases "g = p")
    case True
    from a2 obtain h where "h \<in> F - {p}" and "red {h} p q" unfolding red_def by auto
    from \<open>is_red {g} f\<close> have "is_red {p} f" unfolding True .
    have "is_red {q} f \<or> is_red {h} f" by (rule conversion_property, fact+)
    thus ?thesis
    proof
      assume "is_red {q} f"
      show ?thesis
      proof (rule is_red_singletonD)
        show "q \<in> ?F'" by auto
      qed fact
    next
      assume "is_red {h} f"
      show ?thesis
      proof (rule is_red_singletonD)
        from \<open>h \<in> F - {p}\<close> show "h \<in> ?F'" by simp
      qed fact
    qed
  next
    case False
    show ?thesis
    proof (rule is_red_singletonD)
      from \<open>g \<in> F\<close> False show "g \<in> ?F'" by blast
    qed fact
  qed
qed

lemma GB_remove_0_stable_GB:
  assumes "is_Groebner_basis G"
  shows "is_Groebner_basis (G - {0})"
  using assms by (simp only: is_Groebner_basis_def red_minus_singleton_zero)

end (* ordered_powerprod *)

context gd_powerprod
begin

lemma replace_in_dgrad_p_set:
  assumes "G \<subseteq> dgrad_p_set d m"
  obtains n where "q \<in> dgrad_p_set d n" and "G \<subseteq> dgrad_p_set d n"
    and "insert q (G - {p}) \<subseteq> dgrad_p_set d n"
proof -
  from assms obtain n where "m \<le> n" and 1: "q \<in> dgrad_p_set d n" and 2: "G \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  from this(2, 3) have "insert q (G - {p}) \<subseteq> dgrad_p_set d n" by auto
  with 1 2 show ?thesis ..
qed

lemma GB_replace_lp_adds_stable_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and q: "q \<in> (pideal G)" and "lp q adds lp p"
  shows "is_Groebner_basis (insert q (G - {p}))" (is "is_Groebner_basis ?G'")
proof -
  from assms(2) obtain n where 1: "G \<subseteq> dgrad_p_set d n" and 2: "?G' \<subseteq> dgrad_p_set d n"
    by (rule replace_in_dgrad_p_set)
  from isGB show ?thesis unfolding GB_alt_3_dgrad_p_set[OF assms(1) 1] GB_alt_3_dgrad_p_set[OF assms(1) 2]
  proof (intro ballI impI)
    fix f
    assume f1: "f \<in> (pideal ?G')" and "f \<noteq> 0"
      and a1: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)"
    from f1 replace_pideal[OF q, of p] have "f \<in> pideal G" ..
    from a1[rule_format, OF this \<open>f \<noteq> 0\<close>] obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by auto
    show "\<exists>g\<in>?G'. g \<noteq> 0 \<and> lp g adds lp f"
    proof (cases "g = p")
      case True
      show ?thesis
      proof
        from \<open>lp q adds lp p\<close> have "lp q adds lp g" unfolding True .
        also have "... adds lp f" by fact
        finally have "lp q adds lp f" .
        with \<open>q \<noteq> 0\<close> show "q \<noteq> 0 \<and> lp q adds lp f" ..
      next
        show "q \<in> ?G'" by simp
      qed
    next
      case False
      show ?thesis
      proof
        show "g \<noteq> 0 \<and> lp g adds lp f" by (rule, fact+)
      next
        from \<open>g \<in> G\<close> False show "g \<in> ?G'" by blast
      qed
    qed
  qed
qed
  
lemma GB_replace_lp_adds_stable_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and "q \<in> pideal G" and "lp q adds lp p"
  shows "pideal (insert q (G - {p})) = pideal G" (is "pideal ?G' = pideal G")
proof (rule, rule replace_pideal, fact, rule)
  fix f
  assume "f \<in> pideal G"
  note assms(1)
  moreover from assms(2) obtain n where "?G' \<subseteq> dgrad_p_set d n" by (rule replace_in_dgrad_p_set)
  moreover have "is_Groebner_basis ?G'" by (rule GB_replace_lp_adds_stable_GB_dgrad_p_set, fact+)
  ultimately have "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf_dgrad_p_set)
  then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
  have "\<not> is_red G h"
  proof
    assume "is_red G h"
    have "is_red ?G' h" by (rule replace_lp_adds_stable_is_red, fact+)
    with irredh show False ..
  qed
  have "f - h \<in> pideal ?G'" by (rule red_rtranclp_diff_in_pideal, rule ftoh)
  have "f - h \<in> pideal G" by (rule, fact, rule replace_pideal, fact)
  from pideal_closed_minus[OF this \<open>f \<in> pideal G\<close>] have "-h \<in> pideal G" by simp
  from pideal_closed_uminus[OF this] have "h \<in> pideal G" by simp
  with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_imp_reducibility by auto
  with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
  thus "f \<in> pideal ?G'" by (simp add: red_rtranclp_0_in_pideal)
qed
  
lemma GB_replace_red_stable_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and q: "red (G - {p}) p q"
  shows "is_Groebner_basis (insert q (G - {p}))" (is "is_Groebner_basis ?G'")
proof -
  from assms(2) obtain n where 1: "G \<subseteq> dgrad_p_set d n" and 2: "?G' \<subseteq> dgrad_p_set d n"
    by (rule replace_in_dgrad_p_set)
  from isGB show ?thesis unfolding GB_alt_2_dgrad_p_set[OF assms(1) 1] GB_alt_2_dgrad_p_set[OF assms(1) 2]
  proof (intro ballI impI)
    fix f
    assume f1: "f \<in> (pideal ?G')" and "f \<noteq> 0"
      and a1: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> is_red G f"
    have "q \<in> pideal G"
    proof (rule pideal_closed_red, rule pideal_mono)
      from generator_subset_pideal \<open>p \<in> G\<close> show "p \<in> pideal G" ..
    next
      show "G - {p} \<subseteq> G" by (rule Diff_subset)
    qed (rule q)
    from f1 replace_pideal[OF this, of p] have "f \<in> pideal G" ..
    have "is_red G f" by (rule a1[rule_format], fact+)
    show "is_red ?G' f" by (rule replace_red_stable_is_red, fact+)
  qed
qed

lemma GB_replace_red_stable_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "red (G - {p}) p q"
  shows "pideal (insert q (G - {p})) = pideal G" (is "pideal ?G' = _")
proof -
  from \<open>p \<in> G\<close> generator_subset_pideal have "p \<in> pideal G" ..
  have "q \<in> pideal G"
    by (rule pideal_closed_red, rule pideal_mono, rule Diff_subset, rule \<open>p \<in> pideal G\<close>, rule ptoq)
  show ?thesis
  proof (rule, rule replace_pideal, fact, rule)
    fix f
    assume "f \<in> pideal G"
    note assms(1)
    moreover from assms(2) obtain n where "?G' \<subseteq> dgrad_p_set d n" by (rule replace_in_dgrad_p_set)
    moreover have "is_Groebner_basis ?G'" by (rule GB_replace_red_stable_GB_dgrad_p_set, fact+)
    ultimately have "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf_dgrad_p_set)
    then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
    have "\<not> is_red G h"
    proof
      assume "is_red G h"
      have "is_red ?G' h" by (rule replace_red_stable_is_red, fact+)
      with irredh show False ..
    qed
    have "f - h \<in> pideal ?G'" by (rule red_rtranclp_diff_in_pideal, rule ftoh)
    have "f - h \<in> pideal G" by (rule, fact, rule replace_pideal, fact)
    from pideal_closed_minus[OF this \<open>f \<in> pideal G\<close>] have "-h \<in> pideal G" by simp
    from pideal_closed_uminus[OF this] have "h \<in> pideal G" by simp
    with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_imp_reducibility by auto
    with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
    thus "f \<in> pideal ?G'" by (simp add: red_rtranclp_0_in_pideal)
  qed
qed
  
lemma GB_replace_red_rtranclp_stable_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (G - {p}))\<^sup>*\<^sup>* p q"
  shows "is_Groebner_basis (insert q (G - {p}))"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from isGB \<open>p \<in> G\<close> show ?case by (simp add: insert_absorb)
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    from assms(1) assms(2) isGB \<open>p \<in> G\<close> show ?thesis
    proof (rule GB_replace_red_stable_GB_dgrad_p_set)
      from \<open>red (G - {p}) y z\<close> show "red (G - {p}) p z" unfolding True .
    qed
  next
    case False
    show ?thesis
      proof (cases "y \<in> G")
        case True
        with \<open>y \<noteq> p\<close> have "y \<in> G - {p}" (is "_ \<in> ?G'") by blast
        hence "insert y (G - {p}) = ?G'" by auto
        with step(3) have "is_Groebner_basis ?G'" by simp
        from \<open>y \<in> ?G'\<close> generator_subset_pideal have "y \<in> pideal ?G'" ..
        have "z \<in> pideal ?G'" by (rule pideal_closed_red, rule subset_refl, fact+)
        show "is_Groebner_basis (insert z ?G')" by (rule GB_insert, fact+)
      next
        case False
        from assms(2) obtain n where "insert y (G - {p}) \<subseteq> dgrad_p_set d n"
            by (rule replace_in_dgrad_p_set)
        from assms(1) this step(3) have "is_Groebner_basis (insert z (insert y (G - {p}) - {y}))"
        proof (rule GB_replace_red_stable_GB_dgrad_p_set)
          from \<open>red (G - {p}) y z\<close> False show "red ((insert y (G - {p})) - {y}) y z" by simp
        qed simp
        moreover from False have "... = (insert z (G - {p}))" by simp
        ultimately show ?thesis by simp
      qed
  qed
qed

lemma GB_replace_red_rtranclp_stable_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (G - {p}))\<^sup>*\<^sup>* p q"
  shows "pideal (insert q (G - {p})) = pideal G"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from \<open>p \<in> G\<close> show ?case by (simp add: insert_absorb)
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    from assms(1) assms(2) isGB \<open>p \<in> G\<close> step(2) show ?thesis unfolding True
      by (rule GB_replace_red_stable_pideal_dgrad_p_set)
  next
    case False
    have gb: "is_Groebner_basis (insert y (G - {p}))"
      by (rule GB_replace_red_rtranclp_stable_GB_dgrad_p_set, fact+)
    show ?thesis
    proof (cases "y \<in> G")
      case True
      with \<open>y \<noteq> p\<close> have "y \<in> G - {p}" (is "_ \<in> ?G'") by blast
      hence eq: "insert y ?G' = ?G'" by auto
      from \<open>y \<in> ?G'\<close> generator_subset_pideal have "y \<in> pideal ?G'" ..
      have "z \<in> pideal ?G'" by (rule pideal_closed_red, rule subset_refl, fact+)
      hence "pideal (insert z ?G') = pideal ?G'" by (rule pideal_insert)
      also from step(3) have "... = pideal G" by (simp only: eq)
      finally show ?thesis .
    next
      case False
      from assms(2) obtain n where 1: "insert y (G - {p}) \<subseteq> dgrad_p_set d n"
        by (rule replace_in_dgrad_p_set)
      from False have "pideal (insert z (G - {p})) = pideal (insert z (insert y (G - {p}) - {y}))"
        by auto
      also from assms(1) 1 gb have "... = pideal (insert y (G - {p}))"
      proof (rule GB_replace_red_stable_pideal_dgrad_p_set)
        from step(2) False show "red ((insert y (G - {p})) - {y}) y z" by simp
      qed simp
      also have "... = pideal G" by fact
      finally show ?thesis .
    qed
  qed
qed

lemmas GB_replace_lp_adds_stable_GB_finite =
  GB_replace_lp_adds_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_lp_adds_stable_pideal_finite =
  GB_replace_lp_adds_stable_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_stable_GB_finite =
  GB_replace_red_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_stable_pideal_finite =
  GB_replace_red_stable_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_rtranclp_stable_GB_finite =
  GB_replace_red_rtranclp_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_rtranclp_stable_pideal_finite =
  GB_replace_red_rtranclp_stable_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

end (* gd_powerprod *)
  
subsection \<open>Definition and Uniqueness of Reduced Gr\"obner Bases\<close>

context ordered_powerprod
begin
  
definition is_reduced_GB :: "('a, 'b::field) poly_mapping set \<Rightarrow> bool" where
  "is_reduced_GB B \<equiv> is_Groebner_basis B \<and> is_auto_reduced B \<and> is_monic_set B \<and> 0 \<notin> B"
  
lemma reduced_GB_D1:
  assumes "is_reduced_GB G"
  shows "is_Groebner_basis G"
  using assms unfolding is_reduced_GB_def by simp

lemma reduced_GB_D2:
  assumes "is_reduced_GB G"
  shows "is_auto_reduced G"
  using assms unfolding is_reduced_GB_def by simp

 lemma reduced_GB_D3:
  assumes "is_reduced_GB G"
  shows "is_monic_set G"
  using assms unfolding is_reduced_GB_def by simp
     
lemma reduced_GB_D4:
  assumes "is_reduced_GB G" and "g \<in> G"
  shows "g \<noteq> 0"
  using assms unfolding is_reduced_GB_def by auto
    
lemma reduced_GB_lc:
  assumes major: "is_reduced_GB G" and "g \<in> G"
  shows "lc g = 1"
by (rule is_monic_setD, rule reduced_GB_D3, fact major, fact \<open>g \<in> G\<close>, rule reduced_GB_D4, fact major, fact \<open>g \<in> G\<close>)

lemma (in gd_powerprod) is_reduced_GB_subsetI:
  assumes Ared: "is_reduced_GB A" and BGB: "is_Groebner_basis B" and Bmon: "is_monic_set B"
    and *: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a - b \<noteq> 0 \<Longrightarrow> lp (a - b) \<in> keys b \<Longrightarrow> lp (a - b) \<prec> lp b \<Longrightarrow> False"
    and id_eq: "pideal A = pideal B"
  shows "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
    
  have "a \<noteq> 0" by (rule reduced_GB_D4, fact Ared, fact \<open>a \<in> A\<close>)
  have lca: "lc a = 1" by (rule reduced_GB_lc, fact Ared, fact \<open>a \<in> A\<close>)
  have AGB: "is_Groebner_basis A" by (rule reduced_GB_D1, fact Ared)
      
  from \<open>a \<in> A\<close> generator_subset_pideal have "a \<in> pideal A" ..
  also have "... = pideal B" using id_eq by simp
  finally have "a \<in> pideal B" .

  from BGB this \<open>a \<noteq> 0\<close> obtain b where "b \<in> B" and "b \<noteq> 0" and baddsa: "lp b adds lp a"
    by (rule GB_adds_lp)
  from Bmon this(1) this(2) have lcb: "lc b = 1" by (rule is_monic_setD)
  from \<open>b \<in> B\<close> generator_subset_pideal have "b \<in> pideal B" ..
  also have "... = pideal A" using id_eq by simp
  finally have "b \<in> pideal A" .
      
  have lp_eq: "lp b = lp a"
  proof (rule ccontr)
    assume "lp b \<noteq> lp a"
    from AGB \<open>b \<in> pideal A\<close> \<open>b \<noteq> 0\<close> obtain a'
      where "a' \<in> A" and "a' \<noteq> 0" and a'addsb: "lp a' adds lp b" by (rule GB_adds_lp)
    have a'addsa: "lp a' adds lp a" by (rule adds_trans, fact a'addsb, fact baddsa)
    have "lp a' \<noteq> lp a"
    proof
      assume "lp a' = lp a"
      hence aaddsa': "lp a adds lp a'" by simp
      have "lp a adds lp b" by (rule adds_trans, fact aaddsa', fact a'addsb)
      have "lp a = lp b" by (rule adds_antisym, fact+)
      with \<open>lp b \<noteq> lp a\<close> show False by simp
    qed
    hence "a' \<noteq> a" by auto
    with \<open>a' \<in> A\<close> have "a' \<in> A - {a}" by blast
    have is_red: "is_red (A - {a}) a" by (intro is_red_addsI, fact, fact, rule lp_in_keys, fact+)
    have "\<not> is_red (A - {a}) a" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Ared, fact+)
    from this is_red show False ..
  qed
  
  have "a - b = 0"
  proof (rule ccontr)
    let ?c = "a - b"
    assume "?c \<noteq> 0"
    have "?c \<in> pideal A" by (rule pideal_closed_minus, fact+)
    also have "... = pideal B" using id_eq by simp
    finally have "?c \<in> pideal B" .
        
    from \<open>b \<noteq> 0\<close> have "- b \<noteq> 0" by simp
    have "lp (-b) = lp a" unfolding lp_uminus by fact
    have "lc (-b) = - lc a" unfolding lc_uminus lca lcb ..
    from \<open>?c \<noteq> 0\<close> have "a + (-b) \<noteq> 0" by simp
    
    have "lp ?c \<in> keys ?c" by (rule lp_in_keys, fact)
    have "keys ?c \<subseteq> (keys a \<union> keys b)" by (fact keys_minus)
    with \<open>lp ?c \<in> keys ?c\<close> have "lp ?c \<in> keys a \<or> lp ?c \<in> keys b" by auto
    thus False
    proof
      assume "lp ?c \<in> keys a"
          
      from AGB \<open>?c \<in> pideal A\<close> \<open>?c \<noteq> 0\<close> obtain a'
        where "a' \<in> A" and "a' \<noteq> 0" and a'addsc: "lp a' adds lp ?c" by (rule GB_adds_lp)

      have "lp a' \<preceq> lp ?c" by (rule ord_adds, fact a'addsc)
      also have "... = lp (a + (-b))" by simp
      also have "... \<prec> lp a" by (rule lp_plus_lessI, fact+)
      finally have "lp a' \<prec> lp a" .
      hence "lp a' \<noteq> lp a" by simp
      hence "a' \<noteq> a" by auto
      with \<open>a' \<in> A\<close> have "a' \<in> A - {a}" by blast
          
      have is_red: "is_red (A - {a}) a" by (intro is_red_addsI, fact, fact, fact+)
      have "\<not> is_red (A - {a}) a" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Ared, fact+)
      from this is_red show False ..
    next
      assume "lp ?c \<in> keys b"

      with \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>?c \<noteq> 0\<close> show False
      proof (rule *)
        have "lp ?c = lp ((-b) + a)" by simp
        also have "... \<prec> lp (-b)"
        proof (rule lp_plus_lessI)
          from \<open>?c \<noteq> 0\<close> show "-b + a \<noteq> 0" by simp
        next
          from \<open>lp (-b) = lp a\<close> show "lp a = lp (-b)" by simp
        next
          from \<open>lc (-b) = - lc a\<close> show "lc a = - lc (-b)" by simp
        qed
        finally show "lp ?c \<prec> lp b" unfolding lp_uminus .
      qed
    qed
  qed
  
  hence "a = b" by simp
  with \<open>b \<in> B\<close> show "a \<in> B" by simp
qed

lemma (in gd_powerprod) is_reduced_GB_unique':
  assumes Ared: "is_reduced_GB A" and Bred: "is_reduced_GB B" and id_eq: "pideal A = pideal B"
  shows "A \<subseteq> B"
proof -
  from Bred have BGB: "is_Groebner_basis B" by (rule reduced_GB_D1)
  with assms(1) show ?thesis
  proof (rule is_reduced_GB_subsetI)
    from Bred show "is_monic_set B" by (rule reduced_GB_D3)
  next
    fix a b :: "('a, 'b) poly_mapping"
    let ?c = "a - b"
    assume "a \<in> A" and "b \<in> B" and "a \<noteq> 0" and "b \<noteq> 0" and "?c \<noteq> 0" and "lp ?c \<in> keys b" and "lp ?c \<prec> lp b"
  
    from \<open>a \<in> A\<close> have "a \<in> pideal B" by (simp only: id_eq[symmetric], rule generator_in_pideal)
    moreover from \<open>b \<in> B\<close> have "b \<in> pideal B" by (rule generator_in_pideal)
    ultimately have "?c \<in> pideal B" by (rule pideal_closed_minus)
    from BGB this \<open>?c \<noteq> 0\<close> obtain b'
      where "b' \<in> B" and "b' \<noteq> 0" and b'addsc: "lp b' adds lp ?c" by (rule GB_adds_lp)
  
    have "lp b' \<preceq> lp ?c" by (rule ord_adds, fact b'addsc)
    also have "... \<prec> lp b" by fact
    finally have "lp b' \<prec> lp b" unfolding lp_uminus .
    hence "lp b' \<noteq> lp b" by simp
    hence "b' \<noteq> b" by auto
    with \<open>b' \<in> B\<close> have "b' \<in> B - {b}" by blast
        
    have is_red: "is_red (B - {b}) b" by (intro is_red_addsI, fact, fact, fact+)
    have "\<not> is_red (B - {b}) b" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Bred, fact+)
    from this is_red show False ..
  qed fact
qed
  
theorem (in gd_powerprod) is_reduced_GB_unique:
  assumes Ared: "is_reduced_GB A" and Bred: "is_reduced_GB B" and id_eq: "pideal A = pideal B"
  shows "A = B"
proof
  from assms show "A \<subseteq> B" by (rule is_reduced_GB_unique')
next
  from Bred Ared id_eq[symmetric] show "B \<subseteq> A" by (rule is_reduced_GB_unique')
qed
  
subsection \<open>Computing Reduced Gr\"obner Bases by Auto-Reduction\<close>

subsubsection \<open>Minimal Bases\<close>

lemma (in gd_powerprod) minimal_basis_is_reduced_GB:
  assumes "is_minimal_basis B" and "is_monic_set B" and "is_reduced_GB G" and "G \<subseteq> B"
    and "pideal B = pideal G"
  shows "B = G"
  using _ assms(3) assms(5)
proof (rule is_reduced_GB_unique)
  from assms(3) have "is_Groebner_basis G" by (rule reduced_GB_D1)
  show "is_reduced_GB B" unfolding is_reduced_GB_def
  proof (intro conjI)
    show "0 \<notin> B"
    proof
      assume "0 \<in> B"
      with assms(1) have "0 \<noteq> (0::('a, 'b) poly_mapping)" by (rule is_minimal_basisD1)
      thus False by simp
    qed
  next
    from \<open>is_Groebner_basis G\<close> assms(4) assms(5) show "is_Groebner_basis B" by (rule GB_subset)
  next
    show "is_auto_reduced B" unfolding is_auto_reduced_def
    proof (intro ballI notI)
      fix b
      assume "b \<in> B"
      with assms(1) have "b \<noteq> 0" by (rule is_minimal_basisD1)
      assume "is_red (B - {b}) b"
      then obtain f where "f \<in> B - {b}" and "is_red {f} b" by (rule is_red_singletonI)
      from this(1) have "f \<in> B" and "f \<noteq> b" by simp_all

      from assms(1) \<open>f \<in> B\<close> have "f \<noteq> 0" by (rule is_minimal_basisD1)
      from \<open>f \<in> B\<close> have "f \<in> pideal B" by (rule generator_in_pideal)
      hence "f \<in> pideal G" by (simp only: assms(5))
      from \<open>is_Groebner_basis G\<close> this \<open>f \<noteq> 0\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f"
        by (rule GB_adds_lp)
      from \<open>g \<in> G\<close> \<open>G \<subseteq> B\<close> have "g \<in> B" ..
      have "g = f"
      proof (rule ccontr)
        assume "g \<noteq> f"
        with assms(1) \<open>g \<in> B\<close> \<open>f \<in> B\<close> have "\<not> lp g adds lp f" by (rule is_minimal_basisD2)
        from this \<open>lp g adds lp f\<close> show False ..
      qed
      with \<open>g \<in> G\<close> have "f \<in> G" by simp
      with \<open>f \<in> B - {b}\<close> \<open>is_red {f} b\<close> have red: "is_red (G - {b}) b"
        by (meson Diff_iff is_red_singletonD)

      from \<open>b \<in> B\<close> have "b \<in> pideal B" by (rule generator_in_pideal)
      hence "b \<in> pideal G" by (simp only: assms(5))
      from \<open>is_Groebner_basis G\<close> this \<open>b \<noteq> 0\<close> obtain g' where "g' \<in> G" and "g' \<noteq> 0" and "lp g' adds lp b"
        by (rule GB_adds_lp)
      from \<open>g' \<in> G\<close> \<open>G \<subseteq> B\<close> have "g' \<in> B" ..
      have "g' = b"
      proof (rule ccontr)
        assume "g' \<noteq> b"
        with assms(1) \<open>g' \<in> B\<close> \<open>b \<in> B\<close> have "\<not> lp g' adds lp b" by (rule is_minimal_basisD2)
        from this \<open>lp g' adds lp b\<close> show False ..
      qed
      with \<open>g' \<in> G\<close> have "b \<in> G" by simp

      from assms(3) have "is_auto_reduced G" by (rule reduced_GB_D2)
      from this \<open>b \<in> G\<close> have "\<not> is_red (G - {b}) b" by (rule is_auto_reducedD)
      from this red show False ..
    qed
  qed fact
qed

subsubsection \<open>Computing Minimal Bases\<close>

end (* ordered_powerprod *)

context gd_powerprod
begin

lemma comp_min_basis_aux_Nil_GB:
  assumes "is_Groebner_basis (set xs)" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "is_Groebner_basis (set (comp_min_basis_aux xs []))"
  unfolding GB_alt_2_finite[OF finite_set]
proof (intro ballI impI)
  fix f
  assume fin: "f \<in> pideal (set (comp_min_basis_aux xs []))" and "f \<noteq> 0"
  have "f \<in> pideal (set xs)" by (rule, fact fin, rule pideal_mono, fact comp_min_basis_aux_Nil_subset)
  show "is_red (set (comp_min_basis_aux xs [])) f"
  proof (rule comp_min_basis_aux_Nil_is_red)
    from assms \<open>f \<noteq> 0\<close> \<open>f \<in> pideal (set xs)\<close> show "is_red (set xs) f"
      by (simp add: GB_alt_2_finite[OF finite_set])
  qed fact+
qed

lemma comp_min_basis_aux_Nil_pideal:
  assumes "is_Groebner_basis (set xs)" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "pideal (set (comp_min_basis_aux xs [])) = pideal (set xs)"
proof -
  show ?thesis
  proof (rule, rule pideal_mono, fact comp_min_basis_aux_Nil_subset)
    show "pideal (set xs) \<subseteq> pideal (set (comp_min_basis_aux xs []))"
    proof
      fix f
      assume "f \<in> pideal (set xs)"
      show "f \<in> pideal (set (comp_min_basis_aux xs []))"
      proof (cases "f = 0")
        case True
        show ?thesis unfolding True by (rule zero_in_pideal)
      next
        case False
        let ?xs = "comp_min_basis_aux xs []"
        have "(red (set ?xs))\<^sup>*\<^sup>* f 0"
        proof (rule is_red_implies_0_red_finite[OF finite_set], rule pideal_mono,
                fact comp_min_basis_aux_Nil_subset)
          fix q
          assume "q \<noteq> 0" and "q \<in> pideal (set xs)"
          with assms(1) have "is_red (set xs) q" by (rule GB_imp_reducibility)
          from this assms(2) assms(3) show "is_red (set ?xs) q" by (rule comp_min_basis_aux_Nil_is_red)
        qed fact
        thus ?thesis by (rule red_rtranclp_0_in_pideal)
      qed
    qed
  qed
qed

lemma comp_min_basis_pre_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_min_basis_pre xs))"
  unfolding GB_alt_3_finite[OF finite_set]
proof (intro ballI impI)
  fix f
  assume fin: "f \<in> pideal (set (comp_min_basis_pre xs))" and "f \<noteq> 0"
  have "f \<in> pideal (set xs)" by (rule, fact fin, rule pideal_mono, rule comp_min_basis_pre_subset)
  from assms this \<open>f \<noteq> 0\<close> obtain g where "g \<in> set xs" and "g \<noteq> 0" and "lp g adds lp f" by (rule GB_adds_lp)
  from this(1) this(2) obtain g' where g'_in: "g' \<in> set (comp_min_basis_pre xs)" and "lp g' = lp g"
    by (rule comp_min_basis_pre_lp)
  from this(1) show "\<exists>g\<in>set (comp_min_basis_pre xs). g \<noteq> 0 \<and> lp g adds lp f"
  proof (rule, intro conjI)
    from g'_in show "g' \<noteq> 0" by (rule comp_min_basis_pre_nonzero)
  next
    from \<open>lp g adds lp f\<close> show "lp g' adds lp f" by (simp only: \<open>lp g' = lp g\<close>)
  qed
qed

lemma comp_min_basis_pre_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_min_basis_pre xs)) = pideal (set xs)"
proof -
  show ?thesis
  proof (rule, rule pideal_mono, rule comp_min_basis_pre_subset, rule)
    fix f
    assume "f \<in> pideal (set xs)"
    show "f \<in> pideal (set (comp_min_basis_pre xs))"
    proof (cases "f = 0")
      case True
      show ?thesis unfolding True by (rule zero_in_pideal)
    next
      case False
      let ?xs = "comp_min_basis_pre xs"
      have "(red (set ?xs))\<^sup>*\<^sup>* f 0"
      proof (rule is_red_implies_0_red_finite[OF finite_set], rule pideal_mono, rule comp_min_basis_pre_subset)
        fix q
        assume "q \<noteq> 0" and "q \<in> pideal (set xs)"
        with assms have "is_red (set xs) q" by (rule GB_imp_reducibility)
        thus "is_red (set ?xs) q" by (rule comp_min_basis_pre_is_red)
      qed fact
      thus ?thesis by (rule red_rtranclp_0_in_pideal)
    qed
  qed
qed

lemma comp_min_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_min_basis xs))"
  unfolding comp_min_basis_def
  by (rule comp_min_basis_aux_Nil_GB, rule comp_min_basis_pre_GB, fact,
      fact comp_min_basis_pre_nonzero', fact comp_min_basis_pre_distinct_lp)

lemma comp_min_basis_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_min_basis xs)) = pideal (set xs)"
proof -
  have "pideal (set (comp_min_basis xs)) = pideal (set (comp_min_basis_pre xs))"
    unfolding comp_min_basis_def
    by (rule comp_min_basis_aux_Nil_pideal, rule comp_min_basis_pre_GB, fact,
        fact comp_min_basis_pre_nonzero', fact comp_min_basis_pre_distinct_lp)
  also from assms have "... = pideal (set xs)" by (rule comp_min_basis_pre_pideal)
  finally show ?thesis .
qed

subsubsection \<open>Computing Reduced Bases\<close>

lemma comp_red_basis_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_red_basis xs)) = pideal (set xs)"
proof (rule, fact pideal_comp_red_basis_subset, rule)
  fix f
  assume "f \<in> pideal (set xs)"
  show "f \<in> pideal (set (comp_red_basis xs))"
  proof (cases "f = 0")
    case True
    show ?thesis unfolding True by (rule zero_in_pideal)
  next
    case False
    let ?xs = "comp_red_basis xs"
    have "(red (set ?xs))\<^sup>*\<^sup>* f 0"
    proof (rule is_red_implies_0_red_finite, fact finite_set, fact pideal_comp_red_basis_subset)
      fix q
      assume "q \<noteq> 0" and "q \<in> pideal (set xs)"
      with assms have "is_red (set xs) q" by (rule GB_imp_reducibility)
      thus "is_red (set (comp_red_basis xs)) q" unfolding comp_red_basis_is_red .
    qed fact
    thus ?thesis by (rule red_rtranclp_0_in_pideal)
  qed
qed
  
lemma comp_red_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_red_basis xs))"
  unfolding GB_alt_2_finite[OF finite_set]
proof (intro ballI impI)
  fix f
  assume fin: "f \<in> pideal (set (comp_red_basis xs))"
  hence "f \<in> pideal (set xs)" unfolding comp_red_basis_pideal[OF assms] .
  assume "f \<noteq> 0"
  from assms \<open>f \<noteq> 0\<close> \<open>f \<in> pideal (set xs)\<close> show "is_red (set (comp_red_basis xs)) f"
    by (simp add: comp_red_basis_is_red GB_alt_2_finite)
qed

subsubsection \<open>Computing Reduced Gr\"obner Bases\<close>

lemma comp_red_monic_basis_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_red_monic_basis xs)) = pideal (set xs)"
  unfolding set_comp_red_monic_basis monic_set_pideal comp_red_basis_pideal[OF assms] ..
    
lemma comp_red_monic_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis monic_set_GB using assms by (rule comp_red_basis_GB)
    
lemma comp_red_monic_basis_is_reduced_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_reduced_GB (set (comp_red_monic_basis xs))"
  unfolding is_reduced_GB_def
proof (intro conjI, rule comp_red_monic_basis_GB, fact assms,
       rule comp_red_monic_basis_is_auto_reduced, rule comp_red_monic_basis_is_monic_set, intro notI)
  assume "0 \<in> set (comp_red_monic_basis xs)"
  hence "0 \<noteq> (0::('a, 'b) poly_mapping)" by (rule comp_red_monic_basis_nonzero)
  thus False by simp
qed

(* TODO: Replace "ex_finite_GB_dgrad_p_set" in "Groebner_Bases" by the following result. *)
lemma ex_finite_GB_dgrad_p_set_stronger:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  obtains G where "G \<subseteq> dgrad_p_set d m" and "finite G" and "is_Groebner_basis G" and "pideal G = pideal F"
proof -
  define S where "S = {lp f | f. f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0}"
  have "S \<subseteq> dgrad_set d m"
  proof
    fix s
    assume "s \<in> S"
    then obtain f where "f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0" and "s = lp f"
      unfolding S_def by blast
    from this(1) have "f \<in> dgrad_p_set d m" and "f \<noteq> 0" by simp_all
    from this(2) have "s \<in> keys f" unfolding \<open>s = lp f\<close> by (rule lp_in_keys)
    with \<open>f \<in> dgrad_p_set d m\<close> have "d s \<le> m" by (rule dgrad_p_setD)
    thus "s \<in> dgrad_set d m" by (simp add: dgrad_set_def)
  qed
  with assms(1) obtain T where "finite T" and "T \<subseteq> S" and *: "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. t adds s)"
    by (rule ex_finite_adds, blast)
  define crit where "crit = (\<lambda>t f. f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0 \<and> t = lp f)"
  have ex_crit: "t \<in> T \<Longrightarrow> (\<exists>f. crit t f)" for t
  proof -
    assume "t \<in> T"
    from this \<open>T \<subseteq> S\<close> have "t \<in> S" ..
    then obtain f where "f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0" and "t = lp f"
      unfolding S_def by blast
    thus "\<exists>f. crit t f" unfolding crit_def by blast
  qed
  define G where "G = (\<lambda>t. SOME g. crit t g) ` T"
  have G: "g \<in> G \<Longrightarrow> g \<in> pideal F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" for g
  proof -
    assume "g \<in> G"
    then obtain t where "t \<in> T" and g: "g = (SOME h. crit t h)" unfolding G_def ..
    have "crit t g" unfolding g by (rule someI_ex, rule ex_crit, fact)
    thus "g \<in> pideal F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" by (simp add: crit_def)
  qed
  have **: "t \<in> T \<Longrightarrow> (\<exists>g\<in>G. lp g = t)" for t
  proof -
    assume "t \<in> T"
    define g where "g = (SOME h. crit t h)"
    from \<open>t \<in> T\<close> have "g \<in> G" unfolding g_def G_def by blast
    thus "\<exists>g\<in>G. lp g = t"
    proof
      have "crit t g" unfolding g_def by (rule someI_ex, rule ex_crit, fact)
      thus "lp g = t" by (simp add: crit_def)
    qed
  qed
  have adds: "f \<in> pideal F \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)" for f
  proof -
    assume "f \<in> pideal F" and "f \<in> dgrad_p_set d m" and "f \<noteq> 0"
    hence "lp f \<in> S" unfolding S_def by blast
    hence "\<exists>t\<in>T. t adds (lp f)" by (rule *)
    then obtain t where "t \<in> T" and "t adds (lp f)" ..
    from this(1) have "\<exists>g\<in>G. lp g = t" by (rule **)
    then obtain g where "g \<in> G" and "lp g = t" ..
    show "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f"
    proof (intro bexI conjI)
      from G[OF \<open>g \<in> G\<close>] show "g \<noteq> 0" by (elim conjE)
    next
      from \<open>t adds lp f\<close> show "lp g adds lp f" by (simp only: \<open>lp g = t\<close>)
    qed fact
  qed
  have sub1: "pideal G \<subseteq> pideal F"
  proof (rule pideal_subset_pidealI, rule)
    fix g
    assume "g \<in> G"
    from G[OF this] show "g \<in> pideal F" ..
  qed
  have sub2: "G \<subseteq> dgrad_p_set d m"
  proof
    fix g
    assume "g \<in> G"
    from G[OF this] show "g \<in> dgrad_p_set d m" by (elim conjE)
  qed
  show ?thesis
  proof
    from \<open>finite T\<close> show "finite G" unfolding G_def ..
  next
    from assms(1) sub2 adds show "is_Groebner_basis G"
    proof (rule isGB_I_adds_lp)
      fix f
      assume "f \<in> pideal G"
      from this sub1 show "f \<in> pideal F" ..
    qed
  next
    show "pideal G = pideal F"
    proof
      show "pideal F \<subseteq> pideal G"
      proof (rule pideal_subset_pidealI, rule)
        fix f
        assume "f \<in> F"
        hence "f \<in> pideal F" by (rule generator_in_pideal)
        from \<open>f \<in> F\<close> assms(2) have "f \<in> dgrad_p_set d m" ..
        with assms(1) sub2 sub1 _ \<open>f \<in> pideal F\<close> have "(red G)\<^sup>*\<^sup>* f 0"
        proof (rule is_red_implies_0_red_dgrad_p_set)
          fix q
          assume "q \<in> pideal F" and "q \<in> dgrad_p_set d m" and "q \<noteq> 0"
          hence "(\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp q)" by (rule adds)
          then obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp q" by blast
          thus "is_red G q" using \<open>q \<noteq> 0\<close> is_red_indI1 by blast
        qed
        thus "f \<in> pideal G" by (rule red_rtranclp_0_in_pideal)
      qed
    qed fact
  next
    show "G \<subseteq> dgrad_p_set d m"
    proof
      fix g
      assume "g \<in> G"
      hence "g \<in> pideal F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" by (rule G)
      thus "g \<in> dgrad_p_set d m" by (elim conjE)
    qed
  qed
qed

lemma ex_finite_reduced_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  obtains G where "G \<subseteq> dgrad_p_set d m" and "finite G" and "is_reduced_GB G" and "pideal G = pideal F"
proof -
  from assms obtain G0 where G0_sub: "G0 \<subseteq> dgrad_p_set d m" and fin: "finite G0"
    and gb: "is_Groebner_basis G0" and pid: "pideal G0 = pideal F"
    by (rule ex_finite_GB_dgrad_p_set_stronger)
  from fin obtain xs where set: "G0 = set xs" using finite_list by blast
  let ?G = "set (comp_red_monic_basis xs)"
  show ?thesis
  proof
    from assms(1) have "dgrad_p_set_le d (set (comp_red_monic_basis xs)) G0" unfolding set
      by (rule comp_red_monic_basis_dgrad_p_set_le)
    from this G0_sub show "set (comp_red_monic_basis xs) \<subseteq> dgrad_p_set d m"
      by (rule dgrad_p_set_le_dgrad_p_set)
  next
    from gb show rgb: "is_reduced_GB ?G" unfolding set
      by (rule comp_red_monic_basis_is_reduced_GB)
  next
    from gb show "pideal ?G = pideal F" unfolding set pid[symmetric]
      by (rule comp_red_monic_basis_pideal)
  qed (fact finite_set)
qed

theorem ex_unique_reduced_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "\<exists>!G. G \<subseteq> dgrad_p_set d m \<and> finite G \<and> is_reduced_GB G \<and> pideal G = pideal F"
proof -
  from assms obtain G where "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "is_reduced_GB G" and G: "pideal G = pideal F" by (rule ex_finite_reduced_GB_dgrad_p_set)
  hence "G \<subseteq> dgrad_p_set d m \<and> finite G \<and> is_reduced_GB G \<and> pideal G = pideal F" by simp
  thus ?thesis
  proof (rule ex1I)
    fix G'
    assume "G' \<subseteq> dgrad_p_set d m \<and> finite G' \<and> is_reduced_GB G' \<and> pideal G' = pideal F"
    hence "is_reduced_GB G'" and G': "pideal G' = pideal F" by simp_all
    note this(1) \<open>is_reduced_GB G\<close>
    moreover have "pideal G' = pideal G" by (simp only: G G')
    ultimately show "G' = G" by (rule is_reduced_GB_unique)
  qed
qed

corollary ex_unique_reduced_GB_dgrad_p_set':
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "\<exists>!G. finite G \<and> is_reduced_GB G \<and> pideal G = pideal F"
proof -
  from assms obtain G where "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "is_reduced_GB G" and G: "pideal G = pideal F" by (rule ex_finite_reduced_GB_dgrad_p_set)
  hence "finite G \<and> is_reduced_GB G \<and> pideal G = pideal F" by simp
  thus ?thesis
  proof (rule ex1I)
    fix G'
    assume "finite G' \<and> is_reduced_GB G' \<and> pideal G' = pideal F"
    hence "is_reduced_GB G'" and G': "pideal G' = pideal F" by simp_all
    note this(1) \<open>is_reduced_GB G\<close>
    moreover have "pideal G' = pideal G" by (simp only: G G')
    ultimately show "G' = G" by (rule is_reduced_GB_unique)
  qed
qed
  
definition reduced_GB :: "('a \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) set"
  where "reduced_GB B = (THE G. finite G \<and> is_reduced_GB G \<and> pideal G = pideal B)"

text \<open>@{const reduced_GB} returns the unique reduced Gr\"obner basis of the given set, provided its
  Dickson grading is bounded. Combining @{const comp_red_monic_basis} with any function for computing
  Gr\"obner bases, e.\,g. @{term gb} from theory "Buchberger", makes @{const reduced_GB} computable.\<close>

lemma finite_reduced_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "finite (reduced_GB F)"
  unfolding reduced_GB_def
  by (rule the1I2, rule ex_unique_reduced_GB_dgrad_p_set', fact, fact, elim conjE)

lemma reduced_GB_is_reduced_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "is_reduced_GB (reduced_GB F)"
  unfolding reduced_GB_def
  by (rule the1I2, rule ex_unique_reduced_GB_dgrad_p_set', fact, fact, elim conjE)

lemma reduced_GB_is_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis (reduced_GB F)"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def ..
qed

lemma reduced_GB_is_auto_reduced_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "is_auto_reduced (reduced_GB F)"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed
    
lemma reduced_GB_is_monic_set_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "is_monic_set (reduced_GB F)"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed
  
lemma reduced_GB_nonzero_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "0 \<notin> reduced_GB F"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed

lemma reduced_GB_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "pideal (reduced_GB F) = pideal F"
  unfolding reduced_GB_def
  by (rule the1I2, rule ex_unique_reduced_GB_dgrad_p_set', fact, fact, elim conjE)

lemma reduced_GB_unique_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "is_reduced_GB G" and "pideal G = pideal F"
  shows "reduced_GB F = G"
  by (rule is_reduced_GB_unique, rule reduced_GB_is_reduced_GB_dgrad_p_set, fact+,
      simp only: reduced_GB_pideal_dgrad_p_set[OF assms(1, 2)] assms(4))

lemma reduced_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "reduced_GB F \<subseteq> dgrad_p_set d m"
proof -
  from assms obtain G where G: "G \<subseteq> dgrad_p_set d m" and "is_reduced_GB G" and "pideal G = pideal F"
    by (rule ex_finite_reduced_GB_dgrad_p_set)
  from assms this(2, 3) have "reduced_GB F = G" by (rule reduced_GB_unique_dgrad_p_set)
  with G show ?thesis by simp
qed

lemmas ex_unique_reduced_GB_finite =
  ex_unique_reduced_GB_dgrad_p_set'[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas finite_reduced_GB_finite =
  finite_reduced_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas reduced_GB_is_reduced_GB_finite =
  reduced_GB_is_reduced_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas reduced_GB_is_GB_finite =
  reduced_GB_is_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas reduced_GB_is_auto_reduced_finite =
  reduced_GB_is_auto_reduced_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas reduced_GB_is_monic_set_finite =
  reduced_GB_is_monic_set_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas reduced_GB_nonzero_finite =
  reduced_GB_nonzero_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas reduced_GB_pideal_finite =
  reduced_GB_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas reduced_GB_unique_finite =
  reduced_GB_unique_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

subsubsection \<open>Properties of the Reduced Gr\"obner Basis of an Ideal\<close>

lemma pideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "pideal F = UNIV \<longleftrightarrow> reduced_GB F = {1}"
proof
  assume "pideal F = UNIV"
  from assms show "reduced_GB F = {1}"
  proof (rule reduced_GB_unique_dgrad_p_set)
    show "is_reduced_GB {1}" unfolding is_reduced_GB_def
    proof (intro conjI, fact is_Groebner_basis_singleton)
      show "is_auto_reduced {1}" unfolding is_auto_reduced_def
        by (rule ballI, simp add: remove_def not_is_red_empty)
    next
      show "is_monic_set {1}"
        by (rule is_monic_setI, simp del: single_one add: single_one[symmetric] lc_monomial)
    qed simp
  next
    show "pideal {1} = pideal F"
      by (simp only: \<open>pideal F = UNIV\<close> pideal_eq_UNIV_iff_contains_one, rule generator_in_pideal, simp)
  qed
next
  assume "reduced_GB F = {1}"
  hence "1 \<in> reduced_GB F" by simp
  hence "1 \<in> pideal (reduced_GB F)" by (rule generator_in_pideal)
  also from assms have "... = pideal F" by (rule reduced_GB_pideal_dgrad_p_set)
  finally show "pideal F = UNIV" by (simp only: pideal_eq_UNIV_iff_contains_one)
qed

lemmas pideal_eq_UNIV_iff_reduced_GB_eq_one_finite =
  pideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
                                                                          
end (* gd_powerprod *)

subsubsection \<open>Context @{locale od_powerprod}\<close>

context od_powerprod
begin

lemmas ex_unique_reduced_GB =
  ex_unique_reduced_GB_dgrad_p_set'[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas finite_reduced_GB =
  finite_reduced_GB_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas reduced_GB_is_reduced_GB =
  reduced_GB_is_reduced_GB_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas reduced_GB_is_GB =
  reduced_GB_is_GB_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas reduced_GB_is_auto_reduced =
  reduced_GB_is_auto_reduced_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas reduced_GB_is_monic_set =
  reduced_GB_is_monic_set_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas reduced_GB_nonzero =
  reduced_GB_nonzero_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas reduced_GB_pideal =
  reduced_GB_pideal_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas reduced_GB_unique =
  reduced_GB_unique_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]

end (* od_powerprod *)
  
end (* theory *)
