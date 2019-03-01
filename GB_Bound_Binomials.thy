section \<open>New Bounds for Gr\"obner Bases Computation for Binomial Ideals\<close>

theory GB_Bound_Binomials
  imports Membership_Bound_Binomials
begin

context two_polys
begin

definition gb_problem :: "nat \<Rightarrow> bool"
  where "gb_problem d =
          (\<exists>G. punit.is_Groebner_basis G \<and> ideal G = ideal {f1, f2} \<and> UNION G indets \<subseteq> indets f1 \<union> indets f2 \<and>
            (\<forall>g\<in>G. \<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d))"

lemma gb_problemI:
  "punit.is_Groebner_basis G \<Longrightarrow> ideal G = ideal {f1, f2} \<Longrightarrow> UNION G indets \<subseteq> indets f1 \<union> indets f2 \<Longrightarrow>
    (\<And>g. g \<in> G \<Longrightarrow> \<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d) \<Longrightarrow>
    gb_problem d"
  by (auto simp: gb_problem_def)

lemma gb_problemI_reduced_GB:
  assumes "\<And>g. g \<in> punit.reduced_GB {f1, f2} \<Longrightarrow>
                \<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d"
  shows "gb_problem d"
  using _ _ _ assms
proof (rule gb_problemI)
  let ?G = "punit.reduced_GB {f1, f2}"
  have "finite {f1, f2}" by simp
  thus "punit.is_Groebner_basis ?G" and "ideal ?G = ideal {f1, f2}"
    by (rule punit.reduced_GB_is_GB_finite, rule punit.reduced_GB_pmdl_finite[simplified])

  show "\<Union> (indets ` ?G) \<subseteq> indets f1 \<union> indets f2" (is "_ \<subseteq> ?X")
  proof (rule subsetI, elim UN_E)
    fix x g
    have "finite ?X" by (simp add: finite_indets)
    moreover have "{f1, f2} \<subseteq> P[?X]" by (auto intro: PolysI_alt)
    ultimately have "?G \<subseteq> P[?X]"
      by (rule punit.reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0,
                                          simplified dgrad_p_set_varnum_wrt])
    moreover assume "g \<in> ?G"
    ultimately have "g \<in> P[?X]" ..
    hence "indets g \<subseteq> ?X" by (rule PolysD)
    moreover assume "x \<in> indets g"
    ultimately show "x \<in> ?X" ..
  qed
qed

text \<open>Something similar to the lemma below also holds if \<open>f1\<close> and/or \<open>f2\<close> are no binomials, with
  @{prop "membership_problem_assms f1 f2 g"} replaced by @{prop "\<not> punit.is_red {f1, f2} g"}.\<close>

lemma gb_problemI_reduced_GB_binomials:
  assumes "is_binomial f1" and "is_binomial f2" and "poly_deg f1 \<le> d" and "poly_deg f2 \<le> d"
  assumes "\<And>g. g \<in> punit.reduced_GB {f1, f2} \<Longrightarrow> membership_problem_assms f1 f2 g \<Longrightarrow>
                \<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d"
  shows "gb_problem d"
proof -
  let ?G = "punit.reduced_GB {f1, f2}"
  have "finite {f1, f2}" by simp
  hence GB: "punit.is_Groebner_basis ?G" and ideal: "ideal ?G = ideal {f1, f2}" and fin: "finite ?G"
    and "0 \<notin> ?G" by (rule punit.reduced_GB_is_GB_finite, rule punit.reduced_GB_pmdl_finite[simplified],
                      rule punit.finite_reduced_GB_finite, rule punit.reduced_GB_nonzero_finite)
  let ?H = "{g. lpp g = lpp f1 \<or> lpp g = lpp f2}"
  define G where "G = {f1, f2} \<union> (?G - ?H)"
  have 1: thesis if "g \<in> ?G" and "\<And>g'. g' \<in> G \<Longrightarrow> g' \<noteq> 0 \<Longrightarrow> lpp g' = lpp g \<Longrightarrow> thesis" for g thesis
  proof (cases "g \<in> G")
    case True
    moreover from that(1) \<open>0 \<notin> ?G\<close> have "g \<noteq> 0" by blast
    ultimately show ?thesis using refl by (rule that(2))
  next
    case False
    with that(1) have "lpp f1 = lpp g \<or> lpp f2 = lpp g" by (auto simp: G_def)
    thus ?thesis
    proof (elim disjE)
      have "f1 \<in> G" by (simp add: G_def)
      moreover from assms(1) have "f1 \<noteq> 0" by (rule binomial_not_0)
      moreover assume "lpp f1 = lpp g"
      ultimately show ?thesis by (rule that(2))
    next
      have "f2 \<in> G" by (simp add: G_def)
      moreover from assms(2) have "f2 \<noteq> 0" by (rule binomial_not_0)
      moreover assume "lpp f2 = lpp g"
      ultimately show ?thesis by (rule that(2))
    qed
  qed
  from fin have fin_G: "finite G" by (simp add: G_def)
  hence ideal_G: "ideal G = ideal ?G"
  proof (rule punit.pmdl_eqI_adds_lt_finite[simplified])
    show "ideal G \<subseteq> ideal ?G" unfolding G_def
    proof (intro ideal.span_subset_spanI Un_least)
      have "{f1, f2} \<subseteq> ideal {f1, f2}" by (rule ideal.span_superset)
      also have "\<dots> = ideal ?G" by (simp only: ideal)
      finally show "{f1, f2} \<subseteq> ideal ?G" .
    next
      have "?G - ?H \<subseteq> ?G" by (fact Diff_subset)
      also have "\<dots> \<subseteq> ideal ?G" by (rule ideal.span_superset)
      finally show "?G - ?H \<subseteq> ideal ?G" .
    qed
  next
    fix f
    assume "f \<in> ideal ?G" and "f \<noteq> 0"
    with GB obtain g where "g \<in> ?G" and "lpp g adds lpp f" by (rule punit.GB_adds_lt[simplified])
    from this(1) obtain g' where "g' \<in> G" and "g' \<noteq> 0" and "lpp g' = lpp g" by (rule 1)
    with \<open>lpp g adds lpp f\<close> show "\<exists>g\<in>G. g \<noteq> 0 \<and> lpp g adds lpp f" by auto
  qed

  show ?thesis
  proof (rule gb_problemI)
    show "punit.is_Groebner_basis G" unfolding punit.GB_alt_3_finite[simplified, OF fin_G]
    proof (intro ballI impI)
      fix f
      assume "f \<in> ideal G" and "f \<noteq> 0"
      from this(1) have "f \<in> ideal ?G" by (simp only: ideal_G)
      with GB obtain g where "g \<in> ?G" and "lpp g adds lpp f"
        using \<open>f \<noteq> 0\<close> by (rule punit.GB_adds_lt[simplified])
      from this(1) obtain g' where "g' \<in> G" and "g' \<noteq> 0" and "lpp g' = lpp g" by (rule 1)
      with \<open>lpp g adds lpp f\<close> show "\<exists>g\<in>G. g \<noteq> 0 \<and> lpp g adds lpp f" by auto
    qed

    show "ideal G = ideal {f1, f2}" by (simp only: ideal_G ideal)
  
    show "\<Union> (indets ` G) \<subseteq> indets f1 \<union> indets f2" (is "_ \<subseteq> ?X")
    proof (rule subsetI, elim UN_E)
      fix x g
      have "finite ?X" by (simp add: finite_indets)
      moreover have "{f1, f2} \<subseteq> P[?X]" by (auto intro: PolysI_alt)
      ultimately have "?G \<subseteq> P[?X]"
        by (rule punit.reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0,
                                            simplified dgrad_p_set_varnum_wrt])
      with Diff_subset have "?G - ?H \<subseteq> P[?X]" by (rule subset_trans)
      moreover have "{f1, f2} \<subseteq> P[?X]" by (auto intro: PolysI_alt)
      ultimately have "G \<subseteq> P[?X]" by (simp add: G_def)
      moreover assume "g \<in> G"
      ultimately have "g \<in> P[?X]" ..
      hence "indets g \<subseteq> ?X" by (rule PolysD)
      moreover assume "x \<in> indets g"
      ultimately show "x \<in> ?X" ..
    qed

    fix g
    assume "g \<in> G"
    thus "\<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d"
      unfolding G_def
    proof (elim UnE DiffE)
      assume "g \<in> {f1, f2}"
      hence "g = f1 \<or> g = f2" by simp
      thus ?thesis
      proof
        assume g: "g = f1"
        show ?thesis
        proof (intro exI conjI)
          show "g = 1 * f1 + 0 * f2" by (simp add: g)
        qed (simp_all add: assms(3))
      next
        assume g: "g = f2"
        show ?thesis
        proof (intro exI conjI)
          show "g = 0 * f1 + 1 * f2" by (simp add: g)
        qed (simp_all add: assms(4))
      qed
    next
      assume "g \<in> ?G" and "g \<notin> ?H"
      from \<open>finite {f1, f2}\<close> this(1) show ?thesis
      proof (rule punit.reduced_GB_cases_finite)
        fix f
        assume "f \<in> {f1, f2}" and "f \<noteq> 0" and "lpp g = lpp f"
        hence "g \<in> ?H" by blast
        with \<open>g \<notin> ?H\<close> show ?thesis ..
      next
        assume "\<not> punit.is_red {f1, f2} g"
        have "membership_problem_assms f1 f2 g" unfolding membership_problem_assms_def
        proof (intro conjI impI)
          from assms(1, 2) have "is_binomial_set {f1, f2}" by (simp add: is_binomial_set_def)
          hence "is_binomial_set ?G" by (rule punit.reduced_GB_is_binomial_set) simp
          thus "is_binomial g" using \<open>g \<in> ?G\<close> by (rule is_binomial_setD)
        next
          from \<open>g \<in> ?G\<close> have "g \<in> ideal ?G" by (rule ideal.span_base)
          thus "g \<in> ideal {f1, f2}" by (simp only: ideal)
        next
          assume "is_proper_binomial g"
          with _ \<open>g \<in> ?G\<close> show "monomial 1 ` keys g \<inter> ideal {f1, f2} = {}" by (rule rem_3_1_4_2) simp
        qed fact+
        with \<open>g \<in> ?G\<close> show ?thesis by (rule assms(5))
      qed
    qed
  qed
qed

lemma lem_4_2_1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tpp f \<unlhd> p"
  shows "step p \<le> step (tpp f)"
proof (rule ccontr)
  let ?A = "\<lambda>q. {nat \<lceil>(lookup overlap x - rat (lookup q x)) / lookup (vect f) x\<rceil> |x.
                 0 < lookup (vect f) x \<and> rat (lookup q x) < lookup overlap x}"
  have fin: "finite (?A q)" for q using finite_step_p'_carrier[where p="of_nat_pm q"]
    unfolding lookup_of_nat_pm by (rule finite_image_set)

  assume "\<not> step p \<le> step (tpp f)"
  hence "step (tpp f) < step p" by simp
  with le0 have "0 < step p" by (rule le_less_trans)
  from assms have "step p = step' f p" by (rule step_alt1)
  also have "\<dots> \<in> ?A p \<union> {0}" unfolding step'_alt by (rule Max_in) (simp_all add: fin)
  finally have "step p \<in> ?A p" using \<open>0 < step p\<close> by simp
  then obtain x where "0 < lookup (vect f) x" and "rat (lookup p x) < lookup overlap x"
    and "step p = nat \<lceil>(lookup overlap x - rat (lookup p x)) / lookup (vect f) x\<rceil>" (is "_ = nat \<lceil>?a\<rceil>")
    by blast
  from assms(3) have "lookup (tpp f) x \<le> lookup p x" by (rule le_pmD)
  hence "rat (lookup (tpp f) x) \<le> rat (lookup p x)" by (rule of_nat_mono)
  also have "\<dots> < lookup overlap x" by fact
  finally have "nat \<lceil>(lookup overlap x - rat (lookup (tpp f) x)) / lookup (vect f) x\<rceil> \<in> ?A (tpp f)"
    (is "nat \<lceil>?b\<rceil> \<in> _") using \<open>0 < lookup (vect f) x\<close> by blast
  also have "\<dots> \<subseteq> ?A (tpp f) \<union> {0}" by blast
  finally have "nat \<lceil>?b\<rceil> \<in> ?A (tpp f) \<union> {0}" .
  with _ have "nat \<lceil>?b\<rceil> \<le> step' f (tpp f)" unfolding step'_alt by (rule Max_ge) (simp add: fin)
  also from assms(1, 2) le_pm_refl have "\<dots> = step (tpp f)" by (rule step_alt1[symmetric])
  also have "\<dots> < step p" by fact
  also have "\<dots> = nat \<lceil>?a\<rceil>" by fact
  finally have "\<lceil>?b\<rceil> < \<lceil>?a\<rceil>" by (simp only: zless_nat_conj)
  hence "?b < ?a" by (rule ceiling_less_cancel)
  with \<open>0 < lookup (vect f) x\<close> have "rat (lookup p x) < rat (lookup (tpp f) x)"
    by (simp add: divide_less_cancel)
  also have "\<dots> \<le> rat (lookup p x)" by fact
  finally show False ..
qed

lemma overlapshift_tpp:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f"
  shows "overlapshift (tpp f) = to_nat_pm (of_nat_pm (tpp f) + rat (step (tpp f)) \<cdot> vect f)"
proof -
  from assms(1, 2) le_pm_refl have "overlapshift (tpp f) = overlapshift' f (tpp f)"
    and eq: "step (tpp f) = step' f (tpp f)" by (rule overlapshift_alt1, rule step_alt1)
  note this(1)
  also have "overlapshift' f (tpp f) = to_nat_pm (of_nat_pm (tpp f) + rat (step (tpp f)) \<cdot> vect f)"
    by (rule poly_mapping_eqI) (simp add: overlapshift'_alt lookup_to_nat_pm eq)
  finally show ?thesis .
qed

corollary overlapshift_tpp_ge_pm:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f"
  shows "of_nat_pm (tpp f) + rat (step (tpp f)) \<cdot> vect f \<unlhd> of_nat_pm (overlapshift (tpp f))"
proof -
  have "is_int_pm (of_nat_pm (tpp f) + rat (step (tpp f)) \<cdot> vect f)" (is "is_int_pm ?t")
    by (intro plus_is_int_pm map_scale_is_int_pm Ints_of_nat vect_is_int_pm of_nat_pm_is_int_pm)
  hence "?t \<unlhd> of_nat_pm (to_nat_pm ?t)" by (rule of_nat_to_nat_ge_pm)
  also from assms have "to_nat_pm ?t = overlapshift (tpp f)" by (simp only: overlapshift_tpp)
  finally show ?thesis .
qed

subsection \<open>One Proper Binomial and one Monomial\<close>

text \<open>In @{cite MWW}, the third assumption in the following lemma (@{prop "0 < k"}) is missing.
  Counterexample for @{prop "k = 0"} and (degree-)lexicographic order with @{prop "x \<prec> y"}:
  \<^item> @{prop "f1 = y^2 + x^2"},
  \<^item> @{prop "f2 = y"},
  \<^item> @{prop "f = f1"},
  \<^item> @{prop "overlap = y"},
  \<^item> @{prop "step (tpp f) = 1"}.
  Then the overlapshift of \<open>f\<close> is \<open>y^2\<close>, which is also the lcs on the right-hand-side. But \<open>tpp f\<close> is
  not below \<open>y^2\<close>.\<close>

lemma lem_4_3_1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "0 < k" and "k \<le> step (tpp f)"
  shows "lcs (of_nat_pm (tpp f) + rat k \<cdot> vect f) overlap \<unlhd> lcs (of_nat_pm (overlapshift (tpp f))) overlap"
proof (rule le_pmI, simp add: lookup_lcs_fun lcs_fun_def lookup_add lookup_of_nat_pm)
  fix x
  show "rat (lookup (tpp f) x) + rat k * lookup (vect f) x \<le>
          max (rat (lookup (overlapshift (tpp f)) x)) (lookup overlap x)"
      (is "?a \<le> ?b")
  proof (cases "0 \<le> lookup (vect f) x")
    case True
    from True assms(4) have "?a \<le> rat (lookup (tpp f) x) + rat (step (tpp f)) * lookup (vect f) x"
      (is "_ \<le> ?c") by (simp add: mult_right_mono)
    also have "\<dots> \<le> rat (to_nat ?c)"
      by (intro of_nat_to_nat_ge Ints_add Ints_mult is_int_pmD vect_is_int_pm) (fact Ints_of_nat)+
    also from assms(1, 2) have "\<dots> = rat (lookup (overlapshift (tpp f)) x)"
      by (simp add: overlapshift_tpp lookup_to_nat_pm lookup_add lookup_of_nat_pm)
    also have "\<dots> \<le> ?b" by (rule max.cobounded1)
    finally show ?thesis .
  next
    case False
    hence *: "lookup (vect f) x < 0" by simp
    with assms(3) have "?a \<le> rat (lookup (tpp f) x) + lookup (vect f) x" by simp
    also have "\<dots> = rat (lookup (lpp f) x)" by (simp add: vect_alt lookup_minus lookup_of_nat_pm)
    finally have "?a \<le> rat (lookup (lpp f) x)" .
    also from * have "\<dots> \<le> rat (lookup (tpp f) x)" by (simp add: vect_alt lookup_minus lookup_of_nat_pm)
    finally have "?a \<le> rat (lookup (tpp f) x)" .
    with \<open>?a \<le> rat (lookup (lpp f) x)\<close> have "?a \<le> min (rat (lookup (lpp f) x)) (rat (lookup (tpp f) x))"
      by (rule min.boundedI)
    also from assms(1) have "\<dots> \<le> lookup overlap x"
      by (auto simp: overlap_alt' lookup_of_nat_pm lookup_lcs_fun lcs_fun_def lookup_gcs_fun gcs_fun
            of_nat_min of_nat_max)
    also have "\<dots> \<le> ?b" by (rule max.cobounded2)
    finally show ?thesis .
  qed
qed

context
  assumes f1_pbinomial: "is_proper_binomial f1"
  assumes f2_monomial: "is_monomial f2"
begin

lemma thm_4_3_2_aux_1:
  assumes "g \<in> punit.reduced_GB {f1, f2}" and "\<not> punit.is_red {f1, f2} g"
  assumes "is_monomial g \<Longrightarrow> membership_problem_assms f1 f2 g \<Longrightarrow> tpp f1 adds lpp g \<Longrightarrow>
            0 < step (lpp g) \<Longrightarrow> overlap \<unlhd> of_nat_pm (overlapshift (lpp g)) \<Longrightarrow>
            of_nat_pm (overlapshift (lpp g)) = of_nat_pm (lpp g) + rat (step (lpp g)) \<cdot> vect f1 \<Longrightarrow> thesis"
  shows thesis
proof -
  let ?G = "punit.reduced_GB {f1, f2}"
  from f1_pbinomial have 1: "is_binomial f1" by (rule proper_binomial_imp_binomial)
  from f2_monomial have 2: "is_monomial_set {f2}" by (simp add: is_monomial_set_def)
  have ideal: "ideal ?G = ideal {f1, f2}" by (rule punit.reduced_GB_pmdl_finite[simplified]) simp
  have "0 \<notin> ?G" by (rule punit.reduced_GB_nonzero_finite) simp
  with assms(1) have "g \<noteq> 0" by blast
  have "finite {f1, f2}" by simp
  thus ?thesis using assms(1)
  proof (rule punit.reduced_GB_cases_finite)
    fix f
    assume "f \<in> {f1, f2}" and "f \<noteq> 0" and lp_g: "lpp g = lpp f"
    note this(1, 2)
    moreover from \<open>g \<noteq> 0\<close> have "lpp g \<in> keys g" by (rule punit.lt_in_keys)
    moreover have "lpp f adds lpp g" by (simp add: lp_g)
    ultimately have "punit.is_red {f1, f2} g" by (rule punit.is_red_addsI[simplified])
    with assms(2) show ?thesis ..
  next
    from 1 2 _ assms(1) show ?thesis
    proof (rule punit.reduced_GB_binomial_monomial_set_cases)
      fix c
      assume "c \<noteq> 0" and "g = c \<cdot> f1"
      with assms(2) have "\<not> punit.is_red {f1, f2} f1" by (simp add: punit.is_red_map_scale_iff)
      from f1_pbinomial have "f1 \<noteq> 0" by (rule proper_binomial_not_0)
      with punit.red_supsetE punit.red_supset_insertI have "punit.is_red {f1, f2} f1"
        by fastforce
      with \<open>\<not> punit.is_red {f1, f2} f1\<close> show ?thesis ..
    next
      assume "is_monomial g"
      note 1
      moreover from f2_monomial have 3: "is_binomial f2" by (rule monomial_imp_binomial)
      moreover have g_in: "g \<in> ideal {f1, f2}" unfolding ideal[symmetric] using assms(1)
        by (rule ideal.span_base)
      moreover note assms(2)
      moreover from \<open>g \<noteq> 0\<close> have "lpp g \<in> keys g" by (rule punit.lt_in_keys)
      ultimately obtain f k u where "f \<in> {f1, f2}" and "is_proper_binomial f" and adds: "tpp f adds lpp g"
        and "associated f u (lpp g) k" and "overlap \<unlhd> of_nat_pm u" and "lpp f adds u"
        by (rule binomial_ideal_irredE_assoc)
      from this(1-5) have le: "overlap \<unlhd> of_nat_pm (overlapshift (lpp g))"
        and eq: "of_nat_pm (overlapshift (lpp g)) = of_nat_pm (lpp g) + rat (step (lpp g)) \<cdot> vect f"
        by (rule overlapshift_is_above_overlap, rule of_nat_pm_overlapshift')
      from f2_monomial \<open>f \<in> {f1, f2}\<close> \<open>is_proper_binomial f\<close> have f: "f = f1"
        by (auto simp: is_monomial_def is_proper_binomial_def)
      from \<open>is_monomial g\<close> _ adds _ le eq show ?thesis unfolding f
      proof (rule assms(3))
        from \<open>is_monomial g\<close> have "is_binomial g" by (rule monomial_imp_binomial)
        moreover from \<open>is_monomial g\<close> proper_binomial_no_monomial have "\<not> is_proper_binomial g" by blast
        ultimately show "membership_problem_assms f1 f2 g" using 1 3 assms(2) g_in
          by (simp add: membership_problem_assms_def)
      next
        have "step (lpp g) \<noteq> 0"
        proof
          assume "step (lpp g) = 0"
          with eq have "overlapshift (lpp g) = lpp g" by simp
          with le have "lcs (gcs (lpp f1) (tpp f1)) (gcs (lpp f2) (tpp f2)) \<unlhd> lpp g"
            by (simp add: overlap_alt' le_of_nat_pm)
          with lcs_ge_pm(2) have "gcs (lpp f2) (tpp f2) \<unlhd> lpp g" by (rule le_pm_trans)
          moreover from f2_monomial have "lpp f2 = tpp f2" by (rule punit.lt_eq_tt_monomial)
          ultimately have "lpp f2 adds lpp g" by (simp add: adds_pm)
          with _ monomial_not_0 \<open>lpp g \<in> keys g\<close> have "punit.is_red {f1, f2} g"
            by (rule punit.is_red_addsI[simplified]) (simp_all add: f2_monomial)
          with assms(2) show False ..
        qed
        thus "0 < step (lpp g)" by simp
      qed
    qed simp
  qed
qed

text \<open>In @{cite MWW}, Theorem 4.3.2. lacks @{term "deg_pm (lpp f1)"} on the right-hand-side of the
  inequality. It is needed if @{prop "lpp f2 adds tpp f1"}, as can be seen in the following example
  (lexicographic order with @{prop "x \<prec> y"}):
  \<^item> @{prop "f1 = y^6 + x^2"},
  \<^item> @{prop "f2 = x"},
  \<^item> @{prop "punit.reduced_GB {f1, f2} = {y^6, x}"},
  \<^item> bound without @{term "deg_pm (lpp f1)"} is \<open>2\<close>,
  \<^item> actual degree goes up to \<open>6\<close> (@{prop "y^6 = 1 * f1 - x * f2"}, and @{prop "poly_deg (1 * f1) = 6"}).\<close>

lemma thm_4_3_2_aux_2:
  assumes "P = lcs (of_nat_pm (overlapshift (tpp f1))) overlap"
    and "d = max (deg_pm (lpp f1)) (to_nat (max (deg_pm P) (deg_pm (P - rat (step (tpp f1)) \<cdot> vect f1))))"
  shows "poly_deg f1 \<le> d"
proof (rule poly_deg_leI)
  let ?d = "max (deg_pm P) (deg_pm (P - rat (step (tpp f1)) \<cdot> vect f1))"
  have "is_int_pm (of_nat_pm (tpp f1))" by (intro nat_pm_is_int_pm of_nat_pm_is_nat_pm)
  hence 1: "is_int_pm (overlapshift_p (of_nat_pm (tpp f1)))" by (rule overlapshift_p_is_int_pm)
  have "f1 \<in> {f1, f2}" by simp
  hence eq1: "overlapshift_p (of_nat_pm (tpp f1)) = overlapshift_p' f1 (of_nat_pm (tpp f1))"
    and eq2: "step (tpp f1) = step' f1 (tpp f1)"
    and eq3: "overlapshift (tpp f1) = overlapshift' f1 (tpp f1)"
    using f1_pbinomial le_pm_refl by (rule overlapshift_p_alt1, rule step_alt1, rule overlapshift_alt1)
  have "deg_pm (overlapshift_p (of_nat_pm (tpp f1))) \<le>
          rat (to_nat (deg_pm (overlapshift_p (of_nat_pm (tpp f1)))))"
    by (intro of_nat_to_nat_ge Ints_deg 1)
  also have "\<dots> \<le> rat (deg_pm (to_nat_pm (overlapshift_p (of_nat_pm (tpp f1)))))"
    by (intro of_nat_mono to_nat_deg_pm_le 1)
  also have "\<dots> = rat (deg_pm (overlapshift (tpp f1)))" by (simp only: eq1 eq3 overlapshift'_def)
  finally have le1: "deg_pm (overlapshift_p (of_nat_pm (tpp f1))) \<le> rat (deg_pm (overlapshift (tpp f1)))" .

  fix t
  assume "t \<in> keys f1"
  also from f1_pbinomial have "\<dots> = {lpp f1, tpp f1}" by (rule punit.keys_proper_binomial)
  finally have "t = lpp f1 \<or> t = tpp f1" by simp
  thus "deg_pm t \<le> d"
  proof
    assume t: "t = lpp f1"
    show ?thesis unfolding t assms(2) by (rule max.cobounded1)
  next
    assume "t = tpp f1"
    hence "rat (deg_pm t) = deg_pm (of_nat_pm (tpp f1))" by (simp add: deg_of_nat_pm)
    also have "\<dots> \<le> deg_pm (overlapshift_p (of_nat_pm (tpp f1)) - rat (step (tpp f1)) \<cdot> vect f1)"
      by (simp add: eq1 eq2 overlapshift_p'_def step'_def)
    also have "\<dots> = deg_pm (overlapshift_p (of_nat_pm (tpp f1))) - rat (step (tpp f1)) * deg_pm (vect f1)"
      by (simp only: deg_pm_minus_group deg_pm_map_scale)
    also from le1 have "\<dots> \<le> rat (deg_pm (overlapshift (tpp f1))) - rat (step (tpp f1)) * deg_pm (vect f1)"
      by (rule diff_right_mono)
    also have "\<dots> = deg_pm (of_nat_pm (overlapshift (tpp f1)) - rat (step (tpp f1)) \<cdot> vect f1)"
      by (simp only: deg_pm_minus_group deg_of_nat_pm deg_pm_map_scale)
    also have "\<dots> \<le> deg_pm (P - rat (step (tpp f1)) \<cdot> vect f1)"
      unfolding assms(1) lcs_diff_distrib_left using lcs_ge_pm(1) by (rule deg_pm_mono_le)
    also have "\<dots> \<le> ?d" by (rule max.cobounded2)
    finally have "to_nat (rat (deg_pm t)) \<le> to_nat ?d" by (rule to_nat_mono)
    thus ?thesis by (simp only: to_nat_of_nat assms(2))
  qed
qed

theorem thm_4_3_2:
  assumes "P = lcs (of_nat_pm (overlapshift (tpp f1))) overlap"
    and "d = max (deg_pm (lpp f1)) (to_nat (max (deg_pm P) (deg_pm (P - rat (step (tpp f1)) \<cdot> vect f1))))"
  shows "gb_problem d"
proof (rule gb_problemI_reduced_GB_binomials)
  from f1_pbinomial show "is_binomial f1" by (rule proper_binomial_imp_binomial)
next
  from f2_monomial show "is_binomial f2" by (rule monomial_imp_binomial)
next
  from assms show "poly_deg f1 \<le> d" by (rule thm_4_3_2_aux_2)
next
  let ?d = "max (deg_pm P) (deg_pm (P - rat (step (tpp f1)) \<cdot> vect f1))"

  from f2_monomial have lp_f2: "lpp f2 = tpp f2" by (rule punit.lt_eq_tt_monomial)
  from f2_monomial have "monomial (lcf f2) (lpp f2) = f2" by (rule punit.monomial_eq_itself)
  hence "poly_deg f2 = poly_deg (monomial (lcf f2) (lpp f2))" by simp
  also have "\<dots> \<le> deg_pm (lpp f2)" by (simp add: poly_deg_monomial)
  also have "\<dots> = deg_pm (gcs (lpp f2) (tpp f2))" by (simp add: lp_f2)
  also have "rat \<dots> \<le> deg_pm overlap" unfolding overlap_alt' deg_of_nat_pm
    by (intro of_nat_mono deg_pm_mono_le lcs_ge_pm)
  also have "\<dots> \<le> deg_pm P" unfolding assms(1) using lcs_ge_pm(2) by (rule deg_pm_mono_le)
  finally have "rat (poly_deg f2) \<le> ?d" by simp
  hence "to_nat (rat (poly_deg f2)) \<le> to_nat ?d" by (rule to_nat_mono)
  hence "poly_deg f2 \<le> to_nat ?d" by (simp only: to_nat_of_nat)
  also have "\<dots> \<le> d" unfolding assms(2) by (rule max.cobounded2)
  finally show "poly_deg f2 \<le> d" .

  fix g
  assume "g \<in> punit.reduced_GB {f1, f2}" (is "_ \<in> ?G") and mpa: "membership_problem_assms f1 f2 g"
  have "0 \<notin> ?G" (is "0 \<notin> ?G") by (rule punit.reduced_GB_nonzero_finite) simp
  with \<open>g \<in> ?G\<close> have "g \<noteq> 0" by blast
  hence "lpp g \<in> keys g" by (rule punit.lt_in_keys)
  have tp1_is_int: "is_int_pm (of_nat_pm (tpp f1))" by (intro nat_pm_is_int_pm of_nat_pm_is_nat_pm)
  from mpa have irred: "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
  with \<open>g \<in> ?G\<close> show "\<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d"
  proof (rule thm_4_3_2_aux_1)
    assume "is_monomial g" and "tpp f1 adds lpp g" and "0 < step (lpp g)"
      and le1: "overlap \<unlhd> of_nat_pm (overlapshift (lpp g))"
      and eq1: "of_nat_pm (overlapshift (lpp g)) = of_nat_pm (lpp g) + rat (step (lpp g)) \<cdot> vect f1"
    from this(2) have le2: "tpp f1 \<unlhd> lpp g" by (simp only: adds_pm)
    with _ f1_pbinomial have "step (lpp g) \<le> step (tpp f1)" by (rule lem_4_2_1) simp
    from \<open>0 < step (lpp g)\<close> have eq2: "rat (step (lpp g) - Suc 0) = rat (step (lpp g)) - 1" by simp

    define Q where "Q = lcs (of_nat_pm (tpp f1) + rat (step (lpp g)) \<cdot> vect f1) overlap"
    define Q' where "Q' = Q - rat (step (lpp g)) \<cdot> vect f1"
    have "Q \<unlhd> of_nat_pm (lpp g) + rat (step (lpp g)) \<cdot> vect f1" unfolding Q_def
      by (intro lcs_le_pm le_pm_mono_plus_right) (simp add: le_of_nat_pm le2, simp only: le1 flip: eq1)
    hence "Q' \<unlhd> of_nat_pm (lpp g) + rat (step (lpp g)) \<cdot> vect f1 - rat (step (lpp g)) \<cdot> vect f1"
      unfolding Q'_def by (rule le_pm_mono_minus)
    hence "Q' \<unlhd> of_nat_pm (lpp g)" by simp
    hence "to_nat_pm Q' adds lpp g" by (auto simp: adds_pm dest: to_nat_pm_mono)

    have "of_nat_pm (tpp f1) + rat (step (lpp g)) \<cdot> vect f1 \<unlhd> Q" unfolding Q_def by (rule lcs_ge_pm)
    hence "of_nat_pm (tpp f1) + rat (step (lpp g)) \<cdot> vect f1 - rat (step (lpp g) - 1) \<cdot> vect f1 \<unlhd>
            Q - rat (step (lpp g) - 1) \<cdot> vect f1"
      and "of_nat_pm (tpp f1) + rat (step (lpp g)) \<cdot> vect f1 - rat (step (lpp g)) \<cdot> vect f1 \<unlhd> Q'"
      unfolding Q'_def by (rule le_pm_mono_minus)+
    hence le3: "of_nat_pm (lpp f1) \<unlhd> Q - rat (step (lpp g) - 1) \<cdot> vect f1" and "of_nat_pm (tpp f1) \<unlhd> Q'"
      by (simp_all add: eq2 vect_alt algebra_simps)

    have "of_nat_pm (lpp f1) \<unlhd> Q"
    proof (rule le_pmI)
      fix y
      have "rat (lookup (lpp f1) y) \<le> lookup Q y"
      proof (rule ccontr)
        assume "\<not> rat (lookup (lpp f1) y) \<le> lookup Q y"
        hence "lookup Q y < rat (lookup (lpp f1) y)" by simp
        also from le3 have "\<dots> \<le> lookup Q y - rat (step (lpp g) - 1) * lookup (vect f1) y"
          by (auto dest!: le_pmD simp: lookup_of_nat_pm lookup_minus)
        finally have "rat (step (lpp g) - 1) * lookup (vect f1) y < 0" by simp
        hence "lookup (vect f1) y < 0" by (simp add: mult_less_0_iff)
        hence "lookup (lpp f1) y \<le> lookup (tpp f1) y" by (simp add: vect_alt lookup_minus lookup_of_nat_pm)
        hence "rat (lookup (lpp f1) y) \<le> lookup Q y"
          by (simp add: Q_def lookup_lcs_fun lcs_fun_def overlap_alt lookup_gcs_fun gcs_fun lookup_of_nat_pm)
        also have "\<dots> < rat (lookup (lpp f1) y)" by fact
        finally show False ..
      qed
      thus "lookup (of_nat_pm (lpp f1)) y \<le> lookup Q y" by (simp only: lookup_of_nat_pm)
    qed

    from tp1_is_int Ints_of_nat have "is_int_pm Q" unfolding Q_def
      by (intro lcs_is_int_pm overlap_is_int_pm plus_is_int_pm map_scale_is_int_pm vect_is_int_pm)
    hence "is_nat_pm Q" using of_nat_pm_is_nat_pm \<open>of_nat_pm (lpp f1) \<unlhd> Q\<close> by (rule int_pm_is_nat_pmI)

    from \<open>is_int_pm Q\<close> Ints_of_nat have "is_int_pm Q'"
      unfolding Q'_def by (intro minus_is_int_pm map_scale_is_int_pm vect_is_int_pm)
    hence "is_nat_pm Q'" using of_nat_pm_is_nat_pm \<open>of_nat_pm (tpp f1) \<unlhd> Q'\<close> by (rule int_pm_is_nat_pmI)

    obtain a where "a \<in> ideal {f1, f2}" and "a \<noteq> 0" and lp_a: "lpp a = to_nat_pm Q'"
    proof -
      from f1_pbinomial have "is_binomial f1" by (rule proper_binomial_imp_binomial)
      moreover have "associated f1 (to_nat_pm Q) (to_nat_pm Q') (step (lpp g))"
        using \<open>is_nat_pm Q\<close> \<open>is_nat_pm Q'\<close>
        by (simp add: associated_alt_rat of_nat_pm_comp_to_nat_pm Q'_def)
      moreover from \<open>0 < step (lpp g)\<close> have "step (lpp g) \<noteq> 0" by simp
      moreover from \<open>of_nat_pm (lpp f1) \<unlhd> Q\<close> have "lpp f1 adds to_nat_pm Q"
        by (auto simp: adds_pm dest: to_nat_pm_mono)
      moreover from \<open>of_nat_pm (tpp f1) \<unlhd> Q'\<close> have "tpp f1 adds to_nat_pm Q'"
        by (auto simp: adds_pm dest: to_nat_pm_mono)
      ultimately obtain q where keys_q: "keys (q * f1) = {to_nat_pm Q, to_nat_pm Q'}"
        by (rule associated_adds_obtains_cofactor_keys)
      define c where "c = - lookup (q * f1) (to_nat_pm Q) / lcf f2"
      from f2_monomial have "lcf f2 \<noteq> 0" by (intro punit.lc_not_0 monomial_not_0)
      with keys_q have "c \<noteq> 0" by (simp add: c_def)

      have "lpp f2 = gcs (lpp f2) (tpp f2)" by (simp add: lp_f2)
      also have "of_nat_pm \<dots> \<unlhd> overlap" by (fact gcs_le_overlap')
      also have "\<dots> \<unlhd> Q" unfolding Q_def by (rule lcs_ge_pm)
      finally have "of_nat_pm (lpp f2) \<unlhd> Q" .
      hence "lpp f2 adds to_nat_pm Q" by (auto simp: adds_pm dest: to_nat_pm_mono)
      then obtain t where t: "to_nat_pm Q = t + lpp f2" by (rule addsE) (simp only: add.commute)
      define b where "b = punit.monom_mult c t f2"
      moreover from f2_monomial have "keys f2 = {lpp f2}" by (rule punit.keys_monomial)
      ultimately have keys_b: "keys b = {to_nat_pm Q}"
        using \<open>c \<noteq> 0\<close> by (simp add: punit.keys_monom_mult t)
      have "keys (q * f1 + b) \<subseteq> keys (q * f1) \<union> keys b" by (fact keys_add_subset)
      also have "\<dots> = {to_nat_pm Q, to_nat_pm Q'}" by (simp add: keys_q keys_b)
      finally have sub1: "keys (q * f1 + b) \<subseteq> {to_nat_pm Q, to_nat_pm Q'}" .
      from \<open>c \<noteq> 0\<close> have "lookup b (to_nat_pm Q) = c * lcf f2"
        by (simp add: b_def t punit.lookup_monom_mult_plus[simplified] punit.lc_def)
      also from \<open>lcf f2 \<noteq> 0\<close> have "\<dots> = - lookup (q * f1) (to_nat_pm Q)" by (simp add: c_def)
      finally have "to_nat_pm Q \<notin> keys (q * f1 + b)" by (simp add: lookup_add)
      moreover have "to_nat_pm Q' \<in> keys (q * f1 + b)"
      proof (intro in_keys_plusI1 notI)
        assume "to_nat_pm Q' \<in> keys b"
        hence "to_nat_pm Q' = to_nat_pm Q" by (simp add: keys_b)
        with \<open>is_nat_pm Q\<close> \<open>is_nat_pm Q'\<close> have "Q = Q'" by (metis of_nat_pm_comp_to_nat_pm)
        with \<open>0 < step (lpp (g))\<close> have "vect f1 = 0" by (simp add: Q'_def map_scale_eq_0_iff)
        hence "lpp f1 = tpp f1" by (simp add: vect_alt)
        also from f1_pbinomial have "\<dots> \<prec> lpp f1" by (rule punit.lt_gr_tt_binomial)
        finally show False ..
      qed (simp add: keys_q)
      ultimately have keys: "keys (q * f1 + b) = {to_nat_pm Q'}" using sub1 by blast
      show ?thesis
      proof
        have "q * f1 \<in> ideal {f1, f2}" by (intro ideal.span_scale ideal.span_base) simp
        moreover have "b \<in> ideal {f1, f2}" unfolding b_def
          by (intro punit.pmdl_closed_monom_mult[simplified] ideal.span_base) simp
        ultimately show "q * f1 + b \<in> ideal {f1, f2}" by (rule ideal.span_add)
      next
        from keys show "q * f1 + b \<noteq> 0" by auto

        thus "lpp (q * f1 + b) = to_nat_pm Q'" by (simp add: punit.lt_def keys)
      qed
    qed

    have "to_nat_pm Q' = lpp g"
      using _ \<open>a \<in> ideal {f1, f2}\<close> \<open>a \<noteq> 0\<close> \<open>g \<in> ?G\<close> \<open>lpp g \<in> keys g\<close> \<open>to_nat_pm Q' adds lpp g\<close>
      unfolding lp_a[symmetric] by (rule punit.reduced_GB_lt_addsD_finite(2)[simplified]) simp
    from this[symmetric] \<open>is_nat_pm Q'\<close> have eq4: "of_nat_pm (lpp g) = Q'"
      by (simp only: of_nat_pm_comp_to_nat_pm)
    hence eq3: "of_nat_pm (overlapshift (lpp g)) = Q" by (simp add: eq1 Q'_def)

    have "membership_problem_concl f1 f2 g (max (deg_pm (lpp g)) (deg_pm (overlapshift (lpp g))))"
      (is "membership_problem_concl _ _ _ ?a") using f1_pbinomial f2_monomial mpa by (rule thm_3_2_1)
    then obtain q1 q2 where "g = q1 * f1 + q2 * f2" and deg1: "poly_deg (q1 * f1) \<le> ?a"
      and deg2: "poly_deg (q2 * f2) \<le> ?a" by (auto simp: membership_problem_concl_def)

    have "f1 \<in> {f1, f2}" by simp
    hence "Q \<unlhd> P" unfolding Q_def assms(1) by (rule lem_4_3_1) fact+
    hence "deg_pm Q \<le> deg_pm P" by (rule deg_pm_mono_le)

    have "rat ?a = max (deg_pm (of_nat_pm (lpp g))) (deg_pm (of_nat_pm (overlapshift (lpp g))))"
      (is "_ = max ?b ?c") by (simp only: of_nat_max deg_of_nat_pm)
    also have "\<dots> \<le> ?d"
    proof (cases "0 \<le> deg_pm (vect f1)")
      case True
      hence "?b \<le> ?c" by (simp add: eq1 deg_pm_plus deg_pm_map_scale)
      hence "max ?b ?c = ?c" by simp
      also have "\<dots> \<le> deg_pm P" unfolding eq3 by fact
      also have "\<dots> \<le> ?d" by (rule max.cobounded1)
      finally show ?thesis .
    next
      case False
      hence "deg_pm (vect f1) < 0" by simp
      hence "?c \<le> ?b" by (simp add: eq1 deg_pm_plus deg_pm_map_scale mult_le_0_iff)
      from this(1) have "max ?b ?c = ?b" by simp
      also have "\<dots> = deg_pm Q - rat (step (lpp g)) * deg_pm (vect f1)"
        by (simp only: Q'_def eq4 deg_pm_minus_group deg_pm_map_scale)
      also have "\<dots> \<le> deg_pm Q - rat (step (tpp f1)) * deg_pm (vect f1)"
        using \<open>deg_pm (vect f1) < 0\<close> \<open>step (lpp g) \<le> step (tpp f1)\<close> by simp
      also from \<open>deg_pm Q \<le> deg_pm P\<close> have "\<dots> \<le> deg_pm (P - rat (step (tpp f1)) \<cdot> vect f1)"
        by (simp add: deg_pm_minus deg_pm_map_scale)
      also have "\<dots> \<le> ?d" by (rule max.cobounded2)
      finally show ?thesis .
    qed
    finally have "to_nat (rat ?a) \<le> to_nat ?d" by (rule to_nat_mono)
    hence "?a \<le> to_nat ?d" by (simp only: to_nat_of_nat)

    show ?thesis
    proof (intro exI conjI)
      from deg1 \<open>?a \<le> to_nat ?d\<close> have "poly_deg (q1 * f1) \<le> to_nat ?d" by (rule le_trans)
      also have "\<dots> \<le> d" unfolding assms(2) by (rule max.cobounded2)
      finally show "poly_deg (q1 * f1) \<le> d" .
    next
      from deg2 \<open>?a \<le> to_nat ?d\<close> have "poly_deg (q2 * f2) \<le> to_nat ?d" by (rule le_trans)
      also have "\<dots> \<le> d" unfolding assms(2) by (rule max.cobounded2)
      finally show "poly_deg (q2 * f2) \<le> d" .
    qed fact
  qed
qed

end

subsection \<open>Two Parallel Binomials\<close>

context
  assumes parallel: "parallel_binomials f1 f2"
begin

text \<open>The following theorem is the analogue of lemma \<open>thm_3_2_2_aux_1\<close> for proper binomials:\<close>

lemma thm_4_4_1_aux_1:
  assumes "g \<in> ideal {f1, f2}" and "is_proper_binomial g" and "monomial 1 ` keys g \<inter> ideal {f1, f2} = {}"
  obtains q1 q2 where "g = q1 * f1 + q2 * f2"
    and "\<And>f s t. f \<in> {f1, f2} \<Longrightarrow> (s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2) \<Longrightarrow>
            \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f"
proof -
  from assms(1) obtain q1' q2' where g: "g = q1' * f1 + q2' * f2" by (rule idealE_2)
  define S1 where "S1 = {t. \<forall>s\<in>keys f1. \<forall>l. of_nat_pm (t + s) \<noteq> of_nat_pm (tpp g) + l \<cdot> vect f1}"
  define S2 where "S2 = {t. \<forall>s\<in>keys f2. \<forall>l. of_nat_pm (t + s) \<noteq> of_nat_pm (tpp g) + l \<cdot> vect f1}"
  define q1 where "q1 = except q1' S1"
  define q2 where "q2 = except q2' S2"
  from parallel have "parallel_binomials f2 f1" by (rule parallel_binomials_sym)
  then obtain m where "0 < m" and m: "vect f2 = m \<cdot> vect f1" by (rule parallel_binomialsE_vect)
  have 1: "P" if "s \<in> keys q1" and "t \<in> keys f1"
    and "\<And>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f1 \<Longrightarrow> P" for s t P
  proof -
    from that(1) have "s \<in> keys q1'" and "s \<notin> S1" by (simp_all add: q1_def keys_except)
    from this(2) obtain t0 l where "t0 \<in> keys f1"
      and eq1: "of_nat_pm (s + t0) = of_nat_pm (tpp g) + l \<cdot> vect f1" by (auto simp: S1_def)
    from parallel have "is_proper_binomial f1" by (rule parallel_binomialsD)
    moreover note \<open>t0 \<in> keys f1\<close> that(2)
    ultimately obtain l' where eq2: "of_nat_pm t = of_nat_pm t0 + l' \<cdot> vect f1"
      by (rule proper_binomial_cases)
    show ?thesis
    proof (rule that(3))
      have "of_nat_pm (s + t) = of_nat_pm (s + t0) + l' \<cdot> vect f1" by (simp add: of_nat_pm_plus eq2)
      also have "\<dots> = of_nat_pm (tpp g) + (l + l') \<cdot> vect f1" by (simp add: eq1 map_scale_distrib_right)
      finally show "of_nat_pm (s + t) = of_nat_pm (tpp g) + (l + l') \<cdot> vect f1" .
    qed
  qed
  have 2: "P" if "s \<in> keys q2" and "t \<in> keys f2"
    and "\<And>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f1 \<Longrightarrow> P" for s t P
  proof -
    from that(1) have "s \<in> keys q2'" and "s \<notin> S2" by (simp_all add: q2_def keys_except)
    from this(2) obtain t0 l where "t0 \<in> keys f2"
      and eq1: "of_nat_pm (s + t0) = of_nat_pm (tpp g) + l \<cdot> vect f1" by (auto simp: S2_def)
    from parallel have "is_proper_binomial f2" by (rule parallel_binomialsD)
    moreover note \<open>t0 \<in> keys f2\<close> that(2)
    ultimately obtain l' where eq2: "of_nat_pm t = of_nat_pm t0 + l' \<cdot> vect f2"
      by (rule proper_binomial_cases)
    show ?thesis
    proof (rule that(3))
      have "of_nat_pm (s + t) = of_nat_pm (s + t0) + l' \<cdot> vect f2" by (simp add: of_nat_pm_plus eq2)
      also have "\<dots> = of_nat_pm (tpp g) + (l + l' * m) \<cdot> vect f1"
        by (simp add: m eq1 map_scale_distrib_right map_scale_assoc)
      finally show "of_nat_pm (s + t) = of_nat_pm (tpp g) + (l + l' * m) \<cdot> vect f1" .
    qed
  qed
  show ?thesis
  proof
    from assms(2) have "g \<noteq> 0" and keys_g: "keys g = {lpp g, tpp g}"
      by (rule proper_binomial_not_0, rule punit.keys_proper_binomial)
    let ?P = "\<lambda>t l. of_nat_pm t = of_nat_pm (tpp g) + l \<cdot> vect f1"
    have 3: "lookup (q1 * f1 + q2 * f2) t = lookup g t" if "?P t l" for t l
    proof -
      have "lookup (q1 * f1) t = lookup (q1' * f1) t" unfolding lookup_times
      proof (intro sum.mono_neutral_cong_left ballI)
        fix s
        assume "s \<in> keys q1' - keys q1"
        hence "s \<in> S1" by (auto simp: q1_def keys_except)
        hence "s0 \<in> keys f1 \<Longrightarrow> of_nat_pm (s + s0) \<noteq> (of_nat_pm t :: _ \<Rightarrow>\<^sub>0 rat)" for s0
          by (simp add: that S1_def)
        hence "\<And>s0. s0 \<in> keys f1 \<Longrightarrow> t \<noteq> s + s0" by auto
        hence "(\<Sum>v\<in>keys f1. lookup f1 v when t = s + v) = 0" by (auto intro!: sum.neutral)
        thus "lookup q1' s * (\<Sum>v\<in>keys f1. lookup f1 v when t = s + v) = 0" by simp
      next
        fix s
        assume "s \<in> keys q1"
        hence "s \<notin> S1" by (simp add: q1_def keys_except)
        hence "lookup q1 s = lookup q1' s" by (simp add: q1_def lookup_except)
        thus "lookup q1 s * (\<Sum>v\<in>keys f1. lookup f1 v when t = s + v) =
              lookup q1' s * (\<Sum>v\<in>keys f1. lookup f1 v when t = s + v)"
          by (simp only:)
      qed (auto simp: q1_def keys_except)
      moreover have "lookup (q2 * f2) t = lookup (q2' * f2) t" unfolding lookup_times
      proof (intro sum.mono_neutral_cong_left ballI)
        fix s
        assume "s \<in> keys q2' - keys q2"
        hence "s \<in> S2" by (auto simp: q2_def keys_except)
        hence "s0 \<in> keys f2 \<Longrightarrow> of_nat_pm (s + s0) \<noteq> (of_nat_pm t :: _ \<Rightarrow>\<^sub>0 rat)" for s0
          by (simp add: that S2_def)
        hence "\<And>s0. s0 \<in> keys f2 \<Longrightarrow> t \<noteq> s + s0" by auto
        hence "(\<Sum>v\<in>keys f2. lookup f2 v when t = s + v) = 0" by (auto intro!: sum.neutral)
        thus "lookup q2' s * (\<Sum>v\<in>keys f2. lookup f2 v when t = s + v) = 0" by simp
      next
        fix s
        assume "s \<in> keys q2"
        hence "s \<notin> S2" by (simp add: q2_def keys_except)
        hence "lookup q2 s = lookup q2' s" by (simp add: q2_def lookup_except)
        thus "lookup q2 s * (\<Sum>v\<in>keys f2. lookup f2 v when t = s + v) =
              lookup q2' s * (\<Sum>v\<in>keys f2. lookup f2 v when t = s + v)"
          by (simp only:)
      qed (auto simp: q2_def keys_except)
      ultimately show ?thesis by (simp only: g lookup_add)
    qed
    have 4: "\<exists>l. ?P t l" if "t \<in> keys (q1 * f1 + q2 * f2)" for t
    proof (rule ccontr)
      assume *: "\<nexists>l. ?P t l"
      hence "t \<noteq> tpp g" by (metis add.right_neutral map_scale_zero_left)
      have "t \<notin> keys (q1 * f1)"
      proof
        assume "t \<in> keys (q1 * f1)"
        then obtain t1 t2 where "t1 \<in> keys q1" and "t2 \<in> keys f1" and t: "t = t1 + t2"
          by (rule in_keys_timesE)
        from this(1, 2) obtain l where "of_nat_pm t = of_nat_pm (tpp g) + l \<cdot> vect f1"
          unfolding t by (rule 1)
        with * show False by blast
      qed
      moreover have "t \<notin> keys (q2 * f2)"
      proof
        assume "t \<in> keys (q2 * f2)"
        then obtain t1 t2 where "t1 \<in> keys q2" and "t2 \<in> keys f2" and t: "t = t1 + t2"
          by (rule in_keys_timesE)
        from this(1, 2) obtain l where "of_nat_pm t = of_nat_pm (tpp g) + l \<cdot> vect f1"
          unfolding t by (rule 2)
        with * show False by blast
      qed
      ultimately have "t \<notin> keys (q1 * f1 + q2 * f2)" by (simp add: lookup_add)
      thus False using that ..
    qed
    have eq1: "lookup (q1 * f1 + q2 * f2) (tpp g) = lookup g (tpp g)" by (rule 3[of _ 0]) simp
    also have "\<dots> \<noteq> 0" unfolding punit.tc_def[symmetric] using \<open>g \<noteq> 0\<close> by (rule punit.tc_not_0)
    finally have "tpp g \<in> keys (q1 * f1 + q2 * f2)" by simp
    have "keys (q1 * f1 + q2 * f2) \<subseteq> keys g"
    proof
      fix t
      assume t_in: "t \<in> keys (q1 * f1 + q2 * f2)"
      hence "\<exists>l. ?P t l" by (rule 4)
      then obtain l where "?P t l" ..
      hence "lookup (q1 * f1 + q2 * f2) t = lookup g t" by (rule 3)
      with t_in show "t \<in> keys g" by (simp only: in_keys_iff not_False_eq_True)
    qed
    have "\<exists>l. ?P (lpp g) l"
    proof (rule ccontr)
      assume "\<nexists>l. ?P (lpp g) l"
      with 4 have lp_not_in: "lpp g \<notin> keys (q1 * f1 + q2 * f2)" by blast
      have eq0: "keys (q1 * f1 + q2 * f2) = {tpp g}"
      proof (intro subset_antisym subsetI)
        fix t
        assume t_in: "t \<in> keys (q1 * f1 + q2 * f2)"
        also have "\<dots> \<subseteq> keys g" by fact
        finally have "t \<in> keys g" .
        moreover from lp_not_in t_in have "t \<noteq> lpp g" by blast
        ultimately show "t \<in> {tpp g}" by (simp add: keys_g)
      next
        fix t
        assume "t \<in> {tpp g}"
        with \<open>tpp g \<in> keys (q1 * f1 + q2 * f2)\<close> show "t \<in> keys (q1 * f1 + q2 * f2)" by simp
      qed
      moreover define c where "c = lookup (q1 * f1 + q2 * f2) (tpp g)"
      moreover have "c \<noteq> 0" by (simp add: c_def eq0)
      ultimately have "q1 * f1 + q2 * f2 = monomial c (tpp g)"
        by (metis (mono_tags, lifting) keys_single lookup_not_eq_zero_eq_in_keys lookup_single_eq
            lookup_single_not_eq poly_mapping_keys_eqI)
      with \<open>c \<noteq> 0\<close> have "monomial 1 (tpp g) = punit.monom_mult (1 / c) 0 (q1 * f1 + q2 * f2)"
        by (simp add: punit.monom_mult_monomial)
      also from idealI_2 have "\<dots> \<in> ideal {f1, f2}" by (rule punit.pmdl_closed_monom_mult[simplified])
      finally have "monomial 1 (tpp g) \<in> ideal {f1, f2}" .
      moreover from punit.tt_in_keys have "monomial 1 (tpp g) \<in> monomial 1 ` keys g"
        by (rule imageI) fact
      ultimately have "monomial 1 (tpp g) \<in> monomial 1 ` keys g \<inter> ideal {f1, f2}" by simp
      thus False by (simp add: assms(3))
    qed
    then obtain l where "?P (lpp g) l" ..
    hence eq2: "lookup (q1 * f1 + q2 * f2) (lpp g) = lookup g (lpp g)" by (rule 3)
    also have "\<dots> \<noteq> 0" unfolding punit.lc_def[symmetric] using \<open>g \<noteq> 0\<close> by (rule punit.lc_not_0)
    finally have "keys g = keys (q1 * f1 + q2 * f2)"
      using \<open>tpp g \<in> keys (q1 * f1 + q2 * f2)\<close> \<open>keys (q1 * f1 + q2 * f2) \<subseteq> keys g\<close>
      by (auto simp: keys_g)
    thus "g = q1 * f1 + q2 * f2"
    proof (rule poly_mapping_keys_eqI)
      fix t
      assume "t \<in> keys g"
      thus "lookup g t = lookup (q1 * f1 + q2 * f2) t" by (auto simp: keys_g eq1 eq2)
    qed
  next
    fix f s t
    assume "f \<in> {f1, f2}"
    hence disj: "f = f1 \<or> f = f2" by simp
    from parallel obtain m' where m': "vect f1 = m' \<cdot> vect f2" by (rule parallel_binomialsE_vect)
    assume "(s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2)"
    thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f"
    proof
      assume "s \<in> keys q1 \<and> t \<in> keys f1"
      hence "s \<in> keys q1" and "t \<in> keys f1" by simp_all
      then obtain l where eq: "of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f1" by (rule 1)
      from disj show ?thesis
      proof
        assume "f = f1"
        from eq show ?thesis unfolding \<open>f = f1\<close> ..
      next
        assume "f = f2"
        from eq show ?thesis unfolding \<open>f = f2\<close> m' map_scale_assoc ..
      qed
    next
      assume "s \<in> keys q2 \<and> t \<in> keys f2"
      hence "s \<in> keys q2" and "t \<in> keys f2" by simp_all
      then obtain l where eq: "of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f1" by (rule 2)
      from disj show ?thesis
      proof
        assume "f = f1"
        from eq show ?thesis unfolding \<open>f = f1\<close> ..
      next
        assume "f = f2"
        from eq show ?thesis unfolding \<open>f = f2\<close> m' map_scale_assoc ..
      qed
    qed
  qed
qed

lemma thm_4_4_1_1:
  assumes "deg_pm (tpp f1) < deg_pm (lpp f1)"
    and "V = vect f1 + vect f2" and "P1 = lcs (of_nat_pm (overlapshift (tpp f1)) + V) overlap"
    and "P2 = lcs (of_nat_pm (overlapshift (tpp f2)) + V) overlap"
    and "d = max (deg_pm P1) (deg_pm P2)"
  shows "gb_problem (to_nat d)"
proof (rule gb_problemI_reduced_GB_binomials)
  from parallel have f1_pbinomial: "is_proper_binomial f1" by (rule parallel_binomialsD)
  thus "is_binomial f1" by (rule proper_binomial_imp_binomial)
  hence keys_f1: "keys f1 = {lpp f1, tpp f1}" by (rule punit.keys_binomial)

  from parallel have f2_pbinomial: "is_proper_binomial f2" by (rule parallel_binomialsD)
  thus "is_binomial f2" by (rule proper_binomial_imp_binomial)
  hence keys_f2: "keys f2 = {lpp f2, tpp f2}" by (rule punit.keys_binomial)

  from assms(1) have "0 < deg_pm (vect f1)" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)
  have "0 < deg_pm (vect f2)"
  proof -
    from parallel obtain r where "0 < r" and "vect f1 = r \<cdot> vect f2" by (rule parallel_binomialsE_vect)
    with \<open>0 < deg_pm (vect f1)\<close> show ?thesis by (simp add: deg_pm_map_scale zero_less_mult_iff)
  qed
  hence "deg_pm (tpp f2) < deg_pm (lpp f2)" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)

  show "poly_deg f1 \<le> to_nat d"
  proof (rule poly_deg_leI)
    fix t
    assume "t \<in> keys f1"
    hence "t = lpp f1 \<or> t = tpp f1" by (simp add: keys_f1)
    moreover have "deg_pm (lpp f1) \<le> to_nat d"
    proof -
      have *: "deg_pm (of_nat_pm (tpp f1) + rat (step (tpp f1)) \<cdot> vect f1) \<le>
                  deg_pm (of_nat_pm (overlapshift (tpp f1)))"
        using overlapshift_tpp_ge_pm by (rule deg_pm_mono_le) (simp_all add: f1_pbinomial)
      have V: "V = vect f2 + of_nat_pm (lpp f1) - of_nat_pm (tpp f1)" by (simp add: assms(2) vect_alt)
      have "deg_pm (of_nat_pm (lpp f1)) \<le> deg_pm (of_nat_pm (tpp f1) + rat (step (tpp f1)) \<cdot> vect f1) + deg_pm V"
        using \<open>0 < deg_pm (vect f1)\<close> \<open>0 < deg_pm (vect f2)\<close>
        by (simp add: deg_pm_plus deg_pm_minus deg_pm_map_scale V)
      also from * have "\<dots> \<le> deg_pm (of_nat_pm (overlapshift (tpp f1))) + deg_pm V"
        by (rule add_right_mono)
      also have "\<dots> = deg_pm (of_nat_pm (overlapshift (tpp f1)) + V)" by (simp only: deg_pm_plus)
      also have "\<dots> \<le> deg_pm P1" unfolding assms(3) by (intro deg_pm_mono_le lcs_ge_pm)
      also have "\<dots> \<le> d" unfolding assms(5) by (rule max.cobounded1)
      finally have "to_nat (deg_pm (of_nat_pm (lpp f1) :: _ \<Rightarrow>\<^sub>0 rat)) \<le> to_nat d" by (rule to_nat_mono)
      thus ?thesis by (simp only: deg_of_nat_pm to_nat_of_nat)
    qed
    moreover from assms(1) this have "deg_pm (tpp f1) \<le> to_nat d" by simp
    ultimately show "deg_pm t \<le> to_nat d" by blast
  qed

  show "poly_deg f2 \<le> to_nat d"
  proof (rule poly_deg_leI)
    fix t
    assume "t \<in> keys f2"
    hence "t = lpp f2 \<or> t = tpp f2" by (simp add: keys_f2)
    moreover have "deg_pm (lpp f2) \<le> to_nat d"
    proof -
      have *: "deg_pm (of_nat_pm (tpp f2) + rat (step (tpp f2)) \<cdot> vect f2) \<le>
                  deg_pm (of_nat_pm (overlapshift (tpp f2)))"
        using overlapshift_tpp_ge_pm by (rule deg_pm_mono_le) (simp_all add: f2_pbinomial)
      have V: "V = vect f1 + of_nat_pm (lpp f2) - of_nat_pm (tpp f2)" by (simp add: assms(2) vect_alt)
      have "deg_pm (of_nat_pm (lpp f2)) \<le> deg_pm (of_nat_pm (tpp f2) + rat (step (tpp f2)) \<cdot> vect f2) + deg_pm V"
        using \<open>0 < deg_pm (vect f1)\<close> \<open>0 < deg_pm (vect f2)\<close>
        by (simp add: deg_pm_plus deg_pm_minus deg_pm_map_scale V)
      also from * have "\<dots> \<le> deg_pm (of_nat_pm (overlapshift (tpp f2))) + deg_pm V"
        by (rule add_right_mono)
      also have "\<dots> = deg_pm (of_nat_pm (overlapshift (tpp f2)) + V)" by (simp only: deg_pm_plus)
      also have "\<dots> \<le> deg_pm P2" unfolding assms(4) by (intro deg_pm_mono_le lcs_ge_pm)
      also have "\<dots> \<le> d" unfolding assms(5) by (rule max.cobounded2)
      finally have "to_nat (deg_pm (of_nat_pm (lpp f2) :: _ \<Rightarrow>\<^sub>0 rat)) \<le> to_nat d" by (rule to_nat_mono)
      thus ?thesis by (simp only: deg_of_nat_pm to_nat_of_nat)
    qed
    moreover from \<open>deg_pm (tpp f2) < deg_pm (lpp f2)\<close> this have "deg_pm (tpp f2) \<le> to_nat d" by simp
    ultimately show "deg_pm t \<le> to_nat d" by blast
  qed

  fix g
  assume "g \<in> punit.reduced_GB {f1, f2}" (is "g \<in> ?G") and mpa: "membership_problem_assms f1 f2 g"
  from mpa have g_in: "g \<in> ideal {f1, f2}" and "is_binomial g" by (rule membership_problem_assmsD)+
  note \<open>is_binomial f1\<close> \<open>is_binomial f2\<close> g_in
  moreover from mpa have "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
  moreover from binomial_not_0 have "tpp g \<in> keys g" by (rule punit.tt_in_keys) fact
  ultimately obtain h1 k u where "h1 \<in> {f1, f2}" and "is_proper_binomial h1" and "tpp h1 adds tpp g"
    and "associated h1 u (tpp g) k" and "overlap \<unlhd> of_nat_pm u" and "lpp h1 adds u"
    by (rule binomial_ideal_irredE_assoc)
  from this(1-5) have le1: "overlap \<unlhd> of_nat_pm (overlapshift (tpp g))"
    and eq1: "of_nat_pm (overlapshift (tpp g)) = of_nat_pm (tpp g) + rat (step (tpp g)) \<cdot> vect h1"
    by (rule overlapshift_is_above_overlap, rule of_nat_pm_overlapshift')
  from \<open>tpp h1 adds tpp g\<close> have le2: "tpp h1 \<unlhd> tpp g" by (simp only: adds_pm)
  from \<open>h1 \<in> {f1, f2}\<close> obtain h2 where f1_f2: "{f1, f2} = {h1, h2}" by blast
  with parallel have "parallel_binomials h2 h1" by (auto simp: doubleton_eq_iff parallel_binomials_sym)
  then obtain r where "0 < r" and "vect h2 = r \<cdot> vect h1" by (rule parallel_binomialsE_vect)
  from f1_f2 have V: "V = vect h1 + vect h2" by (auto simp: doubleton_eq_iff assms(2))

  obtain q1' q2' where "g = q1' * h1 + q2' * h2"
    and "\<And>s t. s \<in> keys q1' \<and> t \<in> keys h1 \<or> s \<in> keys q2' \<and> t \<in> keys h2 \<Longrightarrow>
              \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
  proof -
    from \<open>is_binomial g\<close> have "is_monomial g \<or> is_proper_binomial g" by (simp only: is_binomial_alt)
    then obtain q1 q2 where g: "g = q1 * f1 + q2 * f2"
      and *: "\<And>f s t. f \<in> {f1, f2} \<Longrightarrow> s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2 \<Longrightarrow>
                  \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f"
    proof
      assume "is_monomial g"
      hence lp_g: "lpp g = tpp g" by (rule punit.lt_eq_tt_monomial)
      from parallel \<open>is_monomial g\<close> g_in obtain q1 q2 where g: "g = q1 * f1 + q2 * f2"
        and "\<And>f s t. f \<in> {f1, f2} \<Longrightarrow> s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2 \<Longrightarrow>
                \<exists>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f" by (rule thm_3_2_2_aux_2) blast
      thus ?thesis unfolding lp_g ..
    next
      assume "is_proper_binomial g"
      with mpa have "monomial 1 ` keys g \<inter> ideal {f1, f2} = {}" by (rule membership_problem_assmsD)
      with g_in \<open>is_proper_binomial g\<close> obtain q1 q2 where g: "g = q1 * f1 + q2 * f2"
        and *: "\<And>f s t. f \<in> {f1, f2} \<Longrightarrow> s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2 \<Longrightarrow>
                    \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect f"
        by (rule thm_4_4_1_aux_1) blast
      thus ?thesis ..
    qed
    from f1_f2 show ?thesis unfolding doubleton_eq_iff
    proof (elim disjE conjE)
      assume "f1 = h1" and "f2 = h2"
      hence "g = q1 * h1 + q2 * h2" by (simp only: g)
      moreover from * have "\<And>s t. s \<in> keys q1 \<and> t \<in> keys h1 \<or> s \<in> keys q2 \<and> t \<in> keys h2 \<Longrightarrow>
                                \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
        by (auto simp: \<open>f1 = h1\<close> \<open>f2 = h2\<close>)
      ultimately show ?thesis ..
    next
      assume "f1 = h2" and "f2 = h1"
      hence "g = q2 * h1 + q1 * h2" by (simp only: g add.commute)
      moreover from * have "\<And>s t. s \<in> keys q2 \<and> t \<in> keys h1 \<or> s \<in> keys q1 \<and> t \<in> keys h2 \<Longrightarrow>
                                \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
        by (auto simp: \<open>f1 = h2\<close> \<open>f2 = h1\<close>)
      ultimately show ?thesis ..
    qed
  qed
  with parallel mpa f1_f2 \<open>vect h2 = r \<cdot> vect h1\<close> \<open>0 < r\<close> \<open>tpp h1 adds tpp g\<close> obtain q1 q2 l'
    where g: "g = q1 * h1 + q2 * h2" and "0 < l'" and "l' < rat (step (tpp g)) + 1 + r"
    and "of_nat_pm (lpp (q1 * h1)) = of_nat_pm (tpp g) + l' \<cdot> vect h1"
    and "\<And>s t. s \<in> keys q1 \<and> t \<in> keys h1 \<or> s \<in> keys q2 \<and> t \<in> keys h2 \<Longrightarrow>
            \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
    by (rule thm_3_2_2_aux_1) blast+
  from mpa f1_f2 have "membership_problem_assms h1 h2 g" by (auto simp: membership_problem_assms_def)
  hence "q1 * h1 \<noteq> 0" and "q2 * h2 \<noteq> 0" and lp_eq: "lpp (q1 * h1) = lpp (q2 * h2)"
    using g by (rule membership_problem_assms_rep)+

  define Q where "Q = lcs (of_nat_pm (tpp h1) + rat (step (tpp g)) \<cdot> vect h1 + V) overlap"

  (* I don't know whether the following is needed. *)
  define Q1 where "Q1 = Q - rat (step (tpp g)) \<cdot> vect h1 - V\<^sub>-"
  define Q2 where "Q2 = Q - rat (step (tpp g)) \<cdot> vect h1 - V\<^sub>+"
  from pos_comps_ge_zero le1 have "overlap \<unlhd> of_nat_pm (overlapshift (tpp g)) + V\<^sub>+"
    by (rule le_pm_increasing2)
  hence "Q \<unlhd> of_nat_pm (tpp g) + rat (step (tpp g)) \<cdot> vect h1 + V\<^sub>+" unfolding Q_def
    by (intro lcs_le_pm le_pm_mono_plus[where u=V] pos_comps_ge_self le_pm_mono_plus_right)
        (simp add: le_of_nat_pm le2, simp flip: eq1)
  hence "Q2 \<unlhd> of_nat_pm (tpp g) + rat (step (tpp g)) \<cdot> vect h1 + V\<^sub>+ - rat (step (tpp g)) \<cdot> vect h1 - V\<^sub>+"
    unfolding Q2_def by (intro le_pm_mono_minus)
  hence "Q2 \<unlhd> of_nat_pm (tpp g)" by simp
  hence "to_nat_pm Q2 adds tpp g" by (auto simp: adds_pm dest: to_nat_pm_mono)

  have "of_nat_pm (tpp h1) + rat (step (tpp g)) \<cdot> vect h1 + V \<unlhd> Q" unfolding Q_def by (rule lcs_ge_pm)
  hence "of_nat_pm (tpp h1) + rat (step (tpp g)) \<cdot> vect h1 + V - V \<unlhd> Q - V"
    and "of_nat_pm (tpp h1) + rat (step (tpp g)) \<cdot> vect h1 + V - rat (step (tpp g)) \<cdot> vect h1 - V\<^sub>+ \<unlhd> Q2"
  unfolding Q2_def apply (rule le_pm_mono_minus) sorry  (* should be true *)
  hence le3: "of_nat_pm (lpp h1) \<unlhd> Q - (rat (step (tpp g)) + 1 + r) \<cdot> vect h1" and "of_nat_pm (tpp h1) \<unlhd> Q2 + V\<^sub>-"
    sorry (*by (simp_all add: vect_alt algebra_simps)*)   (* should be true *)

  have "of_nat_pm (lpp h1) \<unlhd> Q"
  proof (rule le_pmI)
    fix y
    have "rat (lookup (lpp h1) y) \<le> lookup Q y"
    proof (rule ccontr)
      assume "\<not> rat (lookup (lpp h1) y) \<le> lookup Q y"
      hence "lookup Q y < rat (lookup (lpp h1) y)" by simp
      also from le3 have "\<dots> \<le> lookup Q y - (rat (step (tpp g)) + 1 + r) * lookup (vect h1) y"
        by (auto dest!: le_pmD simp: lookup_of_nat_pm lookup_minus)
      finally have "(rat (step (tpp g)) + 1 + r) * lookup (vect h1) y < 0" by simp
      with \<open>0 < r\<close> have "lookup (vect h1) y < 0" by (simp add: mult_less_0_iff)
      hence "lookup (lpp h1) y \<le> lookup (tpp h1) y" by (simp add: vect_alt lookup_minus lookup_of_nat_pm)
      hence "rat (lookup (lpp h1) y) \<le> lookup Q y"
        sorry
        (*by (simp add: Q_def lookup_lcs_fun lcs_fun_def overlap_alt lookup_gcs_fun gcs_fun lookup_of_nat_pm)*)
        (* should be true *)
      also have "\<dots> < rat (lookup (lpp h1) y)" by fact
      finally show False ..
    qed
    thus "lookup (of_nat_pm (lpp h1)) y \<le> lookup Q y" by (simp only: lookup_of_nat_pm)
  qed

  have "step (tpp g) \<le> step (tpp h1)" by (rule lem_4_2_1) fact+

  have 1: "poly_deg (q1 * h1) \<le> to_nat d" sorry

  have 2: "poly_deg (q2 * h2) \<le> to_nat d" sorry

  show "\<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> to_nat d \<and> poly_deg (q2 * f2) \<le> to_nat d"
    using f1_f2 1 2 by (fastforce simp: doubleton_eq_iff g add.commute)
qed

end

end (* two_binomials *)

subsection \<open>Two Linearly Independent Binomials\<close>

context two_binoms
begin

context
  fixes g
  assumes nparallel: "\<not> parallel_binomials f1 f2"
  assumes g_in: "g \<in> ideal {f1, f2}"
  assumes g_pbinomial: "is_proper_binomial g"
  assumes nadds_lpp: "\<And>f. f \<in> {f1, f2} \<Longrightarrow> \<not> lpp f adds lpp g"
  assumes nadds_tpp: "\<And>f. f \<in> {f1, f2} \<Longrightarrow> \<not> lpp f adds tpp g"
  assumes lpp_not_in: "monomial 1 (lpp g) \<notin> ideal {f1, f2}"
begin

text \<open>The assumptions do not necessarily hold for all proper binomials in the reduced Gr\"obner
  basis @{term G} of @{term "{f1, f2}"}. But, after replacing all elements @{prop "g \<in> G"} satisfying
  @{prop "lpp g = lpp f"} for some @{prop "f \<in> {f1, f2}"} by the respective @{term f}, the other
  binomials in @{term G} \<^emph>\<open>do\<close> satisfy the assumptions. And of course, the new set is still a
  Gr\"obner basis of @{term "{f1, f2}"}.
  Note that assumption \<open>lpp_not_in\<close> is satisfied because otherwise the trailing power-product would
  also be in the ideal, meaning there is another element @{term G} which reduces it -- contradicting
  the fact that @{term g} is reduced.\<close>

context
  fixes f f'
  assumes f_f': "{f1, f2} = {f, f'}"
begin

lemma exists_min_length_vpc:
  assumes "vect g = (rat k - rat l) \<cdot> vect f + (rat k' - rat l') \<cdot> vect f'"
  obtains zs where "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)"
    and "fst (hd zs) = of_nat_pm (lpp g)" and "snd (last zs) = of_nat_pm (tpp g)"
    and "l + num_shifts False zs f = k + num_shifts True zs f"
    and "l' + num_shifts False zs f' = k' + num_shifts True zs f'"
proof -
  obtain zs where zs_min: "min_length_vpc zs" and hd_zs: "fst (hd zs) = of_nat_pm (lpp g)"
    and last_zs: "snd (last zs) = of_nat_pm (tpp g)"
  proof -
    from g_in g_pbinomial lpp_not_in obtain zs' where "is_vpc zs'"
      and 1: "fst (hd zs') = of_nat_pm (lpp g)" and 2: "snd (last zs') = of_nat_pm (tpp g)"
      by (rule idealE_vpc)
    from this(1) obtain zs where "min_length_vpc zs" and "fst (hd zs) = of_nat_pm (lpp g)"
      and "snd (last zs) = of_nat_pm (tpp g)"
      unfolding 1[symmetric] 2[symmetric] by (rule vpcE_min_length_vpc)
    thus ?thesis ..
  qed
  from this(1) have "is_vpc zs" by (rule min_length_vpcD)
  hence "zs \<noteq> []" by (rule is_vpcD)
  from g_pbinomial have "tpp g \<prec> lpp g" by (rule punit.lt_gr_tt_binomial)
  hence zs_dist: "fst (hd zs) \<noteq> snd (last zs)" by (simp add: hd_zs last_zs)

  from f_f' f1_pbinomial f2_pbinomial have f_pbinomial: "is_proper_binomial f"
    and f'_pbinomial: "is_proper_binomial f'" by (auto simp: doubleton_eq_iff)
  from nparallel f_f' have nparallel': "\<not> parallel_binomials f f'"
    by (auto simp: doubleton_eq_iff dest: parallel_binomials_sym)
  from assms have "fst (hd zs) - (rat k - rat l) \<cdot> vect f - (rat k' - rat l') \<cdot> vect f' = snd (last zs)"
    by (simp add: vect_alt hd_zs last_zs algebra_simps)
  also from nparallel \<open>is_vpc zs\<close> have "\<dots> = fst (hd zs) +
                              (rat (num_shifts True zs f1) - rat (num_shifts False zs f1)) \<cdot> vect f1 +
                              (rat (num_shifts True zs f2) - rat (num_shifts False zs f2)) \<cdot> vect f2"
    by (rule vpc_snd_last_conv_vect)
  also from f_f' have "\<dots> = fst (hd zs) +
                              (rat (num_shifts True zs f) - rat (num_shifts False zs f)) \<cdot> vect f +
                              (rat (num_shifts True zs f') - rat (num_shifts False zs f')) \<cdot> vect f'"
    by (auto simp: doubleton_eq_iff)
  finally have "(rat (k + num_shifts True zs f) - rat (l + num_shifts False zs f)) \<cdot> vect f =
                (rat (l' + num_shifts False zs f') - rat (k' + num_shifts True zs f')) \<cdot> vect f'"
    by (simp add: algebra_simps)
  with f_pbinomial f'_pbinomial nparallel'
  have "rat (k + num_shifts True zs f) - rat (l + num_shifts False zs f) = 0"
    and "rat (l' + num_shifts False zs f') - rat (k' + num_shifts True zs f') = 0"
    by (rule not_parallel_binomialsD_vect)+
  hence "l + num_shifts False zs f = k + num_shifts True zs f"
    and "l' + num_shifts False zs f' = k' + num_shifts True zs f'" by simp_all
  with zs_min zs_dist hd_zs last_zs show ?thesis ..
qed

context
  fixes k
  assumes vect_g: "vect g = rat k \<cdot> vect f"
begin

lemma thm_4_5_2_aux_1: "k \<noteq> 0"
proof
  assume "k = 0"
  hence "vect g = 0" by (simp add: vect_g)
  hence "card (keys g) \<le> 1" by (simp add: vect_def fst_eq_snd_poly_point_iff)
  with g_pbinomial show False by (simp add: is_proper_binomial_def)
qed

lemma thm_4_5_2_aux_2:
  obtains zs where "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)"
    and "fst (hd zs) = of_nat_pm (lpp g)" and "snd (last zs) = of_nat_pm (tpp g)"
    and "num_shifts False zs f = k + num_shifts True zs f"
    and "num_shifts False zs f' = num_shifts True zs f'"
    and "hd zs \<in> pn_Nshifts True {f, f'}" and "last zs \<in> pn_Nshifts False {f, f'}"
proof -
  have "vect g = (rat k - rat 0) \<cdot> vect f + (rat 0 - rat 0) \<cdot> vect f'" by (simp add: vect_g)
  then obtain zs where zs_min: "min_length_vpc zs" and zs_dist: "fst (hd zs) \<noteq> snd (last zs)"
    and hd_zs: "fst (hd zs) = of_nat_pm (lpp g)" and last_zs: "snd (last zs) = of_nat_pm (tpp g)"
    and "0 + num_shifts False zs f = k + num_shifts True zs f"
    and "0 + num_shifts False zs f' = 0 + num_shifts True zs f'" by (rule exists_min_length_vpc)
  from this(5, 6) have num_neg_f: "num_shifts False zs f = k + num_shifts True zs f"
    and num_neg_f': "num_shifts False zs f' = num_shifts True zs f'" by simp_all

  from zs_min have "is_vpc zs" by (rule min_length_vpcD)
  hence "zs \<noteq> []" by (rule is_vpcD)
  have hd_zs_nneg: "hd zs \<notin> pn_Nshifts False {f, f'}"
  proof
    assume "hd zs \<in> pn_Nshifts False {f, f'}"
    hence "hd zs \<in> pn_Nshifts False {f1, f2}" by (simp only: f_f')
    then obtain h0 t where "h0 \<in> {f1, f2}" and "hd zs = t +\<^sub>N poly_point h0" by (rule pn_NshiftsE_neg)
    from this(2) have "fst (hd zs) = of_nat_pm (t + lpp h0)"
      by (simp add: nat_plus_point_pair_def poly_point_def of_nat_pm_plus)
    hence "lpp h0 adds lpp g" by (simp add: hd_zs)
    moreover from \<open>h0 \<in> {f1, f2}\<close> have "\<not> lpp h0 adds lpp g" by (rule nadds_lpp)
    ultimately show False by simp
  qed
  from \<open>zs \<noteq> []\<close> have "hd zs \<in> set zs" by simp
  also from \<open>is_vpc zs\<close> have "\<dots> \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  finally have "hd zs \<in> pn_Nshifts True {f, f'} \<union> pn_Nshifts False {f, f'}"
    by (simp only: f_f' Nshifts_def)
  with hd_zs_nneg have hd_zs_pos: "hd zs \<in> pn_Nshifts True {f, f'}" by simp

  have last_zs_npos: "last zs \<notin> pn_Nshifts True {f, f'}"
  proof
    assume "last zs \<in> pn_Nshifts True {f, f'}"
    hence "last zs \<in> pn_Nshifts True {f1, f2}" by (simp only: f_f')
    then obtain h0 t where "h0 \<in> {f1, f2}" and "last zs = t +\<^sub>N prod.swap (poly_point h0)"
      by (rule pn_NshiftsE_pos)
    from this(2) have "snd (last zs) = of_nat_pm (t + lpp h0)"
      by (simp add: nat_plus_point_pair_def poly_point_def of_nat_pm_plus)
    hence "lpp h0 adds tpp g" by (simp add: last_zs)
    moreover from \<open>h0 \<in> {f1, f2}\<close> have "\<not> lpp h0 adds tpp g" by (rule nadds_tpp)
    ultimately show False by simp
  qed
  from \<open>zs \<noteq> []\<close> have "last zs \<in> set zs" by simp
  also from \<open>is_vpc zs\<close> have "\<dots> \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  finally have "last zs \<in> pn_Nshifts True {f, f'} \<union> pn_Nshifts False {f, f'}"
    by (simp only: f_f' Nshifts_def)
  with last_zs_npos have "last zs \<in> pn_Nshifts False {f, f'}" by simp
  with zs_min zs_dist hd_zs last_zs num_neg_f num_neg_f' hd_zs_pos show ?thesis ..
qed

lemma thm_4_5_2_aux_3:
  assumes "overlap \<unlhd> of_nat_pm (lpp g)"
  obtains g' where "g' \<in> ideal {f1, f2}" and "lpp g' = lpp g" and "vect g' = vect f"
proof -
  have f_in: "f \<in> {f1, f2}" and f'_in: "f' \<in> {f1, f2}" by (simp_all add: f_f')
  from f_f' f1_pbinomial f2_pbinomial have f_pbinomial: "is_proper_binomial f"
    and f'_pbinomial: "is_proper_binomial f'" by (auto simp: doubleton_eq_iff)
  from nparallel f_f' have nparallel': "\<not> parallel_binomials f f'"
    by (auto simp: doubleton_eq_iff dest: parallel_binomials_sym)

  from thm_4_5_2_aux_1 have "1 \<le> rat k" by simp

  obtain zs where zs_min: "min_length_vpc zs" and zs_dist: "fst (hd zs) \<noteq> snd (last zs)"
    and hd_zs: "fst (hd zs) = of_nat_pm (lpp g)" and last_zs: "snd (last zs) = of_nat_pm (tpp g)"
    and num_neg_f: "num_shifts False zs f = k + num_shifts True zs f"
    and num_neg_f': "num_shifts False zs f' = num_shifts True zs f'"
    and hd_zs_pos: "hd zs \<in> pn_Nshifts True {f, f'}"
    and last_zs_neg: "last zs \<in> pn_Nshifts False {f, f'}" by (rule thm_4_5_2_aux_2)

  from zs_min have "is_vpc zs" by (rule min_length_vpcD)
  hence "zs \<noteq> []" by (rule is_vpcD)
  hence "hd zs \<in> set zs" and "last zs \<in> set zs" by simp_all
  from zs_min zs_dist obtain zs1 zs2 zs3 where zs: "zs = zs1 @ zs2 @ zs3"
    and part: "vpc_partition zs1 zs2 zs3" by (rule min_length_vpcE_partition)

  have "zs1 = []"
  proof (rule ccontr)
    assume "zs1 \<noteq> []"
    hence "hd zs1 \<in> set zs1" by simp
    with part have "\<not> overlap \<unlhd> fst (hd zs1)" by (rule vpc_partitionD1)
    moreover from assms \<open>zs1 \<noteq> []\<close> have "overlap \<unlhd> fst (hd zs1)" by (simp add: zs flip: hd_zs)
    ultimately show False ..
  qed
  hence zs: "zs = zs2 @ zs3" by (simp add: zs)
  have "zs2 \<noteq> []"
  proof
    assume "zs2 = []"
    from part obtain h' pos' where "h' \<in> {f1, f2}" and "set zs3 \<subseteq> pn_Nshifts pos' {h'}"
      and zs3_disjnt: "set zs3 \<inter> pn_Nshifts (\<not> pos') {h'} = {}" by (rule vpc_partitionD3)
    with \<open>zs2 = []\<close> have zs_sub: "set zs \<subseteq> pn_Nshifts pos' {h'}" by (simp add: zs)
    show False
    proof (cases pos')
      case True
      note \<open>last zs \<in> set zs\<close>
      also from zs_sub True have "set zs \<subseteq> pn_Nshifts True {h'}" by simp
      also from \<open>h' \<in> {f1, f2}\<close> have "\<dots> \<subseteq> pn_Nshifts True {f1, f2}"
        by (intro pn_Nshifts_mono) simp
      finally have "pn_Nshifts True {f1, f2} \<inter> pn_Nshifts False {f, f'} \<noteq> {}"
        using last_zs_neg by blast
      moreover have "pn_Nshifts True {f1, f2} \<inter> pn_Nshifts False {f, f'} = {}"
        unfolding f_f'[symmetric] by (rule pn_Nshifts_disjoint) simp
      ultimately show False ..
    next
      case False
      note \<open>hd zs \<in> set zs\<close>
      also from zs_sub False have "set zs \<subseteq> pn_Nshifts False {h'}" by simp
      also from \<open>h' \<in> {f1, f2}\<close> have "\<dots> \<subseteq> pn_Nshifts False {f1, f2}"
        by (intro pn_Nshifts_mono) simp
      finally have "pn_Nshifts True {f, f'} \<inter> pn_Nshifts False {f1, f2} \<noteq> {}"
        using hd_zs_pos by blast
      moreover have "pn_Nshifts True {f, f'} \<inter> pn_Nshifts False {f1, f2} = {}"
        unfolding f_f'[symmetric] by (rule pn_Nshifts_disjoint) simp
      ultimately show False ..
    qed
  qed
  with part have zs2_min: "min_length_vpc zs2" and zs2_dist: "fst (hd zs2) \<noteq> snd (last zs2)"
    and overlap_hd: "overlap \<unlhd> fst (hd zs2)" and overlap_last: "overlap \<unlhd> snd (last zs2)"
    and "hd zs = hd zs2" by ((rule vpc_partitionD2)+, simp add: zs)
  from \<open>zs2 \<noteq> []\<close> have "hd zs2 \<in> set zs2" and "last zs2 \<in> set zs2" by simp_all
  have rl: P if "{p, p'} = {f, f'}" and "hd zs2 \<in> pn_Nshifts True {p}"
    and "set zs2 \<inter> pn_Nshifts True {p} \<noteq> {} \<Longrightarrow> set zs2 \<inter> Nshifts {p} \<subseteq> pn_Nshifts True {p} \<Longrightarrow>
          set zs2 \<inter> pn_Nshifts (\<not> True) {p} = {} \<Longrightarrow> set zs3 \<inter> pn_Nshifts False {p} \<noteq> {} \<Longrightarrow>
          set zs3 \<subseteq> pn_Nshifts False {p} \<Longrightarrow> set zs3 \<inter> Nshifts {p'} = {} \<Longrightarrow> P" for P p p'
  proof (rule that(3))
    from that(1) have p_in: "p \<in> {f1, f2}" by (auto simp: f_f')
    from \<open>hd zs2 \<in> set zs2\<close> that(2) have "hd zs2 \<in> set zs2 \<inter> pn_Nshifts True {p}" by (rule IntI)
    thus *: "set zs2 \<inter> pn_Nshifts True {p} \<noteq> {}" by blast
    with part p_in show "set zs2 \<inter> Nshifts {p} \<subseteq> pn_Nshifts True {p}" by (rule vpc_partitionD2)
    with part p_in show "set zs2 \<inter> pn_Nshifts (\<not> True) {p} = {}" by (rule vpc_partitionD2)
    hence "num_shifts False zs2 p = 0" by (simp add: num_shifts_eq_zero_iff)
    with p_in num_neg_f num_neg_f' have "num_shifts False zs3 p \<ge> num_shifts True zs p"
      by (auto simp: f_f' zs num_shifts_append)
    moreover from * have "num_shifts True zs p \<noteq> 0"
      by (simp add: zs num_shifts_eq_zero_iff Int_Un_distrib2)
    ultimately show "set zs3 \<inter> pn_Nshifts False {p} \<noteq> {}"
      by (simp flip: num_shifts_eq_zero_iff)
    with part nparallel p_in show zs3_sub: "set zs3 \<subseteq> pn_Nshifts False {p}"
      by (rule vpc_partitionD3)
    show "set zs3 \<inter> Nshifts {p'} = {}"
    proof (rule ccontr)
      from that(1) f_pbinomial f'_pbinomial have p_pbinomial: "is_proper_binomial p"
        and p'_pbinomial: "is_proper_binomial p'" by (auto simp: doubleton_eq_iff)
      from nparallel' that(1) have nparallel': "\<not> parallel_binomials p p'"
        by (auto simp: doubleton_eq_iff dest: parallel_binomials_sym)
      assume "set zs3 \<inter> Nshifts {p'} \<noteq> {}"
      with zs3_sub have "Nshifts {p} \<inter> Nshifts {p'} \<noteq> {}" by (auto simp: Nshifts_def)
      moreover from p_pbinomial p'_pbinomial nparallel' have "Nshifts {p} \<inter> Nshifts {p'} = {}"
        by (rule Nshifts_disjointI)
      ultimately show False ..
    qed
  qed

  from hd_zs_pos have "hd zs2 \<in> pn_Nshifts True {f} \<or> hd zs2 \<in> pn_Nshifts True {f'}"
    by (auto simp: \<open>hd zs = hd zs2\<close> elim: pn_NshiftsE_poly)
  thus ?thesis
  proof
    \<comment>\<open>Case I: \<open>zs\<close> starts with a positive shift of \<open>f\<close>.\<close>

    assume "hd zs2 \<in> pn_Nshifts True {f}"
    with refl obtain "set zs2 \<inter> pn_Nshifts True {f} \<noteq> {}"
      and "set zs2 \<inter> Nshifts {f} \<subseteq> pn_Nshifts True {f}"
      and "set zs2 \<inter> pn_Nshifts (\<not> True) {f} = {}" and ndisjnt: "set zs3 \<inter> pn_Nshifts False {f} \<noteq> {}"
      and zs3_sub: "set zs3 \<subseteq> pn_Nshifts False {f}" and 0: "set zs3 \<inter> Nshifts {f'} = {}" by (rule rl)
    have "set zs \<inter> Nshifts {f'} = {}"
    proof (rule ccontr)
      assume "set zs \<inter> Nshifts {f'} \<noteq> {}"
      hence "set zs \<inter> pn_Nshifts True {f'} \<noteq> {}" and "set zs \<inter> pn_Nshifts False {f'} \<noteq> {}"
        by (simp_all add: Nshifts_def Int_Un_distrib num_neg_f' flip: num_shifts_eq_zero_iff)
      with 0 have "set zs2 \<inter> pn_Nshifts True {f'} \<noteq> {}" and 1: "set zs2 \<inter> pn_Nshifts False {f'} \<noteq> {}"
        by (simp_all add: zs Int_Un_distrib Int_Un_distrib2 Nshifts_def)
      from part f'_in this(1) have "set zs2 \<inter> Nshifts {f'} \<subseteq> pn_Nshifts True {f'}"
        by (rule vpc_partitionD2)
      with part f'_in have "set zs2 \<inter> pn_Nshifts (\<not> True) {f'} = {}" by (rule vpc_partitionD2)
      with 1 show False by simp
    qed
    hence "set zs2 \<inter> Nshifts {f'} = {}" by (simp add: zs Int_Un_distrib2)
    moreover have "set zs2 \<subseteq> Nshifts {f, f'}" unfolding f_f'[symmetric] using zs2_min
      by (intro is_vpcD min_length_vpcD)
    ultimately have "set zs2 = set zs2 \<inter> Nshifts {f}" by (auto elim: NshiftsE_poly)
    also have "\<dots> \<subseteq> pn_Nshifts True {f}" by fact
    finally have "set zs2 \<subseteq> pn_Nshifts True {f}" .
    hence "set zs2 \<subseteq> Nshifts {f}" by (auto simp: Nshifts_def)
    moreover from zs3_sub have "set zs3 \<subseteq> Nshifts {f}" by (auto simp: Nshifts_def)
    ultimately have "set zs \<subseteq> Nshifts {f}" by (simp add: zs)
    with zs_min zs_dist obtain pos where "set zs \<inter> pn_Nshifts pos {f} = {}" by (rule lem_3_3_19'')
    hence "set zs2 \<inter> pn_Nshifts pos {f} = {}" and "set zs3 \<inter> pn_Nshifts pos {f} = {}"
      by (simp_all add: zs Int_Un_distrib2)
    with \<open>set zs2 \<inter> pn_Nshifts True {f} \<noteq> {}\<close> ndisjnt show ?thesis by (cases pos) simp_all

  next
    \<comment>\<open>Case II: \<open>zs\<close> starts with a positive shift of \<open>f'\<close>.\<close>

    have "{f', f} = {f, f'}" by (simp only: insert_commute)
    moreover assume "hd zs2 \<in> pn_Nshifts True {f'}"
    ultimately obtain "set zs2 \<inter> pn_Nshifts True {f'} \<noteq> {}"
      and zs2_sub_f': "set zs2 \<inter> Nshifts {f'} \<subseteq> pn_Nshifts True {f'}"
      and "set zs2 \<inter> pn_Nshifts (\<not> True) {f'} = {}" and "set zs3 \<inter> pn_Nshifts False {f'} \<noteq> {}"
      and zs3_sub: "set zs3 \<subseteq> pn_Nshifts False {f'}" and 0: "set zs3 \<inter> Nshifts {f} = {}" by (rule rl)
    from this(4) have "zs3 \<noteq> []" by auto
    from \<open>k \<noteq> 0\<close> have "num_shifts False zs f \<noteq> 0" by (simp add: num_neg_f)
    hence "set zs \<inter> pn_Nshifts False {f} \<noteq> {}" by (simp add: num_shifts_eq_zero_iff)
    with 0 have "set zs2 \<inter> pn_Nshifts False {f} \<noteq> {}"
      by (simp add: zs Nshifts_def Int_Un_distrib Int_Un_distrib2)
    with part f_in have zs2_sub_f: "set zs2 \<inter> Nshifts {f} \<subseteq> pn_Nshifts False {f}"
      by (rule vpc_partitionD2)
    with part f_in have "set zs2 \<inter> pn_Nshifts (\<not> False) {f} = {}" by (rule vpc_partitionD2)

    obtain i where "0 < i" and "i < length zs2" and i_neg: "zs2 ! i \<in> pn_Nshifts False {f}"
      and num_f'_i: "num_shifts True (take i zs2) f' = i"
    proof -
      let ?A = "{i\<in>{..<length zs2}. zs2 ! i \<in> pn_Nshifts False {f}}"
      define i where "i = Min ?A"
      have "finite ?A" by simp
      moreover have "?A \<noteq> {}"
      proof
        from \<open>set zs2 \<inter> pn_Nshifts False {f} \<noteq> {}\<close> obtain z where "z \<in> set zs2"
          and z_in: "z \<in> pn_Nshifts False {f}" by blast
        from this(1) obtain j where "j < length zs2" and "z = zs2 ! j" by (metis in_set_conv_nth)
        with z_in have "j \<in> ?A" by simp
        also assume "\<dots> = {}"
        finally show False ..
      qed
      ultimately have "i \<in> ?A" unfolding i_def by (rule Min_in)
      hence "i < length zs2" and i_in: "zs2 ! i \<in> pn_Nshifts False {f}" by simp_all
      show ?thesis
      proof
        show "0 < i"
        proof (rule ccontr)
          assume "\<not> 0 < i"
          hence "i = 0" by simp
          with \<open>zs2 \<noteq> []\<close> i_in have "hd zs2 \<in> pn_Nshifts False {f}" by (simp add: hd_conv_nth)
          with \<open>hd zs2 \<in> pn_Nshifts True {f'}\<close> have "pn_Nshifts False {f} \<inter> pn_Nshifts True {f'} \<noteq> {}"
            by blast
          moreover from f_pbinomial have "pn_Nshifts False {f} \<inter> pn_Nshifts True {f'} = {}"
            by (rule pn_Nshifts_disjointI) simp
          ultimately show False ..
        qed
      next
        have "set (take i zs2) \<subseteq> pn_Nshifts True {f'}"
        proof (rule subsetI)
          fix z
          assume "z \<in> set (take i zs2)"
          then obtain j where "j < length (take i zs2)" and "z = (take i zs2) ! j"
            by (metis in_set_conv_nth)
          hence z: "z = zs2 ! j" by simp
          from \<open>j < _\<close> have "j < i" by simp
          from this(1) \<open>i < _\<close> have "j < length zs2" by (rule less_trans)
          hence "zs2 ! j \<in> set zs2" by simp
          also have "\<dots> \<subseteq> Nshifts {f, f'}" unfolding f_f'[symmetric] using zs2_min
            by (intro is_vpcD min_length_vpcD)
          finally have "zs2 ! j \<in> set zs2 \<inter> Nshifts {f} \<or> zs2 ! j \<in> set zs2 \<inter> Nshifts {f'}"
            using \<open>zs2 ! j \<in> _\<close> by (auto elim: NshiftsE_poly)
          thus "z \<in> pn_Nshifts True {f'}"
          proof
            assume "zs2 ! j \<in> set zs2 \<inter> Nshifts {f}"
            hence "zs2 ! j \<in> pn_Nshifts False {f}" using zs2_sub_f ..
            with \<open>j < length zs2\<close> have "j \<in> ?A" by simp
            with \<open>finite ?A\<close> have "i \<le> j" unfolding i_def by (rule Min_le)
            also have "\<dots> < i" by fact
            finally show ?thesis ..
          next
            assume "zs2 ! j \<in> set zs2 \<inter> Nshifts {f'}"
            thus ?thesis unfolding z using zs2_sub_f' ..
          qed
        qed
        hence "num_shifts True (take i zs2) f' = length (take i zs2)"
          by (simp only: num_shifts_eq_length_iff)
        also from \<open>i < length zs2\<close> have "\<dots> = i" by simp
        finally show "num_shifts True (take i zs2) f' = i" .
      qed fact+
    qed
    from this(1) have "1 \<le> rat i" by simp

    define ys1 where "ys1 = take (Suc i) zs2"
    from \<open>zs2 \<noteq> []\<close> have hd_ys1: "fst (hd ys1) = fst (hd zs)" by (simp add: ys1_def zs)
    from \<open>i < length zs2\<close> have len_ys1: "length ys1 = Suc i" by (simp add: ys1_def)
    hence "ys1 \<noteq> []" by auto
    hence "last ys1 \<in> set ys1" by simp
    also have "\<dots> \<subseteq> set zs2" by (simp add: ys1_def set_take_subset)
    finally have "snd (last ys1) \<in> set_of_vpc zs2" by (simp add: set_of_vpc_def)
    with part have "overlap \<unlhd> snd (last ys1)" by (rule vpc_partitionD2)

    from zs2_min have "is_vpc zs2" by (rule min_length_vpcD)
    hence "is_vpc ys1" unfolding ys1_def by (rule is_vpc_takeI) simp
    with nparallel have "length ys1 = num_shifts True ys1 f1 + num_shifts False ys1 f1 +
                                      num_shifts True ys1 f2 + num_shifts False ys1 f2"
      by (rule length_eq_num_pos_shifts_plus_num_neg_shifts)
    also from f_f' have "\<dots> = num_shifts True ys1 f + num_shifts False ys1 f +
                                  num_shifts True ys1 f' + num_shifts False ys1 f'"
      by (auto simp: doubleton_eq_iff)
    finally have "Suc i = num_shifts True ys1 f + num_shifts False ys1 f +
                          num_shifts True ys1 f' + num_shifts False ys1 f'" by (simp only: len_ys1)
    moreover from \<open>i < length zs2\<close> i_neg have "1 \<le> num_shifts False ys1 f"
      by (simp add: ys1_def num_shifts_take_Suc num_shifts_singleton)
    moreover from \<open>i < length zs2\<close> have "i \<le> num_shifts True ys1 f'"
      by (simp add: ys1_def num_shifts_take_Suc num_f'_i)
    ultimately have ys1_pos_f: "num_shifts True ys1 f = 0" and ys1_neg_f: "num_shifts False ys1 f = 1"
      and ys1_pos_f': "num_shifts True ys1 f' = i" and ys1_neg_f': "num_shifts False ys1 f' = 0"
      by auto
    from nparallel \<open>is_vpc ys1\<close> have "snd (last ys1) = fst (hd ys1) +
                        (rat (num_shifts True ys1 f1) - rat (num_shifts False ys1 f1)) \<cdot> vect f1 +
                        (rat (num_shifts True ys1 f2) - rat (num_shifts False ys1 f2)) \<cdot> vect f2"
      by (rule vpc_snd_last_conv_vect)
    also from f_f' have "\<dots> = fst (hd ys1) +
                        (rat (num_shifts True ys1 f) - rat (num_shifts False ys1 f)) \<cdot> vect f +
                        (rat (num_shifts True ys1 f') - rat (num_shifts False ys1 f')) \<cdot> vect f'"
      by (auto simp: doubleton_eq_iff)
    also have "\<dots> = fst (hd ys1) - vect f + rat i \<cdot> vect f'"
      by (simp add: ys1_pos_f ys1_neg_f ys1_pos_f' ys1_neg_f' map_scale_uminus_left)
    finally have last_ys1: "snd (last ys1) = fst (hd ys1) - vect f + rat i \<cdot> vect f'" .

    from \<open>zs3 \<noteq> []\<close> have "last zs3 \<in> set zs3" by simp
    also have "\<dots> \<subseteq> pn_Nshifts False {f'}" by fact
    finally have "of_nat_pm (tpp f') \<unlhd> snd (last zs)" using \<open>zs3 \<noteq> []\<close>
      by (simp add: zs pn_NshiftsD_neg_le)
    also from vect_g have "\<dots> = fst (hd ys1) + (- rat k) \<cdot> vect f"
      by (simp add: hd_ys1 hd_zs last_zs map_scale_uminus_left vect_alt algebra_simps)
    finally have "of_nat_pm (tpp f') \<unlhd> fst (hd ys1) + (- rat k) \<cdot> vect f" .
    moreover from \<open>hd zs2 \<in> pn_Nshifts True {f'}\<close> have "of_nat_pm (tpp f') \<unlhd> fst (hd ys1) + 0 \<cdot> vect f"
      by (simp add: hd_ys1 \<open>hd zs = hd zs2\<close> pn_NshiftsD_pos_le)
    ultimately have "of_nat_pm (tpp f') \<unlhd> fst (hd ys1) + (- 1) \<cdot> vect f"
      by (rule map_scale_le_interval) (simp_all add: \<open>1 \<le> rat k\<close>)
    hence "of_nat_pm (tpp f') \<unlhd> fst (hd ys1) - vect f" by (simp add: map_scale_uminus_left)
    moreover from this _ _ \<open>1 \<le> rat i\<close> have "of_nat_pm (lpp f') \<unlhd> fst (hd ys1) - vect f + rat i \<cdot> vect f'"
      by (rule line_above_tpp_overlapD) (simp_all only: \<open>overlap \<unlhd> snd (last ys1)\<close> f'_in flip: last_ys1)
    moreover have "is_int_pm (fst (hd ys1) - vect f)"
    proof (intro minus_is_int_pm vect_is_int_pm)
      from \<open>is_vpc ys1\<close> have "fst (hd ys1) \<in> set_of_vpc ys1" by (simp add: set_of_vpc_alt_1)
      with \<open>is_vpc ys1\<close> have "is_nat_pm (fst (hd ys1))" by (rule vpc_is_nat_pm)
      thus "is_int_pm (fst (hd ys1))" by (rule nat_pm_is_int_pm)
    qed
    moreover note f'_in
    moreover from \<open>0 < i\<close> have "i \<noteq> 0" by simp
    ultimately obtain ys2' where "is_vpc ys2'" and hd_ys2': "fst (hd ys2') = fst (hd ys1) - vect f"
      and last_ys2': "snd (last ys2') = fst (hd ys1) - vect f + rat i \<cdot> vect f'" by (rule lem_3_3_21')
    
    define ys2 where "ys2 = map prod.swap (rev ys2')"
    from \<open>is_vpc ys2'\<close> have "is_vpc ys2" and hd_ys2: "fst (hd ys2) = snd (last ys2')"
      and last_ys2: "snd (last ys2) = fst (hd ys2')" unfolding ys2_def by (rule is_vpc_revI)+
    from this(1) have "ys2 \<noteq> []" by (rule is_vpcD)
    from \<open>is_vpc ys1\<close> \<open>is_vpc ys2\<close> have "is_vpc (ys1 @ ys2)"
      by (rule is_vpc_appendI) (simp only: hd_ys2 last_ys2' last_ys1)
    from \<open>ys1 \<noteq> []\<close> have hd_app: "hd (ys1 @ ys2) = hd ys1" by simp
    from \<open>ys2 \<noteq> []\<close> have last_app: "last (ys1 @ ys2) = last ys2" by simp
    from f_pbinomial have "tpp f \<prec> lpp f" by (rule punit.lt_gr_tt_binomial)
    hence "fst (hd (ys1 @ ys2)) \<noteq> snd (last (ys1 @ ys2))"
      by (simp add: hd_app last_app hd_ys1 last_ys2 hd_ys2' vect_alt)
    with \<open>is_vpc (ys1 @ ys2)\<close> obtain q1 q2
      where "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {fst (hd (ys1 @ ys2)), snd (last (ys1 @ ys2))}"
      by (rule vpcE_ideal)
    also have "\<dots> = {of_nat_pm (lpp g), of_nat_pm (lpp g) - vect f}"
      by (simp only: hd_app hd_ys1 hd_zs last_app last_ys2 hd_ys2')
    finally have "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {of_nat_pm (lpp g), of_nat_pm (lpp g) - vect f}" .
    moreover define g' where "g' = q1 * f1 + q2 * f2"
    ultimately have eq1: "of_nat_pm ` keys g' = {of_nat_pm (lpp g), of_nat_pm (lpp g) - vect f}" by simp
    have "of_nat_pm ` (+) (lpp f) ` keys g' = (+) (of_nat_pm (lpp f)) ` of_nat_pm ` keys g'"
      by (simp only: image_image of_nat_pm_plus)
    also have "\<dots> = (+) (of_nat_pm (lpp f)) ` {of_nat_pm (lpp g), of_nat_pm (lpp g) - vect f}"
      by (simp only: eq1)
    also have "\<dots> = of_nat_pm ` {lpp f + lpp g, tpp f + lpp g}"
      by (simp add: vect_alt of_nat_pm_plus add.commute)
    finally have eq2: "(+) (lpp f) ` keys g' = {lpp f + lpp g, tpp f + lpp g}"
      by (simp only: inj_image_eq_iff inj_of_nat_pm)
    hence "g' \<noteq> 0" by auto
    show ?thesis
    proof
      show "g' \<in> ideal {f1, f2}" unfolding g'_def by (rule idealI_2)

      show lpp_g': "lpp g' = lpp g"
      proof (rule punit.lt_eqI_keys)
        have "(of_nat_pm (lpp g) :: _ \<Rightarrow>\<^sub>0 rat) \<in> of_nat_pm ` keys g'" by (simp add: eq1)
        hence "to_nat_pm (of_nat_pm (lpp g) :: _ \<Rightarrow>\<^sub>0 rat) \<in>
                to_nat_pm ` (of_nat_pm ` keys g' :: (_ \<Rightarrow>\<^sub>0 rat) set)" by (rule imageI)
        thus "lpp g \<in> keys g'" by (simp add: image_image)
      next
        fix t
        assume "t \<in> keys g'"
        hence "lpp f + t \<in> (+) (lpp f) ` keys g'" by (rule imageI)
        hence "lpp f + t = lpp f + lpp g \<or> lpp f + t = tpp f + lpp g" by (simp add: eq2)
        thus "t \<preceq> lpp g"
          by (metis punit.lt_ge_tt ord_canc_left ordered_powerprod_lin.order.refl plus_monotone)
      qed

      from \<open>g' \<noteq> 0\<close> have "tpp g' \<in> keys g'" by (rule punit.tt_in_keys)
      hence "lpp f + tpp g' \<in> (+) (lpp f) ` keys g'" by (rule imageI)
      moreover have "lpp g' \<noteq> tpp g'" unfolding punit.lt_eq_tt_iff
      proof
        from finite_keys have "card (of_nat_pm ` keys g' :: (_ \<Rightarrow>\<^sub>0 rat) set) \<le> card (keys g')"
          by (rule card_image_le)
        moreover assume "has_bounded_keys 1 g'"
        ultimately have "card {of_nat_pm (lpp g), of_nat_pm (lpp g) - vect f} \<le> 1"
          by (simp add: eq1 has_bounded_keys_def)
        hence "vect f = 0" by (simp add: has_bounded_keys_def card_insert)
        with \<open>tpp f \<prec> lpp f\<close> show False by (simp add: vect_alt)
      qed
      ultimately have "lpp f + tpp g' = tpp f + lpp g'" by (auto simp: eq2 lpp_g')
      also have "\<dots> = lpp g' + tpp f" by (rule add.commute)
      finally show "vect g' = vect f"
        by (simp add: vect_alt lpp_g' diff_eq_eq eq_diff_eq diff_add_eq flip: of_nat_pm_plus)
    qed
  qed
qed

lemma thm_4_5_2_aux_4:
  assumes "\<not> overlap \<unlhd> of_nat_pm (lpp g)"
  obtains g' where "g' \<in> ideal {f1, f2}" and "lpp g' = lpp g" and "vect g' = vect f"
proof -
  have f_in: "f \<in> {f1, f2}" and f'_in: "f' \<in> {f1, f2}" by (simp_all add: f_f')
  from f_f' f1_pbinomial f2_pbinomial have f_pbinomial: "is_proper_binomial f"
    and f'_pbinomial: "is_proper_binomial f'" by (auto simp: doubleton_eq_iff)
  from nparallel f_f' have nparallel': "\<not> parallel_binomials f f'"
    by (auto simp: doubleton_eq_iff dest: parallel_binomials_sym)

  from thm_4_5_2_aux_1 have "1 \<le> rat k" by simp

  obtain zs where zs_min: "min_length_vpc zs" and zs_dist: "fst (hd zs) \<noteq> snd (last zs)"
    and hd_zs: "fst (hd zs) = of_nat_pm (lpp g)" and last_zs: "snd (last zs) = of_nat_pm (tpp g)"
    and num_neg_f: "num_shifts False zs f = k + num_shifts True zs f"
    and num_neg_f': "num_shifts False zs f' = num_shifts True zs f'"
    and hd_zs_pos: "hd zs \<in> pn_Nshifts True {f, f'}"
    and last_zs_neg: "last zs \<in> pn_Nshifts False {f, f'}" by (rule thm_4_5_2_aux_2)

  from zs_min have "is_vpc zs" by (rule min_length_vpcD)
  hence "zs \<noteq> []" by (rule is_vpcD)
  hence "hd zs \<in> set zs" and "last zs \<in> set zs" by simp_all
  from zs_min zs_dist obtain zs1 zs2 zs3 where zs: "zs = zs1 @ zs2 @ zs3"
    and part: "vpc_partition zs1 zs2 zs3" by (rule min_length_vpcE_partition)

  show ?thesis sorry
qed

end

end

lemma thm_4_5_2:
  assumes "f \<in> {f1, f2}" and "vect g = rat k \<cdot> vect f"
  obtains g' where "g' \<in> ideal {f1, f2}" and "lpp g' = lpp g" and "vect g' = vect f"
proof -
  from assms(1) obtain f' where f_f': "{f1, f2} = {f, f'}" by blast
  show ?thesis
  proof (cases "overlap \<unlhd> of_nat_pm (lpp g)")
    case True
    with f_f' assms(2) show ?thesis using that by (rule thm_4_5_2_aux_3)
  next
    case False
    with f_f' assms(2) show ?thesis using that by (rule thm_4_5_2_aux_4)
  qed
qed

end

end (* two_binoms *)

end (* theory *)
