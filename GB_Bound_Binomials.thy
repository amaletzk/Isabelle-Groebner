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

lemma lem_4_2_1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<unlhd> p"
  shows "step p \<le> step (tp f)"
proof (rule ccontr)
  let ?A = "\<lambda>q. {nat \<lceil>(lookup overlap x - rat (lookup q x)) / lookup (vect f) x\<rceil> |x.
                 0 < lookup (vect f) x \<and> rat (lookup q x) < lookup overlap x}"
  have fin: "finite (?A q)" for q using finite_step_p'_carrier[where p="of_nat_pm q"]
    unfolding lookup_of_nat_pm by (rule finite_image_set)

  assume "\<not> step p \<le> step (tp f)"
  hence "step (tp f) < step p" by simp
  with le0 have "0 < step p" by (rule le_less_trans)
  from assms have "step p = step' f p" by (rule step_alt1)
  also have "\<dots> \<in> ?A p \<union> {0}" unfolding step'_alt by (rule Max_in) (simp_all add: fin)
  finally have "step p \<in> ?A p" using \<open>0 < step p\<close> by simp
  then obtain x where "0 < lookup (vect f) x" and "rat (lookup p x) < lookup overlap x"
    and "step p = nat \<lceil>(lookup overlap x - rat (lookup p x)) / lookup (vect f) x\<rceil>" (is "_ = nat \<lceil>?a\<rceil>")
    by blast
  from assms(3) have "lookup (tp f) x \<le> lookup p x" by (rule le_pmD)
  hence "rat (lookup (tp f) x) \<le> rat (lookup p x)" by (rule of_nat_mono)
  also have "\<dots> < lookup overlap x" by fact
  finally have "nat \<lceil>(lookup overlap x - rat (lookup (tp f) x)) / lookup (vect f) x\<rceil> \<in> ?A (tp f)"
    (is "nat \<lceil>?b\<rceil> \<in> _") using \<open>0 < lookup (vect f) x\<close> by blast
  also have "\<dots> \<subseteq> ?A (tp f) \<union> {0}" by blast
  finally have "nat \<lceil>?b\<rceil> \<in> ?A (tp f) \<union> {0}" .
  with _ have "nat \<lceil>?b\<rceil> \<le> step' f (tp f)" unfolding step'_alt by (rule Max_ge) (simp add: fin)
  also from assms(1, 2) le_pm_refl have "\<dots> = step (tp f)" by (rule step_alt1[symmetric])
  also have "\<dots> < step p" by fact
  also have "\<dots> = nat \<lceil>?a\<rceil>" by fact
  finally have "\<lceil>?b\<rceil> < \<lceil>?a\<rceil>" by (simp only: zless_nat_conj)
  hence "?b < ?a" by (rule ceiling_less_cancel)
  with \<open>0 < lookup (vect f) x\<close> have "rat (lookup p x) < rat (lookup (tp f) x)"
    by (simp add: divide_less_cancel)
  also have "\<dots> \<le> rat (lookup p x)" by fact
  finally show False ..
qed

subsection \<open>One Proper Binomial and one Monomial\<close>

text \<open>In @{cite MWW}, the third assumption in the following lemma (@{prop "0 < k"}) is missing.
  Counterexample for @{prop "k = 0"} and (degree-)lexicographic order with @{prop "x \<prec> y"}:
  \<^item> @{prop "f1 = y^2 + x^2"},
  \<^item> @{prop "f2 = y"},
  \<^item> @{prop "f = f1"},
  \<^item> @{prop "overlap = y"},
  \<^item> @{prop "step (tp f) = 1"}.
  Then the overlapshift of \<open>f\<close> is \<open>y^2\<close>, which is also the lcs on the right-hand-side. But \<open>tp f\<close> is
  not below \<open>y^2\<close>.\<close>

lemma lem_4_3_1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "0 < k" and "k \<le> step (tp f)"
  shows "lcs (of_nat_pm (tp f) + rat k \<cdot> vect f) overlap \<unlhd> lcs (of_nat_pm (overlapshift (tp f))) overlap"
proof (rule le_pmI, simp add: lookup_lcs_fun lcs_fun_def lookup_add lookup_of_nat_pm)
  fix x
  show "rat (lookup (tp f) x) + rat k * lookup (vect f) x \<le>
          max (rat (lookup (overlapshift (tp f)) x)) (lookup overlap x)"
      (is "?a \<le> ?b")
  proof (cases "0 \<le> lookup (vect f) x")
    case True
    from assms(1, 2) le_pm_refl have eq1: "overlapshift (tp f) = overlapshift' f (tp f)"
      and eq2: "step (tp f) = step' f (tp f)" by (rule overlapshift_alt1, rule step_alt1)
    from True assms(4) have "?a \<le> rat (lookup (tp f) x) + rat (step (tp f)) * lookup (vect f) x"
      (is "_ \<le> ?c") by (simp add: mult_right_mono)
    also have "\<dots> \<le> rat (to_nat ?c)"
      by (intro of_nat_to_nat_ge Ints_add Ints_mult is_int_pmD vect_is_int_pm) (fact Ints_of_nat)+
    also have "\<dots> = rat (lookup (overlapshift (tp f)) x)"
      by (simp add: eq1 eq2 overlapshift'_alt lookup_add lookup_of_nat_pm)
    also have "\<dots> \<le> ?b" by (rule max.cobounded1)
    finally show ?thesis .
  next
    case False
    hence *: "lookup (vect f) x < 0" by simp
    with assms(3) have "?a \<le> rat (lookup (tp f) x) + lookup (vect f) x" by simp
    also have "\<dots> = rat (lookup (lp f) x)" by (simp add: vect_alt lookup_minus lookup_of_nat_pm)
    finally have "?a \<le> rat (lookup (lp f) x)" .
    also from * have "\<dots> \<le> rat (lookup (tp f) x)" by (simp add: vect_alt lookup_minus lookup_of_nat_pm)
    finally have "?a \<le> rat (lookup (tp f) x)" .
    with \<open>?a \<le> rat (lookup (lp f) x)\<close> have "?a \<le> min (rat (lookup (lp f) x)) (rat (lookup (tp f) x))"
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

lemma binomial_monomial_reduced_GB_cases:
  assumes "g \<in> punit.reduced_GB {f1, f2}"
  assumes "\<And>c. c \<noteq> 0 \<Longrightarrow> g = c \<cdot> f1 \<Longrightarrow> is_proper_binomial g \<Longrightarrow> thesis"
  assumes "\<And>c. c \<noteq> 0 \<Longrightarrow> g = c \<cdot> f2 \<Longrightarrow> is_monomial g \<Longrightarrow> thesis"
  assumes "is_monomial g \<Longrightarrow> lp g = lp f1 \<Longrightarrow> lp g \<noteq> lp f2 \<Longrightarrow> thesis"
  assumes "is_monomial g \<Longrightarrow> membership_problem_assms f1 f2 g \<Longrightarrow> tp f1 adds lp g \<Longrightarrow>
            0 < step (lp g) \<Longrightarrow> overlap \<unlhd> of_nat_pm (overlapshift (lp g)) \<Longrightarrow>
            of_nat_pm (overlapshift (lp g)) = of_nat_pm (lp g) + rat (step (lp g)) \<cdot> vect f1 \<Longrightarrow> thesis"
  shows thesis
proof -
  from f1_pbinomial have 1: "is_binomial f1" by (rule proper_binomial_imp_binomial)
  from f2_monomial have 2: "is_monomial_set {f2}" by (simp add: is_monomial_set_def)
  have ideal: "ideal (punit.reduced_GB {f1, f2}) = ideal {f1, f2}"
    by (rule punit.reduced_GB_pmdl_finite[simplified]) simp
  have "finite {f1, f2}" by simp
  thus ?thesis using assms(1)
  proof (rule punit.reduced_GB_cases_finite)
    fix f
    assume "f \<in> {f1, f2}" and lp_g: "lp g = lp f"
    from this(1) have disj: "f = f1 \<or> f = f2" by simp
    from 1 2 _ assms(1) show ?thesis
    proof (rule punit.reduced_GB_binomial_monomial_set_cases)
      fix c
      assume "c \<noteq> 0" and "g = c \<cdot> f1" and "is_proper_binomial g"
      thus ?thesis by (rule assms(2))
    next
      assume *: "is_monomial g"
      show ?thesis
      proof (cases "lp g = lp f2")
        case True
        from f2_monomial have "f2 \<noteq> 0" by (rule monomial_not_0)
        hence "lc f2 \<noteq> 0" by (rule punit.lc_not_0)
        moreover from * have "monomial (lc g) (lp g) = g" by (rule punit.monomial_eq_itself)
        ultimately have "g = (lc g / lc f2) \<cdot> monomial (lc f2) (lp f2)" by (simp add: True)
        also from f2_monomial have "monomial (lc f2) (lp f2) = f2" by (rule punit.monomial_eq_itself)
        finally have g: "g = (lc g / lc f2) \<cdot> f2" .
        from * have "g \<noteq> 0" by (rule monomial_not_0)
        hence "lc g \<noteq> 0" by (rule punit.lc_not_0)
        with \<open>lc f2 \<noteq> 0\<close> have "lc g / lc f2 \<noteq> 0" by simp
        thus ?thesis using g * by (rule assms(3))
      next
        case False
        with disj have "lp g = lp f1" by (auto simp: lp_g)
        with * show ?thesis using False by (rule assms(4))
      qed
    qed simp
  next
    assume irred: "\<not> punit.is_red {f1, f2} g"
    from 1 2 _ assms(1) show ?thesis
    proof (rule punit.reduced_GB_binomial_monomial_set_cases)
      fix c
      assume "c \<noteq> 0" and "g = c \<cdot> f1"
      with irred have "\<not> punit.is_red {f1, f2} f1" by (simp add: punit.is_red_map_scale_iff)
      from f1_pbinomial have "f1 \<noteq> 0" by (rule proper_binomial_not_0)
      with punit.red_supsetE punit.red_supset_insertI have "punit.is_red {f1, f2} f1"
        by fastforce
      with \<open>\<not> punit.is_red {f1, f2} f1\<close> show ?thesis ..
    next
      assume "is_monomial g"
      hence "g \<noteq> 0" by (rule monomial_not_0)
      note 1
      moreover from f2_monomial have 3: "is_binomial f2" by (rule monomial_imp_binomial)
      moreover have g_in: "g \<in> ideal {f1, f2}" unfolding ideal[symmetric] using assms(1)
        by (rule ideal.span_base)
      moreover note irred
      moreover from \<open>g \<noteq> 0\<close> have "lp g \<in> keys g" by (rule punit.lt_in_keys)
      ultimately obtain f k u where "f \<in> {f1, f2}" and "is_proper_binomial f" and adds: "tp f adds lp g"
        and "associated f u (lp g) k" and "overlap \<unlhd> of_nat_pm u" and "lp f adds u"
        by (rule binomial_ideal_irredE_assoc)
      from this(1-5) have le: "overlap \<unlhd> of_nat_pm (overlapshift (lp g))"
        and eq: "of_nat_pm (overlapshift (lp g)) = of_nat_pm (lp g) + rat (step (lp g)) \<cdot> vect f"
        by (rule overlapshift_is_above_overlap, rule of_nat_pm_overlapshift')
      from f2_monomial \<open>f \<in> {f1, f2}\<close> \<open>is_proper_binomial f\<close> have f: "f = f1"
        by (auto simp: is_monomial_def is_proper_binomial_def)
      from \<open>is_monomial g\<close> _ adds _ le eq show ?thesis unfolding f
      proof (rule assms(5))
        from \<open>is_monomial g\<close> have "is_binomial g" by (rule monomial_imp_binomial)
        moreover from \<open>is_monomial g\<close> proper_binomial_no_monomial have "\<not> is_proper_binomial g" by blast
        ultimately show "membership_problem_assms f1 f2 g" using 1 3 irred g_in
          by (simp add: membership_problem_assms_def)
      next
        have "step (lp g) \<noteq> 0"
        proof
          assume "step (lp g) = 0"
          with eq have "overlapshift (lp g) = lp g" by simp
          with le have "lcs (gcs (lp f1) (tp f1)) (gcs (lp f2) (tp f2)) \<unlhd> lp g"
            by (simp add: overlap_alt' le_of_nat_pm)
          with lcs_ge_pm(2) have "gcs (lp f2) (tp f2) \<unlhd> lp g" by (rule le_pm_trans)
          moreover from f2_monomial have "lp f2 = tp f2" by (rule punit.lt_eq_tt_monomial)
          ultimately have "lp f2 adds lp g" by (simp add: adds_pm)
          with _ monomial_not_0 \<open>lp g \<in> keys g\<close> have "punit.is_red {f1, f2} g"
            by (rule punit.is_red_addsI[simplified]) (simp_all add: f2_monomial)
          with irred show False ..
        qed
        thus "0 < step (lp g)" by simp
      qed
    qed simp
  qed
qed

text \<open>In @{cite MWW}, Theorem 4.3.2. lacks @{term "deg_pm (lp f1)"} on the right-hand-side of the
  inequality. It is needed if @{prop "lp f2 adds tp f1"}, as can be seen in the following example
  (lexicographic order with @{prop "x \<prec> y"}):
  \<^item> @{prop "f1 = y^6 + x^2"},
  \<^item> @{prop "f2 = x"},
  \<^item> @{prop "punit.reduced_GB {f1, f2} = {y^6, x}"},
  \<^item> bound without @{term "deg_pm (lp f1)"} is \<open>2\<close>,
  \<^item> actual degree goes up to \<open>6\<close> (@{prop "y^6 = 1 * f1 - x * f2"}, and @{prop "poly_deg (1 * f1) = 6"}).\<close>

lemma thm_4_3_2_aux_1:
  assumes "P = lcs (of_nat_pm (overlapshift (tp f1))) overlap"
    and "d = max (deg_pm (lp f1)) (to_nat (max (deg_pm P) (deg_pm (P - rat (step (tp f1)) \<cdot> vect f1))))"
  shows "poly_deg f1 \<le> d"
proof (rule poly_deg_leI)
  let ?d = "max (deg_pm P) (deg_pm (P - rat (step (tp f1)) \<cdot> vect f1))"
  have "is_int_pm (of_nat_pm (tp f1))" by (intro nat_pm_is_int_pm of_nat_pm_is_nat_pm)
  hence 1: "is_int_pm (overlapshift_p (of_nat_pm (tp f1)))" by (rule overlapshift_p_is_int_pm)
  have "f1 \<in> {f1, f2}" by simp
  hence eq1: "overlapshift_p (of_nat_pm (tp f1)) = overlapshift_p' f1 (of_nat_pm (tp f1))"
    and eq2: "step (tp f1) = step' f1 (tp f1)"
    and eq3: "overlapshift (tp f1) = overlapshift' f1 (tp f1)"
    using f1_pbinomial le_pm_refl by (rule overlapshift_p_alt1, rule step_alt1, rule overlapshift_alt1)
  have "deg_pm (overlapshift_p (of_nat_pm (tp f1))) \<le>
          rat (to_nat (deg_pm (overlapshift_p (of_nat_pm (tp f1)))))"
    by (intro of_nat_to_nat_ge Ints_deg 1)
  also have "\<dots> \<le> rat (deg_pm (to_nat_pm (overlapshift_p (of_nat_pm (tp f1)))))"
    by (intro of_nat_mono to_nat_deg_pm_le 1)
  also have "\<dots> = rat (deg_pm (overlapshift (tp f1)))" by (simp only: eq1 eq3 overlapshift'_def)
  finally have le1: "deg_pm (overlapshift_p (of_nat_pm (tp f1))) \<le> rat (deg_pm (overlapshift (tp f1)))" .

  fix t
  assume "t \<in> keys f1"
  also from f1_pbinomial have "\<dots> = {lp f1, tp f1}" by (rule punit.keys_proper_binomial)
  finally have "t = lp f1 \<or> t = tp f1" by simp
  thus "deg_pm t \<le> d"
  proof
    assume t: "t = lp f1"
    show ?thesis unfolding t assms(2) by (rule max.cobounded1)
  next
    assume "t = tp f1"
    hence "rat (deg_pm t) = deg_pm (of_nat_pm (tp f1))" by (simp add: deg_of_nat_pm)
    also have "\<dots> \<le> deg_pm (overlapshift_p (of_nat_pm (tp f1)) - rat (step (tp f1)) \<cdot> vect f1)"
      by (simp add: eq1 eq2 overlapshift_p'_def step'_def)
    also have "\<dots> = deg_pm (overlapshift_p (of_nat_pm (tp f1))) - rat (step (tp f1)) * deg_pm (vect f1)"
      by (simp only: deg_pm_minus_group deg_pm_map_scale)
    also from le1 have "\<dots> \<le> rat (deg_pm (overlapshift (tp f1))) - rat (step (tp f1)) * deg_pm (vect f1)"
      by (rule diff_right_mono)
    also have "\<dots> = deg_pm (of_nat_pm (overlapshift (tp f1)) - rat (step (tp f1)) \<cdot> vect f1)"
      by (simp only: deg_pm_minus_group deg_of_nat_pm deg_pm_map_scale)
    also have "\<dots> \<le> deg_pm (P - rat (step (tp f1)) \<cdot> vect f1)"
      unfolding assms(1) lcs_diff_distrib_left using lcs_ge_pm(1) by (rule deg_pm_mono_le)
    also have "\<dots> \<le> ?d" by (rule max.cobounded2)
    finally have "to_nat (rat (deg_pm t)) \<le> to_nat ?d" by (rule to_nat_mono)
    thus ?thesis by (simp only: to_nat_of_nat assms(2))
  qed
qed

lemma thm_4_3_2_aux_2:
  assumes "g \<in> punit.reduced_GB {f1, f2}" and "\<not> is_monomial g \<or> lp g \<noteq> lp f1 \<or> lp g = lp f2"
    and "P = lcs (of_nat_pm (overlapshift (tp f1))) overlap"
    and "d = max (deg_pm (lp f1)) (to_nat (max (deg_pm P) (deg_pm (P - rat (step (tp f1)) \<cdot> vect f1))))"
  obtains q1 q2 where "g = q1 * f1 + q2 * f2" and "poly_deg (q1 * f1) \<le> d" and "poly_deg (q2 * f2) \<le> d"
proof -
  let ?d = "max (deg_pm P) (deg_pm (P - rat (step (tp f1)) \<cdot> vect f1))"
  have "0 \<notin> punit.reduced_GB {f1, f2}" (is "0 \<notin> ?G") by (rule punit.reduced_GB_nonzero_finite) simp
  with assms(1) have "g \<noteq> 0" by blast
  hence "lp g \<in> keys g" by (rule punit.lt_in_keys)
  from f2_monomial have lp_f2: "lp f2 = tp f2" by (rule punit.lt_eq_tt_monomial)
  have tp1_is_int: "is_int_pm (of_nat_pm (tp f1))" by (intro nat_pm_is_int_pm of_nat_pm_is_nat_pm)
  from assms(1) show ?thesis
  proof (rule binomial_monomial_reduced_GB_cases)
    fix c
    assume g: "g = c \<cdot> f1"
    show ?thesis
    proof
      show "g = monomial c 0 * f1 + 0 * f2" by (simp add: g map_scale_eq_times)
    next
      have "poly_deg (monomial c 0 * f1) \<le> poly_deg f1"
        by (simp add: poly_deg_map_scale flip: map_scale_eq_times)
      also from assms(3, 4) have "\<dots> \<le> d" by (rule thm_4_3_2_aux_1)
      finally show "poly_deg (monomial c 0 * f1) \<le> d" .
    next
      show "poly_deg (0 * f2) \<le> d" by simp
    qed
  next
    assume "is_monomial g" and "lp g = lp f1" and "lp g \<noteq> lp f2"
    with assms(2) show ?thesis by simp
  next
    fix c
    assume g: "g = c \<cdot> f2"
    show ?thesis
    proof
      show "g = 0 * f1 + monomial c 0 * f2" by (simp add: g map_scale_eq_times)
    next
      show "poly_deg (0 * f1) \<le> d" by simp
    next
      from f2_monomial have "monomial (lc f2) (lp f2) = f2" by (rule punit.monomial_eq_itself)
      hence "poly_deg (monomial c 0 * f2) \<le> poly_deg (monomial (lc f2) (lp f2))"
        by (simp add: poly_deg_map_scale flip: map_scale_eq_times)
      also have "\<dots> \<le> deg_pm (lp f2)" by (simp add: poly_deg_monomial)
      also have "\<dots> = deg_pm (gcs (lp f2) (tp f2))" by (simp add: lp_f2)
      also from lcs_ge_pm(2) have "\<dots> \<le> deg_pm (lcs (gcs (lp f1) (tp f1)) (gcs (lp f2) (tp f2)))"
        by (rule deg_pm_mono_le)
      also have "rat \<dots> = deg_pm overlap" by (simp add: overlap_alt' deg_of_nat_pm)
      also from lcs_ge_pm(2) have "\<dots> \<le> deg_pm P" unfolding assms(3) by (rule deg_pm_mono_le)
      also have "\<dots> \<le> ?d" by (rule max.cobounded1)
      finally have "rat (poly_deg (monomial c 0 * f2)) \<le> ?d" using of_nat_mono by blast
      hence "to_nat (rat (poly_deg (monomial c 0 * f2))) \<le> to_nat ?d" by (rule to_nat_mono)
      hence "poly_deg (monomial c 0 * f2) \<le> to_nat ?d" by (simp only: to_nat_of_nat)
      also have "\<dots> \<le> d" unfolding assms(4) by (rule max.cobounded2)
      finally show "poly_deg (monomial c 0 * f2) \<le> d" .
    qed
  next
    assume "is_monomial g" and mpa: "membership_problem_assms f1 f2 g"
      and "tp f1 adds lp g" and "0 < step (lp g)" and le1: "overlap \<unlhd> of_nat_pm (overlapshift (lp g))"
      and eq1: "of_nat_pm (overlapshift (lp g)) = of_nat_pm (lp g) + rat (step (lp g)) \<cdot> vect f1"
    from this(3) have le2: "tp f1 \<unlhd> lp g" by (simp only: adds_pm)
    with _ f1_pbinomial have "step (lp g) \<le> step (tp f1)" by (rule lem_4_2_1) simp
    from \<open>0 < step (lp g)\<close> have eq2: "rat (step (lp g) - Suc 0) = rat (step (lp g)) - 1" by simp

    define Q where "Q = lcs (of_nat_pm (tp f1) + rat (step (lp g)) \<cdot> vect f1) overlap"
    define Q' where "Q' = Q - rat (step (lp g)) \<cdot> vect f1"
    have "Q \<unlhd> of_nat_pm (lp g) + rat (step (lp g)) \<cdot> vect f1" unfolding Q_def
      by (intro lcs_le_pm le_pm_mono_plus_right) (simp add: le_of_nat_pm le2, simp only: le1 flip: eq1)
    hence "Q' \<unlhd> of_nat_pm (lp g) + rat (step (lp g)) \<cdot> vect f1 - rat (step (lp g)) \<cdot> vect f1"
      unfolding Q'_def by (rule le_pm_mono_minus)
    hence "Q' \<unlhd> of_nat_pm (lp g)" by simp
    hence "to_nat_pm Q' adds lp g" by (auto simp: adds_pm dest: to_nat_pm_mono)

    have "of_nat_pm (tp f1) + rat (step (lp g)) \<cdot> vect f1 \<unlhd> Q" unfolding Q_def by (rule lcs_ge_pm)
    hence "of_nat_pm (tp f1) + rat (step (lp g)) \<cdot> vect f1 - rat (step (lp g) - 1) \<cdot> vect f1 \<unlhd>
            Q - rat (step (lp g) - 1) \<cdot> vect f1"
      and "of_nat_pm (tp f1) + rat (step (lp g)) \<cdot> vect f1 - rat (step (lp g)) \<cdot> vect f1 \<unlhd> Q'"
      unfolding Q'_def by (rule le_pm_mono_minus)+
    hence le3: "of_nat_pm (lp f1) \<unlhd> Q - rat (step (lp g) - 1) \<cdot> vect f1" and "of_nat_pm (tp f1) \<unlhd> Q'"
      by (simp_all add: eq2 vect_alt algebra_simps)

    have "of_nat_pm (lp f1) \<unlhd> Q"
    proof (rule le_pmI)
      fix y
      have "rat (lookup (lp f1) y) \<le> lookup Q y"
      proof (rule ccontr)
        assume "\<not> rat (lookup (lp f1) y) \<le> lookup Q y"
        hence "lookup Q y < rat (lookup (lp f1) y)" by simp
        also from le3 have "\<dots> \<le> lookup Q y - rat (step (lp g) - 1) * lookup (vect f1) y"
          by (auto dest!: le_pmD simp: lookup_of_nat_pm lookup_minus)
        finally have "rat (step (lp g) - 1) * lookup (vect f1) y < 0" by simp
        hence "lookup (vect f1) y < 0" by (simp add: mult_less_0_iff)
        hence "lookup (lp f1) y \<le> lookup (tp f1) y" by (simp add: vect_alt lookup_minus lookup_of_nat_pm)
        hence "rat (lookup (lp f1) y) \<le> lookup Q y"
          by (simp add: Q_def lookup_lcs_fun lcs_fun_def overlap_alt lookup_gcs_fun gcs_fun lookup_of_nat_pm)
        also have "\<dots> < rat (lookup (lp f1) y)" by fact
        finally show False ..
      qed
      thus "lookup (of_nat_pm (lp f1)) y \<le> lookup Q y" by (simp only: lookup_of_nat_pm)
    qed

    from tp1_is_int Ints_of_nat have "is_int_pm Q" unfolding Q_def
      by (intro lcs_is_int_pm overlap_is_int_pm plus_is_int_pm map_scale_is_int_pm vect_is_int_pm)
    hence "is_nat_pm Q" using of_nat_pm_is_nat_pm \<open>of_nat_pm (lp f1) \<unlhd> Q\<close> by (rule int_pm_is_nat_pmI)

    from \<open>is_int_pm Q\<close> Ints_of_nat have "is_int_pm Q'"
      unfolding Q'_def by (intro minus_is_int_pm map_scale_is_int_pm vect_is_int_pm)
    hence "is_nat_pm Q'" using of_nat_pm_is_nat_pm \<open>of_nat_pm (tp f1) \<unlhd> Q'\<close> by (rule int_pm_is_nat_pmI)

    obtain a where "a \<in> ideal {f1, f2}" and "a \<noteq> 0" and lp_a: "lp a = to_nat_pm Q'"
    proof -
      from f1_pbinomial have "is_binomial f1" by (rule proper_binomial_imp_binomial)
      moreover have "associated f1 (to_nat_pm Q) (to_nat_pm Q') (step (lp g))"
        using \<open>is_nat_pm Q\<close> \<open>is_nat_pm Q'\<close>
        by (simp add: associated_alt_rat of_nat_pm_comp_to_nat_pm Q'_def)
      moreover from \<open>0 < step (lp g)\<close> have "step (lp g) \<noteq> 0" by simp
      moreover from \<open>of_nat_pm (lp f1) \<unlhd> Q\<close> have "lp f1 adds to_nat_pm Q"
        by (auto simp: adds_pm dest: to_nat_pm_mono)
      moreover from \<open>of_nat_pm (tp f1) \<unlhd> Q'\<close> have "tp f1 adds to_nat_pm Q'"
        by (auto simp: adds_pm dest: to_nat_pm_mono)
      ultimately obtain q where keys_q: "keys (q * f1) = {to_nat_pm Q, to_nat_pm Q'}"
        by (rule associated_adds_obtains_cofactor_keys)
      define c where "c = - lookup (q * f1) (to_nat_pm Q) / lc f2"
      from f2_monomial have "lc f2 \<noteq> 0" by (intro punit.lc_not_0 monomial_not_0)
      with keys_q have "c \<noteq> 0" by (simp add: c_def)

      have "lp f2 = gcs (lp f2) (tp f2)" by (simp add: lp_f2)
      also have "of_nat_pm \<dots> \<unlhd> overlap" by (fact gcs_le_overlap')
      also have "\<dots> \<unlhd> Q" unfolding Q_def by (rule lcs_ge_pm)
      finally have "of_nat_pm (lp f2) \<unlhd> Q" .
      hence "lp f2 adds to_nat_pm Q" by (auto simp: adds_pm dest: to_nat_pm_mono)
      then obtain t where t: "to_nat_pm Q = t + lp f2" by (rule addsE) (simp only: add.commute)
      define b where "b = punit.monom_mult c t f2"
      moreover from f2_monomial have "keys f2 = {lp f2}" by (rule punit.keys_monomial)
      ultimately have keys_b: "keys b = {to_nat_pm Q}"
        using \<open>c \<noteq> 0\<close> by (simp add: punit.keys_monom_mult t)
      have "keys (q * f1 + b) \<subseteq> keys (q * f1) \<union> keys b" by (fact keys_add_subset)
      also have "\<dots> = {to_nat_pm Q, to_nat_pm Q'}" by (simp add: keys_q keys_b)
      finally have sub1: "keys (q * f1 + b) \<subseteq> {to_nat_pm Q, to_nat_pm Q'}" .
      from \<open>c \<noteq> 0\<close> have "lookup b (to_nat_pm Q) = c * lc f2"
        by (simp add: b_def t punit.lookup_monom_mult_plus[simplified] punit.lc_def)
      also from \<open>lc f2 \<noteq> 0\<close> have "\<dots> = - lookup (q * f1) (to_nat_pm Q)" by (simp add: c_def)
      finally have "to_nat_pm Q \<notin> keys (q * f1 + b)" by (simp add: lookup_add)
      moreover have "to_nat_pm Q' \<in> keys (q * f1 + b)"
      proof (intro in_keys_plusI1 notI)
        assume "to_nat_pm Q' \<in> keys b"
        hence "to_nat_pm Q' = to_nat_pm Q" by (simp add: keys_b)
        with \<open>is_nat_pm Q\<close> \<open>is_nat_pm Q'\<close> have "Q = Q'" by (metis of_nat_pm_comp_to_nat_pm)
        with \<open>0 < step (lp (g))\<close> have "vect f1 = 0" by (simp add: Q'_def map_scale_eq_0_iff)
        hence "lp f1 = tp f1" by (simp add: vect_alt)
        also from f1_pbinomial have "\<dots> \<prec> lp f1" by (rule punit.lt_gr_tt_binomial)
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

        thus "lp (q * f1 + b) = to_nat_pm Q'" by (simp add: punit.lt_def keys)
      qed
    qed

    have "punit.is_Groebner_basis ?G" by (rule punit.reduced_GB_is_GB_finite) simp
    moreover from \<open>a \<in> ideal {f1, f2}\<close> have "a \<in> ideal ?G"
      by (simp add: punit.reduced_GB_pmdl_finite[simplified])
    ultimately obtain g' where "g' \<in> ?G" and "g' \<noteq> 0" and *: "lp g' adds lp a" using \<open>a \<noteq> 0\<close>
      by (rule punit.GB_adds_lt[simplified])
    from this(3) \<open>to_nat_pm Q' adds lp g\<close> have "lp g' adds lp g" unfolding lp_a by (rule adds_trans)
    with _ \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> \<open>lp g \<in> keys g\<close> have "g' = g" by (rule rem_3_1_4_aux_1) simp
    with * have "lp g adds to_nat_pm Q'" by (simp only: lp_a)
    from this \<open>to_nat_pm Q' adds lp g\<close> have "lp g = to_nat_pm Q'" by (rule adds_antisym)
    with \<open>is_nat_pm Q'\<close> have eq4: "of_nat_pm (lp g) = Q'" by (simp only: of_nat_pm_comp_to_nat_pm)
    hence eq3: "of_nat_pm (overlapshift (lp g)) = Q" by (simp add: eq1 Q'_def)

    have "membership_problem_concl f1 f2 g (max (deg_pm (lp g)) (deg_pm (overlapshift (lp g))))"
      (is "membership_problem_concl _ _ _ ?a") using f1_pbinomial f2_monomial mpa by (rule thm_3_2_1)
    then obtain q1 q2 where "g = q1 * f1 + q2 * f2" and deg1: "poly_deg (q1 * f1) \<le> ?a"
      and deg2: "poly_deg (q2 * f2) \<le> ?a" by (auto simp: membership_problem_concl_def)

    have "f1 \<in> {f1, f2}" by simp
    hence "Q \<unlhd> P" unfolding Q_def assms(3) by (rule lem_4_3_1) fact+
    hence "deg_pm Q \<le> deg_pm P" by (rule deg_pm_mono_le)

    have "rat ?a = max (deg_pm (of_nat_pm (lp g))) (deg_pm (of_nat_pm (overlapshift (lp g))))"
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
      also have "\<dots> = deg_pm Q - rat (step (lp g)) * deg_pm (vect f1)"
        by (simp only: Q'_def eq4 deg_pm_minus_group deg_pm_map_scale)
      also have "\<dots> \<le> deg_pm Q - rat (step (tp f1)) * deg_pm (vect f1)"
        using \<open>deg_pm (vect f1) < 0\<close> \<open>step (lp g) \<le> step (tp f1)\<close> by simp
      also from \<open>deg_pm Q \<le> deg_pm P\<close> have "\<dots> \<le> deg_pm (P - rat (step (tp f1)) \<cdot> vect f1)"
        by (simp add: deg_pm_minus deg_pm_map_scale)
      also have "\<dots> \<le> ?d" by (rule max.cobounded2)
      finally show ?thesis .
    qed
    finally have "to_nat (rat ?a) \<le> to_nat ?d" by (rule to_nat_mono)
    hence "?a \<le> to_nat ?d" by (simp only: to_nat_of_nat)

    show ?thesis
    proof
      from deg1 \<open>?a \<le> to_nat ?d\<close> have "poly_deg (q1 * f1) \<le> to_nat ?d" by (rule le_trans)
      also have "\<dots> \<le> d" unfolding assms(4) by (rule max.cobounded2)
      finally show "poly_deg (q1 * f1) \<le> d" .
    next
      from deg2 \<open>?a \<le> to_nat ?d\<close> have "poly_deg (q2 * f2) \<le> to_nat ?d" by (rule le_trans)
      also have "\<dots> \<le> d" unfolding assms(4) by (rule max.cobounded2)
      finally show "poly_deg (q2 * f2) \<le> d" .
    qed fact
  qed
qed

theorem thm_4_3_2:
  assumes "P = lcs (of_nat_pm (overlapshift (tp f1))) overlap"
    and "d = max (deg_pm (lp f1)) (to_nat (max (deg_pm P) (deg_pm (P - rat (step (tp f1)) \<cdot> vect f1))))"
  shows "gb_problem d"
proof (rule gb_problemI_reduced_GB)
  fix g
  assume "g \<in> punit.reduced_GB {f1, f2}" (is "g \<in> ?G")
  moreover have "0 \<notin> ?G" by (rule punit.reduced_GB_nonzero_finite) simp
  ultimately have "g \<noteq> 0" by blast
  hence "lp g \<in> keys g" by (rule punit.lt_in_keys)
  from f2_monomial have lp_f2: "lp f2 = tp f2" by (rule punit.lt_eq_tt_monomial)
  have GB_G: "punit.is_Groebner_basis ?G" by (rule punit.reduced_GB_is_GB_finite) simp
  have ideal_G: "ideal ?G = ideal {f1, f2}" by (rule punit.reduced_GB_pmdl_finite[simplified]) simp
  have lc: "lc h = 1" if "h \<in> ?G" for h using _ that
  proof (rule punit.is_monic_setD)
    show "punit.is_monic_set ?G" by (rule punit.reduced_GB_is_monic_set_finite) simp
  next
    from that \<open>0 \<notin> ?G\<close> show "h \<noteq> 0" by blast
  qed
  from f1_pbinomial have "f1 \<noteq> 0" by (rule proper_binomial_not_0)
  have tp1_is_int: "is_int_pm (of_nat_pm (tp f1))" by (intro nat_pm_is_int_pm of_nat_pm_is_nat_pm)
  from \<open>g \<in> ?G\<close> show "\<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d"
  proof (rule binomial_monomial_reduced_GB_cases)
    assume "is_proper_binomial g"
    hence "\<not> is_monomial g \<or> lp g \<noteq> lp f1 \<or> lp g = lp f2"
      by (simp add: is_proper_binomial_def is_monomial_def)
    with \<open>g \<in> ?G\<close> obtain q1 q2 where "g = q1 * f1 + q2 * f2" and "poly_deg (q1 * f1) \<le> d"
      and "poly_deg (q2 * f2) \<le> d" using assms by (rule thm_4_3_2_aux_2)
    thus ?thesis by (intro exI conjI)
  next
    assume "is_monomial g"
    hence "monomial (lc g) (lp g) = g" by (rule punit.monomial_eq_itself)
    moreover assume "lp g = lp f1"
    moreover from \<open>g \<in> ?G\<close> have "lc g = 1" by (rule lc)
    ultimately have g: "g = monomial 1 (lp f1)" by simp
    from \<open>f1 \<noteq> 0\<close> have "lc f1 \<noteq> 0" and "tc f1 \<noteq> 0" by (rule punit.lc_not_0, rule punit.tc_not_0)
    let ?m = "monomial (tc f1) (tp f1)"
    from f1_pbinomial have "binomial (lc f1) (lp f1) (tc f1) (tp f1) = f1"
      by (rule punit.binomial_eq_itself)
    hence "?m + monomial (lc f1) 0 * g = f1"
      by (simp add: g times_monomial_monomial binomial_def add.commute)
    hence g2: "monomial (lc f1) 0 * g = f1 - ?m" by (metis add_diff_cancel_left')
    hence "?m = f1 - monomial (lc f1) 0 * g" by simp
    also have "\<dots> \<in> ideal ?G"
    proof (rule ideal.span_diff)
      show "f1 \<in> ideal ?G" unfolding ideal_G by (rule ideal.span_base) simp
    next
      from \<open>g \<in> ?G\<close> show "monomial (lc f1) 0 * g \<in> ideal ?G" by (intro ideal.span_scale ideal.span_base)
    qed
    finally have "?m \<in> ideal ?G" .
    with GB_G obtain g' where "g' \<in> ?G" and "g' \<noteq> 0" and "lp g' adds lp ?m"
    proof (rule punit.GB_adds_lt[simplified])
      from \<open>tc f1 \<noteq> 0\<close> show "?m \<noteq> 0" by (simp add: monomial_0_iff)
    qed
    from \<open>tc f1 \<noteq> 0\<close> this(3) have "lp g' adds tp f1" by (simp add: punit.lt_monomial)
    hence "lp g' \<preceq> tp f1" by (rule ord_adds)
    also from f1_pbinomial have "\<dots> \<prec> lp f1" by (rule punit.lt_gr_tt_binomial)
    finally have neq: "lp g' \<noteq> lp f1" by simp
    from g2 have "(1 / lc f1) \<cdot> (monomial (lc f1) 0 * g) = (1 / lc f1) \<cdot> (f1 - ?m)" by simp
    with \<open>lc f1 \<noteq> 0\<close> have g3: "g = (1 / lc f1) \<cdot> f1 - monomial (tc f1 / lc f1) (tp f1)"
      by (simp flip: map_scale_eq_times add: map_scale_assoc map_scale_minus_distrib_left)
    from \<open>g' \<in> ?G\<close> show ?thesis
    proof (rule binomial_monomial_reduced_GB_cases)
      fix c
      assume "c \<noteq> 0" and "g' = c \<cdot> f1"
      hence "lp g' = lp f1" by (simp add: punit.lt_map_scale)
      with neq show ?thesis ..
    next
      fix c
      assume "c \<noteq> 0" and "g' = c \<cdot> f2"
      hence "lp g' = lp f2" by (simp add: punit.lt_map_scale)
      from \<open>lp g' adds tp f1\<close> obtain t where t: "tp f1 = lp f2 + t"
        unfolding \<open>lp g' = lp f2\<close> by (rule addsE)
      from f2_monomial have "lc f2 \<noteq> 0" by (intro punit.lc_not_0 monomial_not_0)
      from f2_monomial have "monomial (lc f2) (lp f2) = f2" by (rule punit.monomial_eq_itself)
      hence "monomial (- tc f1 / (lc f1 * lc f2)) t * f2 =
              - monomial (tc f1 / (lc f1 * lc f2)) t * monomial (lc f2) (lp f2)"
        by (simp add: monomial_uminus)
      also from \<open>lc f2 \<noteq> 0\<close> t have "\<dots> = - monomial (tc f1 / lc f1) (tp f1)"
        by (simp add: times_monomial_monomial add.commute)
      finally have eq: "- monomial (tc f1 / lc f1) (tp f1) = monomial (- tc f1 / (lc f1 * lc f2)) t * f2"
        by (rule sym)
      show ?thesis
      proof (intro exI conjI)
        show "g = monomial (1 / lc f1) 0 * f1 + monomial (- tc f1 / (lc f1 * lc f2)) t * f2"
          by (simp add: g3 map_scale_eq_times eq)
      next
        have "poly_deg (monomial (1 / lc f1) 0 * f1) \<le> poly_deg f1"
          by (simp add: poly_deg_map_scale flip: map_scale_eq_times)
        also from assms have "\<dots> \<le> d" by (rule thm_4_3_2_aux_1)
        finally show "poly_deg (monomial (1 / lc f1) 0 * f1) \<le> d" .
      next
        have "poly_deg (monomial (- tc f1 / (lc f1 * lc f2)) t * f2) =
                poly_deg (- monomial (tc f1 / lc f1) (tp f1))" by (simp only: eq)
        also have "\<dots> \<le> deg_pm (tp f1)" by (simp add: poly_deg_monomial)
        also from \<open>f1 \<noteq> 0\<close> have "\<dots> \<le> poly_deg f1" by (intro poly_deg_max_keys punit.tt_in_keys)
        also from assms have "\<dots> \<le> d" by (rule thm_4_3_2_aux_1)
        finally show "poly_deg (monomial (- tc f1 / (lc f1 * lc f2)) t * f2) \<le> d" .
      qed
    next
      assume "lp g' = lp f1"
      with neq show ?thesis ..
    next
      assume "tp f1 adds lp g'"
      with \<open>lp g' adds tp f1\<close> have "lp g' = tp f1" by (rule adds_antisym)
      assume "is_monomial g'"
      hence "monomial (lc g') (lp g') = g'" by (rule punit.monomial_eq_itself)
      moreover from \<open>g' \<in> ?G\<close> have "lc g' = 1" by (rule lc)
      ultimately have g': "g' = monomial 1 (tp f1)" by (simp only: \<open>lp g' = tp f1\<close>)
      have g4: "g = (1 / lc f1) \<cdot> f1 + (- tc f1 / lc f1) \<cdot> g'" by (simp add: g3 g' monomial_uminus)
      from neq have "\<not> is_monomial g' \<or> lp g' \<noteq> lp f1 \<or> lp g' = lp f2" by simp
      with \<open>g' \<in> ?G\<close> obtain q1 q2 where g': "g' = q1 * f1 + q2 * f2" and "poly_deg (q1 * f1) \<le> d"
        and "poly_deg (q2 * f2) \<le> d" using assms by (rule thm_4_3_2_aux_2)
      show ?thesis
      proof (intro exI conjI)
        show "g = (monomial (1 / lc f1) 0 - (tc f1 / lc f1) \<cdot> q1) * f1 + ((- tc f1 / lc f1) \<cdot> q2) * f2"
          by (simp add: g4 g' map_scale_eq_times algebra_simps flip: monomial_uminus)
      next
        have "poly_deg ((monomial (1 / lc f1) 0 - (tc f1 / lc f1) \<cdot> q1) * f1) =
                poly_deg ((1 / lc f1) \<cdot> f1 - (tc f1 / lc f1) \<cdot> (q1 * f1))"
          by (simp only: map_scale_eq_times algebra_simps)
        also have "\<dots> \<le> max (poly_deg ((1 / lc f1) \<cdot> f1)) (poly_deg ((tc f1 / lc f1) \<cdot> (q1 * f1)))"
          by (fact poly_deg_minus_le)
        also have "\<dots> \<le> d"
        proof (rule max.boundedI)
          have "poly_deg ((1 / lc f1) \<cdot> f1) \<le> poly_deg f1" by (simp add: poly_deg_map_scale)
          also from assms have "\<dots> \<le> d" by (rule thm_4_3_2_aux_1)
          finally show "poly_deg ((1 / lc f1) \<cdot> f1) \<le> d" .
        next
          have "poly_deg ((tc f1 / lc f1) \<cdot> (q1 * f1)) \<le> poly_deg (q1 * f1)"
            by (simp add: poly_deg_map_scale)
          also have "\<dots> \<le> d" by fact
          finally show "poly_deg ((tc f1 / lc f1) \<cdot> (q1 * f1)) \<le> d" .
        qed
        finally show "poly_deg ((monomial (1 / lc f1) 0 - (tc f1 / lc f1) \<cdot> q1) * f1) \<le> d" .
      next
        have "poly_deg ((- tc f1 / lc f1) \<cdot> q2 * f2) = poly_deg ((- tc f1 / lc f1) \<cdot> (q2 * f2))"
          by (simp only: map_scale_eq_times mult.assoc)
        also have "\<dots> \<le> poly_deg (q2 * f2)" by (simp add: poly_deg_map_scale)
        also have "\<dots> \<le> d" by fact
        finally show "poly_deg ((- tc f1 / lc f1) \<cdot> q2 * f2) \<le> d" .
      qed
    qed
  next
    fix c
    assume "c \<noteq> 0" and "g = c \<cdot> f2"
    hence "lp g = lp f2" by (simp add: punit.lt_map_scale)
    hence "\<not> is_monomial g \<or> lp g \<noteq> lp f1 \<or> lp g = lp f2" by simp
    with \<open>g \<in> ?G\<close> obtain q1 q2 where "g = q1 * f1 + q2 * f2" and "poly_deg (q1 * f1) \<le> d"
      and "poly_deg (q2 * f2) \<le> d" using assms by (rule thm_4_3_2_aux_2)
    thus ?thesis by (intro exI conjI)
  next
    assume "membership_problem_assms f1 f2 g"
    hence "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
    have "lp g \<noteq> lp f1"
    proof
      assume "lp g = lp f1"
      have "f1 \<in> {f1, f2}" by simp
      moreover from f1_pbinomial have "f1 \<noteq> 0" by (rule proper_binomial_not_0)
      moreover note \<open>lp g \<in> keys g\<close>
      moreover have "lp f1 adds lp g" by (simp add: \<open>lp g = lp f1\<close>)
      ultimately have "punit.is_red {f1, f2} g" by (rule punit.is_red_addsI[simplified])
      with \<open>\<not> punit.is_red {f1, f2} g\<close> show False ..
    qed
    hence "\<not> is_monomial g \<or> lp g \<noteq> lp f1 \<or> lp g = lp f2" by simp
    with \<open>g \<in> ?G\<close> obtain q1 q2 where "g = q1 * f1 + q2 * f2" and "poly_deg (q1 * f1) \<le> d"
      and "poly_deg (q2 * f2) \<le> d" using assms by (rule thm_4_3_2_aux_2)
    thus ?thesis by (intro exI conjI)
  qed
qed

end

end (* two_polys *)

end (* theory *)
