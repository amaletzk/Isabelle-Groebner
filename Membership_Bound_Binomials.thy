section \<open>New Bounds for the Membership Problem for Binomial Ideals\<close>

theory Membership_Bound_Binomials
  imports VPC
begin

subsection \<open>Structure of Binomial Ideals\<close>

(* The following lemmas could be proved in context "gd_term", but the abbreviations for "punit.lt"
  etc. introduced in theory "MPoly_PM" are inconsistent with similar abbreviations introduced
  in "gd_term". *)

context gd_powerprod
begin

abbreviation "lp_set \<equiv> punit.lt_set"

lemma rem_3_1_4_aux_1:
  assumes "finite F" and "g \<in> punit.reduced_GB F" and "g' \<in> punit.reduced_GB F" and "t \<in> keys g"
    and "lp g' adds t"
  shows "g' = g"
proof (rule ccontr)
  let ?G = "punit.reduced_GB F"
  assume "g' \<noteq> g"
  with \<open>g' \<in> ?G\<close> have "g' \<in> ?G - {g}" by simp
  have "\<not> punit.is_red (?G - {g}) g"
    by (rule punit.is_auto_reducedD, rule punit.reduced_GB_is_auto_reduced_finite, fact+)
  moreover have "punit.is_red (?G - {g}) g"
  proof (rule punit.is_red_singletonD, rule punit.is_red_addsI[simplified], rule)
    from punit.reduced_GB_nonzero_finite[OF assms(1)] \<open>g' \<in> ?G\<close> show "g' \<noteq> 0" by auto
  qed fact+
  ultimately show False ..
qed

lemma rem_3_1_4_aux_2:
  assumes fin: "finite F" and "g \<in> punit.reduced_GB F" and "g' \<in> punit.reduced_GB F" and "t \<in> keys g"
    and "lp g' adds t"
  shows "t = lp g"
proof -
  from assms have "g' = g" by (rule rem_3_1_4_aux_1)
  from \<open>lp g' adds t\<close> have "lp g \<preceq> t" unfolding \<open>g' = g\<close> by (rule ord_adds)
  with punit.lt_max_keys[OF \<open>t \<in> keys g\<close>] show ?thesis by simp
qed
  
text \<open>The following two lemmas are contained in Remark 3.1.4. of @{cite WW2015}.\<close>
  
lemma rem_3_1_4_1:
  assumes "finite F" and "g \<in> punit.reduced_GB F" and "lp g \<notin> lp_set F"
  shows "\<not> punit.is_red F g"
proof
  let ?G = "punit.reduced_GB F"
  assume "punit.is_red F g"
  then obtain f t where "f \<in> F" and "t \<in> keys g" and "f \<noteq> 0" and lpf: "lp f adds t"
    by (rule punit.is_red_addsE[simplified])
  have "f \<in> ideal ?G" unfolding punit.reduced_GB_pmdl_finite[OF assms(1), simplified]
    by (rule, fact \<open>f \<in> F\<close>, rule ideal.span_superset)
  from punit.reduced_GB_is_GB_finite[OF assms(1)] this \<open>f \<noteq> 0\<close> obtain g'
    where "g' \<in> ?G" and "g' \<noteq> 0" and lpg': "lp g' adds lp f" by (rule punit.GB_adds_lt[simplified])
  from lpg' lpf have lpg'': "lp g' adds t" by (rule adds_trans)
  from _ \<open>g' \<noteq> 0\<close> \<open>t \<in> keys g\<close> this have red: "punit.is_red {g'} g"
    by (rule punit.is_red_addsI[simplified], simp)
  from assms(1) \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> \<open>t \<in> keys g\<close> lpg'' have "g' = g" and "t = lp g"
    by (rule rem_3_1_4_aux_1, rule rem_3_1_4_aux_2)
  from lpg' lpf have "lp g = lp f" unfolding \<open>t = lp g\<close> \<open>g' = g\<close> by (rule adds_antisym)
  from \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> have "lp g \<in> lp_set F" unfolding \<open>lp g = lp f\<close> by (rule punit.lt_setI)
  with assms(3) show False ..
qed

lemma rem_3_1_4_2:
  assumes "finite F" and "g \<in> punit.reduced_GB F" and "is_proper_binomial g"
  shows "monomial 1 ` (keys g) \<inter> ideal F = {}"
  unfolding disjoint_eq_subset_Compl
proof (rule, rule)
  let ?G = "punit.reduced_GB F"
  fix x
  assume xin1: "x \<in> monomial 1 ` (keys g)" and xin2: "x \<in> ideal F"
  from assms(3) obtain c d s t where obd: "punit.is_obd c s d t" and g: "g = binomial c s d t"
    by (rule punit.is_proper_binomial_binomial_od)
  from obd have pbd: "is_pbd c s d t" by (rule punit.obd_imp_pbd)
  have keysg: "keys g = {s, t}" unfolding g by (rule keys_binomial_pbd, fact pbd)
  
  have a: "monomial 1 t \<notin> ideal F"
  proof
    assume "monomial 1 t \<in> ideal F" (is "?p \<in> ideal F")
    with assms(1) have "?p \<in> ideal ?G" by (simp only: punit.reduced_GB_pmdl_finite[simplified])
    have "?p \<noteq> 0" by (simp add: monomial_0_iff)
    from punit.reduced_GB_is_GB_finite[OF assms(1)] \<open>?p \<in> ideal ?G\<close> this obtain g'
      where "g' \<in> ?G" and "g' \<noteq> 0" and lpg': "lp g' adds lp ?p" by (rule punit.GB_adds_lt[simplified])
    from lpg' have lpg'': "lp g' adds t" by (simp add: punit.lt_monomial)
    have "t \<in> keys g" unfolding keysg by simp
    from assms(1) \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> this lpg'' have "t = lp g" by (rule rem_3_1_4_aux_2)
    also have "\<dots> = s" unfolding g punit.lt_binomial[OF obd] ..
    finally show False using obd by (simp add: punit.is_obd_def)
  qed

  from xin1 have "x = monomial 1 s \<or> x = monomial 1 t" unfolding keysg by simp
  thus False
  proof
    assume x: "x = monomial 1 s"
    from pbd have "d \<noteq> 0" by (rule is_pbdD)
    have "g \<in> ideal F" unfolding punit.reduced_GB_pmdl_finite[simplified, OF assms(1), symmetric]
      by (rule, fact \<open>g \<in> ?G\<close>, rule ideal.span_superset)
    from xin2 have "monomial 1 s \<in> ideal F" unfolding x .
    hence "punit.monom_mult c 0 (monomial 1 s) \<in> ideal F"
      by (rule punit.pmdl_closed_monom_mult[simplified])
    hence "monomial c s \<in> ideal F" by (simp add: punit.monom_mult_monomial)
    with \<open>g \<in> ideal F\<close> have "g - monomial c s \<in> ideal F" by (rule ideal.span_diff)
    hence "monomial d t \<in> ideal F" by (simp add: g binomial_def)
    hence "punit.monom_mult (1 / d) 0 (monomial d t) \<in> ideal F"
      by (rule punit.pmdl_closed_monom_mult[simplified])
    hence "monomial 1 t \<in> ideal F" using \<open>d \<noteq> 0\<close> by (simp add: punit.monom_mult_monomial)
    with a show False ..
  next
    assume x: "x = monomial 1 t"
    from a xin2 show False unfolding x ..
  qed
qed

end (* gd_powerprod *)

subsection \<open>Preliminaries\<close>

context ordered_powerprod
begin

lemma rem_3_1_7_aux:
  assumes "g \<in> ideal F" and "t \<in> keys g"
  obtains f s where "f \<in> F" and "s \<in> keys f" and "s adds (t::'a)"
  using assms
proof (induct g arbitrary: thesis rule: ideal.span_induct')
  case base
  from base(2) show ?case unfolding keys_zero ..
next
  case (step g c f')
  from step(6) keys_add_subset have "t \<in> keys g \<union> keys (c * f')" ..
  thus ?case
  proof
    assume "t \<in> keys g"
    obtain f s where "f \<in> F" and "s \<in> keys f" and "s adds t"
    proof (rule step(2))
      show "t \<in> keys g" by fact
    qed
    thus ?thesis by (rule step(5))
  next
    assume "t \<in> keys (c * f')"
    then obtain s1 s2 where "s2 \<in> keys f'" and "t = s1 + s2" by (rule in_keys_timesE)
    from \<open>f' \<in> F\<close> this(1) show ?thesis
    proof (rule step(5))
      show "s2 adds t" by (simp add: \<open>t = s1 + s2\<close>)
    qed
  qed
qed

lemma rem_3_1_7:
  assumes "is_binomial_set F" and gin: "g \<in> ideal F" and "\<not> punit.is_red F g" and tin: "t \<in> keys g"
  obtains f where "f \<in> F" and "is_proper_binomial f" and "tp f adds t"
proof -
  from gin tin obtain f s where "f \<in> F" and "s \<in> keys f" and "s adds t" by (rule rem_3_1_7_aux)
  have "s \<noteq> lp f"
  proof
    assume "s = lp f"
    from \<open>f \<in> F\<close> have "punit.is_red F g"
    proof (rule punit.is_red_addsI[simplified])
      show "f \<noteq> 0"
      proof
        assume "f = 0"
        from \<open>s \<in> keys f\<close> show False unfolding \<open>f = 0\<close> keys_zero ..
      qed
    next
      from \<open>s adds t\<close> show "lp f adds t" unfolding \<open>s = lp f\<close> .
    qed fact
    with \<open>\<not> punit.is_red F g\<close> show False ..
  qed
  from assms(1) \<open>f \<in> F\<close> have "is_binomial f" by (rule is_binomial_setD)
  hence "is_monomial f \<or> is_proper_binomial f" unfolding is_binomial_alt .
  hence "is_proper_binomial f"
  proof
    assume "is_monomial f"
    hence "keys f = {lp f}" by (rule punit.keys_monomial)
    with \<open>s \<in> keys f\<close> \<open>s \<noteq> lp f\<close> show ?thesis by simp
  qed
  with \<open>f \<in> F\<close> show ?thesis
  proof
    from \<open>is_binomial f\<close> have "keys f = {lp f, tp f}" by (rule punit.keys_binomial)
    with \<open>s \<in> keys f\<close> \<open>s \<noteq> lp f\<close> have "s = tp f" by simp
    with \<open>s adds t\<close> show "tp f adds t" by simp
  qed
qed

end (* ordered_powerprod *)

context pm_powerprod
begin

definition membership_problem_assms ::
    "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> bool"
    where "membership_problem_assms f1 f2 g =
        (is_binomial f1 \<and> is_binomial f2 \<and> is_binomial g \<and> g \<in> ideal {f1, f2} \<and>
          \<not> punit.is_red {f1, f2} g \<and> (is_proper_binomial g \<longrightarrow> \<not> (monomial 1 ` keys g) \<subseteq> ideal {f1, f2}))"

definition membership_problem_concl ::
    "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_1) \<Rightarrow> nat \<Rightarrow> bool"
  where "membership_problem_concl f1 f2 g d =
        (\<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and>
          (q1 \<noteq> 0 \<longrightarrow> poly_deg (q1 * f1) \<le> d) \<and>
          (q2 \<noteq> 0 \<longrightarrow> poly_deg (q2 * f2) \<le> d))"

definition membership_problem :: "('b::field itself) \<Rightarrow> nat \<Rightarrow> bool"
  where "membership_problem _ d =
      (\<forall>f1 f2 g::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b. membership_problem_assms f1 f2 g \<longrightarrow>
        membership_problem_concl f1 f2 g d)"
    
lemma membership_problem_assmsD:
  assumes "membership_problem_assms f1 f2 g"
  shows "is_binomial f1" and "is_binomial f2" and "is_binomial g" and "g \<in> ideal {f1, f2}"
    and "\<not> punit.is_red {f1, f2} g" and "is_proper_binomial g \<Longrightarrow> \<not> (monomial 1 ` keys g) \<subseteq> ideal {f1, f2}"
  using assms by (simp_all add: membership_problem_assms_def)

lemma membership_problemI:
  assumes "\<And>f1 f2 g::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field. membership_problem_assms f1 f2 g \<Longrightarrow>
            membership_problem_concl f1 f2 g d"
  shows "membership_problem TYPE('b) d"
  unfolding membership_problem_def using assms by auto

lemma membership_problem_assms_lp_f1_nadds:
  assumes "membership_problem_assms f1 f2 g" and "t \<in> keys g"
  shows "\<not> lp f1 adds t"
proof
  assume "lp f1 adds t"
  from _ _ \<open>t \<in> keys g\<close> this have "punit.is_red {f1, f2} g"
  proof (rule punit.is_red_addsI[simplified], simp)
    from assms(1) have "is_binomial f1" by (rule membership_problem_assmsD)
    thus "f1 \<noteq> 0" by (rule binomial_not_0)
  qed
  moreover from assms(1) have "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
  ultimately show False by simp
qed

lemma membership_problem_assms_lp_f2_nadds:
  assumes "membership_problem_assms f1 f2 g" and "t \<in> keys g"
  shows "\<not> lp f2 adds t"
proof
  assume "lp f2 adds t"
  from _ _ \<open>t \<in> keys g\<close> this have "punit.is_red {f1, f2} g"
  proof (rule punit.is_red_addsI[simplified], simp)
    from assms(1) have "is_binomial f2" by (rule membership_problem_assmsD)
    thus "f2 \<noteq> 0" by (rule binomial_not_0)
  qed
  moreover from assms(1) have "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
  ultimately show False by simp
qed

lemma membership_problem_assms_rep:
  assumes "membership_problem_assms f1 f2 g" and "g = q1 * f1 + q2 * f2"
  shows "q1 * f1 \<noteq> 0" and "q2 * f2 \<noteq> 0" and "lp (q1 * f1) = lp (q2 * f2)" and "lc (q1 * f1) = - lc (q2 * f2)"
proof -
  from assms(1) have "is_binomial f1" by (rule membership_problem_assmsD)
  hence "f1 \<noteq> 0" by (rule binomial_not_0)
  from assms(1) have "is_binomial f2" by (rule membership_problem_assmsD)
  hence "f2 \<noteq> 0" by (rule binomial_not_0)
  from assms(1) have "is_binomial g" by (rule membership_problem_assmsD)
  hence "g \<noteq> 0" by (rule binomial_not_0)

  have "q1 \<noteq> 0"
  proof
    assume "q1 = 0"
    with assms(2) have g: "g = q2 * f2" by simp
    with \<open>g \<noteq> 0\<close> have "q2 * f2 \<noteq> 0" by simp
    hence "q2 \<noteq> 0" by auto
    hence "lp q2 + lp f2 = lp (q2 * f2)" using \<open>f2 \<noteq> 0\<close> by (rule lp_times[symmetric])
    also from \<open>q2 * f2 \<noteq> 0\<close> have "\<dots> \<in> keys (q2 * f2)" by (rule punit.lt_in_keys)
    finally have "lp q2 + lp f2 \<in> keys g" by (simp only: g)
    with assms(1) have "\<not> lp f2 adds lp q2 + lp f2" by (rule membership_problem_assms_lp_f2_nadds)
    thus False by simp
  qed
  thus "q1 * f1 \<noteq> 0" using \<open>f1 \<noteq> 0\<close> by (simp add: times_not_zero)
  have 1: "lp (q1 * f1) \<notin> keys g"
  proof
    from \<open>q1 \<noteq> 0\<close> \<open>f1 \<noteq> 0\<close> have "lp q1 + lp f1 = lp (q1 * f1)" by (rule lp_times[symmetric])
    also assume "\<dots> \<in> keys g"
    finally have "lp q1 + lp f1 \<in> keys g" .
    with assms(1) have "\<not> lp f1 adds lp q1 + lp f1" by (rule membership_problem_assms_lp_f1_nadds)
    thus False by simp
  qed

  have "q2 \<noteq> 0"
  proof
    assume "q2 = 0"
    with assms(2) have g: "g = q1 * f1" by simp
    from \<open>q1 * f1 \<noteq> 0\<close> have "lp (q1 * f1) \<in> keys g" unfolding g by (rule punit.lt_in_keys)
    with 1 show False ..
  qed
  thus "q2 * f2 \<noteq> 0" using \<open>f2 \<noteq> 0\<close> by (simp add: times_not_zero)
  have 2: "lp (q2 * f2) \<notin> keys g"
  proof
    from \<open>q2 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have "lp q2 + lp f2 = lp (q2 * f2)" by (rule lp_times[symmetric])
    also assume "\<dots> \<in> keys g"
    finally have "lp q2 + lp f2 \<in> keys g" .
    with assms(1) have "\<not> lp f2 adds lp q2 + lp f2" by (rule membership_problem_assms_lp_f2_nadds)
    thus False by simp
  qed

  show 3: "lp (q1 * f1) = lp (q2 * f2)"
  proof (rule ordered_powerprod_lin.linorder_cases)
    assume *: "lp (q1 * f1) \<prec> lp (q2 * f2)"
    from \<open>q2 * f2 \<noteq> 0\<close> have "lp (q2 * f2) \<in> keys (q2 * f2)" by (rule punit.lt_in_keys)
    moreover from * have "lp (q2 * f2) \<notin> keys (q1 * f1)" by (auto dest: punit.lt_max_keys simp only:)
    ultimately have "lp (q2 * f2) \<in> keys g" unfolding assms(2) by (rule in_keys_plusI2)
    with 2 show ?thesis ..
  next
    assume *: "lp (q2 * f2) \<prec> lp (q1 * f1)"
    from \<open>q1 * f1 \<noteq> 0\<close> have "lp (q1 * f1) \<in> keys (q1 * f1)" by (rule punit.lt_in_keys)
    moreover from * have "lp (q1 * f1) \<notin> keys (q2 * f2)" by (auto dest: punit.lt_max_keys simp only:)
    ultimately have "lp (q1 * f1) \<in> keys g" unfolding assms(2) by (rule in_keys_plusI1)
    with 1 show ?thesis ..
  qed

  from 1 have "0 = lookup (q1 * f1) (lp (q1 * f1)) + lookup (q2 * f2) (lp (q1 * f1))"
    by (simp add: assms(2) lookup_add)
  also have "\<dots> = lookup (q1 * f1) (lp (q1 * f1)) + lookup (q2 * f2) (lp (q2 * f2))"
    by (simp only: 3)
  also have "\<dots> = lc (q1 * f1) + lc (q2 * f2)" by (simp only: punit.lc_def)
  finally show "lc (q1 * f1) = - lc (q2 * f2)" by (simp add: eq_neg_iff_add_eq_0)
qed

(* TODO: Maybe it's better to extend (\<preceq>) canonically to an ordering (\<preceq>\<^sub>Q) for rational exponents?
  (\<preceq>\<^sub>Q) is no admissible ordering, because 0 is not the smallest element, but nevertheless it
  shares *a lot* of properties with (\<preceq>). *)
lemma ord_rat:
  assumes "s \<prec> t" and "of_nat_pm s = p + l \<cdot> vect f" and "of_nat_pm t = p + l' \<cdot> vect f"
  shows "l < l'"
proof -
  have eq: "of_nat_pm t - of_nat_pm s = (l' - l) \<cdot> vect f"
    by (simp add: assms(2, 3) map_scale_minus_distrib_right)
  obtain a b :: int where 1: "l' - l = Fract a b" and "0 < b" by (rule Rat_cases)
  moreover have "0 < a"
  proof (rule ccontr)
    assume "\<not> 0 < a"
    hence "0 \<le> - a" by simp
    moreover define m where "m = nat (- a)"
    ultimately have m: "rat m = - rat_of_int a" by simp
    define n where "n = nat b"
    with \<open>0 < b\<close> have "0 < n" and n: "rat n = rat_of_int b" by simp_all
    have 2: "l' - l = (- rat m) / rat n" by (simp only: 1 m n Fract_of_int_quotient)
    hence "rat n \<cdot> (of_nat_pm t - of_nat_pm s) = rat n \<cdot> ((- rat m) / rat n) \<cdot> vect f"
      by (simp only: eq)
    with \<open>0 < n\<close> have "rat n \<cdot> of_nat_pm t + rat m \<cdot> of_nat_pm (lp f) =
                        rat n \<cdot> of_nat_pm s + rat m \<cdot> of_nat_pm (tp f)"
      by (simp add: vect_alt algebra_simps map_scale_assoc map_scale_uminus_left)
    hence "of_nat_pm (n \<cdot> t + m \<cdot> lp f) = (of_nat_pm (n \<cdot> s + m \<cdot> tp f) ::_ \<Rightarrow>\<^sub>0 rat)"
      by (simp only: of_nat_pm_plus of_nat_pm_map_scale)
    hence eq2: "n \<cdot> t + m \<cdot> lp f = n \<cdot> s + m \<cdot> tp f" by simp
    from assms(1) \<open>0 < n\<close> have "n \<cdot> s \<prec> n \<cdot> t" by (rule map_scale_mono_strict_left)
    hence "n \<cdot> s + m \<cdot> tp f \<prec> n \<cdot> t + m \<cdot> tp f" by (rule plus_monotone_strict)
    from punit.lt_ge_tt have "m \<cdot> tp f \<preceq> m \<cdot> lp f" by (rule map_scale_mono_left)
    hence "n \<cdot> t + m \<cdot> tp f \<preceq> n \<cdot> t + m \<cdot> lp f" by (rule plus_monotone_left)
    with \<open>n \<cdot> s + m \<cdot> tp f \<prec> n \<cdot> t + m \<cdot> tp f\<close> have "n \<cdot> s + m \<cdot> tp f \<prec> n \<cdot> t + m \<cdot> lp f"
      by (rule ordered_powerprod_lin.less_le_trans)
    thus False by (simp add: eq2)
  qed
  ultimately have "0 < l' - l" by (simp add: zero_less_Fract_iff)
  thus "l < l'" by simp
qed

subsubsection \<open>Parallel Binomials\<close>

definition parallel_binomials :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "parallel_binomials f1 f2 \<longleftrightarrow> (is_proper_binomial f1 \<and> is_proper_binomial f2 \<and>
    (\<exists>m1 m2::nat. m1 \<noteq> 0 \<and> m2 \<noteq> 0 \<and> m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2))"

lemma parallel_binomialsD:
  assumes "parallel_binomials f1 f2"
  shows "is_proper_binomial f1" and "is_proper_binomial f2"
  using assms by (simp_all add: parallel_binomials_def)

lemma parallel_binomialsE:
  assumes "parallel_binomials f1 f2"
  obtains m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0" and "m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2"
  using assms unfolding parallel_binomials_def by blast

lemma parallel_binomials_sym:
  assumes "parallel_binomials f1 f2"
  shows "parallel_binomials f2 f1"
proof -
  from assms have "is_proper_binomial f1" and "is_proper_binomial f2" by (rule parallel_binomialsD)+
  from assms obtain m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0" and eq: "m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2"
    by (rule parallel_binomialsE)
  show ?thesis unfolding parallel_binomials_def
  proof (intro conjI exI)
    show "m2 \<cdot> lp f2 + m1 \<cdot> tp f1 = m2 \<cdot> tp f2 + m1 \<cdot> lp f1" by (simp add: ac_simps eq)
  qed fact+
qed

lemma parallel_binomialsI_vect:
  assumes "is_proper_binomial f1" and "is_proper_binomial f2" and "vect f1 = m \<cdot> vect f2"
  shows "parallel_binomials f1 f2"
  unfolding parallel_binomials_def
proof (intro conjI)
  from assms(1) have "tp f1 \<prec> lp f1" by (rule punit.lt_gr_tt_binomial)
  moreover have "of_nat_pm (tp f1) = of_nat_pm (tp f1) + 0 \<cdot> vect f2" by simp
  moreover have "of_nat_pm (lp f1) = of_nat_pm (tp f1) + m \<cdot> vect f2"
    by (simp flip: assms(3)) (simp add: vect_alt)
  ultimately have "0 < m" by (rule ord_rat)
  obtain m2 m1 where "0 < m1" and m: "m = Fract m2 m1" by (rule Rat_cases)
  with \<open>0 < m\<close> have "0 < m2" by (simp only: zero_less_Fract_iff)
  from \<open>0 < m1\<close> have m1: "rat (nat m1) = rat_of_int m1" by auto
  from \<open>0 < m2\<close> have m2: "rat (nat m2) = rat_of_int m2" by auto
  show "\<exists>m1 m2. m1 \<noteq> 0 \<and> m2 \<noteq> 0 \<and> m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2"
  proof (intro exI conjI)
    from \<open>0 < m1\<close> show "nat m1 \<noteq> 0" by simp
  next
    from \<open>0 < m2\<close> show "nat m2 \<noteq> 0" by simp
  next
    have "rat_of_int m1 \<cdot> vect f1 = rat_of_int m1 \<cdot> m \<cdot> vect f2" by (simp only: assms(3))
    also from \<open>0 < m1\<close> have "\<dots> = rat_of_int m2 \<cdot> vect f2"
      by (simp add: m map_scale_assoc Fract_of_int_quotient)
    finally have "of_nat_pm (nat m1 \<cdot> lp f1 + nat m2 \<cdot> tp f2) =
                  (of_nat_pm (nat m1 \<cdot> tp f1 + nat m2 \<cdot> lp f2) :: _ \<Rightarrow>\<^sub>0 rat)"
      by (simp only: vect_alt algebra_simps of_nat_pm_map_scale of_nat_pm_plus m1 m2)
    thus "nat m1 \<cdot> lp f1 + nat m2 \<cdot> tp f2 = nat m1 \<cdot> tp f1 + nat m2 \<cdot> lp f2" by simp
  qed
qed fact+

lemma parallel_binomialsI_vect':
  assumes "keys f1 = {s1, t1}" and "keys f2 = {s2, t2}" and "s1 \<noteq> t1" and "s2 \<noteq> t2"
    and "of_nat_pm s1 - of_nat_pm t1 = (m::rat) \<cdot> (of_nat_pm s2 - of_nat_pm t2)"
  shows "parallel_binomials f1 (f2::_ \<Rightarrow>\<^sub>0 'b::comm_monoid_add)"
proof -
  let ?c1 = "lookup f1 s1"
  let ?d1 = "lookup f1 t1"
  let ?c2 = "lookup f2 s2"
  let ?d2 = "lookup f2 t2"
  from assms(3) have "is_proper_binomial f1" by (simp add: is_proper_binomial_def assms(1))
  moreover have "s1 \<in> keys f1" and "t1 \<in> keys f1" by (simp_all add: assms(1))
  ultimately have f1: "binomial ?c1 s1 ?d1 t1 = f1"
    using assms(3) by (rule is_proper_binomial_eq_binomial[symmetric])
  from \<open>s1 \<in> keys f1\<close> \<open>t1 \<in> keys f1\<close> have "?c1 \<noteq> 0" and "?d1 \<noteq> 0" by simp_all
  from assms(4) have "is_proper_binomial f2" by (simp add: is_proper_binomial_def assms(2))
  moreover have "s2 \<in> keys f2" and "t2 \<in> keys f2" by (simp_all add: assms(2))
  ultimately have f2: "binomial ?c2 s2 ?d2 t2 = f2"
    using assms(4) by (rule is_proper_binomial_eq_binomial[symmetric])
  from \<open>s2 \<in> keys f2\<close> \<open>t2 \<in> keys f2\<close> have "?c2 \<noteq> 0" and "?d2 \<noteq> 0" by simp_all
  show ?thesis
  proof (rule ordered_powerprod_lin.linorder_cases)
    assume "s1 \<prec> t1"
    with \<open>?c1 \<noteq> 0\<close> \<open>?d1 \<noteq> 0\<close> have "punit.is_obd ?d1 t1 ?c1 s1" by (simp add: punit.is_obd_def)
    hence "lp (binomial ?c1 s1 ?d1 t1) = t1" and "tp (binomial ?c1 s1 ?d1 t1) = s1"
      by (simp_all add: punit.lt_binomial punit.tt_binomial binomial_comm[of ?c1])
    hence v1: "vect f1 = - (of_nat_pm s1 - of_nat_pm t1)" by (simp add: f1 vect_alt)
    show ?thesis
    proof (rule ordered_powerprod_lin.linorder_cases)
      assume "s2 \<prec> t2"
      with \<open>?c2 \<noteq> 0\<close> \<open>?d2 \<noteq> 0\<close> have "punit.is_obd ?d2 t2 ?c2 s2" by (simp add: punit.is_obd_def)
      hence "lp (binomial ?c2 s2 ?d2 t2) = t2" and "tp (binomial ?c2 s2 ?d2 t2) = s2"
        by (simp_all add: punit.lt_binomial punit.tt_binomial binomial_comm[of ?c2])
      hence v2: "vect f2 = - (of_nat_pm s2 - of_nat_pm t2)" by (simp add: f2 vect_alt)
      show ?thesis
      proof (rule parallel_binomialsI_vect)
        show "vect f1 = m \<cdot> vect f2" by (simp only: v1 v2 assms(5) map_scale_uminus_right)
      qed fact+
    next
      assume "t2 \<prec> s2"
      with \<open>?c2 \<noteq> 0\<close> \<open>?d2 \<noteq> 0\<close> have "punit.is_obd ?c2 s2 ?d2 t2" by (simp add: punit.is_obd_def)
      hence "tp (binomial ?c2 s2 ?d2 t2) = t2" and "lp (binomial ?c2 s2 ?d2 t2) = s2"
        by (simp_all add: punit.lt_binomial punit.tt_binomial)
      hence v2: "vect f2 = of_nat_pm s2 - of_nat_pm t2" by (simp add: f2 vect_alt)
      show ?thesis
      proof (rule parallel_binomialsI_vect)
        show "vect f1 = (- m) \<cdot> vect f2"
          by (simp only: v1 v2 assms(5) map_scale_uminus_right map_scale_uminus_left)
      qed fact+
    next
      assume "s2 = t2"
      with assms(4) show ?thesis ..
    qed
  next
    assume "t1 \<prec> s1"
    with \<open>?c1 \<noteq> 0\<close> \<open>?d1 \<noteq> 0\<close> have "punit.is_obd ?c1 s1 ?d1 t1" by (simp add: punit.is_obd_def)
    hence "tp (binomial ?c1 s1 ?d1 t1) = t1" and "lp (binomial ?c1 s1 ?d1 t1) = s1"
      by (simp_all add: punit.lt_binomial punit.tt_binomial)
    hence v1: "vect f1 = of_nat_pm s1 - of_nat_pm t1" by (simp add: f1 vect_alt)
    show ?thesis
    proof (rule ordered_powerprod_lin.linorder_cases)
      assume "s2 \<prec> t2"
      with \<open>?c2 \<noteq> 0\<close> \<open>?d2 \<noteq> 0\<close> have "punit.is_obd ?d2 t2 ?c2 s2" by (simp add: punit.is_obd_def)
      hence "lp (binomial ?c2 s2 ?d2 t2) = t2" and "tp (binomial ?c2 s2 ?d2 t2) = s2"
        by (simp_all add: punit.lt_binomial punit.tt_binomial binomial_comm[of ?c2])
      hence v2: "vect f2 = - (of_nat_pm s2 - of_nat_pm t2)" by (simp add: f2 vect_alt)
      show ?thesis
      proof (rule parallel_binomialsI_vect)
        show "vect f1 = (- m) \<cdot> vect f2"
          by (simp only: v1 v2 assms(5) map_scale_uminus_right map_scale_uminus_left) simp
      qed fact+
    next
      assume "t2 \<prec> s2"
      with \<open>?c2 \<noteq> 0\<close> \<open>?d2 \<noteq> 0\<close> have "punit.is_obd ?c2 s2 ?d2 t2" by (simp add: punit.is_obd_def)
      hence "tp (binomial ?c2 s2 ?d2 t2) = t2" and "lp (binomial ?c2 s2 ?d2 t2) = s2"
        by (simp_all add: punit.lt_binomial punit.tt_binomial)
      hence v2: "vect f2 = of_nat_pm s2 - of_nat_pm t2" by (simp add: f2 vect_alt)
      show ?thesis
      proof (rule parallel_binomialsI_vect)
        show "vect f1 = m \<cdot> vect f2" by (simp only: v1 v2 assms(5))
      qed fact+
    next
      assume "s2 = t2"
      with assms(4) show ?thesis ..
    qed
  next
    assume "s1 = t1"
    with assms(3) show ?thesis ..
  qed
qed

lemma parallel_binomialsE_vect:
  assumes "parallel_binomials f1 f2"
  obtains m::rat where "0 < m" and "vect f1 = m \<cdot> vect f2"
proof -
  from assms obtain m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0"
    and eq: "m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2" by (rule parallel_binomialsE)
  show ?thesis
  proof
    from \<open>m1 \<noteq> 0\<close> \<open>m2 \<noteq> 0\<close> show "0 < rat m2 / rat m1" by simp
  next
    have "of_nat_pm (m1 \<cdot> lp f1 + m2 \<cdot> tp f2) = (of_nat_pm (m1 \<cdot> tp f1 + m2 \<cdot> lp f2) :: _ \<Rightarrow>\<^sub>0 rat)"
      by (simp only: eq)
    hence "rat m1 \<cdot> of_nat_pm (lp f1) + rat m2 \<cdot> of_nat_pm (tp f2) =
            rat m1 \<cdot> of_nat_pm (tp f1) + rat m2 \<cdot> of_nat_pm (lp f2)"
      by (simp add: of_nat_pm_plus of_nat_pm_map_scale)
    hence "rat m1 \<cdot> vect f1 = rat m2 \<cdot> vect f2" by (simp add: vect_alt algebra_simps)
    hence "(1 / rat m1) \<cdot> rat m1 \<cdot> vect f1 = (1 / rat m1) \<cdot> rat m2 \<cdot> vect f2" by (simp only:)
    with \<open>m1 \<noteq> 0\<close> show "vect f1 = (rat m2 / rat m1) \<cdot> vect f2" by (simp add: map_scale_assoc)
  qed
qed

lemma parallel_binomialsE_lookup:
  assumes "parallel_binomials f1 f2"
  obtains m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0"
    and "\<forall>x. m1 * lookup (lp f1) x + m2 * lookup (tp f2) x = m1 * lookup (tp f1) x + m2 * lookup (lp f2) x"
proof -
  from assms obtain m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0" and *: "m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2"
    by (rule parallel_binomialsE)
  from this(1) this(2) show ?thesis
  proof
    show "\<forall>x. m1 * lookup (lp f1) x + m2 * lookup (tp f2) x = m1 * lookup (tp f1) x + m2 * lookup (lp f2) x"
    proof
      fix x
      from * have "lookup (m1 \<cdot> lp f1 + m2 \<cdot> tp f2) x = lookup (m1 \<cdot> tp f1 + m2 \<cdot> lp f2) x" by simp
      thus "m1 * lookup (lp f1) x + m2 * lookup (tp f2) x = m1 * lookup (tp f1) x + m2 * lookup (lp f2) x"
        by (simp add: lookup_add)
    qed
  qed
qed

text \<open>This version is weaker but sometimes easier to use:\<close>
lemma parallel_binomialsE_lookup':
  assumes "parallel_binomials f1 f2"
  obtains m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0"
    and "m1 * lookup (lp f1) x + m2 * lookup (tp f2) x = m1 * lookup (tp f1) x + m2 * lookup (lp f2) x"
proof -
  from assms obtain m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0"
    and "\<forall>x. m1 * lookup (lp f1) x + m2 * lookup (tp f2) x = m1 * lookup (tp f1) x + m2 * lookup (lp f2) x"
    by (rule parallel_binomialsE_lookup)
  from this(3) have "m1 * lookup (lp f1) x + m2 * lookup (tp f2) x = m1 * lookup (tp f1) x + m2 * lookup (lp f2) x" ..
  with \<open>m1 \<noteq> 0\<close> \<open>m2 \<noteq> 0\<close> show ?thesis ..
qed

lemma parallel_binomials_homogenizeI:
  assumes "parallel_binomials f1 f2" and "h \<notin> indets f1" and "h \<notin> indets f2"
  shows "parallel_binomials (homogenize h f1) (homogenize h f2)"
proof -
  let ?f = "(\<lambda>p t. Poly_Mapping.single h (poly_deg p - deg_pm t) + t)"
  let ?f1 = "homogenize h f1"
  let ?f2 = "homogenize h f2"
  from assms(1) have "is_proper_binomial f1" by (rule parallel_binomialsD)
  hence k1: "keys f1 = {lp f1, tp f1}" and 1: "card (keys f1) = 2"
    by (rule punit.keys_proper_binomial, simp only: is_proper_binomial_def)
  from assms(2) this(1) have "keys ?f1 = {?f f1 (lp f1), ?f f1 (tp f1)}"
    by (simp add: keys_homogenize)
  moreover from assms(2) have "card (keys ?f1) = 2" by (simp add: card_keys_homogenize 1)
  ultimately have "?f f1 (lp f1) \<noteq> ?f f1 (tp f1)" by auto
  from assms(1) have "is_proper_binomial f2" by (rule parallel_binomialsD)
  hence k2: "keys f2 = {lp f2, tp f2}" and 2: "card (keys f2) = 2"
    by (rule punit.keys_proper_binomial, simp only: is_proper_binomial_def)
  from assms(3) this(1) have "keys ?f2 = {?f f2 (lp f2), ?f f2 (tp f2)}"
    by (simp add: keys_homogenize)
  moreover from assms(3) have "card (keys ?f2) = 2" by (simp add: card_keys_homogenize 2)
  ultimately have "?f f2 (lp f2) \<noteq> ?f f2 (tp f2)" by auto
  from assms(1) obtain m where m: "vect f1 = m \<cdot> vect f2" by (rule parallel_binomialsE_vect)
  hence "deg_pm (vect f1) = m * deg_pm (vect f2)" by (simp only: deg_pm_map_scale)
  hence eq0: "rat (deg_pm (tp f1)) - rat (deg_pm (lp f1)) = m * (rat (deg_pm (tp f2)) - rat (deg_pm (lp f2)))"
    by (simp add: vect_alt deg_pm_minus_group deg_of_nat_pm algebra_simps)
  show ?thesis
  proof (rule parallel_binomialsI_vect')
    have "lp f1 \<in> keys f1" and "tp f1 \<in> keys f1" by (simp_all add: k1)
    hence "deg_pm (lp f1) \<le> poly_deg f1" and "deg_pm (tp f1) \<le> poly_deg f1"
      by (auto intro: poly_deg_max_keys)
    hence eq1: "rat (poly_deg f1 - deg_pm (lp f1)) = rat (poly_deg f1) - rat (deg_pm (lp f1))"
      and eq2: "rat (poly_deg f1 - deg_pm (tp f1)) = rat (poly_deg f1) - rat (deg_pm (tp f1))"
      by simp_all
    have "lp f2 \<in> keys f2" and "tp f2 \<in> keys f2" by (simp_all add: k2)
    hence "deg_pm (lp f2) \<le> poly_deg f2" and "deg_pm (tp f2) \<le> poly_deg f2"
      by (auto intro: poly_deg_max_keys)
    hence eq3: "rat (poly_deg f2 - deg_pm (lp f2)) = rat (poly_deg f2) - rat (deg_pm (lp f2))"
      and eq4: "rat (poly_deg f2 - deg_pm (tp f2)) = rat (poly_deg f2) - rat (deg_pm (tp f2))"
      by simp_all
    have "of_nat_pm (?f f1 (lp f1)) - of_nat_pm (?f f1 (tp f1)) =
            Poly_Mapping.single h (rat (poly_deg f1 - deg_pm (lp f1)) -
            rat (poly_deg f1 - deg_pm (tp f1))) + vect f1"
      by (simp add: of_nat_pm_plus vect_alt of_nat_pm_single flip: single_diff)
    also have "\<dots> = Poly_Mapping.single h (rat (deg_pm (tp f1)) - rat (deg_pm (lp f1))) + m \<cdot> vect f2"
      by (simp add: eq1 eq2 m)
    also have "\<dots> = m \<cdot> (Poly_Mapping.single h (rat (deg_pm (tp f2)) - rat (deg_pm (lp f2))) + vect f2)"
      by (simp only: map_scale_distrib_left map_scale_single eq0)
    also have "Poly_Mapping.single h (rat (deg_pm (tp f2)) - rat (deg_pm (lp f2))) + vect f2 =
                Poly_Mapping.single h (rat (poly_deg f2 - deg_pm (lp f2)) -
                rat (poly_deg f2 - deg_pm (tp f2))) + vect f2"
      by (simp add: eq3 eq4)
    also have "\<dots> = of_nat_pm (?f f2 (lp f2)) - of_nat_pm (?f f2 (tp f2))"
      by (simp add: of_nat_pm_plus vect_alt of_nat_pm_single flip: single_diff)
    finally show "of_nat_pm (?f f1 (lp f1)) - of_nat_pm (?f f1 (tp f1)) =
                    m \<cdot> (of_nat_pm (?f f2 (lp f2)) - of_nat_pm (?f f2 (tp f2)))" .
  qed fact+
qed

end (* pm_powerprod *)

subsection \<open>Degree Bounds on the Shifts for Generating a Monomial\<close>

context two_polys
begin

lemma thm_3_2_aux_0:
  assumes "is_binomial f2" and "membership_problem_assms f1 f2 g"
    and "\<And>t. t \<in> keys g \<Longrightarrow> \<not> tp f2 adds t"
  obtains q1 q2 where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)"
    and "keys g \<inter> keys (q2 * f2) = {}" and "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>keys q1. t = v + tp f1"
proof -
  from assms(2) have "g \<in> ideal {f1, f2}" by (rule membership_problem_assmsD)
  then obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" by (rule idealE_2)
  
  have 1: "keys g \<inter> keys (q2 * f2) = {}"
  proof (simp only: disjoint_eq_subset_Compl, rule, rule)
    fix t
    assume "t \<in> keys g" and "t \<in> keys (q2 * f2)"
    from this(2) obtain x y where "x \<in> keys q2" and "y \<in> keys f2" and "t = x + y"
      by (rule in_keys_timesE)
    from assms(1) have "keys f2 = {lp f2, tp f2}" by (rule punit.keys_binomial)
    with \<open>y \<in> keys f2\<close> have "y = lp f2 \<or> y = tp f2" by simp
    thus False
    proof
      assume "y = lp f2"
      from assms(2) \<open>t \<in> keys g\<close> have "\<not> lp f2 adds t" by (rule membership_problem_assms_lp_f2_nadds)
      moreover have "lp f2 adds t" unfolding adds_def \<open>y = lp f2\<close> \<open>t = x + y\<close> by (simp add: add.commute)
      ultimately show False ..
    next
      assume "y = tp f2"
      from \<open>t \<in> keys g\<close> have "\<not> tp f2 adds t" by (rule assms(3))
      moreover have "tp f2 adds t" unfolding adds_def \<open>y = tp f2\<close> \<open>t = x + y\<close> by (simp add: add.commute)
      ultimately show False ..
    qed
  qed
  hence 2: "keys g \<subseteq> keys (q1 * f1)" using keys_add_subset[of "q1 * f1" "q2 * f2"] unfolding g_eq
    by auto
    
  with g_eq show ?thesis using 1
  proof
    fix t
    assume "t \<in> keys g"
    with 2 have "t \<in> keys (q1 * f1)" ..
    then obtain x y where "x \<in> keys q1" and "y \<in> keys f1" and "t = x + y"
      by (rule in_keys_timesE)
    have keys_f1: "keys f1 = {lp f1, tp f1}"
      by (rule punit.keys_binomial, rule membership_problem_assmsD, fact)
    from \<open>y \<in> keys f1\<close> have "y = tp f1" unfolding keys_f1
    proof
      assume "y = lp f1"
      from assms(2) \<open>t \<in> keys g\<close> have "\<not> lp f1 adds t" by (rule membership_problem_assms_lp_f1_nadds)
      moreover have "lp f1 adds t" unfolding adds_def \<open>y = lp f1\<close> \<open>t = x + y\<close> by (simp add: add.commute)
      ultimately show ?thesis ..
    next
      assume "y \<in> {tp f1}"
      thus ?thesis by simp
    qed
    from \<open>x \<in> keys q1\<close> show "\<exists>v\<in>(keys q1). t = v + tp f1" unfolding \<open>t = x + y\<close> \<open>y = tp f1\<close>
      by (rule, simp)
  qed
qed

lemma proper_binomial_cases:
  assumes "is_proper_binomial p" and "s \<in> keys p" and "t \<in> keys p"
  obtains l where "l \<in> {-1, 0, 1}" and "of_nat_pm t = of_nat_pm s + l \<cdot> vect p"
proof -
  from assms(1) have "keys p = {lp p, tp p}" by (rule punit.keys_proper_binomial)
  with assms(2, 3) have "s = lp p \<or> s = tp p" and "t = lp p \<or> t = tp p" by simp_all
  thus ?thesis
  proof (elim disjE)
    assume "s = lp p" and "t = lp p"
    hence "of_nat_pm t = of_nat_pm s + 0 \<cdot> vect p" by simp
    show ?thesis
    proof
      show "0 \<in> {-1, 0, 1::rat}" by simp
    qed fact
  next
    assume "s = lp p" and "t = tp p"
    hence "of_nat_pm t = of_nat_pm s + (- 1) \<cdot> vect p" by (simp add: vect_alt map_scale_uminus_left)
    show ?thesis
    proof
      show "-1 \<in> {-1, 0, 1::rat}" by simp
    qed fact
  next
    assume "s = tp p" and "t = lp p"
    hence "of_nat_pm t = of_nat_pm s + 1 \<cdot> vect p" by (simp add: vect_alt)
    show ?thesis
    proof
      show "1 \<in> {-1, 0, 1::rat}" by simp
    qed fact
  next
    assume "s = tp p" and "t = tp p"
    hence "of_nat_pm t = of_nat_pm s + 0 \<cdot> vect p" by simp
    show ?thesis
    proof
      show "0 \<in> {-1, 0, 1::rat}" by simp
    qed fact
  qed
qed

subsubsection \<open>One Proper Binomial and one Monomial\<close>

context
  fixes g
  assumes f1_pbinomial: "is_proper_binomial f1"
  assumes f2_monomial: "is_monomial f2"
  assumes mpa: "membership_problem_assms f1 f2 g"
begin

lemma thm_3_2_1_aux_1:
  assumes "t \<in> keys g"
  shows "tp f1 adds t"
proof -
  from f1_pbinomial f2_monomial have "is_binomial_set {f1, f2}"
    by (auto simp: is_binomial_set_def dest: proper_binomial_imp_binomial monomial_imp_binomial)
  moreover from mpa have "g \<in> ideal {f1, f2}" and "\<not> punit.is_red {f1, f2} g"
    by (rule membership_problem_assmsD)+
  ultimately obtain f where "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f adds t"
    using assms by (rule rem_3_1_7)
  from \<open>f \<in> {f1, f2}\<close> have "f = f1 \<or> f = f2" by simp
  thus ?thesis
  proof
    assume "f = f1"
    with \<open>tp f adds t\<close> show ?thesis by simp
  next
    from \<open>is_proper_binomial f\<close> have "\<not> is_monomial f" by (rule proper_binomial_no_monomial)
    assume "f = f2"
    with \<open>\<not> is_monomial f\<close> f2_monomial show ?thesis by simp
  qed
qed

lemma thm_3_2_1_aux_1': "tp f1 adds lp g"
proof (rule thm_3_2_1_aux_1)
  from mpa have "is_binomial g" by (rule membership_problem_assmsD)
  hence "g \<noteq> 0" by (rule binomial_not_0)
  thus "lp g \<in> keys g" by (rule punit.lt_in_keys)
qed

lemma thm_3_2_1_aux_2:
  obtains q1 q2 where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)"
    and "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>keys q1. t = v + tp f1"
proof -
  from f2_monomial have "is_binomial f2" by (rule monomial_imp_binomial)
  moreover note mpa
  moreover have "\<not> tp f2 adds t" if "t \<in> keys g" for t
    unfolding punit.lt_eq_tt_monomial[OF f2_monomial, symmetric]
    using mpa that by (rule membership_problem_assms_lp_f2_nadds)
  ultimately obtain q1 q2 where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)"
    and "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>keys q1. t = v + tp f1"
    by (rule thm_3_2_aux_0) blast+
  thus ?thesis ..
qed

lemma thm_3_2_1_aux_3: "is_monomial g"
proof -
  from f2_monomial obtain c2 t2 where "c2 \<noteq> 0" and "lc f2 = c2" and "lp f2 = t2"
    and f2_eq: "f2 = monomial c2 t2" by (rule punit.is_monomial_monomial_ordered)
  from \<open>c2 \<noteq> 0\<close> have keys_f2: "keys f2 = {t2}" unfolding f2_eq by (rule keys_of_monomial)
  from mpa have "is_binomial g" by (rule membership_problem_assmsD)
  hence "is_monomial g \<or> is_proper_binomial g" unfolding is_binomial_alt by simp
  thus ?thesis
  proof
    assume "is_proper_binomial g"
    hence keys_g: "keys g = {lp g, tp g}" by (simp add: proper_binomial_imp_binomial punit.keys_binomial)
    from keys_g have "lp g \<in> keys g" and "tp g \<in> keys g" by simp_all
        
    obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" and keys_g_sub: "keys g \<subseteq> keys (q1 * f1)"
      and rl: "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>(keys q1). t = v + tp f1" by (rule thm_3_2_1_aux_2) blast
      
    have **: "\<And>t. t \<in> keys g \<Longrightarrow> monomial 1 t \<in> ideal {f1, f2}"
    proof -
      fix t
      assume "t \<in> keys g"
      hence "\<exists>v\<in>(keys q1). t = v + tp f1" by (rule rl)
      then obtain v where "v \<in> keys q1" and v: "t = v + tp f1" ..
      have "v + tp f1 \<in> keys (q1 * f1)" unfolding v[symmetric] by (rule, fact \<open>t \<in> keys g\<close>, fact keys_g_sub)
      from \<open>is_proper_binomial f1\<close> \<open>v \<in> keys q1\<close> this obtain q1'
        where keys_q1'f1: "keys (q1' * f1) = {lp q1' + lp f1, v + tp f1}" and "lp q1' + lp f1 \<in> keys (q1 * f1)"
        by (rule binomial_mult_shape_tp)
      have "lp q1' + lp f1 \<in> keys (q2 * f2)"
      proof (rule ccontr)
        assume "lp q1' + lp f1 \<notin> keys (q2 * f2)"
        with \<open>lp q1' + lp f1 \<in> keys (q1 * f1)\<close> have "lp q1' + lp f1 \<in> keys g" unfolding g_eq
          by (rule in_keys_plusI1)
        with mpa have "\<not> lp f1 adds lp q1' + lp f1" by (rule membership_problem_assms_lp_f1_nadds)
        thus False by simp
      qed
      then obtain x y where "x \<in> keys q2" and "y \<in> keys f2" and "lp q1' + lp f1 = x + y"
        by (rule in_keys_timesE)
      from \<open>y \<in> keys f2\<close> have "y = t2" unfolding keys_f2 by simp
      let ?q2 = "monomial (-(lookup (q1' * f1) (lp q1' + lp f1)) / c2) x"
      from \<open>c2 \<noteq> 0\<close> have "?q2 * f2 = monomial (- (lookup (q1' * f1) (lp q1' + lp f1))) (lp q1' + lp f1)" (is "_ = ?p")
        by (simp add: times_monomial_left \<open>lp q1' + lp f1 = x + y\<close> \<open>y = t2\<close> f2_eq punit.monom_mult_monomial)
      have keys_p: "keys ?p = {lp q1' + lp f1}" by (rule keys_of_monomial, simp add: keys_q1'f1)
      have "keys (q1' * f1 + ?q2 * f2) = {t}" unfolding \<open>?q2 * f2 = ?p\<close> v
      proof
        from keys_add_subset[of "q1' * f1" ?p] have "keys (q1' * f1 + ?p) \<subseteq> {lp q1' + lp f1, v + tp f1}"
          unfolding keys_q1'f1 keys_p by simp
        moreover have "lp q1' + lp f1 \<notin> keys (q1' * f1 + ?p)" by (simp add: lookup_add lookup_single)
        ultimately show "keys (q1' * f1 + ?p) \<subseteq> {v + tp f1}" by auto
      next
        have "v + tp f1 \<in> keys (q1' * f1 + ?p)"
        proof (rule in_keys_plusI1, simp add: keys_q1'f1, simp add: keys_p, rule, rule)
          assume "v + tp f1 = lp q1' + lp f1"
          hence "lp q1' + lp f1 \<in> keys g" using \<open>t \<in> keys g\<close> unfolding v by simp
          from membership_problem_assms_lp_f1_nadds[OF mpa this] show False by simp
        qed
        thus "{v + tp f1} \<subseteq> keys (q1' * f1 + ?p)" by simp
      qed
      with _ show "monomial 1 t \<in> ideal {f1, f2}"
      proof (rule punit.monomial_1_in_pmdlI[simplified])
        show "q1' * f1 + ?q2 * f2 \<in> ideal {f1, f2}" by (rule idealI_2)
      qed
    qed
      
    from mpa \<open>is_proper_binomial g\<close> have "\<not> monomial 1 ` (keys g) \<subseteq> ideal {f1, f2}"
      by (rule membership_problem_assmsD)
    moreover from **[OF \<open>lp g \<in> keys g\<close>] **[OF \<open>tp g \<in> keys g\<close>]
      have "monomial 1 ` (keys g) \<subseteq> ideal {f1, f2}" unfolding keys_g by simp
    ultimately show ?thesis ..
  qed
qed
  
lemma thm_3_2_1_aux_4:
  obtains k u where "k \<noteq> 0" and "lp f1 adds u" and "lp f2 adds u" and "associated f1 u (lp g) k"
proof -
  obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" and g_keys_sub: "keys g \<subseteq> keys (q1 * f1)"
    and rl: "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>(keys q1). t = v + tp f1" by (rule thm_3_2_1_aux_2) blast
  have "g \<noteq> 0" by (rule binomial_not_0, rule membership_problem_assmsD, fact)
  hence "lp g \<in> keys g" by (rule punit.lt_in_keys)
  hence "\<exists>v\<in>(keys q1). lp g = v + tp f1" by (rule rl)
  then obtain v where "v \<in> keys q1" and v: "lp g = v + tp f1" ..
  from \<open>lp g \<in> keys g\<close> g_keys_sub have "v + tp f1 \<in> keys (q1 * f1)" unfolding v ..
  
  (* Note: the "q" in MWW's thesis is the sub-polynomial of "q1'" that lacks all power-products that are
    strictly greater than the minimal "t \<in> keys q1'" such that "t * lp f1" is divisible by "lp f2". *)
  
  from \<open>is_proper_binomial f1\<close> \<open>v \<in> keys q1\<close> this obtain q1' where "q1' \<noteq> 0" and "q1' \<sqsubseteq> q1"
    and tp_q1': "tp q1' = v" and assoc: "associated_poly f1 q1'"
    and **: "lp q1' + lp f1 \<in> keys (q1 * f1)" by (rule binomial_mult_shape_tp')
  
  define u where "u = lp q1'"
  
  have "u + lp f1 \<in> keys (q2 * f2)"
  proof (rule ccontr)
    assume "u + lp f1 \<notin> keys (q2 * f2)"
    with ** have "u + lp f1 \<in> keys g" unfolding g_eq u_def by (rule in_keys_plusI1)
    with mpa have "\<not> lp f1 adds u + lp f1" by (rule membership_problem_assms_lp_f1_nadds)
    thus False by simp
  qed
  then obtain w w' where "w' \<in> keys f2" and w0: "u + lp f1 = w + w'" by (rule in_keys_timesE)
  from \<open>is_monomial f2\<close> have "keys f2 = {lp f2}" by (rule punit.keys_monomial)
  with \<open>w' \<in> keys f2\<close> have w': "w' = lp f2" by simp
  with w0 have w: "u + lp f1 = w + lp f2" by simp
  
  show ?thesis
  proof
    from \<open>q1' \<noteq> 0\<close> have "keys q1' \<noteq> {}" by simp
    with finite_keys[of q1'] show "card (keys q1') \<noteq> 0" by auto
  next
    from \<open>q1' \<noteq> 0\<close> assoc show "associated f1 (w + lp f2) (lp g) (card (keys q1'))"
      unfolding v tp_q1'[symmetric] w[symmetric] u_def by (rule associated_poly_times_binomial_associated)
  next
    show "lp f1 adds w + lp f2" by (simp add: w[symmetric])
  qed simp
qed

lemma thm_3_2_1_aux_5:
  assumes "k \<noteq> 0" and "lp f1 adds u" and "lp f2 adds u" and "associated f1 u (lp g) k"
  shows "membership_problem_concl f1 f2 g (max (deg_pm (lp g)) (deg_pm u))"
proof -
  have "is_monomial g" and "tp f1 adds lp g" by (rule thm_3_2_1_aux_3, rule thm_3_2_1_aux_1')
  from f2_monomial have "f2 \<noteq> 0" by (rule monomial_not_0)
  hence "lc f2 \<noteq> 0" by (rule punit.lc_not_0)
  from \<open>is_monomial g\<close> have "g \<noteq> 0" by (rule monomial_not_0)
  hence "lc g \<noteq> 0" by (rule punit.lc_not_0)
  with f1_pbinomial assms(4) \<open>k \<noteq> 0\<close> assms(2) \<open>tp f1 adds lp g\<close> obtain q1 c
    where eq1: "q1 * f1 = binomial c u (lc g) (lp g)" and obd: "punit.is_obd c u (lc g) (lp g)"
    by (rule associated_adds_obtains_cofactor_binomial_tc)
  from obd have pbd: "is_pbd c u (lc g) (lp g)" by (rule punit.obd_imp_pbd)
  from assms(3) obtain v where u_eq: "u = v + lp f2" by (metis addsE add.commute)
  define lc2 where "lc2 = lc f2"
  let ?q2 = "monomial (- c / lc2) v"
  from obd have "-c \<noteq> 0" by (simp add: punit.is_obd_def)
  with \<open>lc f2 \<noteq> 0\<close> have "(-c) / lc f2 \<noteq> 0" by simp
  have eq2: "?q2 * f2 = monomial (-c) u"
    by (subst punit.monomial_eq_itself[OF \<open>is_monomial f2\<close>, symmetric],
        simp add: times_monomial_left \<open>lc f2 \<noteq> 0\<close> punit.monom_mult_monomial u_eq lc2_def)
  show ?thesis
  proof (simp only: membership_problem_concl_def, intro exI conjI impI)
    show "g = q1 * f1 + ?q2 * f2"
      by (simp only: eq1 eq2 binomial_def monomial_uminus[symmetric],
          simp add: punit.monomial_eq_itself[OF \<open>is_monomial g\<close>])
  next
    show "poly_deg (q1 * f1) \<le> max (deg_pm (lp g)) (deg_pm u)"
      by (simp add: eq1 poly_deg_def keys_binomial_pbd[OF pbd])
  next
    from \<open>-c \<noteq> 0\<close> have "keys (?q2 * f2) = {u}" unfolding eq2 by (rule keys_of_monomial)
    thus "poly_deg (?q2 * f2) \<le> max (deg_pm (lp g)) (deg_pm u)" by (simp add: poly_deg_def)
  qed
qed

lemma thm_3_2_1_aux_6: "lp f2 adds overlapshift (lp g)"
proof -
  from f2_monomial have "tp f2 = lp f2" by (simp only: punit.lt_eq_tt_monomial)
  obtain k u where "k \<noteq> 0" and d1: "lp f1 adds u" and d2: "lp f2 adds u"
    and *: "associated f1 u (lp g) k" by (rule thm_3_2_1_aux_4)
  from gcs_adds[of "lp f1" "tp f1"] d1 have "gcs (lp f1) (tp f1) adds u" by (rule adds_trans)
  moreover from gcs_adds[of "lp f2" "tp f2"] d2 have "gcs (lp f2) (tp f2) adds u" by (rule adds_trans)
  ultimately have "overlap \<unlhd> of_nat_pm u" by (rule overlap_leI)
  with _ f1_pbinomial thm_3_2_1_aux_1' * have "overlap \<unlhd> of_nat_pm (overlapshift (lp g))"
    by (rule overlapshift_is_above_overlap) simp
  hence "gcs (lp f2) (tp f2) adds overlapshift (lp g)" by (rule overlap_leD)
  thus ?thesis by (simp only: gcs_same \<open>tp f2 = lp f2\<close>)
qed

lemma thm_3_2_1_aux_7: "step (lp g) \<noteq> 0"
proof
  assume eq: "step (lp g) = 0"
  hence "overlapshift (lp g) = lp g" by (rule overlapshift_step_idI)
  moreover have "lp f2 adds overlapshift (lp g)" by (rule thm_3_2_1_aux_6)
  ultimately have "lp f2 adds lp g" by simp
  have "punit.is_red {f1, f2} g"
  proof (rule punit.is_red_addsI[simplified])
    from mpa have "is_binomial f2" by (rule membership_problem_assmsD)
    thus "f2 \<noteq> 0" by (rule binomial_not_0)
  next
    from mpa have "is_binomial g" by (rule membership_problem_assmsD)
    hence "g \<noteq> 0" by (rule binomial_not_0)
    thus "lp g \<in> keys g" by (rule punit.lt_in_keys)
  qed (simp, fact)
  moreover from mpa have "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
  ultimately show False by simp
qed

theorem thm_3_2_1:
  "membership_problem_concl f1 f2 g (max (deg_pm (lp g)) (deg_pm (overlapshift (lp g))))"
proof -
  obtain k u where "k \<noteq> 0" and "lp f1 adds u" and "lp f2 adds u" and *: "associated f1 u (lp g) k"
    by (rule thm_3_2_1_aux_4)
  have "f1 \<in> {f1, f2}" by simp
  moreover note f1_pbinomial
  moreover have "tp f1 adds lp g" by (rule thm_3_2_1_aux_1')
  moreover note \<open>associated f1 u (lp g) k\<close>
  moreover have "overlap \<unlhd> of_nat_pm u"
  proof (rule overlap_leI)
    from gcs_adds \<open>lp f1 adds u\<close> show "gcs (lp f1) (tp f1) adds u" by (rule adds_trans)
  next
    from gcs_adds \<open>lp f2 adds u\<close> show "gcs (lp f2) (tp f2) adds u" by (rule adds_trans)
  qed
  ultimately have "step (lp g) \<le> k" and **: "associated f1 (overlapshift (lp g)) (lp g) (step (lp g))"
    by (rule step_min, rule associated_overlapshift)
  have "step (lp g) \<noteq> 0" by (rule thm_3_2_1_aux_7)
  from this _ _ ** show ?thesis
  proof (rule thm_3_2_1_aux_5)
    from * ** \<open>lp f1 adds u\<close> \<open>tp f1 adds lp g\<close> \<open>step (lp g) \<le> k\<close> \<open>step (lp g) \<noteq> 0\<close>
    show "lp f1 adds overlapshift (lp g)" by (rule associated_lp_adds_between'')
  next
    show "lp f2 adds overlapshift (lp g)" by (rule thm_3_2_1_aux_6)
  qed
qed

end

subsubsection \<open>Two Parallel Proper Binomials\<close>

context
  fixes g
  assumes parallel: "parallel_binomials f1 f2"
  assumes g_monomial: "is_monomial g"
  assumes tp_adds_lp: "tp f1 adds lp g"
  assumes mpa: "membership_problem_assms f1 f2 g"
begin

lemma thm_3_2_2_aux_1:
  assumes "\<not> tp f2 adds lp g"
  obtains q1 q2 v where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)" and "v \<in> keys q1"
    and "lp g = v + tp f1"
proof -
  from parallel have "is_proper_binomial f2" by (rule parallel_binomialsD)
  hence "is_binomial f2" by (rule proper_binomial_imp_binomial)
  moreover note mpa
  moreover have "\<not> tp f2 adds t" if "t \<in> keys g" for t
  proof -
    from g_monomial have "keys g = {lp g}" by (rule punit.keys_monomial)
    with that assms show ?thesis by simp
  qed
  ultimately obtain q1 q2 where 1: "g = q1 * f1 + q2 * f2" and 2: "keys g \<subseteq> keys (q1 * f1)"
    and rl: "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>keys q1. t = v + tp f1"
    by (rule thm_3_2_aux_0) blast+
  from g_monomial have "g \<noteq> 0" by (rule monomial_not_0)
  hence "lp g \<in> keys g" by (rule punit.lt_in_keys)
  hence "\<exists>v\<in>keys q1. lp g = v + tp f1" by (rule rl)
  then obtain v where "v \<in> keys q1" and "lp g = v + tp f1" ..
  with 1 2 show ?thesis ..
qed

lemma thm_3_2_2_aux_2:
  obtains k u where "associated f1 u (lp g) k" and "overlap \<unlhd> of_nat_pm u"
proof (cases "tp f2 adds lp g")
  case True
  show ?thesis
  proof
    show "associated f1 (lp g) (lp g) 0" by (simp only: associated_0)
  next
    from gcs_adds_2 tp_adds_lp have "gcs (lp f1) (tp f1) adds lp g" by (rule adds_trans)
    moreover from gcs_adds_2 True have "gcs (lp f2) (tp f2) adds lp g" by (rule adds_trans)
    ultimately have "lcs (gcs (lp f1) (tp f1)) (gcs (lp f2) (tp f2)) adds lp g" by (rule lcs_adds)
    thus "overlap \<unlhd> of_nat_pm (lp g)" by (simp add: overlap_alt' adds_pm le_of_nat_pm)
  qed
next
  case False
  then obtain q1 q2 v where g_eq: "g = q1 * f1 + q2 * f2" and g_keys_sub: "keys g \<subseteq> keys (q1 * f1)"
    and "v \<in> keys q1" and v: "lp g = v + tp f1" by (rule thm_3_2_2_aux_1) blast
  from parallel have "is_proper_binomial f1" by (rule parallel_binomialsD)
  from g_monomial have "g \<noteq> 0" by (rule monomial_not_0)
  hence "lp g \<in> keys g" by (rule punit.lt_in_keys)
  hence "v + tp f1 \<in> keys (q1 * f1)" using g_keys_sub unfolding v ..
  with \<open>is_proper_binomial f1\<close> \<open>v \<in> keys q1\<close> obtain q1' where "q1' \<noteq> 0" and "q1' \<sqsubseteq> q1"
    and tp_q1': "tp q1' = v" and assoc: "associated_poly f1 q1'"
    and **: "lp q1' + lp f1 \<in> keys (q1 * f1)" by (rule binomial_mult_shape_tp')
  
  define u where "u = lp q1'"
  
  have "u + lp f1 \<in> keys (q2 * f2)"
  proof (rule ccontr)
    assume "u + lp f1 \<notin> keys (q2 * f2)"
    with ** have "u + lp f1 \<in> keys g" unfolding g_eq u_def by (rule in_keys_plusI1)
    with mpa have "\<not> lp f1 adds u + lp f1" by (rule membership_problem_assms_lp_f1_nadds)
    thus False by simp
  qed
  then obtain w w' where "w' \<in> keys f2" and w0: "u + lp f1 = w + w'" by (rule in_keys_timesE)
  
  show ?thesis
  proof
    from \<open>q1' \<noteq> 0\<close> assoc show "associated f1 (u + lp f1) (lp g) (card (keys q1'))"
      unfolding v tp_q1'[symmetric] u_def by (rule associated_poly_times_binomial_associated)
  next
    have "gcs (lp f1) (tp f1) adds u + lp f1" by (simp add: gcs_adds)
    from parallel have "is_proper_binomial f2" by (rule parallel_binomialsD)
    hence "keys f2 = {lp f2, tp f2}" by (rule punit.keys_proper_binomial)
    with \<open>w' \<in> keys f2\<close> have "w' = lp f2 \<or> w' = tp f2" by simp
    hence "lp f2 adds u + lp f1 \<or> tp f2 adds u + lp f1" by (auto simp: w0)
    hence "gcs (lp f2) (tp f2) adds u + lp f1" by (auto intro: gcs_adds gcs_adds_2 adds_trans)
    with \<open>gcs (lp f1) (tp f1) adds u + lp f1\<close> have "lcs (gcs (lp f1) (tp f1)) (gcs (lp f2) (tp f2)) adds u + lp f1"
      by (rule lcs_adds)
    thus "overlap \<unlhd> of_nat_pm (u + lp f1)" by (simp add: overlap_alt' adds_pm le_of_nat_pm)
  qed
qed

lemma thm_3_2_2_aux_3':
  obtains q1 q2 where "g = q1 * f1 + q2 * f2"
    and "\<And>s t. (s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2) \<Longrightarrow>
            \<exists>l. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
proof -
  from mpa have "g \<in> ideal {f1, f2}" by (rule membership_problem_assmsD)
  then obtain q1' q2' where g: "g = q1' * f1 + q2' * f2" by (rule idealE_2)
  define S1 where "S1 = {t. \<forall>s\<in>keys f1. \<forall>l. of_nat_pm (t + s) \<noteq> of_nat_pm (lp g) + l \<cdot> vect f1}"
  define S2 where "S2 = {t. \<forall>s\<in>keys f2. \<forall>l. of_nat_pm (t + s) \<noteq> of_nat_pm (lp g) + l \<cdot> vect f1}"
  define q1 where "q1 = except q1' S1"
  define q2 where "q2 = except q2' S2"
  from parallel have "parallel_binomials f2 f1" by (rule parallel_binomials_sym)
  then obtain m where "0 < m" and m: "vect f2 = m \<cdot> vect f1" by (rule parallel_binomialsE_vect)
  have 1: "P" if "s \<in> keys q1" and "t \<in> keys f1"
    and "\<And>l. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1 \<Longrightarrow> P" for s t P
  proof -
    from that(1) have "s \<in> keys q1'" and "s \<notin> S1" by (simp_all add: q1_def keys_except)
    from this(2) obtain t0 l where "t0 \<in> keys f1"
      and eq1: "of_nat_pm (s + t0) = of_nat_pm (lp g) + l \<cdot> vect f1" by (auto simp: S1_def)
    from parallel have "is_proper_binomial f1" by (rule parallel_binomialsD)
    moreover note \<open>t0 \<in> keys f1\<close> that(2)
    ultimately obtain l' where eq2: "of_nat_pm t = of_nat_pm t0 + l' \<cdot> vect f1"
      by (rule proper_binomial_cases)
    show ?thesis
    proof (rule that(3))
      have "of_nat_pm (s + t) = of_nat_pm (s + t0) + l' \<cdot> vect f1" by (simp add: of_nat_pm_plus eq2)
      also have "\<dots> = of_nat_pm (lp g) + (l + l') \<cdot> vect f1" by (simp add: eq1 map_scale_distrib_right)
      finally show "of_nat_pm (s + t) = of_nat_pm (lp g) + (l + l') \<cdot> vect f1" .
    qed
  qed
  have 2: "P" if "s \<in> keys q2" and "t \<in> keys f2"
    and "\<And>l. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1 \<Longrightarrow> P" for s t P
  proof -
    from that(1) have "s \<in> keys q2'" and "s \<notin> S2" by (simp_all add: q2_def keys_except)
    from this(2) obtain t0 l where "t0 \<in> keys f2"
      and eq1: "of_nat_pm (s + t0) = of_nat_pm (lp g) + l \<cdot> vect f1" by (auto simp: S2_def)
    from parallel have "is_proper_binomial f2" by (rule parallel_binomialsD)
    moreover note \<open>t0 \<in> keys f2\<close> that(2)
    ultimately obtain l' where eq2: "of_nat_pm t = of_nat_pm t0 + l' \<cdot> vect f2"
      by (rule proper_binomial_cases)
    show ?thesis
    proof (rule that(3))
      have "of_nat_pm (s + t) = of_nat_pm (s + t0) + l' \<cdot> vect f2" by (simp add: of_nat_pm_plus eq2)
      also have "\<dots> = of_nat_pm (lp g) + (l + l' * m) \<cdot> vect f1"
        by (simp add: m eq1 map_scale_distrib_right map_scale_assoc)
      finally show "of_nat_pm (s + t) = of_nat_pm (lp g) + (l + l' * m) \<cdot> vect f1" .
    qed
  qed
  show ?thesis
  proof
    show "g = q1 * f1 + q2 * f2"
    proof (rule poly_mapping_eqI)
      fix t
      show "lookup g t = lookup (q1 * f1 + q2 * f2) t"
      proof (cases "\<exists>l. of_nat_pm t = of_nat_pm (lp g) + l \<cdot> vect f1")
        case True
        then obtain l where l: "of_nat_pm t = of_nat_pm (lp g) + l \<cdot> vect f1" ..
        from finite_keys have "lookup (q1 * f1) t = lookup (q1' * f1) t" unfolding lookup_times
        proof (intro sum.mono_neutral_cong_left ballI)
          fix s
          assume "s \<in> keys q1' - keys q1"
          hence "s \<in> S1" by (auto simp: q1_def keys_except)
          hence "\<And>s0. s0 \<in> keys f1 \<Longrightarrow> of_nat_pm (s + s0) \<noteq> (of_nat_pm t :: _ \<Rightarrow>\<^sub>0 rat)"
            by (simp add: S1_def l)
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
          hence "\<And>s0. s0 \<in> keys f2 \<Longrightarrow> of_nat_pm (s + s0) \<noteq> (of_nat_pm t :: _ \<Rightarrow>\<^sub>0 rat)"
            by (simp add: S2_def l)
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
      next
        case False
        hence "t \<noteq> lp g" by (metis add.right_neutral map_scale_zero_left)
        with g_monomial have "t \<notin> keys g" by (auto dest: punit.keys_monomial simp only:)
        moreover have "t \<notin> keys (q1 * f1)"
        proof
          assume "t \<in> keys (q1 * f1)"
          then obtain t1 t2 where "t1 \<in> keys q1" and "t2 \<in> keys f1" and t: "t = t1 + t2"
            by (rule in_keys_timesE)
          from this(1, 2) obtain l where "of_nat_pm t = of_nat_pm (lp g) + l \<cdot> vect f1"
            unfolding t by (rule 1)
          with False show False by blast
        qed
        moreover have "t \<notin> keys (q2 * f2)"
        proof
          assume "t \<in> keys (q2 * f2)"
          then obtain t1 t2 where "t1 \<in> keys q2" and "t2 \<in> keys f2" and t: "t = t1 + t2"
            by (rule in_keys_timesE)
          from this(1, 2) obtain l where "of_nat_pm t = of_nat_pm (lp g) + l \<cdot> vect f1"
            unfolding t by (rule 2)
          with False show False by blast
        qed
        ultimately show ?thesis by (simp add: lookup_add)
      qed
    qed
  next
    fix s t
    assume "s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2"
    thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
    proof
      assume "s \<in> keys q1 \<and> t \<in> keys f1"
      hence "s \<in> keys q1" and "t \<in> keys f1" by simp_all
      then obtain l where "of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1" by (rule 1)
      thus ?thesis ..
    next
      assume "s \<in> keys q2 \<and> t \<in> keys f2"
      hence "s \<in> keys q2" and "t \<in> keys f2" by simp_all
      then obtain l where "of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1" by (rule 2)
      thus ?thesis ..
    qed
  qed
qed

lemma thm_3_2_2_aux_3:
  obtains q1 q2 where "g = q1 * f1 + q2 * f2"
    and "\<And>s t. (s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2) \<Longrightarrow>
            \<exists>l\<ge>0. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
proof -
  (* Note: We only need "0 \<le> l" for those "s + t" that are contained in "keys (q1 * f1) \<union> keys (q2 * f2)".
      For the other power-products the sign of "l" is irrelevant. *)
  (* Note: No "s + t" appearing 'below' "lp g" (i.e. with negative "l") can be divisible by "lp f1"
      or "lp f2", because then "lp g" would be divisible by that leading power-product, too.
      This follows from the fact that multiples of both "lp f1" and "lp f2" must appear 'above'
      "lp g" (i.e. with non-negative "l"), and if "lp f1" divides a power-product below and above
      "lp g", it also divides "lp g". *)
  obtain q1' q2' where "g = q1' * f1 + q2' * f2"
    and "\<And>s t. (s \<in> keys q1' \<and> t \<in> keys f1) \<or> (s \<in> keys q2' \<and> t \<in> keys f2) \<Longrightarrow>
            \<exists>l. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
    by (rule thm_3_2_2_aux_3') blast
  (* Proof strategy?
      - First prove that q1' and q2' exist such that all pps lie on the main diagonal (see above).
      - Among all such q1', q2', pick some q1, q2 where the number of pps below "lp g" is minimal.
      - If there are no pps below "lp g", we are done; otherwise, let t be the pp with smallest l.
      - Because of the observation above, there exist "s1 \<in> keys q1" and "s2 \<in> keys q2" with
        "t = s1 + tp f1 = s2 + tp f2" and "lookup q1 s1 * tc f1 = - lookup q2 s2 * tc f2";
        actually, "s1 = tp q1" and "s2 = tp q2".
      ? Show that "except q1 {s1} + ..." and "except q2 {s2} + ..." generate g but have one
        pp less below "lp g", contradicting the minimality of q1 and q2. *)
  show ?thesis sorry
qed

text \<open>I do not know whether the above lemma really holds. Intuitively, it seems reasonable, but I have
  no idea how to prove it rigorously, and MWW's thesis does not say anything about it either (it
  even wrongly claims that such non-negative \<open>l\<close> exist for \<^emph>\<open>all\<close> cofactors \<open>q1\<close> and \<open>q2\<close>, although
  one can easily construct counterexamples using syzygies).

  In any case, an alternative overall strategy would be to homogenize the input, and then infer
  cofactor bounds for the elements in the homogeneous Gr\"obner basis \<open>G\<^sup>*\<close> by virtue of MWW's thesis.
  Homogenizing parallel binomials yields again parallel binomials, see lemma
  "parallel_binomials_homogenizeI". Only be aware that
  \<^item> \<open>(G\<^sup>*)\<^sub>*\<close> is not necessarily a \<^emph>\<open>reduced\<close> Gr\"obner basis, and
  \<^item> \<open>(G\<^sup>*)\<^sub>*\<close> might contain monomials that stem from proper binomials in \<open>G\<^sup>*\<close>.
  So, this proposal must be understood as an overall strategy for obtaining \<^emph>\<open>cofactor\<close> bounds for
  \<^emph>\<open>some\<close> Gr\"obner basis of \<open>f1\<close> and \<open>f2\<close> (if \<open>f1\<close> and \<open>f2\<close> are parallel binomials, but also in
  general); it cannot be used, however, to only circumvent the single theorem below.\<close>

text \<open>It seems that the degree bounds obtained for a proper binomial in the Groebner basis can,
  in some sense, also be applied to a monomial: Assume \<open>g\<close> is a monomial. If it is possible to prove
  that there is a VPC from \<open>g\<close> to \<open>g\<close> (which intuitively seems possible), then there is also a VPC
  from \<open>g + vect f\<close> to \<open>g\<close> for some @{prop "f \<in> {f1, f2}"}, and these two points are distinct. Hence,
  the results from theory @{theory Draft.VPC} can be applied to obtain similar (though slightly weaker)
  bounds as the ones MWW derived directly.\<close>

theorem thm_3_2_2:
  "membership_problem_concl f1 f2 g
          (to_nat (max (rat (deg_pm (lp g))) (deg_pm (of_nat_pm (lp g) + (rat (step (lp g)) + 1) \<cdot> vect f1 + vect f2) - 1)))"
proof -
  define k where "k = step (lp g)"
  from parallel have "is_proper_binomial f2" by (rule parallel_binomialsD)
  have "f1 \<in> {f1, f2}" by simp
  moreover from parallel have "is_proper_binomial f1" by (rule parallel_binomialsD)
  moreover note tp_adds_lp
  moreover obtain k' u where "associated f1 u (lp g) k'" and "overlap \<unlhd> of_nat_pm u" by (rule thm_3_2_2_aux_2)
  ultimately have "overlap \<unlhd> of_nat_pm (overlapshift (lp g))"
    and "of_nat_pm (overlapshift (lp g)) = of_nat_pm (lp g) + rat (step (lp g)) \<cdot> vect f1"
    and "step (lp g) \<le> k'"
    by (rule overlapshift_is_above_overlap, rule of_nat_pm_overlapshift', rule step_min)
  hence overlap_le: "overlap \<unlhd> of_nat_pm (lp g) + rat k \<cdot> vect f1" by (simp only: k_def)

  let ?a = "rat (deg_pm (lp g))"
  let ?b = "deg_pm (of_nat_pm (lp g) + (rat (step (lp g)) + 1) \<cdot> vect f1 + vect f2) - 1"

  show ?thesis
  proof (cases "deg_pm (lp f1) \<le> deg_pm (tp f1)")
    case True
    obtain q1 q2 where "g = q1 * f1 + q2 * f2"
      and 1: "\<And>s t. s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2 \<Longrightarrow>
              \<exists>l\<ge>0. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
      by (rule thm_3_2_2_aux_3) blast
    have 2: "deg_pm t \<le> deg_pm (lp g)" if "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)" for t
    proof -
      from that obtain t1 t2 where "(t1 \<in> keys q1 \<and> t2 \<in> keys f1) \<or> (t1 \<in> keys q2 \<and> t2 \<in> keys f2)"
        and t: "t = t1 + t2" by (auto elim!: in_keys_timesE)
      from this(1) have "\<exists>l\<ge>0. of_nat_pm t = of_nat_pm (lp g) + l \<cdot> vect f1"
        unfolding t by (rule 1)
      then obtain l::rat where "0 \<le> l" and eq: "of_nat_pm t = of_nat_pm (lp g) + l \<cdot> vect f1" by blast
      have "rat (deg_pm t) = deg_pm (of_nat_pm t)" by (simp only: deg_of_nat_pm)
      also have "\<dots> = deg_pm (of_nat_pm (lp g)) + l * deg_pm (vect f1)"
        by (simp add: eq deg_pm_plus deg_pm_map_scale)
      also from \<open>0 \<le> l\<close> have "\<dots> \<le> deg_pm (of_nat_pm (lp g))" unfolding add_le_same_cancel1
      proof (rule mult_nonneg_nonpos)
        from True show "deg_pm (vect f1) \<le> 0" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)
      qed
      also have "\<dots> = rat (deg_pm (lp g))" by (simp only: deg_of_nat_pm)
      finally show ?thesis by simp
    qed
    show ?thesis unfolding membership_problem_concl_def
    proof (intro exI conjI impI)
      have "poly_deg (q1 * f1) \<le> deg_pm (lp g)"
      proof (rule poly_deg_leI)
        fix t
        assume "t \<in> keys (q1 * f1)"
        hence "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)" by simp
        thus "deg_pm t \<le> deg_pm (lp g)" by (rule 2)
      qed
      hence "rat (poly_deg (q1 * f1)) \<le> ?a" by simp
      also have "\<dots> \<le> max ?a ?b" by (rule max.cobounded1)
      finally have "to_nat (rat (poly_deg (q1 * f1))) \<le> to_nat (max ?a ?b)" by (rule to_nat_mono)
      thus "poly_deg (q1 * f1) \<le> to_nat (max ?a ?b)" by (simp only: to_nat_of_nat)
    next
      have "poly_deg (q2 * f2) \<le> deg_pm (lp g)"
      proof (rule poly_deg_leI)
        fix t
        assume "t \<in> keys (q2 * f2)"
        hence "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)" by simp
        thus "deg_pm t \<le> deg_pm (lp g)" by (rule 2)
      qed
      hence "rat (poly_deg (q2 * f2)) \<le> ?a" by simp
      also have "\<dots> \<le> max ?a ?b" by (rule max.cobounded1)
      finally have "to_nat (rat (poly_deg (q2 * f2))) \<le> to_nat (max ?a ?b)" by (rule to_nat_mono)
      thus "poly_deg (q2 * f2) \<le> to_nat (max ?a ?b)" by (simp only: to_nat_of_nat)
    qed fact
  next
    case False
    hence "deg_pm (tp f1) < deg_pm (lp f1)" by simp
    hence "0 < deg_pm (vect f1)" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)
    moreover obtain m::rat where "0 < m" and "vect f2 = m \<cdot> vect f1"
      using parallel_binomials_sym[OF parallel] by (rule parallel_binomialsE_vect)
    ultimately have "0 < deg_pm (vect f2)" by (simp add: deg_pm_map_scale)
    hence 0: "deg_pm (tp f2) < deg_pm (lp f2)" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)

    define A where "A = {Q. g = fst Q * f1 + snd Q * f2 \<and>
                          (\<forall>s t. ((s \<in> keys (fst Q) \<and> t \<in> keys f1) \<or> (s \<in> keys (snd Q) \<and> t \<in> keys f2)) \<longrightarrow>
                            (\<exists>l::rat. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1))}"
    have "A \<noteq> {}"
    proof -
      obtain q1 q2 where "g = q1 * f1 + q2 * f2"
        and "\<And>s t. (s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2) \<Longrightarrow>
                  \<exists>l::rat. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
        by (rule thm_3_2_2_aux_3) blast
      hence "(q1, q2) \<in> A" by (simp add: A_def)
      thus ?thesis by blast
    qed
    obtain q1 q2 where "(q1, q2) \<in> A" and Q_min: "\<And>q1' q2'. (q1', q2') \<in> A \<Longrightarrow> poly_deg q1 \<le> poly_deg q1'"
    proof -
      define l where "l = (LEAST x. x \<in> poly_deg ` fst ` A)"
      from \<open>A \<noteq> {}\<close> have "\<exists>x. x \<in> poly_deg ` fst ` A" by blast
      hence "l \<in> poly_deg ` fst ` A" unfolding l_def by (rule LeastI_ex)
      then obtain Q where "Q \<in> A" and l: "l = poly_deg (fst Q)" by blast
      obtain q1 q2 where Q: "Q = (q1, q2)" using prod.exhaust by blast
      show ?thesis
      proof
        from \<open>Q \<in> A\<close> show "(q1, q2) \<in> A" by (simp only: Q)
      next
        fix q1' q2'
        assume "(q1', q2') \<in> A"
        hence "poly_deg (fst (q1', q2')) \<in> poly_deg ` fst ` A" by (intro imageI)
        hence "poly_deg (fst Q) \<le> poly_deg (fst (q1', q2'))"
          unfolding l[symmetric] l_def by (rule Least_le)
        thus "poly_deg q1 \<le> poly_deg q1'" by (simp only: Q fst_conv)
      qed
    qed
    from this(1) have g: "g = q1 * f1 + q2 * f2"
      and 1: "\<And>s t thesis. (s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2) \<Longrightarrow>
                (\<And>l::rat. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1 \<Longrightarrow> thesis) \<Longrightarrow> thesis"
      by (auto simp: A_def)

    from mpa g have "q1 * f1 \<noteq> 0" and "q2 * f2 \<noteq> 0" and lp_eq: "lp (q1 * f1) = lp (q2 * f2)"
      and lc_eq: "lc (q1 * f1) = - lc (q2 * f2)"
      by (rule membership_problem_assms_rep)+
    from this(1, 2) have "q1 \<noteq> 0" and "f1 \<noteq> 0" and "q2 \<noteq> 0" and "f2 \<noteq> 0" by auto
    from this(1, 2) have lp_q1_f1: "lp (q1 * f1) = lp q1 + lp f1" by (rule lp_times)
    from \<open>q2 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have lp_q2_f2: "lp (q2 * f2) = lp q2 + lp f2" by (rule lp_times)
    have lp_eq2: "lp q1 + lp f1 = lp q2 + lp f2" by (simp only: lp_eq lp_q2_f2 flip: lp_q1_f1)
    from \<open>q1 \<noteq> 0\<close> have "lp q1 \<in> keys q1" by (rule punit.lt_in_keys)
    moreover from \<open>f1 \<noteq> 0\<close> have "lp f1 \<in> keys f1" by (rule punit.lt_in_keys)
    ultimately have "(lp q1 \<in> keys q1 \<and> lp f1 \<in> keys f1) \<or> (lp q1 \<in> keys q2 \<and> lp f1 \<in> keys f2)"
      by simp
    then obtain l' where eq2: "of_nat_pm (lp q1 + lp f1) = of_nat_pm (lp g) + l' \<cdot> vect f1" by (rule 1)
    have 3: "deg_pm (s + t) < deg_pm (lp q1 + lp f1)"
      if "(s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2)" and "s + t \<noteq> lp q1 + lp f1" for s t
    proof -
      from that(1) have "s + t \<prec> lp q1 + lp f1"
      proof
        assume "s \<in> keys q1 \<and> t \<in> keys f1"
        hence "s \<preceq> lp q1" and "t \<preceq> lp f1" by (simp_all add: punit.lt_max_keys)
        from this(1) have "s + t \<preceq> lp q1 + t" by (rule plus_monotone)
        also from \<open>t \<preceq> lp f1\<close> have "\<dots> \<preceq> lp q1 + lp f1" by (rule plus_monotone_left)
        finally have "s + t \<preceq> lp q1 + lp f1" .
        with that(2) show ?thesis by simp
      next
        assume "s \<in> keys q2 \<and> t \<in> keys f2"
        hence "s \<preceq> lp q2" and "t \<preceq> lp f2" by (simp_all add: punit.lt_max_keys)
        from this(1) have "s + t \<preceq> lp q2 + t" by (rule plus_monotone)
        also from \<open>t \<preceq> lp f2\<close> have "\<dots> \<preceq> lp q2 + lp f2" by (rule plus_monotone_left)
        finally have "s + t \<preceq> lp q2 + lp f2" .
        with that(2) show ?thesis by (simp only: lp_eq2)
      qed
      moreover from that(1) obtain l where eq1: "of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
        by (rule 1)
      ultimately have "l < l'" using eq2 by (rule ord_rat)
      have "rat (deg_pm (s + t)) = deg_pm (of_nat_pm (s + t))" by (simp only: deg_of_nat_pm)
      also have "\<dots> = deg_pm (of_nat_pm (lp g)) + l * deg_pm (vect f1)"
        by (simp add: eq1 deg_pm_plus deg_pm_map_scale)
      also have "\<dots> < deg_pm (of_nat_pm (lp g)) + l' * deg_pm (vect f1)"
        using \<open>0 < deg_pm (vect f1)\<close> \<open>l < l'\<close> by simp
      also have "\<dots> = deg_pm (of_nat_pm (lp q1 + lp f1))" by (simp add: eq2 deg_pm_plus deg_pm_map_scale)
      also have "\<dots> = rat (deg_pm (lp q1 + lp f1))" by (simp only: deg_of_nat_pm)
      finally show ?thesis by simp
    qed
    have 4: "deg_pm t < deg_pm (lp q1)" if "t \<in> keys q1" and "t \<noteq> lp q1" for t
    proof -
      from \<open>f1 \<noteq> 0\<close> have "lp f1 \<in> keys f1" by (rule punit.lt_in_keys)
      with that(1) have "(t \<in> keys q1 \<and> lp f1 \<in> keys f1) \<or> (t \<in> keys q2 \<and> lp f1 \<in> keys f2)" by simp
      moreover from that(2) have "t + lp f1 \<noteq> lp q1 + lp f1" by simp
      ultimately have "deg_pm (t + lp f1) < deg_pm (lp q1 + lp f1)" by (rule 3)
      thus "deg_pm t < deg_pm (lp q1)" by (simp only: deg_pm_plus)
    qed

    have 5: "poly_deg (q1 * f1) = deg_pm (lp (q1 * f1))"
    proof (intro antisym poly_deg_leI poly_deg_max_keys punit.lt_in_keys)
      fix t
      assume "t \<in> keys (q1 * f1)"
      show "deg_pm t \<le> deg_pm (lp (q1 * f1))"
      proof (cases "t = lp q1 + lp f1")
        case True
        thus ?thesis by (simp add: lp_q1_f1)
      next
        case False
        from \<open>t \<in> keys (q1 * f1)\<close> obtain t1 t2 where "t1 \<in> keys q1" and "t2 \<in> keys f1" and t: "t = t1 + t2"
          by (rule in_keys_timesE)
        from this(1, 2) have "(t1 \<in> keys q1 \<and> t2 \<in> keys f1) \<or> (t1 \<in> keys q2 \<and> t2 \<in> keys f2)" by simp
        hence "deg_pm t < deg_pm (lp q1 + lp f1)" using False unfolding t by (rule 3)
        thus ?thesis by (simp add: lp_q1_f1)
      qed
    qed fact
    also have "\<dots> = deg_pm (lp (q2 * f2))" by (simp only: lp_eq)
    also have "\<dots> = poly_deg (q2 * f2)"
    proof (rule sym, intro antisym poly_deg_leI poly_deg_max_keys punit.lt_in_keys)
      fix t
      assume "t \<in> keys (q2 * f2)"
      show "deg_pm t \<le> deg_pm (lp (q2 * f2))"
      proof (cases "t = lp q1 + lp f1")
        case True
        thus ?thesis by (simp add: lp_q2_f2 lp_eq2)
      next
        case False
        from \<open>t \<in> keys (q2 * f2)\<close> obtain t1 t2 where "t1 \<in> keys q2" and "t2 \<in> keys f2" and t: "t = t1 + t2"
          by (rule in_keys_timesE)
        from this(1, 2) have "(t1 \<in> keys q1 \<and> t2 \<in> keys f1) \<or> (t1 \<in> keys q2 \<and> t2 \<in> keys f2)" by simp
        hence "deg_pm t < deg_pm (lp q1 + lp f1)" using False unfolding t by (rule 3)
        thus ?thesis by (simp add: lp_q2_f2 lp_eq2)
      qed
    qed fact
    finally have deg_q1_f1: "poly_deg (q1 * f1) = poly_deg (q2 * f2)" .
    show ?thesis unfolding membership_problem_concl_def
    proof (intro exI conjI impI)
      have "rat (poly_deg (q1 * f1)) \<le> ?b"
      proof (rule ccontr)
        assume "\<not> rat (poly_deg (q1 * f1)) \<le> ?b"
        hence "?b < rat (poly_deg (q1 * f1))" by simp
        moreover have "is_int ?b"
          by (intro minus_is_int one_is_int deg_is_int plus_is_int_pm vect_is_int_pm map_scale_is_int_pm plus_is_int)
             (intro nat_pm_is_int_pm of_nat_pm_is_nat_pm nat_is_int of_nat_is_nat)+
        moreover have "is_int (rat (poly_deg (q1 * f1)))" by (intro nat_is_int of_nat_is_nat)
        ultimately have "?b + 1 \<le> deg_pm (of_nat_pm (lp q1 + lp f1))"
          by (simp add: is_int_less_iff 5 deg_of_nat_pm lp_q1_f1)
        also have "\<dots> = deg_pm (of_nat_pm (lp g) + l' \<cdot> vect f1)" by (simp only: eq2)
        finally have "(rat k + m + 1) * deg_pm (vect f1) \<le> l' * deg_pm (vect f1)"
          by (simp add: \<open>vect f2 = m \<cdot> vect f1\<close> k_def algebra_simps deg_pm_plus deg_pm_map_scale)
        with \<open>0 < deg_pm (vect f1)\<close> have "rat k + m + 1 \<le> l'" by simp
        hence "rat k + 1 \<le> l' - m" and "l' - m \<le> l'" and "rat k + m \<le> l' - 1" and "l' - 1 \<le> l'"
          using \<open>0 < m\<close> by simp_all
        from this(1) have "1 \<le> l' - m" by simp
        have "of_nat_pm (lp g) + (l' - m) \<cdot> vect f1 = of_nat_pm (lp q1 + lp f1) - m \<cdot> vect f1"
          by (simp add: map_scale_minus_distrib_right eq2)
        also have "\<dots> = of_nat_pm (lp q2 + lp f2) - vect f2" by (simp only: lp_eq2 \<open>vect f2 = m \<cdot> vect f1\<close>)
        also have "\<dots> = of_nat_pm (lp q2 + tp f2)" by (simp add: of_nat_pm_plus vect_alt)
        finally have eq3: "of_nat_pm (lp g) + (l' - m) \<cdot> vect f1 = of_nat_pm (lp q2 + tp f2)" .
        from tp_adds_lp have "lp f1 + tp f1 adds lp f1 + lp g" by (simp only: adds_canc_2)
        hence "of_nat_pm (lp f1 + tp f1) \<unlhd> (of_nat_pm (lp g + lp f1) :: _ \<Rightarrow>\<^sub>0 rat)"
          by (simp add: le_of_nat_pm adds_pm ac_simps)
        hence "of_nat_pm (lp f1 + tp f1) - of_nat_pm (tp f1) \<unlhd>
                (of_nat_pm (lp g + lp f1) :: _ \<Rightarrow>\<^sub>0 rat) - of_nat_pm (tp f1)"
          by (rule le_pm_mono_minus)
        hence "of_nat_pm (lp f1) \<unlhd> of_nat_pm (lp g) + 1 \<cdot> vect f1"
          by (simp add: of_nat_pm_plus vect_alt add_diff_eq)
        moreover have "of_nat_pm (lp f1) \<unlhd> of_nat_pm (lp g) + l' \<cdot> vect f1"
          by (simp add: le_of_nat_pm flip: eq2 adds_pm)
        ultimately have "of_nat_pm (lp f1) \<unlhd> of_nat_pm (lp g) + (l' - m) \<cdot> vect f1"
          using \<open>1 \<le> l' - m\<close> \<open>l' - m \<le> l'\<close> by (rule map_scale_le_interval)
        hence adds1: "lp f1 adds lp q2 + tp f2" by (simp only: adds_pm eq3 le_of_nat_pm)

        have "of_nat_pm (lp g) + (l' - 1) \<cdot> vect f1 = of_nat_pm (lp q1 + lp f1) - vect f1"
          by (simp add: map_scale_minus_distrib_right eq2)
        also have "\<dots> = of_nat_pm (lp q1 + tp f1)" by (simp add: of_nat_pm_plus vect_alt)
        finally have eq4: "of_nat_pm (lp g) + (l' - 1) \<cdot> vect f1 = of_nat_pm (lp q1 + tp f1)" .
        have "of_nat_pm (lp f2) \<unlhd> of_nat_pm (lp g) + (l' - 1) \<cdot> vect f1"
        proof (rule le_pmI)
          fix x::'x
          have "of_nat_pm (lp f2) \<unlhd> of_nat_pm (lp g) + l' \<cdot> vect f1"
            by (simp add: le_of_nat_pm lp_eq2 flip: eq2 adds_pm)
          hence "lookup (of_nat_pm (lp f2)) x \<le> lookup (of_nat_pm (lp g) + l' \<cdot> vect f1) x"
            by (rule le_pmD)
          hence l': "rat (lookup (lp f2) x) \<le> rat (lookup (lp g) x) + l' * lookup (vect f1) x"
            by (simp add: lookup_of_nat_pm lookup_add)
          have "of_nat_pm (gcs (lp f2) (tp f2)) \<unlhd> overlap" by (fact gcs_le_overlap')
          also note overlap_le
          finally have "lookup (of_nat_pm (gcs (lp f2) (tp f2))) x \<le>
                          lookup (of_nat_pm (lp g) + rat k \<cdot> vect f1) x"
            by (rule le_pmD)
          hence "min (rat (lookup (lp f2) x)) (rat (lookup (tp f2) x)) \<le>
                  rat (lookup (lp g) x) + rat k * lookup (vect f1) x"
            by (simp add: lookup_of_nat_pm lookup_add lookup_gcs_fun gcs_fun)
          hence "rat (lookup (lp f2) x) \<le> rat (lookup (lp g) x) + (l' - 1) * lookup (vect f1) x"
          proof (simp only: min_def split: if_split_asm)
            assume "rat (lookup (lp f2) x) \<le> rat (lookup (lp g) x) + rat k * lookup (vect f1) x"
            moreover note l'
            moreover from \<open>rat k + m \<le> l' - 1\<close> \<open>0 < m\<close> have "rat k \<le> l' - 1" by simp
            ultimately show ?thesis using \<open>l' - 1 \<le> l'\<close> by (rule times_le_interval)
          next
            assume "rat (lookup (tp f2) x) \<le> rat (lookup (lp g) x) + rat k * lookup (vect f1) x"
            hence "rat (lookup (tp f2) x) + lookup (vect f2) x \<le>
                    rat (lookup (lp g) x) + rat k * lookup (vect f1) x + lookup (vect f2) x"
              by (rule add_right_mono)
            hence "rat (lookup (lp f2) x) \<le>
                    rat (lookup (lp g) x) + rat k * lookup (vect f1) x + lookup (vect f2) x"
              by (simp only: vect_alt lookup_minus lookup_add lookup_of_nat_pm)
            hence "rat (lookup (lp f2) x) \<le> rat (lookup (lp g) x) + (rat k + m) * lookup (vect f1) x"
              by (simp add: \<open>vect f2 = m \<cdot> vect f1\<close> algebra_simps)
            moreover note l'
            ultimately show ?thesis using \<open>rat k + m \<le> l' - 1\<close> \<open>l' - 1 \<le> l'\<close> by (rule times_le_interval)
          qed
          thus "lookup (of_nat_pm (lp f2)) x \<le> lookup (of_nat_pm (lp g) + (l' - 1) \<cdot> vect f1) x"
            by (simp add: lookup_add lookup_of_nat_pm)
        qed
        hence adds2: "lp f2 adds lp q1 + tp f1" by (simp only: adds_pm eq4 le_of_nat_pm)

        let ?c1 = "lc q2 * tc f2 / lc f1"
        let ?c2 = "lc q1 * tc f1 / lc f2"
        let ?t1 = "lp q2 + tp f2 - lp f1"
        let ?t2 = "lp q1 + tp f1 - lp f2"
        define q1' where "q1' = punit.tail q1 + monomial ?c1 ?t1"
        define q2' where "q2' = punit.tail q2 + monomial ?c2 ?t2"
        have keys_q1': "keys q1' \<subseteq> insert ?t1 (keys q1 - {lp q1})"
        proof
          fix t
          assume "t \<in> keys q1'"
          also have "\<dots> \<subseteq> keys (punit.tail q1) \<union> keys (monomial ?c1 ?t1)"
            unfolding q1'_def by (rule keys_add_subset)
          finally show "t \<in> insert ?t1 (keys q1 - {lp q1})"
          proof
            assume "t \<in> keys (punit.tail q1)"
            thus ?thesis by (simp add: punit.keys_tail)
          next
            assume "t \<in> keys (monomial ?c1 ?t1)"
            thus ?thesis by (simp split: if_split_asm)
          qed
        qed
        have keys_q2': "keys q2' \<subseteq> insert ?t2 (keys q2 - {lp q2})"
        proof
          fix t
          assume "t \<in> keys q2'"
          also have "\<dots> \<subseteq> keys (punit.tail q2) \<union> keys (monomial ?c2 ?t2)"
            unfolding q2'_def by (rule keys_add_subset)
          finally show "t \<in> insert ?t2 (keys q2 - {lp q2})"
          proof
            assume "t \<in> keys (punit.tail q2)"
            thus ?thesis by (simp add: punit.keys_tail)
          next
            assume "t \<in> keys (monomial ?c2 ?t2)"
            thus ?thesis by (simp split: if_split_asm)
          qed
        qed

        from \<open>f1 \<noteq> 0\<close> have "lc f1 \<noteq> 0" by (rule punit.lc_not_0)
        from \<open>f2 \<noteq> 0\<close> have "lc f2 \<noteq> 0" by (rule punit.lc_not_0)
        have "f1 * monomial (lc q1) (lp q1) + f2 * monomial (lc q2) (lp q2) =
                binomial (lc f1) (lp f1) (tc f1) (tp f1) * monomial (lc q1) (lp q1) +
                binomial (lc f2) (lp f2) (tc f2) (tp f2) * monomial (lc q2) (lp q2)"
          using \<open>is_proper_binomial f1\<close> \<open>is_proper_binomial f2\<close>
          by (simp only: punit.binomial_eq_itself)
        also have "\<dots> = monomial (lc (q1 * f1)) (lp (q1 * f1)) + monomial (lc (q2 * f2)) (lp (q2 * f2)) +
                        monomial (lc q2 * tc f2) (lp q2 + tp f2) + monomial (lc q1 * tc f1) (lp q1 + tp f1)"
          by (simp only: binomial_def lc_times lp_q1_f1 lp_q2_f2)
             (simp only: times_monomial_monomial algebra_simps)
        also have "\<dots> = monomial (lc q2 * tc f2) (lp q2 + tp f2) + monomial (lc q1 * tc f1) (lp q1 + tp f1)"
          by (simp add: lp_eq lc_eq flip: single_add)
        finally have eq6: "f1 * monomial (lc q1) (lp q1) + f2 * monomial (lc q2) (lp q2) =
                      monomial (lc q2 * tc f2) (lp q2 + tp f2) + monomial (lc q1 * tc f1) (lp q1 + tp f1)" .
        have "f1 * monomial ?c1 ?t1 + f2 * monomial ?c2 ?t2 =
                binomial (lc f1) (lp f1) (tc f1) (tp f1) * monomial ?c1 ?t1 +
                binomial (lc f2) (lp f2) (tc f2) (tp f2) * monomial ?c2 ?t2"
          using \<open>is_proper_binomial f1\<close> \<open>is_proper_binomial f2\<close>
          by (simp only: punit.binomial_eq_itself)
        also have "\<dots> = monomial (lc q2 * tc f2) (lp q2 + tp f2) + monomial (lc q1 * tc f1) (lp q1 + tp f1) +
                        (monomial (?c1 * tc f1) (tp f1 + ?t1) + monomial (?c2 * tc f2) (tp f2 + ?t2))"
          using adds1 adds2 \<open>lc f1 \<noteq> 0\<close> \<open>lc f2 \<noteq> 0\<close>
          by (simp only: binomial_def times_monomial_monomial distrib_right adds_minus
                  add.commute[of "lp f1"] add.commute[of "lp f2"])
             (simp add: field_simps)
        also have "\<dots> = f1 * monomial (lc q1) (lp q1) + f2 * monomial (lc q2) (lp q2) +
                        (monomial (?c1 * tc f1) (tp f1 + ?t1) + monomial (?c2 * tc f2) (tp f2 + ?t2))"
          by (simp only: eq6)
        also have "monomial (?c1 * tc f1) (tp f1 + ?t1) + monomial (?c2 * tc f2) (tp f2 + ?t2) = 0"
          (is "?m = 0")
        proof -
          have "punit.monom_mult (lc f1 * lc f2) (lp f1 + lp f2) ?m =
                punit.monom_mult (tc f1 * tc f2) 0
                  (monomial (lc (q1 * f1)) (lp f1 + tp f2 + ((lp q1 + tp f1 - lp f2) + lp f2)) +
                   monomial (lc (q2 * f2)) (lp f2 + tp f1 + ((lp q2 + tp f2 - lp f1) + lp f1)))"
            using \<open>lc f1 \<noteq> 0\<close> \<open>lc f2 \<noteq> 0\<close>
            by (simp add: punit.monom_mult_dist_right punit.monom_mult_monomial lc_times algebra_simps)
          also have "\<dots> = punit.monom_mult (tc f1 * tc f2) (tp f1 + tp f2)
                    (monomial (lc (q1 * f1)) (lp (q1 * f1)) + monomial (lc (q2 * f2)) (lp (q2 * f2)))"
            using adds1 adds2
            by (simp only: adds_minus lp_q1_f1 lp_q2_f2)
               (simp add: punit.monom_mult_dist_right punit.monom_mult_monomial algebra_simps)
          also have "\<dots> = 0" by (simp add: lp_eq lc_eq flip: single_add)
          finally show ?thesis using \<open>lc f1 \<noteq> 0\<close> \<open>lc f2 \<noteq> 0\<close> by (simp add: punit.monom_mult_eq_zero_iff)
        qed
        finally have "g = q1' * f1 + q2' * f2"
          by (simp add: q1'_def q2'_def punit.tail_alt_2 g algebra_simps)
        with mpa have "q1' * f1 \<noteq> 0" by (rule membership_problem_assms_rep)
        hence "q1' \<noteq> 0" by auto

        have "(q1', q2') \<in> A"
        proof (simp add: A_def, intro conjI allI impI)
          fix s t
          assume "s \<in> keys q1' \<and> t \<in> keys f1"
          hence "s \<in> keys q1'" and "t \<in> keys f1" by simp_all
          from this(1) keys_q1' have "s \<in> insert ?t1 (keys q1 - {lp q1})" ..
          thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
          proof
            assume s: "s = ?t1"
            from \<open>q2 \<noteq> 0\<close> have "lp q2 \<in> keys q2" by (rule punit.lt_in_keys)
            moreover from \<open>f2 \<noteq> 0\<close> have "tp f2 \<in> keys f2" by (rule punit.tt_in_keys)
            ultimately have "lp q2 \<in> keys q1 \<and> tp f2 \<in> keys f1 \<or> lp q2 \<in> keys q2 \<and> tp f2 \<in> keys f2"
              by simp
            then obtain l'' where l'': "of_nat_pm (lp q2 + tp f2) = of_nat_pm (lp g) + l'' \<cdot> vect f1"
              by (rule 1)
            from \<open>is_proper_binomial f1\<close> have "keys f1 = {lp f1, tp f1}"
              by (rule punit.keys_proper_binomial)
            with \<open>t \<in> keys f1\<close> have "t = lp f1 \<or> t = tp f1" by simp
            thus ?thesis
            proof
              assume "t = lp f1"
              with adds1 have eq5: "s + t = lp q2 + tp f2" by (simp only: s adds_minus)
              from l'' show ?thesis unfolding eq5 ..
            next
              assume "t = tp f1"
              with adds1 have "of_nat_pm (s + t) = of_nat_pm (lp q2 + tp f2) - vect f1"
                by (simp add: s vect_alt of_nat_pm_plus of_nat_pm_minus)
              also have "\<dots> = of_nat_pm (lp g) + (l'' - 1) \<cdot> vect f1"
                by (simp add: l'' map_scale_minus_distrib_right)
              finally show ?thesis ..
            qed
          next
            assume "s \<in> keys q1 - {lp q1}"
            with \<open>t \<in> keys f1\<close> have "s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2" by simp
            then obtain l where "of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1" by (rule 1)
            thus ?thesis ..
          qed
        next
          fix s t
          assume "s \<in> keys q2' \<and> t \<in> keys f2"
          hence "s \<in> keys q2'" and "t \<in> keys f2" by simp_all
          from this(1) keys_q2' have "s \<in> insert ?t2 (keys q2 - {lp q2})" ..
          thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1"
          proof
            assume s: "s = lp q1 + tp f1 - lp f2"
            from \<open>f1 \<noteq> 0\<close> have "tp f1 \<in> keys f1" by (rule punit.tt_in_keys)
            with \<open>lp q1 \<in> keys q1\<close> have "lp q1 \<in> keys q1 \<and> tp f1 \<in> keys f1 \<or> lp q1 \<in> keys q2 \<and> tp f1 \<in> keys f2"
              by simp
            then obtain l'' where l'': "of_nat_pm (lp q1 + tp f1) = of_nat_pm (lp g) + l'' \<cdot> vect f1"
              by (rule 1)
            from \<open>is_proper_binomial f2\<close> have "keys f2 = {lp f2, tp f2}"
              by (rule punit.keys_proper_binomial)
            with \<open>t \<in> keys f2\<close> have "t = lp f2 \<or> t = tp f2" by simp
            thus ?thesis
            proof
              assume "t = lp f2"
              with adds2 have eq5: "s + t = lp q1 + tp f1" by (simp only: s adds_minus)
              from l'' show ?thesis unfolding eq5 ..
            next
              assume "t = tp f2"
              with adds2 have "of_nat_pm (s + t) = of_nat_pm (lp q1 + tp f1) - vect f2"
                by (simp add: s vect_alt of_nat_pm_plus of_nat_pm_minus)
              also have "\<dots> = of_nat_pm (lp g) + (l'' - m) \<cdot> vect f1"
                by (simp add: l'' \<open>vect f2 = m \<cdot> vect f1\<close> map_scale_minus_distrib_right)
              finally show ?thesis ..
            qed
          next
            assume "s \<in> keys q2 - {lp q2}"
            with \<open>t \<in> keys f2\<close> have "s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2" by simp
            then obtain l where "of_nat_pm (s + t) = of_nat_pm (lp g) + l \<cdot> vect f1" by (rule 1)
            thus ?thesis ..
          qed
        qed fact
        hence "poly_deg q1 \<le> poly_deg q1'" by (rule Q_min)
        also from \<open>q1' \<noteq> 0\<close> have "poly_deg q1' < deg_pm (lp q1)"
        proof (rule poly_deg_lessI)
          fix t
          assume "t \<in> keys q1'"
          hence "t \<in> insert ?t1 (keys q1 - {lp q1})" using keys_q1' ..
          thus "deg_pm t < deg_pm (lp q1)"
          proof
            from adds1 have *: "deg_pm (lp f1) \<le> deg_pm (lp q2 + tp f2)" by (rule deg_pm_mono)
            assume "t = ?t1"
            with adds1 have "deg_pm t = deg_pm (lp q2 + tp f2) - deg_pm (lp f1)"
              by (simp only: deg_pm_minus)
            also from * have "\<dots> < deg_pm (lp q1)"
              by (simp only: less_diff_conv2 lp_eq2 flip: deg_pm_plus) (simp add: deg_pm_plus 0)
            finally show ?thesis .
          next
            assume "t \<in> keys q1 - {lp q1}"
            hence "t \<in> keys q1" and "t \<noteq> lp q1" by simp_all
            thus "deg_pm t < deg_pm (lp q1)" by (rule 4)
          qed
        qed
        also from \<open>lp q1 \<in> keys q1\<close> have "\<dots> \<le> poly_deg q1" by (rule poly_deg_max_keys)
        finally show False ..
      qed
      hence "rat (poly_deg (q1 * f1)) \<le> max ?a ?b" by (rule max.coboundedI2)
      hence "to_nat (rat (poly_deg (q1 * f1))) \<le> to_nat (max ?a ?b)" by (rule to_nat_mono)
      thus "poly_deg (q1 * f1) \<le> to_nat (max ?a ?b)" by (simp only: to_nat_of_nat)
      thus "poly_deg (q2 * f2) \<le> to_nat (max ?a ?b)" by (simp only: deg_q1_f1)
    qed fact
  qed
qed

end

end (* two_polys *)

end (* theory *)
