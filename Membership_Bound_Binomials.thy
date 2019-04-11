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

abbreviation "lpp_set \<equiv> punit.lt_set"

lemma rem_3_1_4_aux_1:
  assumes "finite F" and "g \<in> punit.reduced_GB F" and "g' \<in> punit.reduced_GB F" and "t \<in> keys g"
    and "lpp g' adds t"
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
    and "lpp g' adds t"
  shows "t = lpp g"
proof -
  from assms have "g' = g" by (rule rem_3_1_4_aux_1)
  from \<open>lpp g' adds t\<close> have "lpp g \<preceq> t" unfolding \<open>g' = g\<close> by (rule ord_adds)
  with punit.lt_max_keys[OF \<open>t \<in> keys g\<close>] show ?thesis by simp
qed
  
text \<open>The following two lemmas are contained in Remark 3.1.4. of @{cite WW2015}.\<close>

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
      where "g' \<in> ?G" and "g' \<noteq> 0" and lppg': "lpp g' adds lpp ?p" by (rule punit.GB_adds_lt[simplified])
    from lppg' have lppg'': "lpp g' adds t" by (simp add: punit.lt_monomial)
    have "t \<in> keys g" unfolding keysg by simp
    from assms(1) \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> this lppg'' have "t = lpp g" by (rule rem_3_1_4_aux_2)
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
  from step(6) Poly_Mapping.keys_add have "t \<in> keys g \<union> keys (c * f')" ..
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
  obtains f where "f \<in> F" and "is_proper_binomial f" and "tpp f adds t"
proof -
  from gin tin obtain f s where "f \<in> F" and "s \<in> keys f" and "s adds t" by (rule rem_3_1_7_aux)
  have "s \<noteq> lpp f"
  proof
    assume "s = lpp f"
    from \<open>f \<in> F\<close> have "punit.is_red F g"
    proof (rule punit.is_red_addsI[simplified])
      show "f \<noteq> 0"
      proof
        assume "f = 0"
        from \<open>s \<in> keys f\<close> show False unfolding \<open>f = 0\<close> keys_zero ..
      qed
    next
      from \<open>s adds t\<close> show "lpp f adds t" unfolding \<open>s = lpp f\<close> .
    qed fact
    with \<open>\<not> punit.is_red F g\<close> show False ..
  qed
  from assms(1) \<open>f \<in> F\<close> have "is_binomial f" by (rule is_binomial_setD)
  hence "is_monomial f \<or> is_proper_binomial f" unfolding is_binomial_alt .
  hence "is_proper_binomial f"
  proof
    assume "is_monomial f"
    hence "keys f = {lpp f}" by (rule punit.keys_monomial)
    with \<open>s \<in> keys f\<close> \<open>s \<noteq> lpp f\<close> show ?thesis by simp
  qed
  with \<open>f \<in> F\<close> show ?thesis
  proof
    from \<open>is_binomial f\<close> have "keys f = {lpp f, tpp f}" by (rule punit.keys_binomial)
    with \<open>s \<in> keys f\<close> \<open>s \<noteq> lpp f\<close> have "s = tpp f" by simp
    with \<open>s adds t\<close> show "tpp f adds t" by simp
  qed
qed

end (* ordered_powerprod *)

context pm_powerprod
begin

definition membership_problem_assms ::
    "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> bool"
    where "membership_problem_assms f1 f2 g =
        (is_binomial f1 \<and> is_binomial f2 \<and> is_binomial g \<and> g \<in> ideal {f1, f2} \<and>
          \<not> punit.is_red {f1, f2} g \<and> (is_proper_binomial g \<longrightarrow> monomial 1 ` keys g \<inter> ideal {f1, f2} = {}))"

definition membership_problem_concl ::
    "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_1) \<Rightarrow> nat \<Rightarrow> bool"
  where "membership_problem_concl f1 f2 g d =
        (\<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and> poly_deg (q1 * f1) \<le> d \<and> poly_deg (q2 * f2) \<le> d)"

definition membership_problem :: "('b::field itself) \<Rightarrow> nat \<Rightarrow> bool"
  where "membership_problem _ d =
      (\<forall>f1 f2 g::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b. membership_problem_assms f1 f2 g \<longrightarrow>
        membership_problem_concl f1 f2 g d)"
    
lemma membership_problem_assmsD:
  assumes "membership_problem_assms f1 f2 g"
  shows "is_binomial f1" and "is_binomial f2" and "is_binomial g" and "g \<in> ideal {f1, f2}"
    and "\<not> punit.is_red {f1, f2} g" and "is_proper_binomial g \<Longrightarrow> monomial 1 ` keys g \<inter> ideal {f1, f2} = {}"
  using assms by (simp_all add: membership_problem_assms_def)

lemma membership_problemI:
  assumes "\<And>f1 f2 g::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field. membership_problem_assms f1 f2 g \<Longrightarrow>
            membership_problem_concl f1 f2 g d"
  shows "membership_problem TYPE('b) d"
  unfolding membership_problem_def using assms by auto

lemma membership_problem_assms_lpp_f1_nadds:
  assumes "membership_problem_assms f1 f2 g" and "t \<in> keys g"
  shows "\<not> lpp f1 adds t"
proof
  assume "lpp f1 adds t"
  from _ _ \<open>t \<in> keys g\<close> this have "punit.is_red {f1, f2} g"
  proof (rule punit.is_red_addsI[simplified], simp)
    from assms(1) have "is_binomial f1" by (rule membership_problem_assmsD)
    thus "f1 \<noteq> 0" by (rule binomial_not_0)
  qed
  moreover from assms(1) have "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
  ultimately show False by simp
qed

lemma membership_problem_assms_lpp_f2_nadds:
  assumes "membership_problem_assms f1 f2 g" and "t \<in> keys g"
  shows "\<not> lpp f2 adds t"
proof
  assume "lpp f2 adds t"
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
  shows "q1 * f1 \<noteq> 0" and "q2 * f2 \<noteq> 0" and "lpp (q1 * f1) = lpp (q2 * f2)" and "lcf (q1 * f1) = - lcf (q2 * f2)"
    and "(tpp (q1 * f1) = tpp (q2 * f2) \<Longrightarrow> thesis) \<Longrightarrow>
          (tpp g \<preceq> tpp (q1 * f1) \<Longrightarrow> tpp g \<preceq> tpp (q2 * f2) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
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
    hence "lpp q2 + lpp f2 = lpp (q2 * f2)" using \<open>f2 \<noteq> 0\<close> by (rule lp_times[symmetric])
    also from \<open>q2 * f2 \<noteq> 0\<close> have "\<dots> \<in> keys (q2 * f2)" by (rule punit.lt_in_keys)
    finally have "lpp q2 + lpp f2 \<in> keys g" by (simp only: g)
    with assms(1) have "\<not> lpp f2 adds lpp q2 + lpp f2" by (rule membership_problem_assms_lpp_f2_nadds)
    thus False by simp
  qed
  thus "q1 * f1 \<noteq> 0" using \<open>f1 \<noteq> 0\<close> by (simp add: times_not_zero)
  have 1: "lpp (q1 * f1) \<notin> keys g"
  proof
    from \<open>q1 \<noteq> 0\<close> \<open>f1 \<noteq> 0\<close> have "lpp q1 + lpp f1 = lpp (q1 * f1)" by (rule lp_times[symmetric])
    also assume "\<dots> \<in> keys g"
    finally have "lpp q1 + lpp f1 \<in> keys g" .
    with assms(1) have "\<not> lpp f1 adds lpp q1 + lpp f1" by (rule membership_problem_assms_lpp_f1_nadds)
    thus False by simp
  qed

  have "q2 \<noteq> 0"
  proof
    assume "q2 = 0"
    with assms(2) have g: "g = q1 * f1" by simp
    from \<open>q1 * f1 \<noteq> 0\<close> have "lpp (q1 * f1) \<in> keys g" unfolding g by (rule punit.lt_in_keys)
    with 1 show False ..
  qed
  thus "q2 * f2 \<noteq> 0" using \<open>f2 \<noteq> 0\<close> by (simp add: times_not_zero)
  have 2: "lpp (q2 * f2) \<notin> keys g"
  proof
    from \<open>q2 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have "lpp q2 + lpp f2 = lpp (q2 * f2)" by (rule lp_times[symmetric])
    also assume "\<dots> \<in> keys g"
    finally have "lpp q2 + lpp f2 \<in> keys g" .
    with assms(1) have "\<not> lpp f2 adds lpp q2 + lpp f2" by (rule membership_problem_assms_lpp_f2_nadds)
    thus False by simp
  qed

  show 3: "lpp (q1 * f1) = lpp (q2 * f2)"
  proof (rule ordered_powerprod_lin.linorder_cases)
    assume *: "lpp (q1 * f1) \<prec> lpp (q2 * f2)"
    from \<open>q2 * f2 \<noteq> 0\<close> have "lpp (q2 * f2) \<in> keys (q2 * f2)" by (rule punit.lt_in_keys)
    moreover from * have "lpp (q2 * f2) \<notin> keys (q1 * f1)" by (auto dest: punit.lt_max_keys simp only:)
    ultimately have "lpp (q2 * f2) \<in> keys g" unfolding assms(2) by (rule in_keys_plusI2)
    with 2 show ?thesis ..
  next
    assume *: "lpp (q2 * f2) \<prec> lpp (q1 * f1)"
    from \<open>q1 * f1 \<noteq> 0\<close> have "lpp (q1 * f1) \<in> keys (q1 * f1)" by (rule punit.lt_in_keys)
    moreover from * have "lpp (q1 * f1) \<notin> keys (q2 * f2)" by (auto dest: punit.lt_max_keys simp only:)
    ultimately have "lpp (q1 * f1) \<in> keys g" unfolding assms(2) by (rule in_keys_plusI1)
    with 1 show ?thesis ..
  qed

  from 1 have "0 = lookup (q1 * f1) (lpp (q1 * f1)) + lookup (q2 * f2) (lpp (q1 * f1))"
    by (simp add: assms(2) lookup_add in_keys_iff)
  also have "\<dots> = lookup (q1 * f1) (lpp (q1 * f1)) + lookup (q2 * f2) (lpp (q2 * f2))"
    by (simp only: 3)
  also have "\<dots> = lcf (q1 * f1) + lcf (q2 * f2)" by (simp only: punit.lc_def)
  finally show "lcf (q1 * f1) = - lcf (q2 * f2)" by (simp add: eq_neg_iff_add_eq_0)

  assume 4: "tpp (q1 * f1) = tpp (q2 * f2) \<Longrightarrow> thesis"
    and 5: "tpp g \<preceq> tpp (q1 * f1) \<Longrightarrow> tpp g \<preceq> tpp (q2 * f2) \<Longrightarrow> thesis"
  show thesis
  proof (rule ordered_powerprod_lin.linorder_cases)
    assume *: "tpp (q1 * f1) \<prec> tpp (q2 * f2)"
    from \<open>q1 * f1 \<noteq> 0\<close> have "tpp (q1 * f1) \<in> keys (q1 * f1)" by (rule punit.tt_in_keys)
    moreover from * have "tpp (q1 * f1) \<notin> keys (q2 * f2)" by (auto dest: punit.tt_min_keys simp only:)
    ultimately have "tpp (q1 * f1) \<in> keys g" unfolding assms(2) by (rule in_keys_plusI1)
    hence "tpp g \<preceq> tpp (q1 * f1)" by (rule punit.tt_min_keys)
    moreover from this * have "tpp g \<preceq> tpp (q2 * f2)" by simp
    ultimately show ?thesis by (rule 5)
  next
    assume *: "tpp (q2 * f2) \<prec> tpp (q1 * f1)"
    from \<open>q2 * f2 \<noteq> 0\<close> have "tpp (q2 * f2) \<in> keys (q2 * f2)" by (rule punit.tt_in_keys)
    moreover from * have "tpp (q2 * f2) \<notin> keys (q1 * f1)" by (auto dest: punit.tt_min_keys simp only:)
    ultimately have "tpp (q2 * f2) \<in> keys g" unfolding assms(2) by (rule in_keys_plusI2)
    hence **: "tpp g \<preceq> tpp (q2 * f2)" by (rule punit.tt_min_keys)
    from this * have "tpp g \<preceq> tpp (q1 * f1)" by simp
    thus ?thesis using ** by (rule 5)
  next
    assume "tpp (q1 * f1) = tpp (q2 * f2)"
    thus ?thesis by (rule 4)
  qed
qed

end (* pm_powerprod *)

subsection \<open>Degree Bounds on the Shifts for Generating a Monomial\<close>

context two_polys
begin

lemma binomial_ideal_irredE_assoc:
  assumes "is_binomial f1" and "is_binomial f2"
  assumes "g \<in> ideal {f1, f2}" and "\<not> punit.is_red {f1, f2} g" and "t \<in> keys g"
  obtains f k u where "f \<in> {f1, f2}" and "is_proper_binomial f" and "tpp f adds t" and "lpp f adds u"
    and "overlap \<unlhd> of_nat_pm u" and "associated f u t k" and "0 < k"
proof -
  obtain f f' q q' where eq: "{f1, f2} = {f, f'}" and g: "g = q * f + q' * f'"
    and t_in: "t \<in> keys (q * f)"
  proof -
    from assms(3) obtain q1 q2 where g: "g = q1 * f1 + q2 * f2" by (rule idealE_2)
    hence "keys g \<subseteq> keys (q1 * f1) \<union> keys (q2 * f2)" by (simp only: Poly_Mapping.keys_add)
    with assms(5) have "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)" ..
    thus ?thesis
    proof
      assume "t \<in> keys (q1 * f1)"
      with refl g show ?thesis ..
    next
      have "{f1, f2} = {f2, f1}" by (simp only: insert_commute)
      moreover have "g = q2 * f2 + q1 * f1" by (simp only: g add.commute)
      moreover assume "t \<in> keys (q2 * f2)"
      ultimately show ?thesis ..
    qed
  qed
  have f_in: "f \<in> {f1, f2}" by (simp add: eq)
  with assms(1, 2) have "is_binomial f" by blast
  have rl: "\<not> lpp f adds s" if "s \<in> keys g" for s
  proof
    note f_in
    moreover from this assms(1, 2) have "f \<noteq> 0" by (auto dest: binomial_not_0)
    moreover note that
    moreover assume "lpp f adds s"
    ultimately have "punit.is_red {f1, f2} g" by (rule punit.is_red_addsI[simplified])
    with assms(4) show False ..
  qed
  from assms(5) have nadds: "\<not> lpp f adds t" by (rule rl)
  from t_in obtain v s where "v \<in> keys q" and "s \<in> keys f" and t: "t = v + s" by (rule in_keys_timesE)
  from \<open>is_binomial f\<close> this(2) have "s = lpp f \<or> s = tpp f" by (simp add: punit.keys_binomial)
  hence s: "s = tpp f"
  proof
    assume "s = lpp f"
    hence "lpp f adds t" by (simp add: t)
    with nadds show ?thesis ..
  qed
  with nadds have "lpp f \<noteq> tpp f" by (auto simp: t)
  with \<open>is_binomial f\<close> have "is_proper_binomial f"
  by (simp add: punit.lt_eq_tt_iff has_bounded_keys_def is_binomial_def is_proper_binomial_def)
  moreover note \<open>v \<in> keys q\<close>
  moreover from t_in have "v + tpp f \<in> keys (q * f)" by (simp only: s t)
  ultimately obtain q'' where "q'' \<noteq> 0" and "q'' \<sqsubseteq> q" and tpp_q1': "tpp q'' = v"
    and assoc: "associated_poly f q''" and **: "lpp q'' + lpp f \<in> keys (q * f)"
    by (rule binomial_mult_shape_tpp')

  define u where "u = lpp q''"
  
  have "u + lpp f \<in> keys (q' * f')"
  proof (rule ccontr)
    assume "u + lpp f \<notin> keys (q' * f')"
    with ** have "u + lpp f \<in> keys g" unfolding g u_def by (rule in_keys_plusI1)
    hence "\<not> lpp f adds u + lpp f" by (rule rl)
    thus False by simp
  qed
  then obtain w w' where "w' \<in> keys f'" and w: "u + lpp f = w + w'" by (rule in_keys_timesE)

  from f_in \<open>is_proper_binomial f\<close> show ?thesis
  proof
    show "tpp f adds t" by (simp add: s t)
  next
    from \<open>q'' \<noteq> 0\<close> show "0 < card (keys q'')" by (simp add: card_gt_0_iff)
  next
    from \<open>q'' \<noteq> 0\<close> assoc show "associated f (u + lpp f) t (card (keys q''))"
      unfolding t s tpp_q1'[symmetric] u_def by (rule associated_poly_times_binomial_associated)
  next
    have "f' \<in> {f1, f2}" by (simp add: eq)
    with assms(1, 2) have "is_binomial f'" by blast
    hence "keys f' = {lpp f', tpp f'}" by (rule punit.keys_binomial)
    with \<open>w' \<in> keys f'\<close> have "w' = lpp f' \<or> w' = tpp f'" by simp
    hence "gcs (lpp f') (tpp f') \<unlhd> u + lpp f"
      by (auto simp: w simp flip: adds_pm intro: adds_trans gcs_adds gcs_adds_2)
    moreover from gcs_le_pm(1) have "gcs (lpp f) (tpp f) \<unlhd> u + lpp f"
      by (rule le_pm_trans) (simp flip: adds_pm)
    ultimately have "lcs (gcs (lpp f') (tpp f')) (gcs (lpp f) (tpp f)) \<unlhd> u + lpp f" by (rule lcs_le_pm)
    also have "lcs (gcs (lpp f') (tpp f')) (gcs (lpp f) (tpp f)) = lcs (gcs (lpp f1) (tpp f1)) (gcs (lpp f2) (tpp f2))"
      using eq by (auto simp: doubleton_eq_iff lcs_comm)
    finally show "overlap \<unlhd> of_nat_pm (u + lpp f)" by (simp only: overlap_alt' le_of_nat_pm)
  qed simp
qed

lemma thm_3_2_aux_0:
  assumes "membership_problem_assms f1 f2 g" and "\<And>t. t \<in> keys g \<Longrightarrow> \<not> tpp f2 adds t"
  obtains q1 q2 where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)"
    and "keys g \<inter> keys (q2 * f2) = {}" and "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>keys q1. t = v + tpp f1"
proof -
  from assms(1) have "g \<in> ideal {f1, f2}" by (rule membership_problem_assmsD)
  then obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" by (rule idealE_2)
  
  have 1: "keys g \<inter> keys (q2 * f2) = {}"
  proof (simp only: disjoint_eq_subset_Compl, rule, rule)
    fix t
    assume "t \<in> keys g" and "t \<in> keys (q2 * f2)"
    from this(2) obtain x y where "x \<in> keys q2" and "y \<in> keys f2" and "t = x + y"
      by (rule in_keys_timesE)
    from assms(1) have "is_binomial f2" by (rule membership_problem_assmsD)
    hence "keys f2 = {lpp f2, tpp f2}" by (rule punit.keys_binomial)
    with \<open>y \<in> keys f2\<close> have "y = lpp f2 \<or> y = tpp f2" by simp
    thus False
    proof
      assume "y = lpp f2"
      from assms(1) \<open>t \<in> keys g\<close> have "\<not> lpp f2 adds t" by (rule membership_problem_assms_lpp_f2_nadds)
      moreover have "lpp f2 adds t" unfolding adds_def \<open>y = lpp f2\<close> \<open>t = x + y\<close> by (simp add: add.commute)
      ultimately show False ..
    next
      assume "y = tpp f2"
      from \<open>t \<in> keys g\<close> have "\<not> tpp f2 adds t" by (rule assms(2))
      moreover have "tpp f2 adds t" unfolding adds_def \<open>y = tpp f2\<close> \<open>t = x + y\<close> by (simp add: add.commute)
      ultimately show False ..
    qed
  qed
  hence 2: "keys g \<subseteq> keys (q1 * f1)" using Poly_Mapping.keys_add[of "q1 * f1" "q2 * f2"] unfolding g_eq
    by auto
    
  with g_eq show ?thesis using 1
  proof
    fix t
    assume "t \<in> keys g"
    with 2 have "t \<in> keys (q1 * f1)" ..
    then obtain x y where "x \<in> keys q1" and "y \<in> keys f1" and "t = x + y"
      by (rule in_keys_timesE)
    have keys_f1: "keys f1 = {lpp f1, tpp f1}"
      by (rule punit.keys_binomial, rule membership_problem_assmsD, fact)
    from \<open>y \<in> keys f1\<close> have "y = tpp f1" unfolding keys_f1
    proof
      assume "y = lpp f1"
      from assms(1) \<open>t \<in> keys g\<close> have "\<not> lpp f1 adds t" by (rule membership_problem_assms_lpp_f1_nadds)
      moreover have "lpp f1 adds t" unfolding adds_def \<open>y = lpp f1\<close> \<open>t = x + y\<close> by (simp add: add.commute)
      ultimately show ?thesis ..
    next
      assume "y \<in> {tpp f1}"
      thus ?thesis by simp
    qed
    from \<open>x \<in> keys q1\<close> show "\<exists>v\<in>(keys q1). t = v + tpp f1" unfolding \<open>t = x + y\<close> \<open>y = tpp f1\<close>
      by (rule, simp)
  qed
qed

lemma proper_binomial_cases:
  assumes "is_proper_binomial p" and "s \<in> keys p" and "t \<in> keys p"
  obtains l where "l \<in> {-1, 0, 1}" and "of_nat_pm t = of_nat_pm s + l \<cdot> vect p"
proof -
  from assms(1) have "keys p = {lpp p, tpp p}" by (rule punit.keys_proper_binomial)
  with assms(2, 3) have "s = lpp p \<or> s = tpp p" and "t = lpp p \<or> t = tpp p" by simp_all
  thus ?thesis
  proof (elim disjE)
    assume "s = lpp p" and "t = lpp p"
    hence "of_nat_pm t = of_nat_pm s + 0 \<cdot> vect p" by simp
    show ?thesis
    proof
      show "0 \<in> {-1, 0, 1::rat}" by simp
    qed fact
  next
    assume "s = lpp p" and "t = tpp p"
    hence "of_nat_pm t = of_nat_pm s + (- 1) \<cdot> vect p" by (simp add: vect_alt map_scale_uminus_left)
    show ?thesis
    proof
      show "-1 \<in> {-1, 0, 1::rat}" by simp
    qed fact
  next
    assume "s = tpp p" and "t = lpp p"
    hence "of_nat_pm t = of_nat_pm s + 1 \<cdot> vect p" by (simp add: vect_alt)
    show ?thesis
    proof
      show "1 \<in> {-1, 0, 1::rat}" by simp
    qed fact
  next
    assume "s = tpp p" and "t = tpp p"
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
  shows "tpp f1 adds t"
proof -
  from f1_pbinomial f2_monomial have "is_binomial_set {f1, f2}"
    by (auto simp: is_binomial_set_def dest: proper_binomial_imp_binomial monomial_imp_binomial)
  moreover from mpa have "g \<in> ideal {f1, f2}" and "\<not> punit.is_red {f1, f2} g"
    by (rule membership_problem_assmsD)+
  ultimately obtain f where "f \<in> {f1, f2}" and "is_proper_binomial f" and "tpp f adds t"
    using assms by (rule rem_3_1_7)
  from \<open>f \<in> {f1, f2}\<close> have "f = f1 \<or> f = f2" by simp
  thus ?thesis
  proof
    assume "f = f1"
    with \<open>tpp f adds t\<close> show ?thesis by simp
  next
    from \<open>is_proper_binomial f\<close> have "\<not> is_monomial f" by (rule proper_binomial_no_monomial)
    assume "f = f2"
    with \<open>\<not> is_monomial f\<close> f2_monomial show ?thesis by simp
  qed
qed

lemma thm_3_2_1_aux_1': "tpp f1 adds lpp g"
proof (rule thm_3_2_1_aux_1)
  from mpa have "is_binomial g" by (rule membership_problem_assmsD)
  hence "g \<noteq> 0" by (rule binomial_not_0)
  thus "lpp g \<in> keys g" by (rule punit.lt_in_keys)
qed

lemma thm_3_2_1_aux_2:
  obtains q1 q2 where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)"
    and "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>keys q1. t = v + tpp f1"
proof -
  have "\<not> tpp f2 adds t" if "t \<in> keys g" for t
    unfolding punit.lt_eq_tt_monomial[OF f2_monomial, symmetric]
    using mpa that by (rule membership_problem_assms_lpp_f2_nadds)
  with mpa obtain q1 q2 where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)"
    and "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>keys q1. t = v + tpp f1"
    by (rule thm_3_2_aux_0) blast+
  thus ?thesis ..
qed

lemma thm_3_2_1_aux_3: "is_monomial g"
proof -
  from f2_monomial obtain c2 t2 where "c2 \<noteq> 0" and "lcf f2 = c2" and "lpp f2 = t2"
    and f2_eq: "f2 = monomial c2 t2" by (rule punit.is_monomial_monomial_ordered)
  from \<open>c2 \<noteq> 0\<close> have keys_f2: "keys f2 = {t2}" unfolding f2_eq by (rule keys_of_monomial)
  from mpa have "is_binomial g" by (rule membership_problem_assmsD)
  hence "is_monomial g \<or> is_proper_binomial g" unfolding is_binomial_alt by simp
  thus ?thesis
  proof
    assume "is_proper_binomial g"
    hence keys_g: "keys g = {lpp g, tpp g}" by (simp add: proper_binomial_imp_binomial punit.keys_binomial)
    from keys_g have "lpp g \<in> keys g" and "tpp g \<in> keys g" by simp_all
        
    obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" and keys_g_sub: "keys g \<subseteq> keys (q1 * f1)"
      and rl: "\<And>t. t \<in> keys g \<Longrightarrow> \<exists>v\<in>(keys q1). t = v + tpp f1" by (rule thm_3_2_1_aux_2) blast
      
    have **: "\<And>t. t \<in> keys g \<Longrightarrow> monomial 1 t \<in> ideal {f1, f2}"
    proof -
      fix t
      assume "t \<in> keys g"
      hence "\<exists>v\<in>(keys q1). t = v + tpp f1" by (rule rl)
      then obtain v where "v \<in> keys q1" and v: "t = v + tpp f1" ..
      have "v + tpp f1 \<in> keys (q1 * f1)" unfolding v[symmetric] by (rule, fact \<open>t \<in> keys g\<close>, fact keys_g_sub)
      from \<open>is_proper_binomial f1\<close> \<open>v \<in> keys q1\<close> this obtain q1'
        where keys_q1'f1: "keys (q1' * f1) = {lpp q1' + lpp f1, v + tpp f1}" and "lpp q1' + lpp f1 \<in> keys (q1 * f1)"
        by (rule binomial_mult_shape_tpp)
      have "lpp q1' + lpp f1 \<in> keys (q2 * f2)"
      proof (rule ccontr)
        assume "lpp q1' + lpp f1 \<notin> keys (q2 * f2)"
        with \<open>lpp q1' + lpp f1 \<in> keys (q1 * f1)\<close> have "lpp q1' + lpp f1 \<in> keys g" unfolding g_eq
          by (rule in_keys_plusI1)
        with mpa have "\<not> lpp f1 adds lpp q1' + lpp f1" by (rule membership_problem_assms_lpp_f1_nadds)
        thus False by simp
      qed
      then obtain x y where "x \<in> keys q2" and "y \<in> keys f2" and "lpp q1' + lpp f1 = x + y"
        by (rule in_keys_timesE)
      from \<open>y \<in> keys f2\<close> have "y = t2" unfolding keys_f2 by simp
      let ?q2 = "monomial (-(lookup (q1' * f1) (lpp q1' + lpp f1)) / c2) x"
      from \<open>c2 \<noteq> 0\<close> have "?q2 * f2 = monomial (- (lookup (q1' * f1) (lpp q1' + lpp f1))) (lpp q1' + lpp f1)" (is "_ = ?p")
        by (simp add: times_monomial_left \<open>lpp q1' + lpp f1 = x + y\<close> \<open>y = t2\<close> f2_eq punit.monom_mult_monomial)
      have keys_p: "keys ?p = {lpp q1' + lpp f1}"
        by (rule keys_of_monomial) (simp add: keys_q1'f1 flip: in_keys_iff)
      have "keys (q1' * f1 + ?q2 * f2) = {t}" unfolding \<open>?q2 * f2 = ?p\<close> v
      proof
        from Poly_Mapping.keys_add[of "q1' * f1" ?p] have "keys (q1' * f1 + ?p) \<subseteq> {lpp q1' + lpp f1, v + tpp f1}"
          unfolding keys_q1'f1 keys_p by simp
        moreover have "lpp q1' + lpp f1 \<notin> keys (q1' * f1 + ?p)"
          by (simp add: lookup_add lookup_single in_keys_iff)
        ultimately show "keys (q1' * f1 + ?p) \<subseteq> {v + tpp f1}" by auto
      next
        have "v + tpp f1 \<in> keys (q1' * f1 + ?p)"
        proof (rule in_keys_plusI1, simp add: keys_q1'f1, simp add: keys_p, rule, rule)
          assume "v + tpp f1 = lpp q1' + lpp f1"
          hence "lpp q1' + lpp f1 \<in> keys g" using \<open>t \<in> keys g\<close> unfolding v by simp
          from membership_problem_assms_lpp_f1_nadds[OF mpa this] show False by simp
        qed
        thus "{v + tpp f1} \<subseteq> keys (q1' * f1 + ?p)" by simp
      qed
      with _ show "monomial 1 t \<in> ideal {f1, f2}"
      proof (rule punit.monomial_1_in_pmdlI[simplified])
        show "q1' * f1 + ?q2 * f2 \<in> ideal {f1, f2}" by (rule idealI_2)
      qed
    qed
      
    from mpa \<open>is_proper_binomial g\<close> have "monomial 1 ` keys g \<inter> ideal {f1, f2} = {}"
      by (rule membership_problem_assmsD)
    moreover from \<open>lpp g \<in> keys g\<close> have "monomial 1 (lpp g) \<in> monomial 1 ` keys g" by (rule imageI)
    moreover from \<open>lpp g \<in> keys g\<close> have "monomial 1 (lpp g) \<in> ideal {f1, f2}" by (rule **)
    ultimately show ?thesis by blast
  qed
qed
  
lemma thm_3_2_1_aux_4:
  obtains k u where "k \<noteq> 0" and "lpp f1 adds u" and "lpp f2 adds u" and "associated f1 u (lpp g) k"
proof -
  have "is_binomial f1" and "is_binomial f2" and "g \<in> ideal {f1, f2}" and "\<not> punit.is_red {f1, f2} g"
    using mpa by (rule membership_problem_assmsD)+
  moreover from mpa have "lpp g \<in> keys g"
    by (intro punit.lt_in_keys binomial_not_0 membership_problem_assmsD(3))
  ultimately obtain f k u where "f \<in> {f1, f2}" and "is_proper_binomial f" and "lpp f adds u"
    and assoc: "associated f u (lpp g) k" and "0 < k" and o: "overlap \<unlhd> of_nat_pm u"
    by (rule binomial_ideal_irredE_assoc)
  from this(1, 2) f2_monomial have "f = f1" by (auto simp: is_proper_binomial_def is_monomial_def)
  from \<open>0 < k\<close> have "k \<noteq> 0" by simp
  have "of_nat_pm (gcs (lpp f2) (tpp f2)) \<unlhd> overlap" by (simp only: overlap_alt' le_of_nat_pm lcs_ge_pm)
  also have "\<dots> \<unlhd> of_nat_pm u" by fact
  finally have "gcs (lpp f2) (tpp f2) adds u" by (simp only: le_of_nat_pm adds_pm)
  moreover from f2_monomial have "lpp f2 = tpp f2" by (rule punit.lt_eq_tt_monomial)
  ultimately have "lpp f2 adds u" by simp
  with \<open>k \<noteq> 0\<close> \<open>lpp f adds u\<close> show ?thesis using assoc unfolding \<open>f = f1\<close> ..
qed

lemma thm_3_2_1_aux_5:
  assumes "k \<noteq> 0" and "lpp f1 adds u" and "lpp f2 adds u" and "associated f1 u (lpp g) k"
  shows "membership_problem_concl f1 f2 g (max (deg_pm (lpp g)) (deg_pm u))"
proof -
  have "is_monomial g" and "tpp f1 adds lpp g" by (rule thm_3_2_1_aux_3, rule thm_3_2_1_aux_1')
  from f2_monomial have "f2 \<noteq> 0" by (rule monomial_not_0)
  hence "lcf f2 \<noteq> 0" by (rule punit.lc_not_0)
  from \<open>is_monomial g\<close> have "g \<noteq> 0" by (rule monomial_not_0)
  hence "lcf g \<noteq> 0" by (rule punit.lc_not_0)
  with f1_pbinomial assms(4) \<open>k \<noteq> 0\<close> assms(2) \<open>tpp f1 adds lpp g\<close> obtain q1 c
    where eq1: "q1 * f1 = binomial c u (lcf g) (lpp g)" and obd: "punit.is_obd c u (lcf g) (lpp g)"
    by (rule associated_adds_obtains_cofactor_binomial_tcf)
  from obd have pbd: "is_pbd c u (lcf g) (lpp g)" by (rule punit.obd_imp_pbd)
  from assms(3) obtain v where u_eq: "u = v + lpp f2" by (metis addsE add.commute)
  define lc2 where "lc2 = lcf f2"
  let ?q2 = "monomial (- c / lc2) v"
  from obd have "-c \<noteq> 0" by (simp add: punit.is_obd_def)
  with \<open>lcf f2 \<noteq> 0\<close> have "(-c) / lcf f2 \<noteq> 0" by simp
  have eq2: "?q2 * f2 = monomial (-c) u"
    by (subst punit.monomial_eq_itself[OF \<open>is_monomial f2\<close>, symmetric],
        simp add: times_monomial_left \<open>lcf f2 \<noteq> 0\<close> punit.monom_mult_monomial u_eq lc2_def)
  show ?thesis
  proof (simp only: membership_problem_concl_def, intro exI conjI)
    show "g = q1 * f1 + ?q2 * f2"
      by (simp only: eq1 eq2 binomial_def monomial_uminus[symmetric],
          simp add: punit.monomial_eq_itself[OF \<open>is_monomial g\<close>])
  next
    show "poly_deg (q1 * f1) \<le> max (deg_pm (lpp g)) (deg_pm u)"
      by (simp add: eq1 poly_deg_def keys_binomial_pbd[OF pbd])
  next
    from \<open>-c \<noteq> 0\<close> have "keys (?q2 * f2) = {u}" unfolding eq2 by (rule keys_of_monomial)
    thus "poly_deg (?q2 * f2) \<le> max (deg_pm (lpp g)) (deg_pm u)" by (simp add: poly_deg_def)
  qed
qed

lemma thm_3_2_1_aux_6: "lpp f2 adds overlapshift (lpp g)"
proof -
  from f2_monomial have "tpp f2 = lpp f2" by (simp only: punit.lt_eq_tt_monomial)
  obtain k u where "k \<noteq> 0" and d1: "lpp f1 adds u" and d2: "lpp f2 adds u"
    and *: "associated f1 u (lpp g) k" by (rule thm_3_2_1_aux_4)
  from gcs_adds[of "lpp f1" "tpp f1"] d1 have "gcs (lpp f1) (tpp f1) adds u" by (rule adds_trans)
  moreover from gcs_adds[of "lpp f2" "tpp f2"] d2 have "gcs (lpp f2) (tpp f2) adds u" by (rule adds_trans)
  ultimately have "overlap \<unlhd> of_nat_pm u" by (rule overlap_leI)
  with _ f1_pbinomial thm_3_2_1_aux_1' * have "overlap \<unlhd> of_nat_pm (overlapshift (lpp g))"
    by (rule overlapshift_is_above_overlap) simp
  hence "gcs (lpp f2) (tpp f2) adds overlapshift (lpp g)" by (rule overlap_leD)
  thus ?thesis by (simp only: gcs_same \<open>tpp f2 = lpp f2\<close>)
qed

lemma thm_3_2_1_aux_7: "step (lpp g) \<noteq> 0"
proof
  assume eq: "step (lpp g) = 0"
  hence "overlapshift (lpp g) = lpp g" by (rule overlapshift_step_idI)
  moreover have "lpp f2 adds overlapshift (lpp g)" by (rule thm_3_2_1_aux_6)
  ultimately have "lpp f2 adds lpp g" by simp
  have "punit.is_red {f1, f2} g"
  proof (rule punit.is_red_addsI[simplified])
    from mpa have "is_binomial f2" by (rule membership_problem_assmsD)
    thus "f2 \<noteq> 0" by (rule binomial_not_0)
  next
    from mpa have "is_binomial g" by (rule membership_problem_assmsD)
    hence "g \<noteq> 0" by (rule binomial_not_0)
    thus "lpp g \<in> keys g" by (rule punit.lt_in_keys)
  qed (simp, fact)
  moreover from mpa have "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
  ultimately show False by simp
qed

theorem thm_3_2_1:
  "membership_problem_concl f1 f2 g (max (deg_pm (lpp g)) (deg_pm (overlapshift (lpp g))))"
proof -
  obtain k u where "k \<noteq> 0" and "lpp f1 adds u" and "lpp f2 adds u" and *: "associated f1 u (lpp g) k"
    by (rule thm_3_2_1_aux_4)
  have "f1 \<in> {f1, f2}" by simp
  moreover note f1_pbinomial
  moreover have "tpp f1 adds lpp g" by (rule thm_3_2_1_aux_1')
  moreover note \<open>associated f1 u (lpp g) k\<close>
  moreover have "overlap \<unlhd> of_nat_pm u"
  proof (rule overlap_leI)
    from gcs_adds \<open>lpp f1 adds u\<close> show "gcs (lpp f1) (tpp f1) adds u" by (rule adds_trans)
  next
    from gcs_adds \<open>lpp f2 adds u\<close> show "gcs (lpp f2) (tpp f2) adds u" by (rule adds_trans)
  qed
  ultimately have "step (lpp g) \<le> k" and **: "associated f1 (overlapshift (lpp g)) (lpp g) (step (lpp g))"
    by (rule step_min, rule associated_overlapshift)
  have "step (lpp g) \<noteq> 0" by (rule thm_3_2_1_aux_7)
  from this _ _ ** show ?thesis
  proof (rule thm_3_2_1_aux_5)
    from * ** \<open>lpp f1 adds u\<close> \<open>tpp f1 adds lpp g\<close> \<open>step (lpp g) \<le> k\<close> \<open>step (lpp g) \<noteq> 0\<close>
    show "lpp f1 adds overlapshift (lpp g)" by (rule associated_lpp_adds_between'')
  next
    show "lpp f2 adds overlapshift (lpp g)" by (rule thm_3_2_1_aux_6)
  qed
qed

end

subsubsection \<open>Two Parallel Proper Binomials\<close>

lemma membership_problem_assmsE_associated:
  assumes "membership_problem_assms f1 f2 g" and "{f1, f2} = {h1, h2}" and "tpp h1 adds t"
    and "t \<in> keys g"
  obtains k u where "associated h1 u t k" and "overlap \<unlhd> of_nat_pm u"
proof (cases "tpp h2 adds t")
  case True
  show ?thesis
  proof
    show "associated h1 t t 0" by (simp only: associated_0)
  next
    from gcs_adds_2 assms(3) have "gcs (lpp h1) (tpp h1) adds t" by (rule adds_trans)
    moreover from gcs_adds_2 True have "gcs (lpp h2) (tpp h2) adds t" by (rule adds_trans)
    ultimately have "lcs (gcs (lpp h1) (tpp h1)) (gcs (lpp h2) (tpp h2)) adds t" by (rule lcs_adds)
    with assms(2) show "overlap \<unlhd> of_nat_pm t"
      by (auto simp: doubleton_eq_iff overlap_alt' adds_pm le_of_nat_pm lcs_comm)
  qed
next
  case False
  from assms(1) have "is_binomial f1" and "is_binomial f2" and "g \<in> ideal {f1, f2}"
    and "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)+
  then obtain f k u where "f \<in> {f1, f2}" and "is_proper_binomial f" and "tpp f adds t"
    and "lpp f adds u" and assoc: "associated f u t k" and o: "overlap \<unlhd> of_nat_pm u"
    using assms(4) by (rule binomial_ideal_irredE_assoc)
  from this(1, 3) False have "f = h1" by (auto simp: assms(2))
  from assoc o show ?thesis unfolding \<open>f = h1\<close> ..
qed

context
  assumes parallel: "parallel_binomials f1 f2"
begin

lemma thm_3_2_2_aux_1:
  assumes "membership_problem_assms f1 f2 g" and "{f1, f2} = {h1, h2}"
    and "vect h2 = r \<cdot> vect h1" and "0 < r" and "tpp h1 adds tpp g" and "g = q1' * h1 + q2' * h2"
    and "\<And>s t. (s \<in> keys q1' \<and> t \<in> keys h1) \<or> (s \<in> keys q2' \<and> t \<in> keys h2) \<Longrightarrow>
                \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
  obtains q1 q2 l' where "g = q1 * h1 + q2 * h2" and "0 < l'" and "l' < rat (step (tpp g)) + 1 + r"
    and "of_nat_pm (lpp (q1 * h1)) = of_nat_pm (tpp g) + l' \<cdot> vect h1"
    and "\<And>s t. (s \<in> keys q1 \<and> t \<in> keys h1) \<or> (s \<in> keys q2 \<and> t \<in> keys h2) \<Longrightarrow>
                \<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
proof -
  define k where "k = step (tpp g)"
  from assms(1) have "is_binomial g" by (rule membership_problem_assmsD)
  hence "g \<noteq> 0" by (rule binomial_not_0)
  hence "tpp g \<in> keys g" by (rule punit.tt_in_keys)
  have "h2 \<in> {f1, f2}" by (simp add: assms(2))
  from parallel have f1_pb: "is_proper_binomial f1" and f2_pb: "is_proper_binomial f2"
    by (rule parallel_binomialsD)+
  with \<open>h2 \<in> {f1, f2}\<close> have "is_proper_binomial h2" by blast
  have "h1 \<in> {f1, f2}" by (simp add: assms(2))
  moreover from this f1_pb f2_pb have "is_proper_binomial h1" by blast
  moreover note assms(5)
  moreover obtain k' u where "associated h1 u (tpp g) k'" and "overlap \<unlhd> of_nat_pm u"
    using assms(1, 2, 5) \<open>tpp g \<in> keys g\<close> by (rule membership_problem_assmsE_associated)
  ultimately have "overlap \<unlhd> of_nat_pm (overlapshift (tpp g))"
    and "of_nat_pm (overlapshift (tpp g)) = of_nat_pm (tpp g) + rat (step (tpp g)) \<cdot> vect h1"
    and "step (tpp g) \<le> k'"
    by (rule overlapshift_is_above_overlap, rule of_nat_pm_overlapshift', rule step_min)
  hence overlap_le: "overlap \<unlhd> of_nat_pm (tpp g) + rat k \<cdot> vect h1" by (simp only: k_def)

  define X where "X = indets h1 \<union> indets h2 \<union> indets q1' \<union> indets q2'"
  have "finite X" by (simp add: X_def finite_indets)

  define A where "A = {Q. fst Q \<in> P[X] \<and> snd Q \<in> P[X] \<and> g = fst Q * h1 + snd Q * h2 \<and>
                        (\<forall>s t. (s \<in> keys (fst Q) \<and> t \<in> keys h1) \<or> (s \<in> keys (snd Q) \<and> t \<in> keys h2) \<longrightarrow>
                          (\<exists>l::rat. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1))}"
  obtain q1 q2 where "(q1, q2) \<in> A" and Q_min: "\<And>q1' q2'. (q1', q2') \<in> A \<Longrightarrow> lpp q1 \<preceq> lpp q1'"
  proof -
    from \<open>finite X\<close> have "wfp_on (\<prec>) {x. varnum_wrt X x \<le> 0}"
      by (intro wfp_on_ord_strict dickson_grading_varnum_wrt)
    hence "wfp_on (\<prec>) .[X]" by (simp only: varnum_wrt_le_iff) (simp add: PPs_def)
    moreover have "lpp (fst (q1', q2')) \<in> lpp ` fst ` A"
    proof (intro imageI)
      have "q1' \<in> P[X]" and "q2' \<in> P[X]" by (auto intro: PolysI_alt simp: X_def)
      with assms(6, 7) show "(q1', q2') \<in> A" by (simp add: A_def)
    qed
    moreover have "lpp ` fst ` A \<subseteq> .[X]" by (auto simp: A_def PPs_closed_lpp)
    ultimately obtain l where "l \<in> lpp ` fst ` A" and *: "\<And>l'. l' \<prec> l \<Longrightarrow> l' \<notin> lpp ` fst ` A"
      by (rule wfp_onE_min) blast
    from this(1) obtain Q where "Q \<in> A" and l: "l = lpp (fst Q)" by blast
    obtain q1 q2 where Q: "Q = (q1, q2)" using prod.exhaust by blast
    show ?thesis
    proof
      from \<open>Q \<in> A\<close> show "(q1, q2) \<in> A" by (simp only: Q)
    next
      fix q1' q2'
      assume "(q1', q2') \<in> A"
      hence "lpp (fst (q1', q2')) \<in> lpp ` fst ` A" by (intro imageI)
      with * have "\<not> lpp (fst (q1', q2')) \<prec> l" by blast
      thus "lpp q1 \<preceq> lpp q1'" by (simp add: Q l)
    qed
  qed
  from this(1) have "q1 \<in> P[X]" and "q2 \<in> P[X]" and g: "g = q1 * h1 + q2 * h2"
    and 1: "\<And>s t thesis. (s \<in> keys q1 \<and> t \<in> keys h1) \<or> (s \<in> keys q2 \<and> t \<in> keys h2) \<Longrightarrow>
              (\<And>l::rat. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1 \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by (auto simp: A_def)

  from assms(1, 2) have mpa: "membership_problem_assms h1 h2 g"
    by (auto simp: membership_problem_assms_def)
  hence "q1 * h1 \<noteq> 0" and "q2 * h2 \<noteq> 0" and lpp_eq: "lpp (q1 * h1) = lpp (q2 * h2)"
    and lc_eq: "lcf (q1 * h1) = - lcf (q2 * h2)" using g by (rule membership_problem_assms_rep)+
  from this(1, 2) have "q1 \<noteq> 0" and "h1 \<noteq> 0" and "q2 \<noteq> 0" and "h2 \<noteq> 0" by auto
  from this(1, 2) have lpp_q1_h1: "lpp (q1 * h1) = lpp q1 + lpp h1" by (rule lp_times)
  from \<open>q2 \<noteq> 0\<close> \<open>h2 \<noteq> 0\<close> have lpp_q2_h2: "lpp (q2 * h2) = lpp q2 + lpp h2" by (rule lp_times)
  have lpp_eq2: "lpp q1 + lpp h1 = lpp q2 + lpp h2" by (simp only: lpp_eq lpp_q2_h2 flip: lpp_q1_h1)
  from \<open>q1 \<noteq> 0\<close> have "lpp q1 \<in> keys q1" by (rule punit.lt_in_keys)
  moreover from \<open>h1 \<noteq> 0\<close> have "lpp h1 \<in> keys h1" by (rule punit.lt_in_keys)
  ultimately have "(lpp q1 \<in> keys q1 \<and> lpp h1 \<in> keys h1) \<or> (lpp q1 \<in> keys q2 \<and> lpp h1 \<in> keys h2)"
    by simp
  then obtain l' where eq2: "of_nat_pm (lpp q1 + lpp h1) = of_nat_pm (tpp g) + l' \<cdot> vect h1" by (rule 1)

  from g show ?thesis
  proof
    show "of_nat_pm (lpp (q1 * h1)) = of_nat_pm (tpp g) + l' \<cdot> vect h1" by (simp only: eq2 lpp_q1_h1)
  next
    fix s t
    assume "s \<in> keys q1 \<and> t \<in> keys h1 \<or> s \<in> keys q2 \<and> t \<in> keys h2"
    then obtain l where "of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1" by (rule 1)
    thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1" ..
  next
    show "0 < l'"
    proof (rule ccontr)
      assume "\<not> 0 < l'"
      hence "l' \<le> 0" by simp
      have "of_nat_pm (lpp h1) \<unlhd> of_nat_pm (tpp g) + l' \<cdot> vect h1"
        by (simp add: of_nat_pm_plus le_pm_increasing zero_le_of_nat_pm flip: eq2)
      moreover have "of_nat_pm (lpp h1) \<unlhd> of_nat_pm (tpp g) + 1 \<cdot> vect h1"
      proof -
        from assms(5) have "of_nat_pm (tpp h1) \<unlhd> (of_nat_pm (tpp g) :: _ \<Rightarrow>\<^sub>0 rat)"
          by (simp only: le_of_nat_pm adds_pm)
        hence "of_nat_pm (tpp h1) + vect h1 \<unlhd> of_nat_pm (tpp g) + vect h1"
          by (rule le_pm_mono_plus_right)
        thus ?thesis by (simp add: vect_alt)
      qed
      ultimately have "of_nat_pm (lpp h1) \<unlhd> of_nat_pm (tpp g) + 0 \<cdot> vect h1" using \<open>l' \<le> 0\<close>
        by (rule map_scale_le_interval) simp
      hence "lpp h1 adds tpp g" by (simp add: le_of_nat_pm adds_pm)
      with \<open>h1 \<in> {f1, f2}\<close> proper_binomial_not_0 \<open>tpp g \<in> keys g\<close> have "punit.is_red {f1, f2} g"
        by (rule punit.is_red_addsI[simplified]) fact
      moreover from assms(1) have "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
      ultimately show False by simp
    qed
  next
    show "l' < rat (step (tpp g)) + 1 + r" unfolding k_def[symmetric]
    proof (rule ccontr)
      assume "\<not> l' < rat k + 1 + r"
      hence "rat k + 1 + r \<le> l'" by simp
      hence "rat k + 1 \<le> l' - r" and "l' - r \<le> l'" and "rat k + r \<le> l' - 1" and "l' - 1 \<le> l'"
        using \<open>0 < r\<close> by simp_all
      from this(1) have "1 \<le> l' - r" by simp
      have "of_nat_pm (tpp g) + (l' - r) \<cdot> vect h1 = of_nat_pm (lpp q1 + lpp h1) - r \<cdot> vect h1"
        by (simp add: map_scale_minus_distrib_right eq2)
      also have "\<dots> = of_nat_pm (lpp q2 + lpp h2) - vect h2" by (simp only: lpp_eq2 assms(3))
      also have "\<dots> = of_nat_pm (lpp q2 + tpp h2)" by (simp add: of_nat_pm_plus vect_alt)
      finally have eq3: "of_nat_pm (tpp g) + (l' - r) \<cdot> vect h1 = of_nat_pm (lpp q2 + tpp h2)" .
      from assms(5) have "lpp h1 + tpp h1 adds lpp h1 + tpp g" by (simp only: adds_canc_2)
      hence "of_nat_pm (lpp h1 + tpp h1) \<unlhd> (of_nat_pm (tpp g + lpp h1) :: _ \<Rightarrow>\<^sub>0 rat)"
        by (simp add: le_of_nat_pm adds_pm ac_simps)
      hence "of_nat_pm (lpp h1 + tpp h1) - of_nat_pm (tpp h1) \<unlhd>
              (of_nat_pm (tpp g + lpp h1) :: _ \<Rightarrow>\<^sub>0 rat) - of_nat_pm (tpp h1)"
        by (rule le_pm_mono_minus)
      hence "of_nat_pm (lpp h1) \<unlhd> of_nat_pm (tpp g) + 1 \<cdot> vect h1"
        by (simp add: of_nat_pm_plus vect_alt add_diff_eq)
      moreover have "of_nat_pm (lpp h1) \<unlhd> of_nat_pm (tpp g) + l' \<cdot> vect h1"
        by (simp add: le_of_nat_pm flip: eq2 adds_pm)
      ultimately have "of_nat_pm (lpp h1) \<unlhd> of_nat_pm (tpp g) + (l' - r) \<cdot> vect h1"
        using \<open>1 \<le> l' - r\<close> \<open>l' - r \<le> l'\<close> by (rule map_scale_le_interval)
      hence adds1: "lpp h1 adds lpp q2 + tpp h2" by (simp only: adds_pm eq3 le_of_nat_pm)

      have "of_nat_pm (tpp g) + (l' - 1) \<cdot> vect h1 = of_nat_pm (lpp q1 + lpp h1) - vect h1"
        by (simp add: map_scale_minus_distrib_right eq2)
      also have "\<dots> = of_nat_pm (lpp q1 + tpp h1)" by (simp add: of_nat_pm_plus vect_alt)
      finally have eq4: "of_nat_pm (tpp g) + (l' - 1) \<cdot> vect h1 = of_nat_pm (lpp q1 + tpp h1)" .
      have "of_nat_pm (lpp h2) \<unlhd> of_nat_pm (tpp g) + (l' - 1) \<cdot> vect h1"
      proof (rule le_pmI)
        fix x::'x
        have "of_nat_pm (lpp h2) \<unlhd> of_nat_pm (tpp g) + l' \<cdot> vect h1"
          by (simp add: le_of_nat_pm lpp_eq2 flip: eq2 adds_pm)
        hence "lookup (of_nat_pm (lpp h2)) x \<le> lookup (of_nat_pm (tpp g) + l' \<cdot> vect h1) x"
          by (rule le_pmD)
        hence l': "rat (lookup (lpp h2) x) \<le> rat (lookup (tpp g) x) + l' * lookup (vect h1) x"
          by (simp add: lookup_of_nat_pm lookup_add)
        from \<open>h2 \<in> {f1, f2}\<close> gcs_le_overlap' have "of_nat_pm (gcs (lpp h2) (tpp h2)) \<unlhd> overlap"
          by auto
        also note overlap_le
        finally have "lookup (of_nat_pm (gcs (lpp h2) (tpp h2))) x \<le>
                        lookup (of_nat_pm (tpp g) + rat k \<cdot> vect h1) x"
          by (rule le_pmD)
        hence "min (rat (lookup (lpp h2) x)) (rat (lookup (tpp h2) x)) \<le>
                rat (lookup (tpp g) x) + rat k * lookup (vect h1) x"
          by (simp add: lookup_of_nat_pm lookup_add lookup_gcs_fun gcs_fun)
        hence "rat (lookup (lpp h2) x) \<le> rat (lookup (tpp g) x) + (l' - 1) * lookup (vect h1) x"
        proof (simp only: min_def split: if_split_asm)
          assume "rat (lookup (lpp h2) x) \<le> rat (lookup (tpp g) x) + rat k * lookup (vect h1) x"
          moreover note l'
          moreover from \<open>rat k + r \<le> l' - 1\<close> \<open>0 < r\<close> have "rat k \<le> l' - 1" by simp
          ultimately show ?thesis using \<open>l' - 1 \<le> l'\<close> by (rule times_le_interval)
        next
          assume "rat (lookup (tpp h2) x) \<le> rat (lookup (tpp g) x) + rat k * lookup (vect h1) x"
          hence "rat (lookup (tpp h2) x) + lookup (vect h2) x \<le>
                  rat (lookup (tpp g) x) + rat k * lookup (vect h1) x + lookup (vect h2) x"
            by (rule add_right_mono)
          hence "rat (lookup (lpp h2) x) \<le>
                  rat (lookup (tpp g) x) + rat k * lookup (vect h1) x + lookup (vect h2) x"
            by (simp only: vect_alt lookup_minus lookup_add lookup_of_nat_pm)
          hence "rat (lookup (lpp h2) x) \<le> rat (lookup (tpp g) x) + (rat k + r) * lookup (vect h1) x"
            by (simp add: assms(3) algebra_simps)
          moreover note l'
          ultimately show ?thesis using \<open>rat k + r \<le> l' - 1\<close> \<open>l' - 1 \<le> l'\<close> by (rule times_le_interval)
        qed
        thus "lookup (of_nat_pm (lpp h2)) x \<le> lookup (of_nat_pm (tpp g) + (l' - 1) \<cdot> vect h1) x"
          by (simp add: lookup_add lookup_of_nat_pm)
      qed
      hence adds2: "lpp h2 adds lpp q1 + tpp h1" by (simp only: adds_pm eq4 le_of_nat_pm)

      let ?c1 = "lcf q2 * tcf h2 / lcf h1"
      let ?c2 = "lcf q1 * tcf h1 / lcf h2"
      let ?t1 = "lpp q2 + tpp h2 - lpp h1"
      let ?t2 = "lpp q1 + tpp h1 - lpp h2"
      define q1'' where "q1'' = punit.tail q1 + monomial ?c1 ?t1"
      define q2'' where "q2'' = punit.tail q2 + monomial ?c2 ?t2"
      have keys_q1'': "keys q1'' \<subseteq> insert ?t1 (keys q1 - {lpp q1})"
      proof
        fix t
        assume "t \<in> keys q1''"
        also have "\<dots> \<subseteq> keys (punit.tail q1) \<union> keys (monomial ?c1 ?t1)"
          unfolding q1''_def by (rule Poly_Mapping.keys_add)
        finally show "t \<in> insert ?t1 (keys q1 - {lpp q1})"
        proof
          assume "t \<in> keys (punit.tail q1)"
          thus ?thesis by (simp add: punit.keys_tail)
        next
          assume "t \<in> keys (monomial ?c1 ?t1)"
          thus ?thesis by (simp split: if_split_asm)
        qed
      qed
      have keys_q2'': "keys q2'' \<subseteq> insert ?t2 (keys q2 - {lpp q2})"
      proof
        fix t
        assume "t \<in> keys q2''"
        also have "\<dots> \<subseteq> keys (punit.tail q2) \<union> keys (monomial ?c2 ?t2)"
          unfolding q2''_def by (rule Poly_Mapping.keys_add)
        finally show "t \<in> insert ?t2 (keys q2 - {lpp q2})"
        proof
          assume "t \<in> keys (punit.tail q2)"
          thus ?thesis by (simp add: punit.keys_tail)
        next
          assume "t \<in> keys (monomial ?c2 ?t2)"
          thus ?thesis by (simp split: if_split_asm)
        qed
      qed

      from \<open>h1 \<noteq> 0\<close> have "lcf h1 \<noteq> 0" by (rule punit.lc_not_0)
      from \<open>h2 \<noteq> 0\<close> have "lcf h2 \<noteq> 0" by (rule punit.lc_not_0)
      have "h1 * monomial (lcf q1) (lpp q1) + h2 * monomial (lcf q2) (lpp q2) =
              binomial (lcf h1) (lpp h1) (tcf h1) (tpp h1) * monomial (lcf q1) (lpp q1) +
              binomial (lcf h2) (lpp h2) (tcf h2) (tpp h2) * monomial (lcf q2) (lpp q2)"
        using \<open>is_proper_binomial h1\<close> \<open>is_proper_binomial h2\<close>
        by (simp only: punit.binomial_eq_itself)
      also have "\<dots> = monomial (lcf (q1 * h1)) (lpp (q1 * h1)) + monomial (lcf (q2 * h2)) (lpp (q2 * h2)) +
                      monomial (lcf q2 * tcf h2) (lpp q2 + tpp h2) + monomial (lcf q1 * tcf h1) (lpp q1 + tpp h1)"
        by (simp only: binomial_def lc_times lpp_q1_h1 lpp_q2_h2)
           (simp only: times_monomial_monomial algebra_simps)
      also have "\<dots> = monomial (lcf q2 * tcf h2) (lpp q2 + tpp h2) + monomial (lcf q1 * tcf h1) (lpp q1 + tpp h1)"
        by (simp add: lpp_eq lc_eq flip: single_add)
      finally have eq6: "h1 * monomial (lcf q1) (lpp q1) + h2 * monomial (lcf q2) (lpp q2) =
                    monomial (lcf q2 * tcf h2) (lpp q2 + tpp h2) + monomial (lcf q1 * tcf h1) (lpp q1 + tpp h1)" .
      have "h1 * monomial ?c1 ?t1 + h2 * monomial ?c2 ?t2 =
              binomial (lcf h1) (lpp h1) (tcf h1) (tpp h1) * monomial ?c1 ?t1 +
              binomial (lcf h2) (lpp h2) (tcf h2) (tpp h2) * monomial ?c2 ?t2"
        using \<open>is_proper_binomial h1\<close> \<open>is_proper_binomial h2\<close>
        by (simp only: punit.binomial_eq_itself)
      also have "\<dots> = monomial (lcf q2 * tcf h2) (lpp q2 + tpp h2) + monomial (lcf q1 * tcf h1) (lpp q1 + tpp h1) +
                      (monomial (?c1 * tcf h1) (tpp h1 + ?t1) + monomial (?c2 * tcf h2) (tpp h2 + ?t2))"
        using adds1 adds2 \<open>lcf h1 \<noteq> 0\<close> \<open>lcf h2 \<noteq> 0\<close>
        by (simp only: binomial_def times_monomial_monomial distrib_right adds_minus
                add.commute[of "lpp h1"] add.commute[of "lpp h2"])
           (simp add: field_simps)
      also have "\<dots> = h1 * monomial (lcf q1) (lpp q1) + h2 * monomial (lcf q2) (lpp q2) +
                      (monomial (?c1 * tcf h1) (tpp h1 + ?t1) + monomial (?c2 * tcf h2) (tpp h2 + ?t2))"
        by (simp only: eq6)
      also have "monomial (?c1 * tcf h1) (tpp h1 + ?t1) + monomial (?c2 * tcf h2) (tpp h2 + ?t2) = 0"
        (is "?m = 0")
      proof -
        have "punit.monom_mult (lcf h1 * lcf h2) (lpp h1 + lpp h2) ?m =
              punit.monom_mult (tcf h1 * tcf h2) 0
                (monomial (lcf (q1 * h1)) (lpp h1 + tpp h2 + ((lpp q1 + tpp h1 - lpp h2) + lpp h2)) +
                 monomial (lcf (q2 * h2)) (lpp h2 + tpp h1 + ((lpp q2 + tpp h2 - lpp h1) + lpp h1)))"
          using \<open>lcf h1 \<noteq> 0\<close> \<open>lcf h2 \<noteq> 0\<close>
          by (simp add: punit.monom_mult_dist_right punit.monom_mult_monomial lc_times algebra_simps)
        also have "\<dots> = punit.monom_mult (tcf h1 * tcf h2) (tpp h1 + tpp h2)
                  (monomial (lcf (q1 * h1)) (lpp (q1 * h1)) + monomial (lcf (q2 * h2)) (lpp (q2 * h2)))"
          using adds1 adds2
          by (simp only: adds_minus lpp_q1_h1 lpp_q2_h2)
             (simp add: punit.monom_mult_dist_right punit.monom_mult_monomial algebra_simps)
        also have "\<dots> = 0" by (simp add: lpp_eq lc_eq flip: single_add)
        finally show ?thesis using \<open>lcf h1 \<noteq> 0\<close> \<open>lcf h2 \<noteq> 0\<close> by (simp add: punit.monom_mult_eq_zero_iff)
      qed
      finally have "g = q1'' * h1 + q2'' * h2"
        by (simp add: q1''_def q2''_def punit.tail_alt_2 g algebra_simps)
      with mpa have "q1'' * h1 \<noteq> 0" by (rule membership_problem_assms_rep)
      hence "q1'' \<noteq> 0" by auto

      have "(q1'', q2'') \<in> A"
      proof (simp add: A_def, intro conjI allI impI)
        have "h2 \<in> P[X]" by (auto intro: PolysI_alt simp: X_def)
        with \<open>q1 \<in> P[X]\<close> \<open>q2 \<in> P[X]\<close> show "q1'' \<in> P[X]" unfolding q1''_def punit.tail_def punit.lower_def
          by (intro Polys_closed_plus Polys_closed_except Polys_closed_monomial PPs_closed_minus
                  PPs_closed_plus PPs_closed_lpp PPs_closed_tpp)
      next
        have "h1 \<in> P[X]" by (auto intro: PolysI_alt simp: X_def)
        with \<open>q1 \<in> P[X]\<close> \<open>q2 \<in> P[X]\<close> show "q2'' \<in> P[X]" unfolding q2''_def punit.tail_def punit.lower_def
          by (intro Polys_closed_plus Polys_closed_except Polys_closed_monomial PPs_closed_minus
                  PPs_closed_plus PPs_closed_lpp PPs_closed_tpp)
      next
        fix s t
        assume "s \<in> keys q1'' \<and> t \<in> keys h1"
        hence "s \<in> keys q1''" and "t \<in> keys h1" by simp_all
        from this(1) keys_q1'' have "s \<in> insert ?t1 (keys q1 - {lpp q1})" ..
        thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
        proof
          assume s: "s = ?t1"
          from \<open>q2 \<noteq> 0\<close> have "lpp q2 \<in> keys q2" by (rule punit.lt_in_keys)
          moreover from \<open>h2 \<noteq> 0\<close> have "tpp h2 \<in> keys h2" by (rule punit.tt_in_keys)
          ultimately have "lpp q2 \<in> keys q1 \<and> tpp h2 \<in> keys h1 \<or> lpp q2 \<in> keys q2 \<and> tpp h2 \<in> keys h2"
            by simp
          then obtain l'' where l'': "of_nat_pm (lpp q2 + tpp h2) = of_nat_pm (tpp g) + l'' \<cdot> vect h1"
            by (rule 1)
          from \<open>is_proper_binomial h1\<close> have "keys h1 = {lpp h1, tpp h1}"
            by (rule punit.keys_proper_binomial)
          with \<open>t \<in> keys h1\<close> have "t = lpp h1 \<or> t = tpp h1" by simp
          thus ?thesis
          proof
            assume "t = lpp h1"
            with adds1 have eq5: "s + t = lpp q2 + tpp h2" by (simp only: s adds_minus)
            from l'' show ?thesis unfolding eq5 ..
          next
            assume "t = tpp h1"
            with adds1 have "of_nat_pm (s + t) = of_nat_pm (lpp q2 + tpp h2) - vect h1"
              by (simp add: s vect_alt of_nat_pm_plus of_nat_pm_minus)
            also have "\<dots> = of_nat_pm (tpp g) + (l'' - 1) \<cdot> vect h1"
              by (simp add: l'' map_scale_minus_distrib_right)
            finally show ?thesis ..
          qed
        next
          assume "s \<in> keys q1 - {lpp q1}"
          with \<open>t \<in> keys h1\<close> have "s \<in> keys q1 \<and> t \<in> keys h1 \<or> s \<in> keys q2 \<and> t \<in> keys h2" by simp
          then obtain l where "of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1" by (rule 1)
          thus ?thesis ..
        qed
      next
        fix s t
        assume "s \<in> keys q2'' \<and> t \<in> keys h2"
        hence "s \<in> keys q2''" and "t \<in> keys h2" by simp_all
        from this(1) keys_q2'' have "s \<in> insert ?t2 (keys q2 - {lpp q2})" ..
        thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1"
        proof
          assume s: "s = lpp q1 + tpp h1 - lpp h2"
          from \<open>h1 \<noteq> 0\<close> have "tpp h1 \<in> keys h1" by (rule punit.tt_in_keys)
          with \<open>lpp q1 \<in> keys q1\<close> have "lpp q1 \<in> keys q1 \<and> tpp h1 \<in> keys h1 \<or> lpp q1 \<in> keys q2 \<and> tpp h1 \<in> keys h2"
            by simp
          then obtain l'' where l'': "of_nat_pm (lpp q1 + tpp h1) = of_nat_pm (tpp g) + l'' \<cdot> vect h1"
            by (rule 1)
          from \<open>is_proper_binomial h2\<close> have "keys h2 = {lpp h2, tpp h2}"
            by (rule punit.keys_proper_binomial)
          with \<open>t \<in> keys h2\<close> have "t = lpp h2 \<or> t = tpp h2" by simp
          thus ?thesis
          proof
            assume "t = lpp h2"
            with adds2 have eq5: "s + t = lpp q1 + tpp h1" by (simp only: s adds_minus)
            from l'' show ?thesis unfolding eq5 ..
          next
            assume "t = tpp h2"
            with adds2 have "of_nat_pm (s + t) = of_nat_pm (lpp q1 + tpp h1) - vect h2"
              by (simp add: s vect_alt of_nat_pm_plus of_nat_pm_minus)
            also have "\<dots> = of_nat_pm (tpp g) + (l'' - r) \<cdot> vect h1"
              by (simp add: l'' assms(3) map_scale_minus_distrib_right)
            finally show ?thesis ..
          qed
        next
          assume "s \<in> keys q2 - {lpp q2}"
          with \<open>t \<in> keys h2\<close> have "s \<in> keys q1 \<and> t \<in> keys h1 \<or> s \<in> keys q2 \<and> t \<in> keys h2" by simp
          then obtain l where "of_nat_pm (s + t) = of_nat_pm (tpp g) + l \<cdot> vect h1" by (rule 1)
          thus ?thesis ..
        qed
      qed fact
      hence "lpp q1 \<preceq> lpp q1''" by (rule Q_min)
      also from \<open>q1'' \<noteq> 0\<close> have "\<dots> \<prec> lpp q1"
      proof (rule punit.lt_less)
        fix t
        assume "lpp q1 \<preceq> t"
        moreover {
          assume "t \<in> keys q1''"
          hence "t \<in> insert ?t1 (keys q1 - {lpp q1})" using keys_q1'' ..
          hence "t \<prec> lpp q1"
          proof
            assume "t = ?t1"
            from \<open>is_proper_binomial h2\<close> have *: "tpp h2 \<prec> lpp h2" by (rule punit.lt_gr_tt_binomial)
            from adds1 have "t + lpp h1 = lpp q2 + tpp h2" by (simp add: \<open>t = ?t1\<close> adds_minus)
            also from * have "\<dots> \<prec> lpp q2 + lpp h2" by (rule plus_monotone_strict_left)
            also have "\<dots> = lpp q1 + lpp h1" by (simp only: lpp_eq lpp_q2_h2 flip: lpp_q1_h1)
            finally show ?thesis by (rule ord_strict_canc)
          next
            assume "t \<in> keys q1 - {lpp q1}"
            hence "t \<in> keys q1" and "t \<noteq> lpp q1" by simp_all
            from this(1) have "t \<preceq> lpp q1" by (rule punit.lt_max_keys)
            with \<open>t \<noteq> lpp q1\<close> show "t \<prec> lpp q1" by simp
          qed
        }
        ultimately show "lookup q1'' t = 0" by (auto simp flip: not_in_keys_iff_lookup_eq_zero)
      qed
      finally show False ..
    qed
  qed
qed

context
  fixes g :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b"
  assumes g_monomial: "is_monomial g"
begin

lemma thm_3_2_2_aux_2:
  assumes "g \<in> ideal {f1, f2}"
  obtains q1 q2 where "g = q1 * f1 + q2 * f2"
    and "\<And>f s t. f \<in> {f1, f2} \<Longrightarrow> (s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2) \<Longrightarrow>
            \<exists>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f"
proof -
  from assms obtain q1' q2' where g: "g = q1' * f1 + q2' * f2" by (rule idealE_2)
  define S1 where "S1 = {t. \<forall>s\<in>keys f1. \<forall>l. of_nat_pm (t + s) \<noteq> of_nat_pm (lpp g) + l \<cdot> vect f1}"
  define S2 where "S2 = {t. \<forall>s\<in>keys f2. \<forall>l. of_nat_pm (t + s) \<noteq> of_nat_pm (lpp g) + l \<cdot> vect f1}"
  define q1 where "q1 = except q1' S1"
  define q2 where "q2 = except q2' S2"
  from parallel have "parallel_binomials f2 f1" by (rule parallel_binomials_sym)
  then obtain m where "0 < m" and m: "vect f2 = m \<cdot> vect f1" by (rule parallel_binomialsE_vect)
  have 1: "P" if "s \<in> keys q1" and "t \<in> keys f1"
    and "\<And>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1 \<Longrightarrow> P" for s t P
  proof -
    from that(1) have "s \<in> keys q1'" and "s \<notin> S1" by (simp_all add: q1_def keys_except)
    from this(2) obtain t0 l where "t0 \<in> keys f1"
      and eq1: "of_nat_pm (s + t0) = of_nat_pm (lpp g) + l \<cdot> vect f1" by (auto simp: S1_def)
    from parallel have "is_proper_binomial f1" by (rule parallel_binomialsD)
    moreover note \<open>t0 \<in> keys f1\<close> that(2)
    ultimately obtain l' where eq2: "of_nat_pm t = of_nat_pm t0 + l' \<cdot> vect f1"
      by (rule proper_binomial_cases)
    show ?thesis
    proof (rule that(3))
      have "of_nat_pm (s + t) = of_nat_pm (s + t0) + l' \<cdot> vect f1" by (simp add: of_nat_pm_plus eq2)
      also have "\<dots> = of_nat_pm (lpp g) + (l + l') \<cdot> vect f1" by (simp add: eq1 map_scale_distrib_right)
      finally show "of_nat_pm (s + t) = of_nat_pm (lpp g) + (l + l') \<cdot> vect f1" .
    qed
  qed
  have 2: "P" if "s \<in> keys q2" and "t \<in> keys f2"
    and "\<And>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1 \<Longrightarrow> P" for s t P
  proof -
    from that(1) have "s \<in> keys q2'" and "s \<notin> S2" by (simp_all add: q2_def keys_except)
    from this(2) obtain t0 l where "t0 \<in> keys f2"
      and eq1: "of_nat_pm (s + t0) = of_nat_pm (lpp g) + l \<cdot> vect f1" by (auto simp: S2_def)
    from parallel have "is_proper_binomial f2" by (rule parallel_binomialsD)
    moreover note \<open>t0 \<in> keys f2\<close> that(2)
    ultimately obtain l' where eq2: "of_nat_pm t = of_nat_pm t0 + l' \<cdot> vect f2"
      by (rule proper_binomial_cases)
    show ?thesis
    proof (rule that(3))
      have "of_nat_pm (s + t) = of_nat_pm (s + t0) + l' \<cdot> vect f2" by (simp add: of_nat_pm_plus eq2)
      also have "\<dots> = of_nat_pm (lpp g) + (l + l' * m) \<cdot> vect f1"
        by (simp add: m eq1 map_scale_distrib_right map_scale_assoc)
      finally show "of_nat_pm (s + t) = of_nat_pm (lpp g) + (l + l' * m) \<cdot> vect f1" .
    qed
  qed
  show ?thesis
  proof
    show "g = q1 * f1 + q2 * f2"
    proof (rule poly_mapping_eqI)
      fix t
      show "lookup g t = lookup (q1 * f1 + q2 * f2) t"
      proof (cases "\<exists>l. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f1")
        case True
        then obtain l where l: "of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f1" ..
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
        hence "t \<noteq> lpp g" by (metis add.right_neutral map_scale_zero_left)
        with g_monomial have "t \<notin> keys g" by (auto dest: punit.keys_monomial simp only:)
        moreover have "t \<notin> keys (q1 * f1)"
        proof
          assume "t \<in> keys (q1 * f1)"
          then obtain t1 t2 where "t1 \<in> keys q1" and "t2 \<in> keys f1" and t: "t = t1 + t2"
            by (rule in_keys_timesE)
          from this(1, 2) obtain l where "of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f1"
            unfolding t by (rule 1)
          with False show False by blast
        qed
        moreover have "t \<notin> keys (q2 * f2)"
        proof
          assume "t \<in> keys (q2 * f2)"
          then obtain t1 t2 where "t1 \<in> keys q2" and "t2 \<in> keys f2" and t: "t = t1 + t2"
            by (rule in_keys_timesE)
          from this(1, 2) obtain l where "of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f1"
            unfolding t by (rule 2)
          with False show False by blast
        qed
        ultimately show ?thesis by (simp add: lookup_add in_keys_iff)
      qed
    qed
  next
    fix f s t
    assume "f \<in> {f1, f2}"
    hence disj: "f = f1 \<or> f = f2" by simp
    from parallel obtain m' where m': "vect f1 = m' \<cdot> vect f2" by (rule parallel_binomialsE_vect)
    assume "(s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2)"
    thus "\<exists>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f"
    proof
      assume "s \<in> keys q1 \<and> t \<in> keys f1"
      hence "s \<in> keys q1" and "t \<in> keys f1" by simp_all
      then obtain l where eq: "of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1" by (rule 1)
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
      then obtain l where eq: "of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1" by (rule 2)
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

context
  assumes tpp_adds_lpp: "tpp f1 adds lpp g"
  assumes mpa: "membership_problem_assms f1 f2 g"
begin

lemma thm_3_2_2_aux_3:
  obtains q1 q2 where "g = q1 * f1 + q2 * f2"
    and "\<And>f t. f \<in> {f1, f2} \<Longrightarrow> t \<in> keys (q1 * f1) \<union> keys (q2 * f2) \<Longrightarrow>
            \<exists>l>- 1. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f"
proof -
  have f1_in: "f1 \<in> {f1, f2}" and f2_in: "f2 \<in> {f1, f2}" by simp_all
  from parallel have f1_pbinomial: "is_proper_binomial f1" and f2_pbinomial: "is_proper_binomial f2"
    by (rule parallel_binomialsD)+
  from f1_pbinomial have "vect f1 \<noteq> 0" by (auto simp: vect_alt dest: punit.lt_gr_tt_binomial)
  from f2_pbinomial have "vect f2 \<noteq> 0" by (auto simp: vect_alt dest: punit.lt_gr_tt_binomial)
  from g_monomial have "g \<noteq> 0" by (rule monomial_not_0)
  hence "lpp g \<in> keys g" by (rule punit.lt_in_keys)
  with mpa have nadds1: "\<not> lpp f1 adds lpp g" and nadds2: "\<not> lpp f2 adds lpp g"
    by (rule membership_problem_assms_lpp_f1_nadds, rule membership_problem_assms_lpp_f2_nadds)

  from mpa have "g \<in> ideal {f1, f2}" by (rule membership_problem_assmsD)
  then obtain q1 q2 where g: "g = q1 * f1 + q2 * f2"
    and 1: "\<And>f s t. f \<in> {f1, f2} \<Longrightarrow> (s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2) \<Longrightarrow>
                    \<exists>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f"
    by (rule thm_3_2_2_aux_2) blast

  have 2: P if "f \<in> {f1, f2}" and "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)"
            and "\<And>l. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f \<Longrightarrow> P" for f t P
    using that(2)
  proof
    assume "t \<in> keys (q1 * f1)"
    then obtain t1 t2 where "t1 \<in> keys q1" and "t2 \<in> keys f1" and t: "t = t1 + t2"
      by (rule in_keys_timesE)
    from this(1, 2) have "(t1 \<in> keys q1 \<and> t2 \<in> keys f1) \<or> (t1 \<in> keys q2 \<and> t2 \<in> keys f2)" by simp
    with that(1) have "\<exists>l. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f" unfolding t by (rule 1)
    then obtain l where "of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f" ..
    thus ?thesis by (rule that)
  next
    assume "t \<in> keys (q2 * f2)"
    then obtain t1 t2 where "t1 \<in> keys q2" and "t2 \<in> keys f2" and t: "t = t1 + t2"
      by (rule in_keys_timesE)
    from this(1, 2) have "(t1 \<in> keys q1 \<and> t2 \<in> keys f1) \<or> (t1 \<in> keys q2 \<and> t2 \<in> keys f2)" by simp
    with that(1) have "\<exists>l. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f" unfolding t by (rule 1)
    then obtain l where "of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f" ..
    thus ?thesis by (rule that)
  qed

  from mpa g have "q1 * f1 \<noteq> 0" and "q2 * f2 \<noteq> 0" and eq0: "lpp (q1 * f1) = lpp (q2 * f2)"
    by (rule membership_problem_assms_rep)+
  from this(1, 2) have "q1 \<noteq> 0" and "f1 \<noteq> 0" and "q2 \<noteq> 0" and "f2 \<noteq> 0" by simp_all

  from tpp_adds_lpp have "of_nat_pm (tpp f1) \<unlhd> (of_nat_pm (lpp g) :: _ \<Rightarrow>\<^sub>0 rat)"
    by (simp only: le_of_nat_pm adds_pm)
  hence "of_nat_pm (tpp f1) + 1 \<cdot> vect f1 \<unlhd> of_nat_pm (lpp g) + 1 \<cdot> vect f1"
    by (rule le_pm_mono_plus_right)
  hence lpp1: "of_nat_pm (lpp f1) \<unlhd> of_nat_pm (lpp g) + 1 \<cdot> vect f1" by (simp add: vect_alt)

  note \<open>lpp g \<in> keys g\<close>
  also have "keys g \<subseteq> keys (q1 * f1) \<union> keys (q2 * f2)" (is "_ \<subseteq> ?A")
    unfolding g by (rule Poly_Mapping.keys_add)
  finally have "lpp g \<preceq> lpp (q2 * f2)" by (auto dest: punit.lt_max_keys simp only: eq0)
  moreover have "of_nat_pm (lpp g) = of_nat_pm (lpp g) + 0 \<cdot> vect f2" by simp
  moreover obtain k2 where eq: "of_nat_pm (lpp (q2 * f2)) = of_nat_pm (lpp g) + k2 \<cdot> vect f2"
  proof (rule 2)
    show "f2 \<in> {f1, f2}" by simp
  next
    from \<open>q2 * f2 \<noteq> 0\<close> have "lpp (q2 * f2) \<in> keys (q2 * f2)" by (rule punit.lt_in_keys)
    thus "lpp (q2 * f2) \<in> keys (q1 * f1) \<union> keys (q2 * f2)" ..
  qed
  ultimately have "0 \<le> k2" using \<open>vect f2 \<noteq> 0\<close> by (rule ord_rat)
  from \<open>q2 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have lpp2: "of_nat_pm (lpp f2) \<unlhd> of_nat_pm (lpp g) + k2 \<cdot> vect f2"
    by (simp add: le_of_nat_pm lp_times flip: eq adds_pm)

  from g show ?thesis
  proof
    fix f t
    assume "f \<in> {f1, f2}"
    hence disj: "f = f1 \<or> f = f2" by simp
    assume "t \<in> ?A"
    with f1_in obtain m1 where eq1: "of_nat_pm t = of_nat_pm (lpp g) + m1 \<cdot> vect f1" by (rule 2)
    from f2_in \<open>t \<in> ?A\<close> obtain m2 where eq2: "of_nat_pm t = of_nat_pm (lpp g) + m2 \<cdot> vect f2"
      by (rule 2)
    from mpa g show "\<exists>l>- 1. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f"
    proof (rule membership_problem_assms_rep)
      assume eq: "tpp (q1 * f1) = tpp (q2 * f2)"
      with \<open>t \<in> ?A\<close> have "tpp (q2 * f2) \<preceq> t" by (auto dest: punit.tt_min_keys simp only:)
      from disj show ?thesis
      proof
        assume f: "f = f1"
        from \<open>q1 * f1 \<noteq> 0\<close> have "tpp (q1 * f1) \<in> keys (q1 * f1)" by (rule punit.tt_in_keys)
        hence "tpp (q1 * f1) \<in> keys (q1 * f1) \<union> keys (q2 * f2)" ..
        with _ obtain m where eq3: "of_nat_pm (tpp (q1 * f1)) = of_nat_pm (lpp g) + m \<cdot> vect f1"
          by (rule 2) blast
        have "- 1 < m"
        proof (rule ccontr)
          assume "\<not> - 1 < m"
          hence "m + 1 \<le> 0" by simp
          have "of_nat_pm (tpp (q1 * f1)) + vect f1 = of_nat_pm (lpp g) + (m + 1) \<cdot> vect f1"
            by (simp add: eq3 map_scale_distrib_right)
          with \<open>q1 \<noteq> 0\<close> \<open>f1 \<noteq> 0\<close> have "of_nat_pm (tpp q1 + lpp f1) = of_nat_pm (lpp g) + (m + 1) \<cdot> vect f1"
            by (simp add: vect_alt tp_times of_nat_pm_plus)
          moreover have "of_nat_pm (lpp f1) \<unlhd> (of_nat_pm (tpp q1 + lpp f1) :: _ \<Rightarrow>\<^sub>0 rat)"
            by (simp add: le_of_nat_pm flip: adds_pm)
          ultimately have "of_nat_pm (lpp f1) \<unlhd> of_nat_pm (lpp g) + (m + 1) \<cdot> vect f1" by (simp only:)
          hence "of_nat_pm (lpp f1) \<unlhd> of_nat_pm (lpp g) + 0 \<cdot> vect f1" using lpp1 \<open>m + 1 \<le> 0\<close>
            by (rule map_scale_le_interval) simp
          hence "lpp f1 adds lpp g" by (simp add: adds_pm le_of_nat_pm)
          with nadds1 show False ..
        qed
        also from \<open>tpp (q2 * f2) \<preceq> t\<close> eq3 eq1 \<open>vect f1 \<noteq> 0\<close> have "m \<le> m1" unfolding eq by (rule ord_rat)
        finally show ?thesis using eq1 unfolding f by (intro exI conjI)
      next
        assume f: "f = f2"
        from \<open>q2 * f2 \<noteq> 0\<close> have "tpp (q2 * f2) \<in> keys (q2 * f2)" by (rule punit.tt_in_keys)
        hence "tpp (q2 * f2) \<in> keys (q1 * f1) \<union> keys (q2 * f2)" ..
        with f2_in obtain m where eq3: "of_nat_pm (tpp (q2 * f2)) = of_nat_pm (lpp g) + m \<cdot> vect f2"
          by (rule 2)
        have "- 1 < m"
        proof (rule ccontr)
          assume "\<not> - 1 < m"
          hence "m + 1 \<le> 0" by simp
          have "of_nat_pm (tpp (q2 * f2)) + vect f2 = of_nat_pm (lpp g) + (m + 1) \<cdot> vect f2"
            by (simp add: eq3 map_scale_distrib_right)
          with \<open>q2 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have "of_nat_pm (tpp q2 + lpp f2) = of_nat_pm (lpp g) + (m + 1) \<cdot> vect f2"
            by (simp add: vect_alt tp_times of_nat_pm_plus)
          moreover have "of_nat_pm (lpp f2) \<unlhd> (of_nat_pm (tpp q2 + lpp f2) :: _ \<Rightarrow>\<^sub>0 rat)"
            by (simp add: le_of_nat_pm flip: adds_pm)
          ultimately have "of_nat_pm (lpp f2) \<unlhd> of_nat_pm (lpp g) + (m + 1) \<cdot> vect f2" by (simp only:)
          hence "of_nat_pm (lpp f2) \<unlhd> of_nat_pm (lpp g) + 0 \<cdot> vect f2" using lpp2 \<open>m + 1 \<le> 0\<close> \<open>0 \<le> k2\<close>
            by (rule map_scale_le_interval)
          hence "lpp f2 adds lpp g" by (simp add: adds_pm le_of_nat_pm)
          with nadds2 show False ..
        qed
        also from \<open>tpp (q2 * f2) \<preceq> t\<close> eq3 eq2 \<open>vect f2 \<noteq> 0\<close> have "m \<le> m2" by (rule ord_rat)
        finally show ?thesis using eq2 unfolding f by (intro exI conjI)
      qed
    next
      from g_monomial have "lpp g = tpp g" by (rule punit.lt_eq_tt_monomial)
      moreover assume "tpp g \<preceq> tpp (q1 * f1)" and "tpp g \<preceq> tpp (q2 * f2)"
      ultimately have "lpp g \<preceq> tpp (q1 * f1)" and "lpp g \<preceq> tpp (q2 * f2)" by simp_all
      with \<open>t \<in> ?A\<close> have "lpp g \<preceq> t" by (auto dest: punit.tt_min_keys simp only:)
      from disj show ?thesis
      proof
        assume f: "f = f1"
        have "of_nat_pm (lpp g) = of_nat_pm (lpp g) + 0 \<cdot> vect f1" by simp
        with \<open>lpp g \<preceq> t\<close> have "0 \<le> m1" using eq1 \<open>vect f1 \<noteq> 0\<close> by (rule ord_rat)
        hence "- 1 < m1" by simp
        with eq1 show ?thesis unfolding f by (intro exI conjI)
      next
        assume f: "f = f2"
        have "of_nat_pm (lpp g) = of_nat_pm (lpp g) + 0 \<cdot> vect f2" by simp
        with \<open>lpp g \<preceq> t\<close> have "0 \<le> m2" using eq2 \<open>vect f2 \<noteq> 0\<close> by (rule ord_rat)
        hence "- 1 < m2" by simp
        with eq2 show ?thesis unfolding f by (intro exI conjI)
      qed
    qed
  qed
qed

text \<open>Theorem 3.2.2. in @{cite MWW} is wrong if the degree of the leading power-product of \<open>f1\<close> is
  less than the degree of its trailing power-product (see below). Therefore, we have to distinguish
  two cases and provide a different bound if @{prop "deg_pm (lpp f1) \<le> deg_pm (tpp f1)"}.

  Counterexample to Theorem 3.2.2., for lexicographic ordering with @{prop "x \<prec> y"}:
  \<^item> @{prop "f1 = x\<^sup>2 * y^3 + x^8"},
  \<^item> @{prop "f2 = y^3 + x^4 * y"},
  \<^item> @{prop "g = 2 * x^8 * y\<^sup>2"},
  \<^item> @{prop "q1 = y\<^sup>2 - x\<^sup>2 * y"},
  \<^item> @{prop "q2 = - y\<^sup>2 * x\<^sup>2 + x^4 * y + x^6"}.
  Here, the degree bound according to Theorem 3.2.2. is \<open>10\<close>, but @{prop "poly_deg (q1 * f1) = 11"}
  (due to @{term "x^10 * y"} appearing in this polynomial).
  One can prove that the syzygy module of @{term "{f1, f2}"} is generated by the single element
  @{term "(f2, - f1)"}, meaning that @{term "x^10 * y"} appears in \<^emph>\<open>every\<close> representation of \<open>g\<close>,
  and therefore that every representation of \<open>g\<close> has at least degree \<open>11\<close>.\<close>

theorem thm_3_2_2_1:
  assumes "deg_pm (lpp f1) \<le> deg_pm (tpp f1)"
  shows "membership_problem_concl f1 f2 g
          (deg_pm (lpp g) + min (deg_pm (tpp f1) - deg_pm (lpp f1)) (deg_pm (tpp f2) - deg_pm (lpp f2)))"
proof -
  from assms have eq1: "deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f1) =
                          rat (deg_pm (lpp g) + (deg_pm (tpp f1) - deg_pm (lpp f1)))"
    by (simp add: vect_alt deg_pm_minus_group deg_of_nat_pm)
  from parallel obtain m where "0 < m" and "vect f1 = m \<cdot> vect f2" by (rule parallel_binomialsE_vect)
  moreover from assms have "deg_pm (vect f1) \<le> 0" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)
  ultimately have "deg_pm (vect f2) \<le> 0" by (simp add: deg_pm_map_scale mult_le_0_iff)
  hence "deg_pm (lpp f2) \<le> deg_pm (tpp f2)" by (simp add: vect_alt deg_pm_minus_group deg_of_nat_pm)
  hence eq2: "deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f2) =
                          rat (deg_pm (lpp g) + (deg_pm (tpp f2) - deg_pm (lpp f2)))"
    by (simp add: vect_alt deg_pm_minus_group deg_of_nat_pm)
  let ?a = "deg_pm (tpp f1) - deg_pm (lpp f1)"
  let ?b = "deg_pm (tpp f2) - deg_pm (lpp f2)"
  obtain q1 q2 where "g = q1 * f1 + q2 * f2"
    and 1: "\<And>f t. f \<in> {f1, f2} \<Longrightarrow> t \<in> keys (q1 * f1) \<union> keys (q2 * f2) \<Longrightarrow>
                \<exists>l>- 1. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f" by (rule thm_3_2_2_aux_3) blast
  have 2: "deg_pm t \<le> deg_pm (lpp g) + min ?a ?b" if "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)" for t
  proof -
    have "rat (deg_pm t) = deg_pm (of_nat_pm t)" by (simp only: deg_of_nat_pm)
    also have "\<dots> \<le> min (deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f1))
                         (deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f2))"
    proof (rule min.boundedI)
      from _ that have "\<exists>l>- 1. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f1" by (rule 1) simp
      then obtain l where "- 1 < l" and "of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f1" by blast
      from this(2) have "deg_pm (of_nat_pm t) = deg_pm (of_nat_pm (lpp g)) + l * deg_pm (vect f1)"
        by (simp add: deg_pm_plus deg_pm_map_scale)
      also from \<open>- 1 < l\<close> \<open>deg_pm (vect f1) \<le> 0\<close> have "\<dots> \<le> deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f1)"
        by simp (metis less_eq_rat_def mult_minus1 mult_right_mono_neg)
      finally show "deg_pm (of_nat_pm t) \<le> deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f1)" .
    next
      from _ that have "\<exists>l>- 1. of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f2" by (rule 1) simp
      then obtain l where "- 1 < l" and "of_nat_pm t = of_nat_pm (lpp g) + l \<cdot> vect f2" by blast
      from this(2) have "deg_pm (of_nat_pm t) = deg_pm (of_nat_pm (lpp g)) + l * deg_pm (vect f2)"
        by (simp add: deg_pm_plus deg_pm_map_scale)
      also from \<open>- 1 < l\<close> \<open>deg_pm (vect f2) \<le> 0\<close> have "\<dots> \<le> deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f2)"
        by simp (metis less_eq_rat_def mult_minus1 mult_right_mono_neg)
      finally show "deg_pm (of_nat_pm t) \<le> deg_pm (of_nat_pm (lpp g)) - deg_pm (vect f2)" .
    qed
    also have "\<dots> = rat (deg_pm (lpp g) + min ?a ?b)" by (simp add: eq1 eq2)
    finally show "deg_pm t \<le> deg_pm (lpp g) + min ?a ?b" by (simp only: of_nat_le_iff)
  qed
  show ?thesis unfolding membership_problem_concl_def
  proof (intro exI conjI poly_deg_leI)
    fix t
    assume "t \<in> keys (q1 * f1)"
    hence "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)" ..
    thus "deg_pm t \<le> deg_pm (lpp g) + min ?a ?b" by (rule 2)
  next
    fix t
    assume "t \<in> keys (q2 * f2)"
    hence "t \<in> keys (q1 * f1) \<union> keys (q2 * f2)" ..
    thus "deg_pm t \<le> deg_pm (lpp g) + min ?a ?b" by (rule 2)
  qed fact
qed

theorem thm_3_2_2_2:
  assumes "deg_pm (tpp f1) < deg_pm (lpp f1)"
  shows "membership_problem_concl f1 f2 g
                (deg_pm (lpp g) + to_nat (deg_pm ((rat (step (lpp g)) + 1) \<cdot> vect f1 + vect f2) - 1))"
proof -
  define k where "k = step (lpp g)"
  let ?d = "deg_pm (of_nat_pm (lpp g) + (rat (step (lpp g)) + 1) \<cdot> vect f1 + vect f2) - 1"

  from assms have "0 < deg_pm (vect f1)" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)
  moreover obtain m::rat where "0 < m" and "vect f2 = m \<cdot> vect f1"
    using parallel_binomials_sym[OF parallel] by (rule parallel_binomialsE_vect)
  ultimately have "0 < deg_pm (vect f2)" by (simp add: deg_pm_map_scale)
  hence 0: "deg_pm (tpp f2) < deg_pm (lpp f2)" by (simp add: vect_alt deg_pm_minus deg_of_nat_pm)

  from g_monomial have lpp_g: "lpp g = tpp g" by (rule punit.lt_eq_tt_monomial)
  from mpa have "g \<in> ideal {f1, f2}" by (rule membership_problem_assmsD)
  then obtain q1' q2' where "g = q1' * f1 + q2' * f2"
    and "\<And>s t. (s \<in> keys q1' \<and> t \<in> keys f1) \<or> (s \<in> keys q2' \<and> t \<in> keys f2) \<Longrightarrow>
              \<exists>l::rat. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1"
    by (rule thm_3_2_2_aux_2) blast
  with mpa refl \<open>vect f2 = m \<cdot> vect f1\<close> \<open>0 < m\<close> tpp_adds_lpp obtain q1 q2 l'
    where g: "g = q1 * f1 + q2 * f2" and "0 < l'" and "l' < rat k + 1 + m"
      and eq: "of_nat_pm (lpp (q1 * f1)) = of_nat_pm (lpp g) + l' \<cdot> vect f1"
      and "\<And>s t. s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2 \<Longrightarrow>
            \<exists>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1"
    unfolding lpp_g k_def by (rule thm_3_2_2_aux_1) blast+
  from this(5) have 1: thesis if "s \<in> keys q1 \<and> t \<in> keys f1 \<or> s \<in> keys q2 \<and> t \<in> keys f2"
    and "\<And>l. of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1 \<Longrightarrow> thesis" for s t thesis
    using that by auto

  from mpa g have "q1 * f1 \<noteq> 0" and "q2 * f2 \<noteq> 0" and lpp_eq: "lpp (q1 * f1) = lpp (q2 * f2)"
    and lc_eq: "lcf (q1 * f1) = - lcf (q2 * f2)"
    by (rule membership_problem_assms_rep)+
  from this(1, 2) have "q1 \<noteq> 0" and "f1 \<noteq> 0" and "q2 \<noteq> 0" and "f2 \<noteq> 0" by auto
  from this(1, 2) have lpp_q1_f1: "lpp (q1 * f1) = lpp q1 + lpp f1" by (rule lp_times)
  from \<open>q2 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have lpp_q2_f2: "lpp (q2 * f2) = lpp q2 + lpp f2" by (rule lp_times)
  have lpp_eq2: "lpp q1 + lpp f1 = lpp q2 + lpp f2" by (simp only: lpp_eq lpp_q2_f2 flip: lpp_q1_f1)
  from \<open>q1 \<noteq> 0\<close> have "lpp q1 \<in> keys q1" by (rule punit.lt_in_keys)
  from \<open>f1 \<noteq> 0\<close> have "lpp f1 \<in> keys f1" by (rule punit.lt_in_keys)
  have 3: "deg_pm (s + t) < deg_pm (lpp q1 + lpp f1)"
    if "(s \<in> keys q1 \<and> t \<in> keys f1) \<or> (s \<in> keys q2 \<and> t \<in> keys f2)" and "s + t \<noteq> lpp q1 + lpp f1" for s t
  proof -
    from that(1) have "s + t \<prec> lpp (q1 * f1)"
    proof
      assume "s \<in> keys q1 \<and> t \<in> keys f1"
      hence "s \<preceq> lpp q1" and "t \<preceq> lpp f1" by (simp_all add: punit.lt_max_keys)
      from this(1) have "s + t \<preceq> lpp q1 + t" by (rule plus_monotone)
      also from \<open>t \<preceq> lpp f1\<close> have "\<dots> \<preceq> lpp q1 + lpp f1" by (rule plus_monotone_left)
      finally have "s + t \<preceq> lpp q1 + lpp f1" .
      with that(2) show ?thesis by (simp add: lpp_q1_f1)
    next
      assume "s \<in> keys q2 \<and> t \<in> keys f2"
      hence "s \<preceq> lpp q2" and "t \<preceq> lpp f2" by (simp_all add: punit.lt_max_keys)
      from this(1) have "s + t \<preceq> lpp q2 + t" by (rule plus_monotone)
      also from \<open>t \<preceq> lpp f2\<close> have "\<dots> \<preceq> lpp q2 + lpp f2" by (rule plus_monotone_left)
      finally have "s + t \<preceq> lpp q2 + lpp f2" .
      with that(2) show ?thesis by (simp only: lpp_eq2 lpp_q1_f1)
    qed
    moreover from that(1) obtain l where eq1: "of_nat_pm (s + t) = of_nat_pm (lpp g) + l \<cdot> vect f1"
      by (rule 1)
    ultimately have "l < l'" using eq by (rule ord_rat_strict)
    have "rat (deg_pm (s + t)) = deg_pm (of_nat_pm (s + t))" by (simp only: deg_of_nat_pm)
    also have "\<dots> = deg_pm (of_nat_pm (lpp g)) + l * deg_pm (vect f1)"
      by (simp add: eq1 deg_pm_plus deg_pm_map_scale)
    also have "\<dots> < deg_pm (of_nat_pm (lpp g)) + l' * deg_pm (vect f1)"
      using \<open>0 < deg_pm (vect f1)\<close> \<open>l < l'\<close> by simp
    also have "\<dots> = deg_pm (of_nat_pm (lpp (q1 * f1)))" by (simp add: eq deg_pm_plus deg_pm_map_scale)
    also have "\<dots> = rat (deg_pm (lpp q1 + lpp f1))" by (simp only: deg_of_nat_pm lpp_q1_f1)
    finally show ?thesis by simp
  qed
  have 4: "deg_pm t < deg_pm (lpp q1)" if "t \<in> keys q1" and "t \<noteq> lpp q1" for t
  proof -
    from \<open>f1 \<noteq> 0\<close> have "lpp f1 \<in> keys f1" by (rule punit.lt_in_keys)
    with that(1) have "(t \<in> keys q1 \<and> lpp f1 \<in> keys f1) \<or> (t \<in> keys q2 \<and> lpp f1 \<in> keys f2)" by simp
    moreover from that(2) have "t + lpp f1 \<noteq> lpp q1 + lpp f1" by simp
    ultimately have "deg_pm (t + lpp f1) < deg_pm (lpp q1 + lpp f1)" by (rule 3)
    thus "deg_pm t < deg_pm (lpp q1)" by (simp only: deg_pm_plus)
  qed
  have 5: "poly_deg (q1 * f1) = deg_pm (lpp (q1 * f1))"
  proof (intro antisym poly_deg_leI poly_deg_max_keys punit.lt_in_keys)
    fix t
    assume "t \<in> keys (q1 * f1)"
    show "deg_pm t \<le> deg_pm (lpp (q1 * f1))"
    proof (cases "t = lpp q1 + lpp f1")
      case True
      thus ?thesis by (simp add: lpp_q1_f1)
    next
      case False
      from \<open>t \<in> keys (q1 * f1)\<close> obtain t1 t2 where "t1 \<in> keys q1" and "t2 \<in> keys f1" and t: "t = t1 + t2"
        by (rule in_keys_timesE)
      from this(1, 2) have "(t1 \<in> keys q1 \<and> t2 \<in> keys f1) \<or> (t1 \<in> keys q2 \<and> t2 \<in> keys f2)" by simp
      hence "deg_pm t < deg_pm (lpp q1 + lpp f1)" using False unfolding t by (rule 3)
      thus ?thesis by (simp add: lpp_q1_f1)
    qed
  qed fact
  also have "\<dots> = deg_pm (lpp (q2 * f2))" by (simp only: lpp_eq)
  also have "\<dots> = poly_deg (q2 * f2)"
  proof (rule sym, intro antisym poly_deg_leI poly_deg_max_keys punit.lt_in_keys)
    fix t
    assume "t \<in> keys (q2 * f2)"
    show "deg_pm t \<le> deg_pm (lpp (q2 * f2))"
    proof (cases "t = lpp q1 + lpp f1")
      case True
      thus ?thesis by (simp add: lpp_q2_f2 lpp_eq2)
    next
      case False
      from \<open>t \<in> keys (q2 * f2)\<close> obtain t1 t2 where "t1 \<in> keys q2" and "t2 \<in> keys f2" and t: "t = t1 + t2"
        by (rule in_keys_timesE)
      from this(1, 2) have "(t1 \<in> keys q1 \<and> t2 \<in> keys f1) \<or> (t1 \<in> keys q2 \<and> t2 \<in> keys f2)" by simp
      hence "deg_pm t < deg_pm (lpp q1 + lpp f1)" using False unfolding t by (rule 3)
      thus ?thesis by (simp add: lpp_q2_f2 lpp_eq2)
    qed
  qed fact
  finally have deg_q1_f1: "poly_deg (q1 * f1) = poly_deg (q2 * f2)" .
  show ?thesis unfolding membership_problem_concl_def
  proof (intro exI conjI)
    have "rat (poly_deg (q1 * f1)) \<le> ?d"
    proof (rule ccontr)
      assume "\<not> rat (poly_deg (q1 * f1)) \<le> ?d"
      hence "?d < rat (poly_deg (q1 * f1))" by simp
      moreover have "?d \<in> \<int>"
        by (intro Ints_diff Ints_1 Ints_deg plus_is_int_pm vect_is_int_pm map_scale_is_int_pm Ints_add)
           (intro nat_pm_is_int_pm of_nat_pm_is_nat_pm Ints_of_nat)+
      moreover have "rat (poly_deg (q1 * f1)) \<in> \<int>" by (fact Ints_of_nat)
      ultimately have "?d + 1 \<le> deg_pm (of_nat_pm (lpp (q1 * f1)))"
        by (simp add: is_int_less_iff 5 deg_of_nat_pm lpp_q1_f1)
      also have "\<dots> = deg_pm (of_nat_pm (lpp g) + l' \<cdot> vect f1)" by (simp only: eq)
      finally have "(rat k + m + 1) * deg_pm (vect f1) \<le> l' * deg_pm (vect f1)"
        by (simp add: \<open>vect f2 = m \<cdot> vect f1\<close> k_def algebra_simps deg_pm_plus deg_pm_map_scale)
      with \<open>0 < deg_pm (vect f1)\<close> have "rat k + 1 + m \<le> l'" by simp
      also have "\<dots> < rat k + 1 + m" by fact
      finally show False ..
    qed
    hence "rat (poly_deg (q1 * f1)) \<le> rat (deg_pm (lpp g)) +
                                        (deg_pm ((rat (step (lpp g)) + 1) \<cdot> vect f1 + vect f2) - 1)"
      (is "_ \<le> _ + ?a") by (simp only: deg_pm_plus deg_of_nat_pm)
    hence "to_nat (rat (poly_deg (q1 * f1))) \<le> to_nat (rat (deg_pm (lpp g)) + ?a)" by (rule to_nat_mono)
    also from Ints_of_nat have "\<dots> \<le> to_nat (rat (deg_pm (lpp g))) + to_nat ?a"
      by (rule to_nat_plus_le) (intro Ints_diff Ints_1 Ints_deg plus_is_int_pm map_scale_is_int_pm
                                      Ints_add Ints_of_nat vect_is_int_pm)
    finally show "poly_deg (q1 * f1) \<le> deg_pm (lpp g) + to_nat ?a" by (simp only: to_nat_of_nat)
    thus "poly_deg (q2 * f2) \<le> deg_pm (lpp g) + to_nat ?a" by (simp only: deg_q1_f1)
  qed fact
qed

end

end

end

end (* two_polys *)

subsection \<open>Degree Bounds on the Shifts for Generating a Proper Binomial\<close>

context two_binoms
begin

theorem thm_3_3_35:
  assumes "membership_problem_assms f1 f2 g" and "is_proper_binomial g"
  shows "membership_problem_concl f1 f2 g (Max {deg_pm (lpp g), deg_pm (tpp g),
            max (deg_pm (overlapshift (lpp g))) (deg_pm (overlapshift (tpp g))) +
              to_nat (\<bar>deg_pm (vect f1)\<bar> + \<bar>deg_pm (vect f2)\<bar>)})"
proof -
  from assms(1) have "g \<in> ideal {f1, f2}" and disjnt: "monomial 1 ` keys g \<inter> ideal {f1, f2} = {}"
    by (rule membership_problem_assmsD)+ fact
  from assms(2) have keys_g: "keys g = {lpp g, tpp g}" by (rule punit.keys_proper_binomial)
  hence "lpp g \<in> keys g" by simp
  hence "monomial 1 (lpp g) \<in> monomial 1 ` keys g" by (rule imageI)
  with disjnt have *: "monomial 1 (lpp g) \<notin> ideal {f1, f2}" by blast
  obtain zs where "is_vpc zs" and "fst (hd zs) = of_nat_pm (lpp g)"
    and "snd (last zs) = of_nat_pm (tpp g)" using \<open>g \<in> ideal {f1, f2}\<close> assms(2) *
    by (rule idealE_vpc)
  moreover from assms(2) have "lpp g \<noteq> tpp g" by (auto dest: punit.lt_gr_tt_binomial)
  ultimately obtain zs' where "is_vpc zs'" and hd': "fst (hd zs') = of_nat_pm (lpp g)"
    and last': "snd (last zs') = of_nat_pm (tpp g)"
    and deg': "deg_vpc zs' \<le> rat (Max {deg_pm (lpp g), deg_pm (tpp g),
                                     max (deg_pm (overlapshift (lpp g))) (deg_pm (overlapshift (tpp g))) +
                                     to_nat (\<bar>deg_pm (vect f1)\<bar> + \<bar>deg_pm (vect f2)\<bar>)})"
                (is "_ \<le> rat ?m")
  proof (rule thm_3_3_34)
    fix f
    assume "f \<in> {f1, f2}"
    with f1_pbinomial f2_pbinomial have "f \<noteq> 0" by (auto dest: proper_binomial_not_0)
    from assms(1) have irred: "\<not> punit.is_red {f1, f2} g" by (rule membership_problem_assmsD)
    have rl: "\<not> lpp f adds t" if "t \<in> keys g" for t
    proof
      assume "lpp f adds t"
      with \<open>f \<in> {f1, f2}\<close> \<open>f \<noteq> 0\<close> that have "punit.is_red {f1, f2} g"
        by (rule punit.is_red_addsI[simplified])
      with irred show False ..
    qed
    show "\<not> lpp f adds lpp g" and "\<not> lpp f adds tpp g" by (rule rl, simp add: keys_g)+
  qed
  note this(1)
  moreover from \<open>lpp g \<noteq> tpp g\<close> have "fst (hd zs') \<noteq> snd (last zs')" by (simp add: hd' last')
  ultimately obtain q1 q2 where "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {fst (hd zs'), snd (last zs')}"
    and "rat (poly_deg (q1 * f1)) \<le> deg_vpc zs'" and "rat (poly_deg (q2 * f2)) \<le> deg_vpc zs'"
    by (rule vpcE_ideal)
  note this(1)
  also have "{fst (hd zs'), snd (last zs')} = of_nat_pm ` {lpp g, tpp g}" by (simp add: hd' last')
  finally have keys_g': "keys (q1 * f1 + q2 * f2) = {lpp g, tpp g}" (is "keys ?g = _")
    by (simp only: inj_image_eq_iff inj_of_nat_pm)
  define c where "c = tcf g / lookup ?g (tpp g)"
  show ?thesis unfolding membership_problem_concl_def
  proof (intro exI conjI)
    from assms(2) have "g \<noteq> 0" by (rule proper_binomial_not_0)
    hence "tcf g \<noteq> 0" by (rule punit.tc_not_0)
    moreover have **: "lookup ?g (tpp g) \<noteq> 0" by (simp add: keys_g' flip: in_keys_iff)
    ultimately have "c \<noteq> 0" by (simp add: c_def)
    have "?g \<in> ideal {f1, f2}" by (fact idealI_2)
    hence "c \<cdot> ?g \<in> ideal {f1, f2}" unfolding map_scale_eq_times by (rule ideal.span_scale)
    with \<open>g \<in> ideal {f1, f2}\<close> have "g - c \<cdot> ?g \<in> ideal {f1, f2}" by (rule ideal.span_diff)
    have "keys (g - c \<cdot> ?g) \<subseteq> keys g \<union> keys (c \<cdot> ?g)" by (rule keys_minus)
    also from \<open>c \<noteq> 0\<close> have "\<dots> = {lpp g, tpp g}" by (simp add: keys_map_scale keys_g' keys_g)
    finally have "keys (g - c \<cdot> ?g) \<subseteq> {lpp g, tpp g}" .
    moreover from ** have "tpp g \<notin> keys (g - c \<cdot> ?g)"
      by (simp add: lookup_minus c_def in_keys_iff flip: punit.tc_def)
    moreover have "keys (g - c \<cdot> ?g) \<noteq> {lpp g}"
    proof
      assume a: "keys (g - c \<cdot> ?g) = {lpp g}"
      moreover define d where "d = lookup (g - c \<cdot> ?g) (lpp g)"
      ultimately have "d \<noteq> 0" by (simp flip: in_keys_iff)
      have "monomial d (lpp g) = g - c \<cdot> ?g"
        by (rule poly_mapping_keys_eqI) (simp_all add: \<open>d \<noteq> 0\<close> a, simp only: d_def)
      also have "\<dots> \<in> ideal {f1, f2}" by fact
      finally have "inverse d \<cdot> monomial d (lpp g) \<in> ideal {f1, f2}"
        unfolding map_scale_eq_times by (rule ideal.span_scale)
      with \<open>d \<noteq> 0\<close> have "monomial 1 (lpp g) \<in> ideal {f1, f2}" by simp
      with * show False ..
    qed
    ultimately have "keys (g - c \<cdot> ?g) = {}" by blast
    hence "g = c \<cdot> ?g" by simp
    also have "\<dots> = c \<cdot> q1 * f1 + c \<cdot> q2 * f2" by (simp only: map_scale_eq_times algebra_simps)
    finally show "g = c \<cdot> q1 * f1 + c \<cdot> q2 * f2" .
  next
    have "poly_deg (c \<cdot> q1 * f1) = poly_deg (c \<cdot> (q1 * f1))"
      by (simp only: map_scale_eq_times mult.assoc)
    also have "\<dots> \<le> poly_deg (q1 * f1)" by (simp add: poly_deg_map_scale)
    also have "rat \<dots> \<le> deg_vpc zs'" by fact
    also have "\<dots> \<le> rat ?m" by fact
    finally show "poly_deg (c \<cdot> q1 * f1) \<le> ?m" by (simp only: of_nat_le_iff)
  next
    have "poly_deg (c \<cdot> q2 * f2) = poly_deg (c \<cdot> (q2 * f2))"
      by (simp only: map_scale_eq_times mult.assoc)
    also have "\<dots> \<le> poly_deg (q2 * f2)" by (simp add: poly_deg_map_scale)
    also have "rat \<dots> \<le> deg_vpc zs'" by fact
    also have "\<dots> \<le> rat ?m" by fact
    finally show "poly_deg (c \<cdot> q2 * f2) \<le> ?m" by (simp only: of_nat_le_iff)
  qed
qed

end (* two_polys *)

end (* theory *)
