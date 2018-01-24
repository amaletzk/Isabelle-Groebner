section \<open>New Bounds for the Membership Problem for Binomial Ideals\<close>

theory Membership_Bound_Binomials
imports Binomials Binom_Mult
begin

subsection \<open>Structure of Binomial Ideals\<close>
  
context gd_powerprod
begin

lemma rem_3_1_4_aux_1:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and "g' \<in> reduced_GB F" and "t \<in> keys g"
    and "lp g' adds t"
  shows "g' = g"
proof (rule ccontr)
  let ?G = "reduced_GB F"
  assume "g' \<noteq> g"
  with \<open>g' \<in> ?G\<close> have "g' \<in> (remove g ?G)" by (rule in_removeI)
  have "\<not> is_red (remove g ?G) g" by (rule is_auto_reducedD, rule reduced_GB_is_auto_reduced_finite, fact+)
  moreover have "is_red (remove g ?G) g"
  proof (rule is_red_singletonD, rule is_red_addsI, rule)
    from reduced_GB_nonzero_finite[OF fin] \<open>g' \<in> ?G\<close> show "g' \<noteq> 0" by auto
  qed fact+
  ultimately show False ..
qed

lemma rem_3_1_4_aux_2:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and "g' \<in> reduced_GB F" and "t \<in> keys g"
    and "lp g' adds t"
  shows "t = lp g"
proof -
  from assms have "g' = g" by (rule rem_3_1_4_aux_1)
  from \<open>lp g' adds t\<close> have "lp g \<preceq> t" unfolding \<open>g' = g\<close> by (rule ord_adds)
  with lp_max_keys[OF \<open>t \<in> keys g\<close>] show ?thesis by simp
qed
  
text \<open>The following two lemmas are contained in Remark 3.1.4. of @{cite WW2015}.\<close>
  
lemma rem_3_1_4_1:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and lp_notin: "lp g \<notin> lp_set F"
  shows "\<not> is_red F g"
proof
  let ?G = "reduced_GB F"
  assume "is_red F g"
  then obtain f t where "f \<in> F" and "t \<in> keys g" and "f \<noteq> 0" and lpf: "lp f adds t" by (rule is_red_addsE)
  have "f \<in> pideal ?G" unfolding reduced_GB_pideal_finite[OF fin]
    by (rule, fact \<open>f \<in> F\<close>, rule generator_subset_pideal)
  from reduced_GB_is_GB_finite[OF fin] this \<open>f \<noteq> 0\<close> obtain g'
    where "g' \<in> ?G" and "g' \<noteq> 0" and lpg': "lp g' adds lp f" by (rule GB_adds_lp)
  from lpg' lpf have lpg'': "lp g' adds t" by (rule adds_trans)
  from _ \<open>g' \<noteq> 0\<close> \<open>t \<in> keys g\<close> this have red: "is_red {g'} g" by (rule is_red_addsI, simp)
  from fin \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> \<open>t \<in> keys g\<close> lpg'' have "g' = g" and "t = lp g"
    by (rule rem_3_1_4_aux_1, rule rem_3_1_4_aux_2)
  from lpg' lpf have "lp g = lp f" unfolding \<open>t = lp g\<close> \<open>g' = g\<close> by (rule adds_antisym)
  from \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> have "lp g \<in> lp_set F" unfolding \<open>lp g = lp f\<close> by (rule lp_setI)
  with lp_notin show False ..
qed

lemma rem_3_1_4_2:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and bin: "is_proper_binomial g"
  shows "monomial 1 ` (keys g) \<inter> pideal F = {}"
  unfolding disjoint_eq_subset_Compl
proof (rule, rule)
  let ?G = "reduced_GB F"
  fix x
  assume xin1: "x \<in> monomial 1 ` (keys g)" and xin2: "x \<in> pideal F"
  from bin obtain c d s t where obd: "is_obd c s d t" and g: "g = binomial c s d t"
    by (rule is_proper_binomial_binomial_od)
  from obd have pbd: "is_pbd c s d t" by (rule obd_imp_pbd)
  have keysg: "keys g = {s, t}" unfolding g by (rule keys_binomial_pbd, fact pbd)
  
  have a: "monomial 1 t \<notin> pideal F"
  proof
    assume "monomial 1 t \<in> pideal F" (is "?p \<in> pideal F")
    hence "?p \<in> pideal ?G" unfolding reduced_GB_pideal_finite[OF fin] .
    have "?p \<noteq> 0" by (simp add: monomial_0_iff)
    from reduced_GB_is_GB_finite[OF fin] \<open>?p \<in> pideal ?G\<close> this obtain g'
      where "g' \<in> ?G" and "g' \<noteq> 0" and lpg': "lp g' adds lp ?p" by (rule GB_adds_lp)
    from lpg' have lpg'': "lp g' adds t" by (simp add: lp_monomial)
    have "t \<in> keys g" unfolding keysg by simp
    from fin \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> this lpg'' have "t = lp g" by (rule rem_3_1_4_aux_2)
    also have "... = s" unfolding g lp_binomial[OF obd] ..
    finally show False using obd unfolding is_obd_def by simp
  qed

  from xin1 have "x = monomial 1 s \<or> x = monomial 1 t" unfolding keysg by simp
  thus False
  proof
    assume x: "x = monomial 1 s"
    from pbd have "d \<noteq> 0" by (rule is_pbdE2)
    have "g \<in> pideal F" unfolding reduced_GB_pideal_finite[OF fin, symmetric]
      by (rule, fact \<open>g \<in> ?G\<close>, rule generator_subset_pideal)
    from xin2 have "monomial 1 s \<in> pideal F" unfolding x .
    hence "monom_mult c 0 (monomial 1 s) \<in> pideal F" by (rule pideal_closed_monom_mult)
    hence "monomial c s \<in> pideal F" by (simp add: monom_mult_monomial)
    with \<open>g \<in> pideal F\<close> have "g - monomial c s \<in> pideal F" by (rule pideal_closed_minus)
    hence "monomial d t \<in> pideal F" unfolding g binomial_def by simp
    hence "monom_mult (1 / d) 0 (monomial d t) \<in> pideal F" by (rule pideal_closed_monom_mult)
    hence "monomial 1 t \<in> pideal F" using \<open>d \<noteq> 0\<close> by (simp add: monom_mult_monomial)
    with a show False ..
  next
    assume x: "x = monomial 1 t"
    from a xin2 show False unfolding x ..
  qed
qed

end (* gd_powerprod *)

subsection \<open>Preliminaries\<close>
  
text \<open>Since most result in this theory are concerned with ideals generated by two polynomials, we
  prove some specific properties of such ideals below.\<close>
  
lemma in_pideal_2I: "q1 * f1 + q2 * f2 \<in> pideal {f1, f2::('a::comm_powerprod, 'b::semiring_1) poly_mapping}"
by (rule pideal_closed_plus, rule pideal_closed_times, rule generator_in_pideal, simp,
      rule pideal_closed_times, rule generator_in_pideal, simp)

lemma in_pideal_2E:
  assumes "f \<in> pideal {f1, f2}"
  obtains q1 q2 where "f = q1 * f1 + q2 * f2"
  using assms
proof (induct f arbitrary: thesis rule: pideal_induct)
  case base: pideal_0
  show ?case
  proof (rule base)
    show "0 = 0 * f1 + 0 * f2" by simp
  qed
next
  case step: (pideal_plus f' g c t)
  obtain q1 q2 where f'_eq: "f' = q1 * f1 + q2 * f2" by (rule step(2))
  from step(3) have "g = f1 \<or> g = f2" by simp
  thus ?case
  proof
    assume "g = f1"
    show ?case
    proof (rule step(5))
      show "f' + monom_mult c t g = (q1 + monomial c t) * f1 + q2 * f2"
        by (simp add: f'_eq \<open>g = f1\<close> times_monomial_left algebra_simps)
    qed
  next
    assume "g = f2"
    show ?case
    proof (rule step(5))
      show "f' + monom_mult c t g = q1 * f1 + (q2 + monomial c t) * f2"
        by (simp add: f'_eq \<open>g = f2\<close> times_monomial_left algebra_simps)
    qed
  qed
qed

lemma in_pideal_2_iff:
  "f \<in> pideal {f1, f2} \<longleftrightarrow> (\<exists>q1 q2. f = q1 * f1 + q2 * (f2::('a::comm_powerprod, 'b::semiring_1) poly_mapping))"
proof
  assume "f \<in> pideal {f1, f2}"
  then obtain q1 q2 where "f = q1 * f1 + q2 * f2" by (rule in_pideal_2E)
  show "\<exists>q1 q2. f = q1 * f1 + q2 * f2" by (intro exI, fact)
next
  assume "\<exists>q1 q2. f = q1 * f1 + q2 * f2"
  then obtain q1 q2 where f_eq: "f = q1 * f1 + q2 * f2" by auto
  show "f \<in> pideal {f1, f2}" unfolding f_eq by (rule in_pideal_2I)
qed

context ordered_powerprod
begin

lemma rem_3_1_7_aux:
  assumes "g \<in> pideal F" and "t \<in> keys g"
  obtains f s where "f \<in> F" and "s \<in> keys f" and "s adds t"
  using assms
proof (induct g arbitrary: thesis rule: pideal_induct)
  case base: pideal_0
  from base(2) show ?case unfolding keys_zero ..
next
  case ind: (pideal_plus g f' c u)
  from ind(6) keys_add_subset have "t \<in> keys g \<union> keys (monom_mult c u f')" ..
  thus ?case
  proof
    assume "t \<in> keys g"
    obtain f s where "f \<in> F" and "s \<in> keys f" and "s adds t"
    proof (rule ind(2))
      show "t \<in> keys g" by fact
    qed
    thus ?thesis by (rule ind(5))
  next
    assume "t \<in> keys (monom_mult c u f')"
    then obtain s where "s \<in> keys f'" and "t = u + s" by (rule keys_monom_multE)
    from \<open>f' \<in> F\<close> \<open>s \<in> keys f'\<close> show ?thesis
    proof (rule ind(5))
      show "s adds t" by (simp add: \<open>t = u + s\<close>)
    qed
  qed
qed

lemma rem_3_1_7:
  assumes "is_binomial_set F" and gin: "g \<in> pideal F" and "\<not> is_red F g" and tin: "t \<in> keys g"
  obtains f where "f \<in> F" and "is_proper_binomial f" and "tp f adds t"
proof -
  from gin tin obtain f s where "f \<in> F" and "s \<in> keys f" and "s adds t" by (rule rem_3_1_7_aux)
  have "s \<noteq> lp f"
  proof
    assume "s = lp f"
    from \<open>f \<in> F\<close> have "is_red F g"
    proof (rule is_red_addsI)
      show "f \<noteq> 0"
      proof
        assume "f = 0"
        from \<open>s \<in> keys f\<close> show False unfolding \<open>f = 0\<close> keys_zero ..
      qed
    next
      from \<open>s adds t\<close> show "lp f adds t" unfolding \<open>s = lp f\<close> .
    qed fact
    with \<open>\<not> is_red F g\<close> show False ..
  qed
  from \<open>is_binomial_set F\<close> \<open>f \<in> F\<close> have "is_binomial f" by (rule is_binomial_setD)
  hence "is_monomial f \<or> is_proper_binomial f" unfolding is_binomial_alt .
  hence "is_proper_binomial f"
  proof
    assume "is_monomial f"
    hence "keys f = {lp f}" by (rule keys_monomial)
    with \<open>s \<in> keys f\<close> \<open>s \<noteq> lp f\<close> show ?thesis by simp
  qed
  with \<open>f \<in> F\<close> show ?thesis
  proof
    from \<open>is_binomial f\<close> have "keys f = {lp f, tp f}" by (rule keys_binomial)
    with \<open>s \<in> keys f\<close> \<open>s \<noteq> lp f\<close> have "s = tp f" by simp
    with \<open>s adds t\<close> show "tp f adds t" by simp
  qed
qed

end (* ordered_powerprod *)

definition is_nat_pm_pair :: "(('a \<Rightarrow>\<^sub>0 'b) * ('a \<Rightarrow>\<^sub>0 'b::floor_ceiling)) \<Rightarrow> bool" where
  "is_nat_pm_pair pp = (is_nat_pm (fst pp) \<and> is_nat_pm (snd pp))"

definition is_int_pm_pair :: "(('a \<Rightarrow>\<^sub>0 'b) * ('a \<Rightarrow>\<^sub>0 'b::floor_ceiling)) \<Rightarrow> bool" where
  "is_int_pm_pair pp = (is_int_pm (fst pp) \<and> is_int_pm (snd pp))"
  
lemma is_nat_pm_pairI:
  assumes "is_nat_pm (fst pp)" and "is_nat_pm (snd pp)"
  shows "is_nat_pm_pair pp"
  using assms unfolding is_nat_pm_pair_def ..
    
lemma is_nat_pm_pairD1:
  assumes "is_nat_pm_pair pp"
  shows "is_nat_pm (fst pp)"
  using assms unfolding is_nat_pm_pair_def ..

lemma is_nat_pm_pairD2:
  assumes "is_nat_pm_pair pp"
  shows "is_nat_pm (snd pp)"
  using assms unfolding is_nat_pm_pair_def ..

lemma is_int_pm_pairI:
  assumes "is_int_pm (fst pp)" and "is_int_pm (snd pp)"
  shows "is_int_pm_pair pp"
  using assms unfolding is_int_pm_pair_def ..
    
lemma is_int_pm_pairD1:
  assumes "is_int_pm_pair pp"
  shows "is_int_pm (fst pp)"
  using assms unfolding is_int_pm_pair_def ..

lemma is_int_pm_pairD2:
  assumes "is_int_pm_pair pp"
  shows "is_int_pm (snd pp)"
  using assms unfolding is_int_pm_pair_def ..
    
lemma nat_pm_pair_is_int_pm_pair:
  assumes "is_nat_pm_pair pp"
  shows "is_int_pm_pair pp"
proof (rule is_int_pm_pairI)
  from assms have "is_nat_pm (fst pp)" by (rule is_nat_pm_pairD1)
  thus "is_int_pm (fst pp)" by (rule nat_pm_is_int_pm)
next
  from assms have "is_nat_pm (snd pp)" by (rule is_nat_pm_pairD2)
  thus "is_int_pm (snd pp)" by (rule nat_pm_is_int_pm)
qed

type_synonym 'n point = "('n \<Rightarrow>\<^sub>0 real)"

definition overlap_p :: "(('n point) * ('n point)) \<Rightarrow> (('n point) * ('n point)) \<Rightarrow> 'n point"
  where "overlap_p p1 p2 = lcs (gcs (fst p1) (snd p1)) (gcs (fst p2) (snd p2))"
    
definition vect_p :: "(('n point) * ('n point)) \<Rightarrow> ('n point)"
  where "vect_p p = (fst p) - (snd p)"

lemma overlap_p_is_nat_pm:
  assumes "is_nat_pm_pair pp1" and "is_nat_pm_pair pp2"
  shows "is_nat_pm (overlap_p pp1 pp2)"
  unfolding overlap_p_def using assms
  by (simp add: is_nat_pm_pairD1 is_nat_pm_pairD2 gcs_is_nat_pm lcs_is_nat_pm)

lemma overlap_p_is_int_pm:
  assumes "is_int_pm_pair pp1" and "is_int_pm_pair pp2"
  shows "is_int_pm (overlap_p pp1 pp2)"
  unfolding overlap_p_def using assms
  by (simp add: is_int_pm_pairD1 is_int_pm_pairD2 gcs_is_int_pm lcs_is_int_pm)

lemma vect_p_is_int_pm:
  assumes "is_int_pm_pair pp"
  shows "is_int_pm (vect_p pp)"
  unfolding vect_p_def using assms 
  by (simp add: is_int_pm_pairD1 is_int_pm_pairD2 diff_is_int_pm)

lemma lem_3_1_13:
  assumes "snd p1 \<unlhd> p" and "snd p2 \<unlhd> p"
  shows "overlap_p p1 p2 \<unlhd> p"
  unfolding overlap_p_def lookup_lcs_fun le_pm_def
proof (rule lcs_leq_fun)
  have "lookup (gcs (fst p1) (snd p1)) \<le> lookup (snd p1)" unfolding lookup_gcs_fun by (fact gcs_leq_fun_2)
  also from assms(1) have "... \<le> lookup p" by (simp only: le_pm_def)
  finally show "lookup (gcs (fst p1) (snd p1)) \<le> lookup p" .
next
  have "lookup (gcs (fst p2) (snd p2)) \<le> lookup (snd p2)" unfolding lookup_gcs_fun by (fact gcs_leq_fun_2)
  also from assms(2) have "... \<le> lookup p" by (simp only: le_pm_def)
  finally show "lookup (gcs (fst p2) (snd p2)) \<le> lookup p" .
qed

context pm_powerprod
begin

definition membership_problem_assms ::
    "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> bool"
    where "membership_problem_assms f1 f2 g =
        (is_binomial f1 \<and> is_binomial f2 \<and> is_binomial g \<and> g \<in> pideal {f1, f2} \<and>
          \<not> is_red {f1, f2} g \<and> (is_proper_binomial g \<longrightarrow> \<not> (monomial 1 ` keys g) \<subseteq> pideal {f1, f2}))"

definition membership_problem_concl ::
    "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_1) \<Rightarrow> nat \<Rightarrow> bool"
  where "membership_problem_concl f1 f2 g d =
        (\<exists>q1 q2. g = q1 * f1 + q2 * f2 \<and>
          (q1 \<noteq> 0 \<longrightarrow> poly_deg (q1 * f1) \<le> d) \<and>
          (q2 \<noteq> 0 \<longrightarrow> poly_deg (q2 * f2) \<le> d))"

definition membership_problem :: "('b::field itself) \<Rightarrow> nat \<Rightarrow> bool"
  where "membership_problem _ d =
      (\<forall>f1 f2 g::('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b. membership_problem_assms f1 f2 g \<longrightarrow>
        membership_problem_concl f1 f2 g d)"

lemma membership_problem_assmsD1:
  assumes "membership_problem_assms f1 f2 g"
  shows "is_binomial f1"
  using assms unfolding membership_problem_assms_def by simp
    
lemma membership_problem_assmsD2:
  assumes "membership_problem_assms f1 f2 g"
  shows "is_binomial f2"
  using assms unfolding membership_problem_assms_def by simp
    
lemma membership_problem_assmsD3:
  assumes "membership_problem_assms f1 f2 g"
  shows "is_binomial g"
  using assms unfolding membership_problem_assms_def by simp

lemma membership_problem_assmsD4:
  assumes "membership_problem_assms f1 f2 g"
  shows "g \<in> pideal {f1, f2}"
  using assms unfolding membership_problem_assms_def by simp

lemma membership_problem_assmsD5:
  assumes "membership_problem_assms f1 f2 g"
  shows "\<not> is_red {f1, f2} g"
  using assms unfolding membership_problem_assms_def by simp

lemma membership_problem_assmsD6:
  assumes "membership_problem_assms f1 f2 g" and "is_proper_binomial g"
  shows "\<not> (monomial 1 ` keys g) \<subseteq> pideal {f1, f2}"
  using assms unfolding membership_problem_assms_def by simp

lemma membership_problemI:
  assumes "\<And>f1 f2 g::('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field. membership_problem_assms f1 f2 g \<Longrightarrow>
            membership_problem_concl f1 f2 g d"
  shows "membership_problem TYPE('b) d"
  unfolding membership_problem_def using assms by auto

lemma membership_problem_assms_lp_f1_nadds:
  assumes "membership_problem_assms f1 f2 g" and "t \<in> keys g"
  shows "\<not> lp f1 adds t"
proof
  assume "lp f1 adds t"
  from _ _ \<open>t \<in> keys g\<close> this have "is_red {f1, f2} g"
  proof (rule is_red_addsI, simp)
    from assms(1) have "is_binomial f1" by (rule membership_problem_assmsD1)
    thus "f1 \<noteq> 0" by (rule binomial_not_0)
  qed
  moreover from assms(1) have "\<not> is_red {f1, f2} g" by (rule membership_problem_assmsD5)
  ultimately show False by simp
qed

lemma membership_problem_assms_lp_f2_nadds:
  assumes "membership_problem_assms f1 f2 g" and "t \<in> keys g"
  shows "\<not> lp f2 adds t"
proof
  assume "lp f2 adds t"
  from _ _ \<open>t \<in> keys g\<close> this have "is_red {f1, f2} g"
  proof (rule is_red_addsI, simp)
    from assms(1) have "is_binomial f2" by (rule membership_problem_assmsD2)
    thus "f2 \<noteq> 0" by (rule binomial_not_0)
  qed
  moreover from assms(1) have "\<not> is_red {f1, f2} g" by (rule membership_problem_assmsD5)
  ultimately show False by simp
qed

definition poly_point :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('n point * 'n point)" where
  "poly_point q = (of_nat_pm (lp q), of_nat_pm (tp q))"

lemma fst_poly_point: "fst (poly_point q) = of_nat_pm (lp q)"
  by (simp add: poly_point_def)
    
lemma snd_poly_point: "snd (poly_point q) = of_nat_pm (tp q)"
  by (simp add: poly_point_def)

lemma poly_point_is_nat_pm_pair: "is_nat_pm_pair (poly_point q)"
  unfolding poly_point_def by (rule is_nat_pm_pairI, simp_all, (rule of_nat_pm_is_nat_pm)+)
    
definition overlap :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat)"
  where "overlap q1 q2 = to_nat_pm (overlap_p (poly_point q1) (poly_point q2))"

definition vect :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 int)"
  where "vect q = to_int_pm (vect_p (poly_point q))"

lemma vect_alt: "vect q = (of_nat_pm (lp q)) - ((of_nat_pm (tp q))::'n \<Rightarrow>\<^sub>0 int)"
proof (rule poly_mapping_eqI, simp add: lookup_minus lookup_of_nat_pm vect_def lookup_to_int_pm vect_p_def
    fst_poly_point snd_poly_point)
  fix x
  let ?lp = "lookup (lp q)"
  let ?tp = "lookup (tp q)"
  have eq: "real (?lp x) - real (?tp x) = real_of_int (int (?lp x) - int (?tp x))" by simp
  show "\<lfloor>real (?lp x) - real (?tp x)\<rfloor> = int (?lp x) - int (?tp x)" unfolding eq floor_of_int ..
qed
  
subsubsection \<open>@{term associated_p}\<close>

definition associated_p :: "('n point * 'n point) \<Rightarrow> 'n point \<Rightarrow> 'n point \<Rightarrow> real \<Rightarrow> bool" where
  "associated_p p s t k \<longleftrightarrow> (t + k \<cdot> fst p = s + k \<cdot> snd p)"

lemma associated_pI:
  assumes "t + k \<cdot> fst p = s + k \<cdot> snd p"
  shows "associated_p p s t k"
  unfolding associated_p_def using assms .

lemma associated_pI_lookup:
  assumes "\<And>x. lookup t x + k * lookup (fst p) x = lookup s x + k * lookup (snd p) x"
  shows "associated_p p s t k"
  by (intro associated_pI poly_mapping_eqI, simp add: lookup_add assms)

lemma associated_pD:
  assumes "associated_p p s t k"
  shows "t + k \<cdot> fst p = s + k \<cdot> snd p"
  using assms unfolding associated_p_def .

lemma associated_pD_lookup:
  assumes "associated_p p s t k"
  shows "lookup t x + k * lookup (fst p) x = lookup s x + k * lookup (snd p) x"
proof -
  from assms have "t + k \<cdot> fst p = s + k \<cdot> snd p" by (rule associated_pD)
  hence "lookup (t + k \<cdot> fst p) x = lookup (s + k \<cdot> snd p) x" by simp
  thus ?thesis by (simp add: lookup_add)
qed

lemma associated_p_nat:
  "associated_p (of_nat_pm a, of_nat_pm b) (of_nat_pm s) (of_nat_pm t) (of_nat k) \<longleftrightarrow> (t + k \<cdot> a = s + k \<cdot> b)"
  unfolding associated_p_def
proof (simp add: poly_mapping_eq_iff plus_poly_mapping.rep_eq fun_eq_iff lookup_of_nat_pm)
  show "(\<forall>x. real (lookup t x) + real k * real (lookup a x) = real (lookup s x) + real k * real (lookup b x)) =
        (\<forall>x. lookup t x + k * lookup a x = lookup s x + k * lookup b x)"
    by (metis (no_types, hide_lams) of_nat_add of_nat_eq_iff of_nat_mult)
qed

lemma associated_p_int:
  "associated_p (of_int_pm a, of_int_pm b) (of_int_pm s) (of_int_pm t) (of_int k) \<longleftrightarrow> (t + k \<cdot> a = s + k \<cdot> b)"
  unfolding associated_p_def
proof (simp add: poly_mapping_eq_iff plus_poly_mapping.rep_eq fun_eq_iff lookup_of_int_pm)
  show "(\<forall>x. real_of_int (lookup t x) + real_of_int k * real_of_int (lookup a x) =
          real_of_int (lookup s x) + real_of_int k * real_of_int (lookup b x)) =
        (\<forall>x. lookup t x + k * lookup a x = lookup s x + k * lookup b x)"
    by (metis (no_types, hide_lams) of_int_add of_int_eq_iff of_int_mult)
qed

lemma associated_p_rat:
  "associated_p (of_rat_pm a, of_rat_pm b) (of_rat_pm s) (of_rat_pm t) (of_rat k) \<longleftrightarrow> (t + k \<cdot> a = s + k \<cdot> b)"
  unfolding associated_p_def
proof (simp add: poly_mapping_eq_iff plus_poly_mapping.rep_eq fun_eq_iff lookup_of_rat_pm)
  show "(\<forall>x. real_of_rat (lookup t x) + real_of_rat k * real_of_rat (lookup a x) =
          real_of_rat (lookup s x) + real_of_rat k * real_of_rat (lookup b x)) =
        (\<forall>x. lookup t x + k * lookup a x = lookup s x + k * lookup b x)"
    by (metis (no_types, hide_lams) of_rat_add of_rat_eq_iff of_rat_mult)
qed
  
lemma associated_p_alt: "associated_p p s t k \<longleftrightarrow> (s = t + k \<cdot> (vect_p p))"
  by (simp add: associated_p_def vect_p_def scalar_minus_distrib_left,
      metis (no_types, lifting) add_diff_cancel add_diff_eq diff_add_cancel)

lemma associated_p_0: "associated_p p s t 0 \<longleftrightarrow> (s = t)"
  by (auto simp add: associated_p_def)

lemma associated_p_1: "associated_p p s t 1 \<longleftrightarrow> (s + snd p = t + fst p)"
  by (simp add: associated_p_def plus_fun_def, metis)

lemma associated_p_canc_left: "associated_p p (u + s) (u + t) k \<longleftrightarrow> associated_p p s t k"
  by (simp add: associated_p_def ac_simps times_fun_def)

lemma associated_p_canc_right: "associated_p p (s + u) (t + u) k \<longleftrightarrow> associated_p p s t k"
  by (simp add: associated_p_def ac_simps times_fun_def)

lemma associated_p_trans:
  assumes "associated_p p s t k" and "associated_p p u s m"
  shows "associated_p p u t (k + m)"
proof (rule associated_pI)
  from assms(1) have "t + k \<cdot> fst p = s + k \<cdot> snd p" by (rule associated_pD)
  moreover from assms(2) have "s + m \<cdot> fst p = u + m \<cdot> snd p" by (rule associated_pD)
  ultimately show "t + (k + m) \<cdot> fst p = u + (k + m) \<cdot> snd p"
    by (simp add: scalar_distrib_right, metis (no_types, lifting) add.assoc add.commute)
qed

lemma associated_alt_associated_p:
  "associated q s t k \<longleftrightarrow> associated_p (poly_point q) (of_nat_pm s) (of_nat_pm t) (of_nat k)"
  by (simp add: poly_point_def associated_p_nat associated_def)

lemma associated_alt_int:
  "associated q s t k \<longleftrightarrow> (of_nat_pm s = ((of_nat_pm t)::'n \<Rightarrow>\<^sub>0 int) + (int k) \<cdot> (vect q))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R unfolding vect_alt
  proof (rule poly_mapping_eqI, simp add: lookup_of_nat_pm lookup_add lookup_minus)
    fix x
    from \<open>?L\<close> have "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x"
      by (rule associatedD_lookup)
    hence "int (lookup t x + k * lookup (lp q) x) = int (lookup s x + k * lookup (tp q) x)" by simp
    thus "int (lookup s x) = int (lookup t x) + int k * (int (lookup (lp q) x) - int (lookup (tp q) x))"
      by (simp add: right_diff_distrib)
  qed
next
  assume ?R
  show ?L
  proof (rule associatedI_lookup)
    fix x
    from \<open>?R\<close> have "lookup (of_nat_pm t + int k \<cdot> vect q) x = lookup (of_nat_pm s) x" by simp
    hence "int (lookup t x) + int k * (int (lookup (lp q) x) - int (lookup (tp q) x)) = int (lookup s x)"
      by (simp add: vect_alt lookup_of_nat_pm lookup_add lookup_minus)
    hence "int (lookup t x + k * lookup (lp q) x) = int (lookup s x + k * lookup (tp q) x)"
      by (simp add: right_diff_distrib)
    thus "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x" using of_nat_eq_iff by blast 
  qed
qed

lemma associated_alt_real:
  "associated q s t k \<longleftrightarrow> (of_nat_pm s = ((of_nat_pm t)::'n \<Rightarrow>\<^sub>0 real) + of_int_pm (int k \<cdot> (vect q)))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R unfolding vect_alt
  proof (rule poly_mapping_eqI, simp add: lookup_add lookup_minus lookup_of_nat_pm lookup_of_int_pm)
    fix x
    from \<open>?L\<close> have "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x"
      by (rule associatedD_lookup)
    hence "real (lookup t x + k * lookup (lp q) x) = real (lookup s x + k * lookup (tp q) x)" by simp
    thus "real (lookup s x) = real (lookup t x) + real k * (real (lookup (lp q) x) - real (lookup (tp q) x))"
      by (simp add: right_diff_distrib)
  qed
next
  assume ?R
  show ?L
  proof (rule associatedI_lookup)
    fix x
    from \<open>?R\<close> have "lookup (of_nat_pm t + of_int_pm (int k \<cdot> vect q)) x = lookup ((of_nat_pm s)::'n \<Rightarrow>\<^sub>0 real) x"
      by simp
    hence "real (lookup t x) + real k * (real (lookup (lp q) x) - real (lookup (tp q) x)) = real (lookup s x)"
      by (simp add: vect_alt lookup_of_nat_pm lookup_of_int_pm lookup_add lookup_minus)
    hence "real (lookup t x + k * lookup (lp q) x) = real (lookup s x + k * lookup (tp q) x)"
      by (simp add: right_diff_distrib)
    thus "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x" using of_nat_eq_iff by blast 
  qed
qed

subsubsection \<open>Parallel Binomials\<close>

definition parallel_binomials :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "parallel_binomials f1 f2 \<longleftrightarrow> (is_proper_binomial f1 \<and> is_proper_binomial f2 \<and>
    (\<exists>m1 m2::nat. m1 \<noteq> 0 \<and> m2 \<noteq> 0 \<and> m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2))"

lemma parallel_binomialsD1:
  assumes "parallel_binomials f1 f2"
  shows "is_proper_binomial f1"
  using assms unfolding parallel_binomials_def ..

lemma parallel_binomialsD2:
  assumes "parallel_binomials f1 f2"
  shows "is_proper_binomial f2"
  using assms unfolding parallel_binomials_def by simp

lemma parallel_binomialsE:
  assumes "parallel_binomials f1 f2"
  obtains m1 m2 where "m1 \<noteq> 0" and "m2 \<noteq> 0" and "m1 \<cdot> lp f1 + m2 \<cdot> tp f2 = m1 \<cdot> tp f1 + m2 \<cdot> lp f2"
  using assms unfolding parallel_binomials_def by blast

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

end (* pm_powerprod *)

subsection \<open>Two Binomials\<close>
  
locale two_binomials =
  pm_powerprod ord ord_strict
  for ord::"('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('n::countable \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50) +
  (* The reason why we have to name the order relations again is that otherwise we cannot call the
    type variables 'n and 'b. *)
  fixes f1 f2 :: "('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field"
  assumes f1_binomial: "is_binomial f1"
  assumes f2_binomial: "is_binomial f2"
begin

lemma is_binomial_set: "is_binomial_set {f1, f2}"
  unfolding is_binomial_set_def using f1_binomial f2_binomial by simp

lemma overlap_alt: "overlap q1 q2 = lcs (gcs (lp q1) (tp q1)) (gcs (lp q2) (tp q2))"
  by (simp add: overlap_def overlap_p_def fst_poly_point snd_poly_point
      gcs_of_nat_pm_linordered_semidom lcs_of_nat_pm_linordered_semidom)

lemma overlap_addsI:
  assumes "gcs (lp f1) (tp f1) adds g" and "gcs (lp f2) (tp f2) adds g"
  shows "overlap f1 f2 adds g"
  unfolding overlap_alt using assms by (rule lcs_adds)

lemma overlap_addsE1:
  assumes "overlap f1 f2 adds g"
  shows "gcs (lp f1) (tp f1) adds g"
  using adds_lcs assms unfolding overlap_alt by (rule adds_trans)

lemma overlap_addsE2:
  assumes "overlap f1 f2 adds g"
  shows "gcs (lp f2) (tp f2) adds g"
  using adds_lcs assms unfolding overlap_alt lcs_comm[of "gcs (lp f1) (tp f1)"] by (rule adds_trans)

lemma overlap_p_poly_point: "overlap_p (poly_point q1) (poly_point q2) = of_nat_pm (overlap q1 q2)"
  unfolding overlap_def
  by (rule of_nat_pm_comp_to_nat_pm[symmetric], rule overlap_p_is_nat_pm,
      (rule poly_point_is_nat_pm_pair)+)

lemma of_nat_fun_overlap_leqI:
  assumes "lookup (gcs (of_nat_pm (lp f1)) (of_nat_pm (tp f1))) \<le> lookup p"
    and "lookup (gcs (of_nat_pm (lp f2)) (of_nat_pm (tp f2))) \<le> lookup p"
  shows "lookup (of_nat_pm (overlap f1 f2)) \<le> lookup (p::'n point)"
  using assms
  by (simp only: overlap_p_poly_point[symmetric] overlap_p_def lookup_lcs_fun le_fun_def max.bounded_iff
      lookup_gcs_fun min_le_iff_disj fst_poly_point snd_poly_point of_nat_pm.rep_eq, simp add: lcs_fun_def)

lemma vect_p_poly_point: "vect_p (poly_point q) = of_int_pm (vect q)"
  unfolding vect_def
  by (rule of_int_pm_comp_to_int_pm[symmetric], rule vect_p_is_int_pm,
      rule nat_pm_pair_is_int_pm_pair, rule poly_point_is_nat_pm_pair)

definition step_p' :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'n point \<Rightarrow> nat" where
  "step_p' f p = Max ({nat \<lceil>(real (lookup (overlap f1 f2) x) - lookup p x) / real_of_int (lookup (vect f) x)\<rceil> |
                      x::'n. 0 < lookup (vect f) x \<and> lookup p x < real (lookup (overlap f1 f2) x)} \<union> {0})"

text \<open>Note that the original definition of @{term step_p'} requires @{term \<open>lookup (vect f) x \<noteq> 0\<close>} instead
      of @{term \<open>0 < lookup (vect f) x\<close>}. One can easily prove, however, that both formulations are equivalent.\<close>

definition step_p :: "'n point \<Rightarrow> nat" where
  "step_p p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) then
      step_p' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p
    else
      0
    )"

lemma finite_step_p'_carrier:
  "finite {x::'n. 0 < lookup (vect f) x \<and> lookup p x < real (lookup (overlap f1 f2) x)}"
proof (rule finite_subset)
  show "{x. 0 < lookup (vect f) x \<and> lookup p x < real (lookup (overlap f1 f2) x)} \<subseteq> keys (vect f)"
  proof (rule, simp, elim conjE)
    fix x
    assume "0 < lookup (vect f) x"
    hence "lookup (vect f) x \<noteq> 0" by simp
    thus "x \<in> keys (vect f)" by simp
  qed
qed (fact finite_keys)

lemma step_p'_alt:
  "step_p' f p = nat \<lceil>Max ({(real (lookup (overlap f1 f2) x) - lookup p x) / real_of_int (lookup (vect f) x) |
                          x::'n. 0 < lookup (vect f) x \<and> lookup p x < real (lookup (overlap f1 f2) x)} \<union> {0::real})\<rceil>"
proof -
  let ?ol = "lookup (overlap f1 f2)"
  let ?vc = "lookup (vect f)"
  have "\<lceil>Max ({(real (?ol x) - lookup p x) / real_of_int (?vc x) |
                          x::'n. 0 < ?vc x \<and> lookup p x < real (?ol x)} \<union> {0::real})\<rceil> =
        Max (ceiling ` ({(real (?ol x) - lookup p x) / real_of_int (?vc x) |
                          x::'n. 0 < ?vc x \<and> lookup p x < real (?ol x)} \<union> {0::real}))"
    by (rule mono_Max_commute, rule, fact ceiling_mono, simp_all add: finite_step_p'_carrier)
  also have "... = Max ({\<lceil>(real (?ol x) - lookup p x) / real_of_int (?vc x)\<rceil> |
                      x::'n. 0 < ?vc x \<and> lookup p x < real (?ol x)} \<union> {0::int})"
    by (simp add: image_image_Collect)
  also have "nat (...) = Max (nat ` ({\<lceil>(real (?ol x) - lookup p x) / real_of_int (?vc x)\<rceil> |
                      x::'n. 0 < ?vc x \<and> lookup p x < real (?ol x)} \<union> {0::int}))"
    by (rule mono_Max_commute, rule, simp_all add: finite_step_p'_carrier)
  moreover have "... = step_p' f p" by (simp add: step_p'_def image_image_Collect)
    text \<open>Another "also" here is, for some strange reason, much slower ...\<close>
  ultimately show ?thesis by simp
qed

lemma int_step_p':
  "int (step_p' f p) = \<lceil>Max ({(real (lookup (overlap f1 f2) x) - lookup p x) / real_of_int (lookup (vect f) x) |
                          x::'n. 0 < lookup (vect f) x \<and> lookup p x < real (lookup (overlap f1 f2) x)} \<union> {0})\<rceil>"
  (is "?l = \<lceil>?r\<rceil>")
proof -
  define c where "c = ?r"
  have "0 \<le> c" by (simp only: c_def, rule Max_ge, simp_all add: finite_step_p'_carrier)
  hence "0 \<le> \<lceil>c\<rceil>" by simp
  hence "int (nat \<lceil>c\<rceil>) = \<lceil>c\<rceil>" by simp
  thus ?thesis by (simp only: step_p'_alt c_def)
qed

lemma step_p'_above_overlap:
  assumes "of_nat_pm (overlap f1 f2) \<unlhd> p"
  shows "step_p' f p = 0"
proof -
  let ?A = "{nat \<lceil>(real (lookup (overlap f1 f2) x) - lookup p x) / real_of_int (lookup (vect f) x)\<rceil> |
                      x::'n. 0 < lookup (vect f) x \<and> lookup p x < real (lookup (overlap f1 f2) x)}"
  have eq: "?A = {}"
  proof (simp, intro allI impI)
    fix x
    assume "0 < lookup (vect f) x"
    from assms have "real (lookup (overlap f1 f2) x) \<le> lookup p x"
      by (simp add: le_pm_def le_fun_def of_nat_pm.rep_eq of_nat_fun_def)
    thus "\<not> lookup p x < lookup (overlap f1 f2) x" by simp
  qed
  show ?thesis unfolding step_p'_def eq by simp
qed
  
lemmas lem_3_1_13' = lem_3_1_13[of "poly_point f1" _ "poly_point f2", simplified overlap_p_poly_point snd_poly_point]

lemma step_p_welldefined:
  assumes "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p"
  shows "step_p p = 0"
  unfolding step_p_def
proof (split if_split, intro conjI impI)
  from assms have "of_nat_pm (overlap f1 f2) \<unlhd> p" by (rule lem_3_1_13')
  thus "step_p' (SOME f. f\<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p = 0"
    by (rule step_p'_above_overlap)
qed rule

lemma some_step_p_eqI:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
    and "\<exists>g\<in>{f1,f2}. \<not> of_nat_pm (tp g) \<unlhd> p"
  shows "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) = f"
proof (rule some_equality)
  from assms show "f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p" by simp
next
  fix f'
  assume "f' \<in> {f1, f2} \<and> is_proper_binomial f' \<and> of_nat_pm (tp f') \<unlhd> p"
  hence "f' \<in> {f1, f2}" and "of_nat_pm (tp f') \<unlhd> p" by simp_all
  show "f' = f"
  proof (rule ccontr)
    assume "f' \<noteq> f"
    have "\<forall>g\<in>{f1, f2}. of_nat_pm (tp g) \<unlhd> p"
    proof
      fix g
      assume "g \<in> {f1, f2}"
      with \<open>f \<in> {f1, f2}\<close> \<open>f' \<in> {f1, f2}\<close> \<open>f' \<noteq> f\<close> have "g = f \<or> g = f'" by auto
      with \<open>of_nat_pm (tp f) \<unlhd> p\<close> \<open>of_nat_pm (tp f') \<unlhd> p\<close> show "of_nat_pm (tp g) \<unlhd> p" by auto
    qed
    with assms(4) show False by simp
  qed
qed

lemma step_p_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
  shows "step_p p = step_p' f p"
proof (cases "\<forall>g\<in>{f1, f2}. of_nat_pm (tp g) \<unlhd> p")
  case True
  hence "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p" by simp_all
  hence "step_p p = 0" and "of_nat_pm (overlap f1 f2) \<unlhd> p"
    by (rule step_p_welldefined, rule lem_3_1_13')
  from this(2) have "step_p' f p = 0" by (rule step_p'_above_overlap)
  with \<open>step_p p = 0\<close> show ?thesis by simp
next
  case False
  hence "\<exists>g\<in>{f1,f2}. \<not> of_nat_pm (tp g) \<unlhd> p" by simp
  with assms have eq: "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) = f"
    by (rule some_step_p_eqI)
  show ?thesis unfolding step_p_def eq
  proof (split if_split, intro conjI impI, rule)
    assume "\<not> (\<exists>g\<in>{f1, f2}.is_proper_binomial g \<and> of_nat_pm (tp g) \<unlhd> p)"
    hence "\<forall>g\<in>{f1,f2}. (\<not> is_proper_binomial g) \<or> \<not> of_nat_pm (tp g) \<unlhd> p" by simp
    from this \<open>f \<in> {f1, f2}\<close> have "(\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" ..
    with assms(2) assms(3) show "0 = step_p' f p" by simp
  qed
qed

lemma step_p_alt2:
  assumes "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p)"
  shows "step_p p = 0"
  using assms unfolding step_p_def by auto

definition overlapshift_p' :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'n point \<Rightarrow> 'n point" where
  "overlapshift_p' f p = p + of_int_pm (int (step_p' f p) \<cdot> (vect f))"

definition overlapshift_p :: "'n point \<Rightarrow> 'n point" where
  "overlapshift_p p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) then
      overlapshift_p' (SOME f. f \<in> {f1,f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p
    else
      p
    )"

lemma overlapshift_p'_is_int_pm:
  assumes "is_int_pm p"
  shows "is_int_pm (overlapshift_p' f p)"
  unfolding overlapshift_p'_def
  by (rule plus_is_int_pm, fact, rule of_int_pm_is_int_pm)

lemma overlapshift_p'_above_overlap:
  assumes "of_nat_pm (overlap f1 f2) \<unlhd> p"
  shows "overlapshift_p' f p = p"
  by (simp add: overlapshift_p'_def step_p'_above_overlap[OF assms])

lemma overlapshift_p_welldefined:
  assumes "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p"
  shows "overlapshift_p p = p"
  unfolding overlapshift_p_def
proof (split if_split, intro conjI impI)
  from assms have "of_nat_pm (overlap f1 f2) \<unlhd> p" by (rule lem_3_1_13')
  thus "overlapshift_p' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p = p"
    by (rule overlapshift_p'_above_overlap)
qed rule

lemma overlapshift_p_alt0:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
  shows "overlapshift_p p = p + of_int_pm (int (step_p p) \<cdot> (vect f))"
proof (cases "\<forall>g\<in>{f1, f2}. of_nat_pm (tp g) \<unlhd> p")
  case True
  hence "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p" by simp_all
  hence "overlapshift_p p = p" and "step_p p = 0" by (rule overlapshift_p_welldefined, rule step_p_welldefined)
  thus ?thesis by simp
next
  case False
  hence "\<exists>g\<in>{f1,f2}. \<not> of_nat_pm (tp g) \<unlhd> p" by simp
  with assms have eq: "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) = f"
    by (rule some_step_p_eqI)
  show ?thesis unfolding overlapshift_p_def eq
  proof (split if_split, intro conjI impI)
    from assms have "step_p p = step_p' f p" by (rule step_p_alt1)
    thus "overlapshift_p' f p = p + of_int_pm (int (step_p p) \<cdot> vect f)" by (simp add: overlapshift_p'_def)
  next
    assume "\<not> (\<exists>f\<in>{f1, f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p)"
    hence "\<forall>f\<in>{f1,f2}. (\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" by simp
    from this \<open>f \<in> {f1, f2}\<close> have "(\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" ..
    with assms(2) assms(3) show "p = p + of_int_pm (int (step_p p) \<cdot> vect f)" by simp
  qed
qed

lemma overlapshift_p_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
  shows "overlapshift_p p = overlapshift_p' f p"
  by (simp only: overlapshift_p'_def overlapshift_p_alt0[OF assms] step_p_alt1[OF assms])

lemma overlapshift_p_alt2:
  assumes "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p)"
  shows "overlapshift_p p = p"
  using assms unfolding overlapshift_p_def by auto
  
lemma overlapshift_p_is_int_pm:
  assumes "is_int_pm p"
  shows "is_int_pm (overlapshift_p p)"
  unfolding overlapshift_p_def
  by (split if_split, intro conjI impI, rule overlapshift_p'_is_int_pm, (rule assms)+)

lemma step_p'_min:
  assumes "of_nat_pm (overlap f1 f2) \<unlhd> p + of_int_pm (int k \<cdot> vect f)"
  shows "step_p' f p \<le> k"
proof (simp add: step_p'_alt finite_step_p'_carrier, intro allI impI, elim exE)
  fix a x
  assume "a = (real (lookup (overlap f1 f2) x) - lookup p x) / real_of_int (lookup (vect f) x) \<and>
          0 < lookup (vect f) x \<and> lookup p x < real (lookup (overlap f1 f2) x)"
  hence a_eq: "a = (real (lookup (overlap f1 f2) x) - lookup p x) / real_of_int (lookup (vect f) x)"
    and "0 < lookup (vect f) x" and "lookup p x < real (lookup (overlap f1 f2) x)" by simp_all
  from this(2) have "0 < real_of_int (lookup (vect f) x)" by simp
  show "a \<le> real k"
  proof (simp only: a_eq pos_divide_le_eq[OF \<open>0 < real_of_int (lookup (vect f) x)\<close>])
    from assms have "real (lookup (overlap f1 f2) x) \<le> lookup p x + real k * real_of_int (lookup (vect f) x)"
      by (simp add: le_pm_def of_nat_pm.rep_eq plus_poly_mapping.rep_eq lookup_of_int_pm le_fun_def of_nat_fun_def)
    thus "real (lookup (overlap f1 f2) x) - lookup p x \<le> real k * real_of_int (lookup (vect f) x)" by simp
  qed
qed

lemma overlapshift_p'_is_above_overlap:
  assumes "of_nat_pm (overlap f1 f2) \<unlhd> p + of_int_pm (int k \<cdot> vect f)"
  shows "of_nat_pm (overlap f1 f2) \<unlhd> overlapshift_p' f p"
proof -
  let ?ol = "lookup (overlap f1 f2)"
  let ?os = "lookup (overlapshift_p' f p)"
  let ?vc = "lookup (vect f)"
  let ?p = "lookup p"
  show ?thesis
  proof (simp only: le_pm_def le_fun_def lookup_of_nat_pm of_nat_fun_def o_def, rule)
    fix x
    show "real (?ol x) \<le> ?os x"
    proof (cases "0 < ?vc x \<and> ?p x < real (?ol x)")
      case True
      hence "0 < ?vc x" and "?p x < real (?ol x)" by simp_all
      from this(1) have "0 < real_of_int (?vc x)" by simp
      have "(real (?ol x) - ?p x) / real_of_int (?vc x)
              \<le> Max ({(real (?ol x) - ?p x) / real_of_int (?vc x) | x. 0 < ?vc x \<and>
                       ?p x < real (?ol x)} \<union> {0})"
        by (rule Max_ge, simp add: finite_step_p'_carrier, rule, rule, rule, rule conjI, rule refl, rule True)
      hence "\<lceil>(real (?ol x) - ?p x) / real_of_int (?vc x)\<rceil> \<le> int (step_p' f p)"
        unfolding int_step_p' by (rule ceiling_mono)
      hence "(real (?ol x) - ?p x) / real_of_int (?vc x) \<le> real_of_int (int (step_p' f p))"
        by linarith
      hence "real (?ol x) - ?p x \<le> real_of_int (int (step_p' f p)) * real_of_int (?vc x)"
        by (simp only: pos_divide_le_eq[OF \<open>0 < real_of_int (?vc x)\<close>])
      thus ?thesis by (simp add: overlapshift_p'_def lookup_add lookup_of_int_pm)
    next
      case False
      hence disj: "?vc x \<le> 0 \<or> real (?ol x) \<le> ?p x" by auto
      show ?thesis
      proof (cases "?vc x \<le> 0")
        case True
        from assms have "step_p' f p \<le> k" by (rule step_p'_min)
        hence "int (step_p' f p) \<le> int k" by simp
        from this True have "(int k) * ?vc x \<le> int (step_p' f p) * ?vc x"
          by (rule mult_right_mono_neg)
        hence "?p x + real_of_int ((int k) * ?vc x) \<le> ?p x + real_of_int (int (step_p' f p) * ?vc x)"
          by linarith
        hence "lookup (p + of_int_pm (int k \<cdot> vect f)) x \<le> lookup (p + of_int_pm (int (step_p' f p) \<cdot> vect f)) x"
          by (simp add: lookup_add lookup_of_int_pm)
        moreover from assms have "real (?ol x) \<le> lookup (p + of_int_pm (int k \<cdot> vect f)) x"
          by (simp only: le_pm_def le_fun_def lookup_of_nat_pm)
        ultimately show ?thesis by (simp add: overlapshift_p'_def)
      next
        case False
        with disj have "0 < ?vc x" and *: "real (?ol x) \<le> ?p x" by simp_all
        from this(1) have "0 \<le> int (step_p' f p) * ?vc x" by simp
        hence "?p x \<le> ?p x + real_of_int (int (step_p' f p) * ?vc x)"
          by linarith
        hence "?p x \<le> lookup (p + of_int_pm (int (step_p' f p) \<cdot> vect f)) x"
          by (simp add: lookup_add lookup_of_int_pm)
        with * show ?thesis unfolding overlapshift_p'_def by simp
      qed
    qed
  qed
qed

definition step' :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "step' f t = step_p' f (of_nat_pm t)"

definition step :: "('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "step t = step_p (of_nat_pm t)"

definition overlapshift' :: "(('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat)" where
  "overlapshift' f p = to_nat_pm (overlapshift_p' f (of_nat_pm p))"

definition overlapshift :: "('n \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('n \<Rightarrow>\<^sub>0 nat)" where
  "overlapshift = to_nat_pm o overlapshift_p o of_nat_pm"

lemma step'_alt:
  "step' f p = Max ({nat \<lceil>(rat_of_nat (lookup (overlap f1 f2) x - lookup p x)) / rat_of_int (lookup (vect f) x)\<rceil> |
                      x::'n. 0 < lookup (vect f) x \<and> lookup p x < lookup (overlap f1 f2) x} \<union> {0})"
proof -
  let ?ol = "lookup (overlap f1 f2)"
  let ?vc = "lookup (vect f)"
  let ?p = "lookup p"
  let ?pn = "lookup (of_nat_pm p)"
  have "{nat \<lceil>(real (?ol x) - ?pn x) / real_of_int (?vc x)\<rceil> |
                  x. 0 < ?vc x \<and> ?pn x < real (?ol x)} =
                {nat \<lceil>rat_of_nat (?ol x - ?p x) / rat_of_int (?vc x)\<rceil> |
                  x. 0 < ?vc x \<and> ?p x < ?ol x}"
  proof (rule image_Collect_eqI)
    fix x
    show "(0 < ?vc x \<and> ?pn x < real (?ol x)) \<longleftrightarrow>
          (0 < ?vc x \<and> ?p x < ?ol x)" by (simp add: lookup_of_nat_pm of_nat_fun_def)
  next
    fix x
    assume "0 < ?vc x \<and> ?p x < ?ol x"
    hence "?p x < ?ol x" ..
    hence "?pn x < real (?ol x)" by (simp add: lookup_of_nat_pm of_nat_fun_def)
    hence "(real (?ol x) - ?pn x) / real_of_int (?vc x) =
          real (?ol x - ?p x) / real_of_int (?vc x)" by (auto simp add: lookup_of_nat_pm of_nat_fun_def)
    also have "... = real_of_rat (rat_of_nat (?ol x - ?p x)) / real_of_rat (rat_of_int (?vc x))"
      by simp
    also have "... = real_of_rat (rat_of_nat (?ol x - ?p x) / rat_of_int (?vc x))"
      by (simp add: of_rat_divide)
    finally have "\<lceil>(real (?ol x) - ?pn x) / real_of_int (?vc x)\<rceil> =
          \<lceil>rat_of_nat (?ol x - ?p x) / rat_of_int (?vc x)\<rceil>"
      by (simp add: ceil_real_of_rat)
    thus "nat \<lceil>(real (?ol x) - ?pn x) / real_of_int (?vc x)\<rceil> =
          nat \<lceil>rat_of_nat (?ol x - ?p x) / rat_of_int (?vc x)\<rceil>" by (simp only:)
  qed
  thus ?thesis by (simp add: step'_def step_p'_def)
qed

lemma step_alt:
  "step p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p) then
      step' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<unlhd> p) p
    else
      0
    )"
  by (simp only: le_pm_def step_def step_p_def step'_def[symmetric] leq_of_nat_fun of_nat_pm.rep_eq)

lemma step_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<unlhd> p"
  shows "step p = step' f p"
  unfolding step_def step'_def
  by (rule step_p_alt1, fact, fact, simp only: le_of_nat_pm, fact)

lemma step_alt2:
  assumes "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p)"
  shows "step p = 0"
  unfolding step_def
  by (rule step_p_alt2, simp only: le_of_nat_pm, fact)

lemma overlapshift'_alt:
  "lookup (overlapshift' f p) = nat o (lookup (of_nat_pm p + int (step' f p) \<cdot> (vect f)))"
  apply (simp add: overlapshift'_def overlapshift_p'_def step'_def[symmetric] to_nat_pm.rep_eq plus_poly_mapping.rep_eq
      lookup_of_nat_pm lookup_of_int_pm to_nat_fun_def to_nat_def, rule, simp)
  by (metis floor_of_int of_int_mult of_int_of_nat_eq)

lemma overlapshift_alt:
  "overlapshift p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p) then
      overlapshift' (SOME f. f \<in> {f1,f2} \<and> is_proper_binomial f \<and> tp f \<unlhd> p) p
    else
      p
    )"
  by (simp only: overlapshift_def o_def overlapshift_p_def le_of_nat_pm if_distrib[of to_nat_pm]
      overlapshift'_def[symmetric] to_nat_pm_comp_of_nat_pm)

lemma overlapshift_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<unlhd> p"
  shows "overlapshift p = overlapshift' f p"
proof -
  have "overlapshift_p (of_nat_pm p) = overlapshift_p' f (of_nat_pm p)"
    by (rule overlapshift_p_alt1, fact, fact, simp only: le_of_nat_pm, fact)
  thus ?thesis by (simp add: overlapshift_def overlapshift'_def)
qed

lemma overlapshift_alt2:
  assumes "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p)"
  shows "overlapshift p = p"
proof -
  have "overlapshift_p (of_nat_pm p) = of_nat_pm p"
    by (rule overlapshift_p_alt2, simp_all only: le_of_nat_pm, fact+)
  thus ?thesis by (simp add: overlapshift_def to_nat_fun_comp_of_nat_fun)
qed

lemma overlapshift_step_idI:
  assumes "step p = 0"
  shows "overlapshift p = p"
proof (cases "\<exists>f\<in>{f1, f2}. is_proper_binomial f \<and> tp f \<unlhd> p")
  case True
  then obtain f where "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<unlhd> p" by auto
  hence eq: "step p = step' f p" and "overlapshift p = overlapshift' f p"
    by (rule step_alt1, rule overlapshift_alt1)
  note this(2)
  also have "lookup (...) = nat \<circ> lookup (of_nat_pm p + int (step' f p) \<cdot> vect f)"
    by (fact overlapshift'_alt)
  also have "... = nat \<circ> lookup (of_nat_pm p)" by (simp add: eq[symmetric] assms)
  finally show ?thesis by (simp add: poly_mapping_eq_iff nat_comp_of_nat_fun of_nat_pm.rep_eq)
next
  case False
  thus ?thesis by (rule overlapshift_alt2)
qed

lemma step'_min:
  assumes "associated f p q k" and "overlap f1 f2 adds p"
  shows "step' f q \<le> k"
  unfolding step'_def
proof (rule step_p'_min)
  from assms(1) have eq: "(of_nat_pm p = ((of_nat_pm q)::'n \<Rightarrow>\<^sub>0 real) + of_int_pm (int k \<cdot> vect f))"
    by (simp only: associated_alt_real)
  from assms(2) have "of_nat_pm (overlap f1 f2) \<unlhd> ((of_nat_pm p)::'n \<Rightarrow>\<^sub>0 real)"
    by (simp only: adds_pm le_of_nat_pm)
  thus "of_nat_pm (overlap f1 f2) \<unlhd> ((of_nat_pm q)::'n \<Rightarrow>\<^sub>0 real) + of_int_pm (int k \<cdot> vect f)"
    by (simp only: eq)
qed

lemma overlapshift'_is_above_overlap:
  assumes "associated f p q k" and "overlap f1 f2 adds p"
  shows "overlap f1 f2 adds overlapshift' f q"
proof -
  have "of_nat_pm (overlap f1 f2) \<unlhd> overlapshift_p' f (of_nat_pm q)"
  proof (rule overlapshift_p'_is_above_overlap)
    from assms(1) have eq: "(of_nat_pm p = ((of_nat_pm q)::'n \<Rightarrow>\<^sub>0 real) + of_int_pm (int k \<cdot> vect f))"
      by (simp only: associated_alt_real)
    from assms(2) have "of_nat_pm (overlap f1 f2) \<unlhd> ((of_nat_pm p)::'n \<Rightarrow>\<^sub>0 real)"
      by (simp only: adds_pm le_of_nat_pm)
    thus "of_nat_pm (overlap f1 f2) \<unlhd> ((of_nat_pm q)::'n \<Rightarrow>\<^sub>0 real) + of_int_pm (int k \<cdot> vect f)"
      by (simp only: eq)
  qed
  hence "to_nat_pm ((of_nat_pm (overlap f1 f2))::'n \<Rightarrow>\<^sub>0 real) \<unlhd> to_nat_pm (overlapshift_p' f (of_nat_pm q))"
    by (rule le_to_nat_pm)
  thus ?thesis by (simp only: adds_pm overlapshift'_def to_nat_pm_comp_of_nat_pm)
qed

lemma step_min:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f adds q" and "associated f p q k"
    and "overlap f1 f2 adds p"
  shows "step q \<le> k"
proof -
  from assms(3) have "tp f \<unlhd> q" by (simp only: adds_pm)
  from assms(4) assms(5) have "step' f q \<le> k" by (rule step'_min)
  thus ?thesis by (simp only: step_alt1[OF \<open>f \<in> {f1, f2}\<close> \<open>is_proper_binomial f\<close> \<open>tp f \<unlhd> q\<close>])
qed

lemma overlapshift_is_above_overlap:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f adds q" and "associated f p q k"
    and "overlap f1 f2 adds p"
  shows "overlap f1 f2 adds overlapshift q"
proof -
  from assms(3) have "tp f \<unlhd> q" by (simp only: adds_pm)
  from assms(4) assms(5) have "overlap f1 f2 adds overlapshift' f q" by (rule overlapshift'_is_above_overlap)
  thus ?thesis by (simp only: overlapshift_alt1[OF \<open>f \<in> {f1, f2}\<close> \<open>is_proper_binomial f\<close> \<open>tp f \<unlhd> q\<close>])
qed

lemma associated_overlapshift:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f adds q" and "associated f p q k"
    and "overlap f1 f2 adds p"
  shows "associated f (overlapshift q) q (step q)"
proof -
  have nat_pm: "is_nat_pm (overlapshift_p (of_nat_pm q))"
  proof (rule int_pm_is_nat_pm, rule overlapshift_p_is_int_pm, rule nat_pm_is_int_pm,
        rule of_nat_pm_is_nat_pm)
    fix x
    from assms(5) have "of_nat_pm (overlap f1 f2) \<unlhd> ((of_nat_pm p)::'n \<Rightarrow>\<^sub>0 real)"
      by (simp only: adds_pm le_of_nat_pm)
    also have "... = of_nat_pm q + of_int_pm (int k \<cdot> vect f)" using assms(4)
      by (simp add: associated_alt_real)
    finally have "of_nat_pm (overlap f1 f2) \<unlhd> overlapshift_p' f (of_nat_pm q)"
      by (rule overlapshift_p'_is_above_overlap)
    hence "lookup (of_nat_pm (overlap f1 f2)) x \<le> lookup (overlapshift_p' f (of_nat_pm q)) x"
      by (rule le_pmD)
    have eq: "overlapshift_p (of_nat_pm q) = overlapshift_p' f (of_nat_pm q)"
      by (rule overlapshift_p_alt1, fact assms(1), fact assms(2),
          simp only: le_of_nat_pm adds_pm[symmetric], fact assms(3))
    have "is_nat_pm (of_nat_pm (overlap f1 f2))" by (rule of_nat_pm_is_nat_pm)
    hence "is_nat (lookup (of_nat_pm (overlap f1 f2)) x)"
      by (simp add: of_nat_pm.rep_eq of_nat_fun_def of_nat_is_nat)
    hence "(0::real) \<le> lookup (of_nat_pm (overlap f1 f2)) x" by (rule is_nat_geq_zero)
    also have "... \<le> lookup (overlapshift_p' f (of_nat_pm q)) x" by fact
    finally show "0 \<le> lookup (overlapshift_p (of_nat_pm q)) x" by (simp only: eq)
  qed
  have "overlapshift_p (of_nat_pm q) = of_nat_pm q + of_int_pm (int (step q) \<cdot> vect f)"
    unfolding step_def by (rule overlapshift_p_alt0, fact assms(1), fact assms(2),
                           simp only: le_of_nat_pm adds_pm[symmetric], fact assms(3))
  also have "... = of_int_pm (of_nat_pm q + int (step q) \<cdot> vect f)" by (simp add: of_int_pm_plus)
  finally have eq: "overlapshift_p (of_nat_pm q) = of_int_pm (of_nat_pm q + int (step q) \<cdot> vect f)" .
  show ?thesis by (simp only: associated_alt_int of_nat_pm_comp_to_nat_pm_eq_to_int_pm[OF nat_pm]
                  overlapshift_def o_def, simp only: eq to_int_pm_comp_of_int_pm)
qed

subsection \<open>Degree Bounds on the Shifts for Generating a Monomial\<close>

subsubsection \<open>One Proper Binomial and one Monomial\<close>

text \<open>We do not introduce a new locale for one proper binomial and one monomial and prove that it is
  a sublocale of @{locale two_binomials}, since then the interpretation "tpp" would get lost. Maybe
  there is a way to make this interpretation persist (maybe with "global_interpretation"?) ...
  So, we just introduce a predicate that expresses that f1 is a proper binomial and f2 is a
  monomial, and we constrain every lemma in this subsection by this predicate.\<close>
  
definition binomial_monom :: bool where "binomial_monom \<longleftrightarrow> (is_proper_binomial f1 \<and> is_monomial f2)"
  
lemma binomial_monomD1:
  assumes binomial_monom
  shows "is_proper_binomial f1"
  using assms unfolding binomial_monom_def ..

lemma binomial_monomD2:
  assumes binomial_monom
  shows "is_monomial f2"
  using assms unfolding binomial_monom_def ..

lemma thm_3_2_1_aux_1:
  assumes binomial_monom and "membership_problem_assms f1 f2 g" and "t \<in> keys g"
  shows "tp f1 adds t"
proof-
  from assms(2) have "g \<in> pideal {f1, f2}" and "\<not> is_red {f1, f2} g"
    by (rule membership_problem_assmsD4, rule membership_problem_assmsD5)
  from is_binomial_set this assms(3) obtain f where "f \<in> {f1, f2}" and "is_proper_binomial f"
    and "tp f adds t" by (rule rem_3_1_7)
  from \<open>f \<in> {f1, f2}\<close> have "f = f1 \<or> f = f2" by simp
  thus ?thesis
  proof
    assume "f = f1"
    with \<open>tp f adds t\<close> show ?thesis by simp
  next
    from \<open>is_proper_binomial f\<close> have "\<not> is_monomial f" by (rule proper_binomial_no_monomial)
    assume "f = f2"
    with \<open>\<not> is_monomial f\<close> binomial_monomD2[OF \<open>binomial_monom\<close>] show ?thesis by simp
  qed
qed

lemma thm_3_2_1_aux_1':
  assumes binomial_monom and "membership_problem_assms f1 f2 g"
  shows "tp f1 adds lp g"
  using assms
proof (rule thm_3_2_1_aux_1)
  from assms(2) have "is_binomial g" by (rule membership_problem_assmsD3)
  hence "g \<noteq> 0" by (rule binomial_not_0)
  thus "lp g \<in> keys g" by (rule lp_in_keys)
qed

lemma thm_3_2_1_aux_2:
  assumes binomial_monom and "membership_problem_assms f1 f2 g"
  obtains q1 q2 where "g = q1 * f1 + q2 * f2" and "keys g \<subseteq> keys (q1 * f1)"
    (* Note: we could also obtain the stronger assertion "keys g \<inter> keys (q2 * f2) = {}". *)
    and "\<forall>t\<in>(keys g). \<exists>v\<in>(keys q1). t = v + tp f1"
proof -
  from assms(2) have "g \<in> pideal {f1, f2}" by (rule membership_problem_assmsD4)
  then obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" by (rule in_pideal_2E)
  
  have "keys g \<inter> keys (q2 * f2) = {}"
  proof (simp only: disjoint_eq_subset_Compl, rule, rule)
    fix t
    assume "t \<in> keys g" and "t \<in> keys (q2 * f2)"
    from this(2) obtain x y where "x \<in> keys q2" and "y \<in> keys f2" and "t = x + y"
      by (rule in_keys_timesE)
    from \<open>binomial_monom\<close> have "is_monomial f2" by (rule binomial_monomD2)
    hence "keys f2 = {lp f2}" by (rule keys_monomial)
    with \<open>y \<in> keys f2\<close> have "y = lp f2" by simp
    from assms(2) \<open>t \<in> keys g\<close> have "\<not> lp f2 adds t" by (rule membership_problem_assms_lp_f2_nadds)
    moreover have "lp f2 adds t" unfolding adds_def \<open>y = lp f2\<close> \<open>t = x + y\<close> by (simp add: add.commute)
    ultimately show False ..
  qed
  hence *: "keys g \<subseteq> keys (q1 * f1)" using keys_add_subset[of "q1 * f1" "q2 * f2"] unfolding g_eq
    by auto
    
  show ?thesis
  proof (rule, fact g_eq, fact *, rule)
    fix t
    assume "t \<in> keys g"
    with * have "t \<in> keys (q1 * f1)" by auto
    then obtain x y where "x \<in> keys q1" and "y \<in> keys f1" and "t = x + y"
      by (rule in_keys_timesE)
    from \<open>binomial_monom\<close> have "is_proper_binomial f1" by (rule binomial_monomD1)
    have keys_f1: "keys f1 = {lp f1, tp f1}" by (rule keys_binomial, rule membership_problem_assmsD1, fact)
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

lemma thm_3_2_1_aux_3:
  assumes binomial_monom and "membership_problem_assms f1 f2 g"
  shows "is_monomial g"
proof -
  from \<open>binomial_monom\<close> have "is_proper_binomial f1" by (rule binomial_monomD1)
  from \<open>binomial_monom\<close> have "is_monomial f2" by (rule binomial_monomD2)
  then obtain c2 t2 where "c2 \<noteq> 0" and "lc f2 = c2" and "lp f2 = t2" and f2_eq: "f2 = monomial c2 t2"
    by (rule is_monomial_monomial_ordered)
  from \<open>c2 \<noteq> 0\<close> have keys_f2: "keys f2 = {t2}" unfolding f2_eq by (rule keys_of_monomial)
  from assms(2) have "is_binomial g" by (rule membership_problem_assmsD3)
  hence "is_monomial g \<or> is_proper_binomial g" unfolding is_binomial_alt by simp
  thus ?thesis
  proof
    assume "is_proper_binomial g"
    hence keys_g: "keys g = {lp g, tp g}" by (simp add: proper_binomial_imp_binomial keys_binomial)
    from keys_g have "lp g \<in> keys g" and "tp g \<in> keys g" by simp_all
        
    from assms obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" and keys_g_sub: "keys g \<subseteq> keys (q1 * f1)"
      and *: "\<forall>t\<in>(keys g). \<exists>v\<in>(keys q1). t = v + tp f1" by (rule thm_3_2_1_aux_2)
      
    have **: "\<And>t. t \<in> keys g \<Longrightarrow> monomial 1 t \<in> pideal {f1, f2}"
    proof -
      fix t
      assume "t \<in> keys g"
      with * have "\<exists>v\<in>(keys q1). t = v + tp f1" ..
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
        with assms(2) have "\<not> lp f1 adds lp q1' + lp f1" by (rule membership_problem_assms_lp_f1_nadds)
        thus False by simp
      qed
      then obtain x y where "x \<in> keys q2" and "y \<in> keys f2" and "lp q1' + lp f1 = x + y"
        by (rule in_keys_timesE)
      from \<open>y \<in> keys f2\<close> have "y = t2" unfolding keys_f2 by simp
      let ?q2 = "monomial (-(lookup (q1' * f1) (lp q1' + lp f1)) / c2) x"
      from \<open>c2 \<noteq> 0\<close> have "?q2 * f2 = monomial (- (lookup (q1' * f1) (lp q1' + lp f1))) (lp q1' + lp f1)" (is "_ = ?p")
        by (simp add: times_monomial_left \<open>lp q1' + lp f1 = x + y\<close> \<open>y = t2\<close> f2_eq monom_mult_monomial)
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
          from membership_problem_assms_lp_f1_nadds[OF assms(2) this] show False by simp
        qed
        thus "{v + tp f1} \<subseteq> keys (q1' * f1 + ?p)" by simp
      qed
      with _ show "monomial 1 t \<in> pideal {f1, f2}"
      proof (rule monomial_1_in_pidealI)
        show "q1' * f1 + ?q2 * f2 \<in> pideal {f1, f2}" by (rule in_pideal_2I)
      qed
    qed
      
    from assms(2) \<open>is_proper_binomial g\<close> have "\<not> monomial 1 ` (keys g) \<subseteq> pideal {f1, f2}"
      by (rule membership_problem_assmsD6)
    moreover from **[OF \<open>lp g \<in> keys g\<close>] **[OF \<open>tp g \<in> keys g\<close>]
      have "monomial 1 ` (keys g) \<subseteq> pideal {f1, f2}" unfolding keys_g by simp
    ultimately show ?thesis ..
  qed
qed
  
lemma thm_3_2_1_aux_4:
  assumes binomial_monom and "membership_problem_assms f1 f2 g"
  obtains k u where "k \<noteq> 0" and "lp f1 adds u" and "lp f2 adds u" and "associated f1 u (lp g) k"
proof -
  from \<open>binomial_monom\<close> have "is_proper_binomial f1" and "is_monomial f2"
    by (rule binomial_monomD1, rule binomial_monomD2)
  from assms obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" and g_keys_sub: "keys g \<subseteq> keys (q1 * f1)"
    and *: "\<forall>t\<in>(keys g). \<exists>v\<in>(keys q1). t = v + tp f1" by (rule thm_3_2_1_aux_2)
  have "g \<noteq> 0" by (rule binomial_not_0, rule membership_problem_assmsD3, fact)
  hence "lp g \<in> keys g" by (rule lp_in_keys)
  with * have "\<exists>v\<in>(keys q1). lp g = v + tp f1" ..
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
    with assms(2) have "\<not> lp f1 adds u + lp f1" by (rule membership_problem_assms_lp_f1_nadds)
    thus False by simp
  qed
  then obtain w w' where "w' \<in> keys f2" and w0: "u + lp f1 = w + w'" by (rule in_keys_timesE)
  from \<open>is_monomial f2\<close> have "keys f2 = {lp f2}" by (rule keys_monomial)
  with \<open>w' \<in> keys f2\<close> have w': "w' = lp f2" by simp
  with w0 have w: "u + lp f1 = w + lp f2" by simp
  
  show ?thesis
  proof
    from \<open>q1' \<noteq> 0\<close> have "keys q1' \<noteq> {}" by simp
    with finite_keys[of q1'] show "card (keys q1') \<noteq> 0" by auto
  next
    from \<open>is_proper_binomial f1\<close> \<open>q1' \<noteq> 0\<close> assoc show "associated f1 (w + lp f2) (lp g) (card (keys q1'))"
      unfolding v tp_q1'[symmetric] w[symmetric] u_def by (rule associated_poly_times_binomial_associated)
  next
    show "lp f1 adds w + lp f2" by (simp add: w[symmetric])
  qed simp
qed

lemma thm_3_2_1_aux_5:
  assumes binomial_monom and "membership_problem_assms f1 f2 g" and "k \<noteq> 0"
    and "lp f1 adds u" and "lp f2 adds u" and "associated f1 u (lp g) k"
  shows "membership_problem_concl f1 f2 g (ord_class.max (deg_pm (lp g)) (deg_pm u))"
proof -
  from assms(1) assms(2) have "is_monomial g" and "tp f1 adds lp g"
    by (rule thm_3_2_1_aux_3, rule thm_3_2_1_aux_1')
  from assms(1) have "is_proper_binomial f1" and "is_monomial f2"
    by (rule binomial_monomD1, rule binomial_monomD2)
  from \<open>is_monomial f2\<close> have "f2 \<noteq> 0" by (rule monomial_not_0)
  hence "lc f2 \<noteq> 0" by (rule lc_not_0)
  from \<open>is_monomial g\<close> have "g \<noteq> 0" by (rule monomial_not_0)
  hence "lc g \<noteq> 0" by (rule lc_not_0)
  with \<open>is_proper_binomial f1\<close> assms(6) \<open>k \<noteq> 0\<close> assms(4) \<open>tp f1 adds lp g\<close> obtain q1 c
    where eq1: "q1 * f1 = binomial c u (lc g) (lp g)" and obd: "is_obd c u (lc g) (lp g)"
    by (rule associated_adds_obtains_cofactor_binomial_tc)
  from obd have pbd: "is_pbd c u (lc g) (lp g)" by (rule obd_imp_pbd)
  from assms(5) obtain v where u_eq: "u = v + lp f2" by (metis addsE add.commute)
  define lc2 where "lc2 = lc f2"
  let ?q2 = "monomial (- c / lc2) v"
  from obd have "-c \<noteq> 0" by (simp add: is_obd_def)
  with \<open>lc f2 \<noteq> 0\<close> have "(-c) / lc f2 \<noteq> 0" by simp
  have eq2: "?q2 * f2 = monomial (-c) u"
    by (subst monomial_eq_itself[OF \<open>is_monomial f2\<close>, symmetric],
        simp add: times_monomial_left \<open>lc f2 \<noteq> 0\<close> monom_mult_monomial u_eq lc2_def)
  show ?thesis
  proof (simp only: membership_problem_concl_def, intro exI conjI impI)
    show "g = q1 * f1 + ?q2 * f2"
      by (simp only: eq1 eq2 binomial_def monomial_uminus[symmetric],
          simp add: monomial_eq_itself[OF \<open>is_monomial g\<close>])
  next
    show "poly_deg (q1 * f1) \<le> ord_class.max (deg_pm (lp g)) (deg_pm u)"
      by (simp add: eq1 poly_deg_def keys_binomial_pbd[OF pbd])
  next
    from \<open>-c \<noteq> 0\<close> have "keys (?q2 * f2) = {u}" unfolding eq2 by (rule keys_of_monomial)
    thus "poly_deg (?q2 * f2) \<le> ord_class.max (deg_pm (lp g)) (deg_pm u)" by (simp add: poly_deg_def)
  qed
qed

lemma thm_3_2_1_aux_6:
  assumes binomial_monom and "membership_problem_assms f1 f2 g"
  shows "lp f2 adds overlapshift (lp g)"
proof -
  from assms(1) have "is_monomial f2" by (rule binomial_monomD2)
  hence "tp f2 = lp f2" by (simp only: lp_eq_tp_monomial)
  from assms obtain k u where "k \<noteq> 0" and d1: "lp f1 adds u" and d2: "lp f2 adds u"
    and "associated f1 u (lp g) k" by (rule thm_3_2_1_aux_4)
  from gcs_adds[of "lp f1" "tp f1"] d1 have "gcs (lp f1) (tp f1) adds u" by (rule adds_trans)
  moreover from gcs_adds[of "lp f2" "tp f2"] d2 have "gcs (lp f2) (tp f2) adds u" by (rule adds_trans)
  ultimately have "overlap f1 f2 adds u" by (rule overlap_addsI)
  have "overlap f1 f2 adds overlapshift (lp g)"
  proof (rule overlapshift_is_above_overlap)
    from assms(1) show "is_proper_binomial f1" by (rule binomial_monomD1)
  next
    from assms show "tp f1 adds lp g" by (rule thm_3_2_1_aux_1')
  next
    show "associated f1 u (lp g) k" by fact
  qed (simp, fact)
  hence "gcs (lp f2) (tp f2) adds overlapshift (lp g)" by (rule overlap_addsE2)
  thus ?thesis by (simp only: gcs_same \<open>tp f2 = lp f2\<close>)
qed

lemma thm_3_2_1_aux_7:
  assumes binomial_monom and "membership_problem_assms f1 f2 g"
  shows "step (lp g) \<noteq> 0"
proof
  assume eq: "step (lp g) = 0"
  hence "overlapshift (lp g) = lp g" by (rule overlapshift_step_idI)
  moreover from assms have "lp f2 adds overlapshift (lp g)" by (rule thm_3_2_1_aux_6)
  ultimately have "lp f2 adds lp g" by simp
  have "is_red {f1, f2} g"
  proof (rule is_red_addsI)
    from assms(2) have "is_binomial f2" by (rule membership_problem_assmsD2)
    thus "f2 \<noteq> 0" by (rule binomial_not_0)
  next
    from assms(2) have "is_binomial g" by (rule membership_problem_assmsD3)
    hence "g \<noteq> 0" by (rule binomial_not_0)
    thus "lp g \<in> keys g" by (rule lp_in_keys)
  qed (simp, fact)
  moreover from assms(2) have "\<not> is_red {f1, f2} g" by (rule membership_problem_assmsD5)
  ultimately show False by simp
qed

theorem thm_3_2_1:
  assumes binomial_monom and "membership_problem_assms f1 f2 g"
  shows "membership_problem_concl f1 f2 g (ord_class.max (deg_pm (lp g)) (deg_pm (overlapshift (lp g))))"
proof -
  from assms obtain k u where "k \<noteq> 0" and "lp f1 adds u" and "lp f2 adds u" and *: "associated f1 u (lp g) k"
    by (rule thm_3_2_1_aux_4)
  have "f1 \<in> {f1, f2}" by simp
  moreover from assms(1) have "is_proper_binomial f1" by (rule binomial_monomD1)
  moreover from assms have "tp f1 adds lp g" by (rule thm_3_2_1_aux_1')
  moreover note \<open>associated f1 u (lp g) k\<close>
  moreover have "overlap f1 f2 adds u"
  proof (rule overlap_addsI)
    from gcs_adds \<open>lp f1 adds u\<close> show "gcs (lp f1) (tp f1) adds u" by (rule adds_trans)
  next
    from gcs_adds \<open>lp f2 adds u\<close> show "gcs (lp f2) (tp f2) adds u" by (rule adds_trans)
  qed
  ultimately have "step (lp g) \<le> k" and **: "associated f1 (overlapshift (lp g)) (lp g) (step (lp g))"
    by (rule step_min, rule associated_overlapshift)
  from assms have "step (lp g) \<noteq> 0" by (rule thm_3_2_1_aux_7)
  from assms this _ _ ** show ?thesis
  proof (rule thm_3_2_1_aux_5)
    from * ** \<open>lp f1 adds u\<close> \<open>tp f1 adds lp g\<close> \<open>step (lp g) \<le> k\<close> \<open>step (lp g) \<noteq> 0\<close>
    show "lp f1 adds overlapshift (lp g)" by (rule associated_lp_adds_between'')
  next
    from assms show "lp f2 adds overlapshift (lp g)" by (rule thm_3_2_1_aux_6)
  qed
qed

subsubsection \<open>Two Parallel Proper Binomials\<close>

(* For proving Theorem 3.2.2. it *might* be advantageous to employ valid polygonial chains, although
  this is not the case in MWW's thesis. *)

theorem thm_3_2_2:
  assumes "parallel_binomials f1 f2" and "is_monomial g" and "tp f1 adds lp g"
    and "membership_problem_assms f1 f2 g"
  shows "membership_problem_concl f1 f2 g
          (nat (ord_class.max (deg_pm (lp g)) (deg_pm (of_nat_pm (lp g) + (of_nat (step (lp g)) + 1) \<cdot> vect f1 + vect f2))))"
  sorry

end (* two_binomials *)

end (* theory *)
