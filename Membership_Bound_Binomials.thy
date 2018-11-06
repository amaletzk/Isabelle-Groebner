section \<open>New Bounds for the Membership Problem for Binomial Ideals\<close>

theory Membership_Bound_Binomials
  imports VPC
begin

subsection \<open>Structure of Binomial Ideals\<close>

(* The following lemmas could be proved in context "gd_term", but the abbreviations for "punit.lt"
  etc. introduced in theory "Binom_Mult" are inconsistent with similar abbreviations introduced
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
    by (rule, fact \<open>f \<in> F\<close>, rule ideal.generator_subset_module)
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
      by (rule, fact \<open>g \<in> ?G\<close>, rule ideal.generator_subset_module)
    from xin2 have "monomial 1 s \<in> ideal F" unfolding x .
    hence "punit.monom_mult c 0 (monomial 1 s) \<in> ideal F"
      by (rule punit.pmdl_closed_monom_mult[simplified])
    hence "monomial c s \<in> ideal F" by (simp add: punit.monom_mult_monomial)
    with \<open>g \<in> ideal F\<close> have "g - monomial c s \<in> ideal F" by (rule ideal.module_closed_minus)
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
proof (induct g arbitrary: thesis rule: ideal.module_induct)
  case base: module_0
  from base(2) show ?case unfolding keys_zero ..
next
  case ind: (module_plus g c f')
  from ind(6) keys_add_subset have "t \<in> keys g \<union> keys (c * f')" ..
  thus ?case
  proof
    assume "t \<in> keys g"
    obtain f s where "f \<in> F" and "s \<in> keys f" and "s adds t"
    proof (rule ind(2))
      show "t \<in> keys g" by fact
    qed
    thus ?thesis by (rule ind(5))
  next
    assume "t \<in> keys (c * f')"
    then obtain s1 s2 where "s2 \<in> keys f'" and "t = s1 + s2" by (rule in_keys_timesE)
    from \<open>f' \<in> F\<close> this(1) show ?thesis
    proof (rule ind(5))
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
  from assms(1) \<open>f \<in> F\<close> have "is_binomial f" by (rule punit.is_binomial_setD)
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
  
subsubsection \<open>@{term associated_p}\<close>

definition associated_p :: "('x point * 'x point) \<Rightarrow> 'x point \<Rightarrow> 'x point \<Rightarrow> rat \<Rightarrow> bool" where
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
proof (simp add: associated_p_def poly_mapping_eq_iff plus_poly_mapping.rep_eq fun_eq_iff lookup_of_nat_pm)
  show "(\<forall>x. rat (lookup t x) + rat k * rat (lookup a x) =
              rat (lookup s x) + rat k * rat (lookup b x)) =
        (\<forall>x. lookup t x + k * lookup a x = lookup s x + k * lookup b x)"
    by (metis (no_types, hide_lams) of_nat_add of_nat_eq_iff of_nat_mult)
qed

lemma associated_p_int:
  "associated_p (of_int_pm a, of_int_pm b) (of_int_pm s) (of_int_pm t) (of_int k) \<longleftrightarrow> (t + k \<cdot> a = s + k \<cdot> b)"
proof (simp add: associated_p_def poly_mapping_eq_iff plus_poly_mapping.rep_eq fun_eq_iff lookup_of_int_pm)
  show "(\<forall>x. rat_of_int (lookup t x) + rat_of_int k * rat_of_int (lookup a x) =
          rat_of_int (lookup s x) + rat_of_int k * rat_of_int (lookup b x)) =
        (\<forall>x. lookup t x + k * lookup a x = lookup s x + k * lookup b x)"
    by (metis (no_types, hide_lams) of_int_add of_int_eq_iff of_int_mult)
qed

lemma associated_p_rat:
  "associated_p (of_rat_pm a, of_rat_pm b) (of_rat_pm s) (of_rat_pm t) (of_rat k) \<longleftrightarrow> (t + k \<cdot> a = s + k \<cdot> b)"
  by (simp add: associated_p_def poly_mapping_eq_iff plus_poly_mapping.rep_eq fun_eq_iff lookup_of_rat_pm)
  
lemma associated_p_alt: "associated_p p s t k \<longleftrightarrow> (s = t + k \<cdot> (fst p - snd p))"
  by (simp add: associated_p_def scalar_minus_distrib_left,
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
  "associated q s t k \<longleftrightarrow> associated_p (poly_point q) (of_nat_pm s) (of_nat_pm t) (rat k)"
  by (simp add: poly_point_def associated_p_nat associated_def)

lemma associated_alt_rat:
  "associated q s t k \<longleftrightarrow> of_nat_pm s = ((of_nat_pm t)::'x point) + rat k \<cdot> vect q" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R unfolding vect_alt
  proof (rule poly_mapping_eqI, simp add: lookup_of_nat_pm lookup_add lookup_minus)
    fix x
    from \<open>?L\<close> have "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x"
      by (rule associatedD_lookup)
    hence "rat (lookup t x + k * lookup (lp q) x) = rat (lookup s x + k * lookup (tp q) x)" by simp
    thus "rat (lookup s x) = rat (lookup t x) + rat k * (rat (lookup (lp q) x) - rat (lookup (tp q) x))"
      by (simp add: right_diff_distrib)
  qed
next
  assume ?R
  show ?L
  proof (rule associatedI_lookup)
    fix x
    from \<open>?R\<close> have "lookup (of_nat_pm t + rat k \<cdot> vect q) x = lookup (of_nat_pm s) x" by simp
    hence "rat (lookup t x) + rat k * (rat (lookup (lp q) x) - rat (lookup (tp q) x)) = rat (lookup s x)"
      by (simp add: vect_alt lookup_of_nat_pm lookup_add lookup_minus)
    hence "rat (lookup t x + k * lookup (lp q) x) = rat (lookup s x + k * lookup (tp q) x)"
      by (simp add: right_diff_distrib)
    thus "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x" using of_nat_eq_iff by blast 
  qed
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

context two_polys
begin

definition step_p' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'x point \<Rightarrow> nat" where
  "step_p' f p = Max ({nat \<lceil>(lookup overlap x - lookup p x) / lookup (vect f) x\<rceil> |
                      x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<union> {0})"

text \<open>Note that the original definition of @{term step_p'} requires @{term \<open>lookup (vect f) x \<noteq> 0\<close>} instead
      of @{term \<open>0 < lookup (vect f) x\<close>}. One can easily prove, however, that both formulations are equivalent.\<close>

definition step_p :: "'x point \<Rightarrow> nat" where
  "step_p p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) then
      step_p' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p
    else 0)"

definition overlapshift_p' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'x point \<Rightarrow> 'x point" where
  "overlapshift_p' f p = p + rat (step_p' f p) \<cdot> vect f"

definition overlapshift_p :: "'x point \<Rightarrow> 'x point" where
  "overlapshift_p p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) then
      overlapshift_p' (SOME f. f \<in> {f1,f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p
    else p)"

definition step' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "step' f t = step_p' f (of_nat_pm t)"

definition step :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "step t = step_p (of_nat_pm t)"

definition overlapshift' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat)" where
  "overlapshift' f p = to_nat_pm (overlapshift_p' f (of_nat_pm p))"

definition overlapshift :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat)" where
  "overlapshift = to_nat_pm o overlapshift_p o of_nat_pm"

lemma overlap_leI:
  "gcs (lp f1) (tp f1) adds g \<Longrightarrow> gcs (lp f2) (tp f2) adds g \<Longrightarrow> overlap \<unlhd> of_nat_pm g"
  unfolding overlap_alt' le_of_nat_pm adds_pm[symmetric] by (rule lcs_adds)

lemma overlap_leD:
  assumes "overlap \<unlhd> of_nat_pm g"
  shows "gcs (lp f1) (tp f1) adds g" and "gcs (lp f2) (tp f2) adds g"
  using assms by (auto simp: overlap_alt' le_of_nat_pm adds_pm[symmetric]
                       intro: adds_trans[OF adds_lcs] adds_trans[OF adds_lcs_2])

lemma finite_step_p'_carrier: "finite {x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x}"
proof (rule finite_subset)
  show "{x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<subseteq> keys (vect f)"
  proof (rule, simp, elim conjE)
    fix x
    assume "0 < lookup (vect f) x"
    hence "lookup (vect f) x \<noteq> 0" by simp
    thus "x \<in> keys (vect f)" by simp
  qed
qed (fact finite_keys)

lemma step_p'_alt:
  "step_p' f p = nat \<lceil>Max ({(lookup overlap x - lookup p x) / lookup (vect f) x |
                          x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<union> {0::rat})\<rceil>"
proof -
  let ?ol = "lookup overlap"
  let ?vc = "lookup (vect f)"
  have "\<lceil>Max ({(?ol x - lookup p x) / ?vc x | x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::rat})\<rceil> =
        Max (ceiling ` ({(?ol x - lookup p x) / ?vc x | x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::rat}))"
    by (rule mono_Max_commute, rule, fact ceiling_mono, simp_all add: finite_step_p'_carrier)
  also have "\<dots> = Max ({\<lceil>(?ol x - lookup p x) / ?vc x\<rceil> | x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::int})"
    by (simp add: image_image_Collect)
  also have "nat \<dots> = Max (nat ` ({\<lceil>(?ol x - lookup p x) / ?vc x\<rceil> |
                      x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::int}))"
    by (rule mono_Max_commute, rule, simp_all add: finite_step_p'_carrier)
  also have "\<dots> = step_p' f p" by (simp add: step_p'_def image_image_Collect)
  finally show ?thesis by (rule sym)
qed

lemma int_step_p':
  "int (step_p' f p) = \<lceil>Max ({(lookup overlap x - lookup p x) / lookup (vect f) x |
                          x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<union> {0})\<rceil>"
  (is "?l = \<lceil>?r\<rceil>")
proof -
  define c where "c = ?r"
  have "0 \<le> c" by (simp only: c_def, rule Max_ge, simp_all add: finite_step_p'_carrier)
  hence "0 \<le> \<lceil>c\<rceil>" by simp
  hence "int (nat \<lceil>c\<rceil>) = \<lceil>c\<rceil>" by simp
  thus ?thesis by (simp only: step_p'_alt c_def)
qed

lemma step_p'_above_overlap:
  assumes "overlap \<unlhd> p"
  shows "step_p' f p = 0"
proof -
  let ?A = "{nat \<lceil>(lookup overlap x - lookup p x) / lookup (vect f) x\<rceil> |
                      x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x}"
  have eq: "?A = {}"
  proof (simp, intro allI impI)
    fix x
    assume "0 < lookup (vect f) x"
    from assms have "lookup overlap x \<le> lookup p x"
      by (simp add: le_pm_def le_fun_def of_nat_pm.rep_eq of_nat_fun_def)
    thus "\<not> lookup p x < lookup overlap x" by simp
  qed
  show ?thesis unfolding step_p'_def eq by simp
qed

lemma step_p_welldefined:
  assumes "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p"
  shows "step_p p = 0"
  unfolding step_p_def
proof (split if_split, intro conjI impI)
  from assms have "overlap \<unlhd> p" by (rule lem_3_1_13)
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
  hence "step_p p = 0" and "overlap \<unlhd> p" by (rule step_p_welldefined, rule lem_3_1_13)
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

lemma step_p_alt2: "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) \<Longrightarrow> step_p p = 0"
  by (auto simp: step_p_def)

lemma overlapshift_p'_is_int_pm:
  assumes "is_int_pm p"
  shows "is_int_pm (overlapshift_p' f p)"
  unfolding overlapshift_p'_def
  by (rule plus_is_int_pm, fact, rule scalar_is_int_pm, simp add: is_int_def, fact vect_is_int_pm)

lemma overlapshift_p'_above_overlap: "overlap \<unlhd> p \<Longrightarrow> overlapshift_p' f p = p"
  by (simp add: overlapshift_p'_def step_p'_above_overlap)

lemma overlapshift_p_welldefined:
  assumes "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p"
  shows "overlapshift_p p = p"
  unfolding overlapshift_p_def
proof (split if_split, intro conjI impI)
  from assms have "overlap \<unlhd> p" by (rule lem_3_1_13)
  thus "overlapshift_p' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p = p"
    by (rule overlapshift_p'_above_overlap)
qed rule

lemma overlapshift_p_alt0:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
  shows "overlapshift_p p = p + rat (step_p p) \<cdot> vect f"
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
    thus "overlapshift_p' f p = p + rat (step_p p) \<cdot> vect f" by (simp add: overlapshift_p'_def)
  next
    assume "\<not> (\<exists>f\<in>{f1, f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p)"
    hence "\<forall>f\<in>{f1,f2}. (\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" by simp
    from this \<open>f \<in> {f1, f2}\<close> have "(\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" ..
    with assms(2) assms(3) show "p = p + rat (step_p p) \<cdot> vect f" by simp
  qed
qed

lemma overlapshift_p_alt1:
  "f \<in> {f1, f2} \<Longrightarrow> is_proper_binomial f \<Longrightarrow> of_nat_pm (tp f) \<unlhd> p \<Longrightarrow> overlapshift_p p = overlapshift_p' f p"
  by (simp only: overlapshift_p'_def overlapshift_p_alt0 step_p_alt1)

lemma overlapshift_p_alt2:
  "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) \<Longrightarrow> overlapshift_p p = p"
  by (auto simp: overlapshift_p_def)
  
lemma overlapshift_p_is_int_pm:
  assumes "is_int_pm p"
  shows "is_int_pm (overlapshift_p p)"
  unfolding overlapshift_p_def
  by (split if_split, intro conjI impI, rule overlapshift_p'_is_int_pm, (rule assms)+)

lemma step_p'_min:
  assumes "overlap \<unlhd> p + rat k \<cdot> vect f"
  shows "step_p' f p \<le> k"
proof (simp add: step_p'_alt finite_step_p'_carrier ceiling_le_iff nat_le_iff, intro allI impI, elim exE)
  fix a x
  assume "a = (lookup overlap x - lookup p x) / lookup (vect f) x \<and>
              0 < lookup (vect f) x \<and> lookup p x < lookup overlap x"
  hence a_eq: "a = (lookup overlap x - lookup p x) / lookup (vect f) x"
    and "0 < lookup (vect f) x" and "lookup p x < lookup overlap x" by simp_all
  show "a \<le> rat k"
  proof (simp only: a_eq pos_divide_le_eq[OF \<open>0 < lookup (vect f) x\<close>])
    from assms have "lookup overlap x \<le> lookup p x + rat k * lookup (vect f) x"
      by (simp add: le_pm_def of_nat_pm.rep_eq plus_poly_mapping.rep_eq lookup_of_int_pm le_fun_def of_nat_fun_def)
    thus "lookup overlap x - lookup p x \<le> rat k * lookup (vect f) x" by simp
  qed
qed

lemma overlapshift_p'_is_above_overlap:
  assumes "overlap \<unlhd> p + rat k \<cdot> vect f"
  shows "overlap \<unlhd> overlapshift_p' f p"
proof -
  let ?ol = "lookup overlap"
  let ?os = "lookup (overlapshift_p' f p)"
  let ?vc = "lookup (vect f)"
  let ?p = "lookup p"
  show ?thesis
  proof (simp only: le_pm_def le_fun_def lookup_of_nat_pm of_nat_fun_def o_def, rule)
    fix x
    show "?ol x \<le> ?os x"
    proof (cases "0 < ?vc x \<and> ?p x < ?ol x")
      case True
      hence "0 < ?vc x" and "?p x < ?ol x" by simp_all
      have "(?ol x - ?p x) / ?vc x \<le> Max ({(?ol x - ?p x) / ?vc x | x. 0 < ?vc x \<and> ?p x < ?ol x} \<union> {0})"
        by (rule Max_ge, simp add: finite_step_p'_carrier, rule, rule, rule, rule conjI, rule refl, rule True)
      hence "\<lceil>(?ol x - ?p x) / ?vc x\<rceil> \<le> int (step_p' f p)" unfolding int_step_p' by (rule ceiling_mono)
      hence "(?ol x - ?p x) / ?vc x \<le> rat_of_int (int (step_p' f p))" by linarith
      hence "?ol x - ?p x \<le> rat_of_int (int (step_p' f p)) * ?vc x"
        by (simp only: pos_divide_le_eq[OF \<open>0 < ?vc x\<close>])
      thus ?thesis by (simp add: overlapshift_p'_def lookup_add lookup_of_int_pm)
    next
      case False
      hence disj: "?vc x \<le> 0 \<or> ?ol x \<le> ?p x" by auto
      show ?thesis
      proof (cases "?vc x \<le> 0")
        case True
        from assms have "step_p' f p \<le> k" by (rule step_p'_min)
        hence "rat (step_p' f p) \<le> rat k" by simp
        from this True have "rat k * ?vc x \<le> rat (step_p' f p) * ?vc x"
          by (rule mult_right_mono_neg)
        hence "?p x + rat k * ?vc x \<le> ?p x + rat (step_p' f p) * ?vc x" by linarith
        hence "lookup (p + rat k \<cdot> vect f) x \<le> lookup (p + rat (step_p' f p) \<cdot> vect f) x"
          by (simp add: lookup_add lookup_of_int_pm)
        moreover from assms have "?ol x \<le> lookup (p + rat k \<cdot> vect f) x"
          by (simp only: le_pm_def le_fun_def lookup_of_nat_pm)
        ultimately show ?thesis by (simp add: overlapshift_p'_def)
      next
        case False
        with disj have "0 < ?vc x" and *: "?ol x \<le> ?p x" by simp_all
        from this(1) have "0 \<le> rat (step_p' f p) * ?vc x" by simp
        hence "?p x \<le> ?p x + rat (step_p' f p) * ?vc x" by linarith
        hence "?p x \<le> lookup (p + rat (step_p' f p) \<cdot> vect f) x"
          by (simp add: lookup_add lookup_of_int_pm)
        with * show ?thesis by (simp add: overlapshift_p'_def)
      qed
    qed
  qed
qed

lemma step'_alt:
  "step' f p = Max ({nat \<lceil>(lookup overlap x - of_nat (lookup p x)) / lookup (vect f) x\<rceil> |
                      x::'x. 0 < lookup (vect f) x \<and> of_nat (lookup p x) < lookup overlap x} \<union> {0})"
  by (simp only: step'_def step_p'_def lookup_of_nat_pm)

lemma step_alt:
  "step p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p) then
      step' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<unlhd> p) p
    else 0)"
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
  "lookup (overlapshift' f p) = to_nat \<circ> (lookup (of_nat_pm p + rat (step' f p) \<cdot> vect f))"
  by (simp add: overlapshift'_def overlapshift_p'_def to_nat_pm.rep_eq plus_poly_mapping.rep_eq
      lookup_of_nat_pm to_nat_fun_def flip: step'_def)

lemma overlapshift_alt:
  "overlapshift p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p) then
      overlapshift' (SOME f. f \<in> {f1,f2} \<and> is_proper_binomial f \<and> tp f \<unlhd> p) p
    else p)"
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
  also have "lookup \<dots> = to_nat \<circ> lookup (of_nat_pm p + rat (step' f p) \<cdot> vect f)"
    by (fact overlapshift'_alt)
  also have "\<dots> = to_nat \<circ> lookup ((of_nat_pm p)::_ \<Rightarrow>\<^sub>0 rat)" by (simp add: eq[symmetric] assms)
  finally show ?thesis by (simp add: poly_mapping_eq_iff to_nat_comp_of_nat_fun of_nat_pm.rep_eq)
next
  case False
  thus ?thesis by (rule overlapshift_alt2)
qed

lemma step'_min:
  assumes "associated f p q k" and "overlap \<unlhd> of_nat_pm p"
  shows "step' f q \<le> k"
  unfolding step'_def
proof (rule step_p'_min)
  from assms(1) have eq: "(of_nat_pm p = ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f)"
    by (simp only: associated_alt_rat)
  from assms(2) show "overlap \<unlhd> ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f" by (simp only: eq)
qed

lemma overlapshift'_is_above_overlap:
  assumes "associated f p q k" and "overlap \<unlhd> of_nat_pm p"
  shows "overlap \<unlhd> of_nat_pm (overlapshift' f q)"
proof -
  have "overlap \<unlhd> overlapshift_p' f (of_nat_pm q)"
  proof (rule overlapshift_p'_is_above_overlap)
    from assms(1) have eq: "(of_nat_pm p = ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f)"
      by (simp only: associated_alt_rat)
    from assms(2) show "overlap \<unlhd> ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f" by (simp only: eq)
  qed
  also have "\<dots> \<unlhd> of_nat_pm (overlapshift' f q)"
  proof (rule leD_to_int_pm)
    show "to_int_pm (overlapshift_p' f (of_nat_pm q)) \<unlhd> to_int_pm (of_nat_pm (overlapshift' f q))"
      by (simp add: overlapshift'_def le_pm_def le_fun_def lookup_to_int_pm lookup_of_nat_pm
          lookup_to_nat_pm to_nat_def)
  next
    show "is_int_pm (overlapshift_p' f (of_nat_pm q))"
      by (intro overlapshift_p'_is_int_pm nat_pm_is_int_pm of_nat_pm_is_nat_pm)
  next
    from of_nat_pm_is_nat_pm show "is_int_pm (of_nat_pm (overlapshift' f q))" by (rule nat_pm_is_int_pm)
  qed
  finally show ?thesis .
qed

lemma step_min:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f adds q" and "associated f p q k"
    and "overlap \<unlhd> of_nat_pm p"
  shows "step q \<le> k"
proof -
  from assms(3) have "tp f \<unlhd> q" by (simp only: adds_pm)
  from assms(4) assms(5) have "step' f q \<le> k" by (rule step'_min)
  thus ?thesis by (simp only: step_alt1[OF \<open>f \<in> {f1, f2}\<close> \<open>is_proper_binomial f\<close> \<open>tp f \<unlhd> q\<close>])
qed

lemma overlapshift_is_above_overlap:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f adds q" and "associated f p q k"
    and "overlap \<unlhd> of_nat_pm p"
  shows "overlap \<unlhd> of_nat_pm (overlapshift q)"
proof -
  from assms(3) have "tp f \<unlhd> q" by (simp only: adds_pm)
  from assms(4) assms(5) have "overlap \<unlhd> of_nat_pm (overlapshift' f q)"
    by (rule overlapshift'_is_above_overlap)
  thus ?thesis by (simp only: overlapshift_alt1[OF \<open>f \<in> {f1, f2}\<close> \<open>is_proper_binomial f\<close> \<open>tp f \<unlhd> q\<close>])
qed

lemma associated_overlapshift:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f adds q" and "associated f p q k"
    and "overlap \<unlhd> of_nat_pm p"
  shows "associated f (overlapshift q) q (step q)"
proof -
  have nat_pm: "is_nat_pm (overlapshift_p (of_nat_pm q))"
  proof (rule int_pm_is_nat_pm, rule overlapshift_p_is_int_pm, rule nat_pm_is_int_pm,
        rule of_nat_pm_is_nat_pm)
    fix x
    note assms(5)
    also have "of_nat_pm p = of_nat_pm q + rat k \<cdot> vect f" using assms(4)
      by (simp add: associated_alt_rat)
    finally have "overlap \<unlhd> overlapshift_p' f (of_nat_pm q)"
      by (rule overlapshift_p'_is_above_overlap)
    hence "lookup overlap x \<le> lookup (overlapshift_p' f (of_nat_pm q)) x" by (rule le_pmD)
    have eq: "overlapshift_p (of_nat_pm q) = overlapshift_p' f (of_nat_pm q)"
      by (rule overlapshift_p_alt1, fact assms(1), fact assms(2),
          simp only: le_of_nat_pm adds_pm[symmetric], fact assms(3))
    from overlap_is_nat_pm have "is_nat (lookup overlap x)"
      by (simp only: is_nat_pm_def is_nat_fun_def)
    hence "(0::rat) \<le> lookup overlap x" by (rule is_nat_geq_zero)
    also have "\<dots> \<le> lookup (overlapshift_p' f (of_nat_pm q)) x" by fact
    finally show "0 \<le> lookup (overlapshift_p (of_nat_pm q)) x" by (simp only: eq)
  qed
  have eq: "overlapshift_p (of_nat_pm q) = of_nat_pm q + rat (step q) \<cdot> vect f"
    unfolding step_def by (rule overlapshift_p_alt0, fact assms(1), fact assms(2),
                           simp only: le_of_nat_pm adds_pm[symmetric], fact assms(3))
  show ?thesis
    by (simp only: associated_alt_rat overlapshift_def o_def of_nat_pm_comp_to_nat_pm[OF nat_pm],
        simp only: eq)
qed

subsection \<open>Degree Bounds on the Shifts for Generating a Monomial\<close>

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
  have "is_binomial_set {f1, f2}" sorry
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
    (* Note: we could also obtain the stronger assertion "keys g \<inter> keys (q2 * f2) = {}". *)
    and "\<forall>t\<in>(keys g). \<exists>v\<in>(keys q1). t = v + tp f1"
proof -
  from mpa have "g \<in> ideal {f1, f2}" by (rule membership_problem_assmsD)
  then obtain q1 q2 where g_eq: "g = q1 * f1 + q2 * f2" by (rule in_idealE_2)
  
  have "keys g \<inter> keys (q2 * f2) = {}"
  proof (simp only: disjoint_eq_subset_Compl, rule, rule)
    fix t
    assume "t \<in> keys g" and "t \<in> keys (q2 * f2)"
    from this(2) obtain x y where "x \<in> keys q2" and "y \<in> keys f2" and "t = x + y"
      by (rule in_keys_timesE)
    from f2_monomial have "keys f2 = {lp f2}" by (rule punit.keys_monomial)
    with \<open>y \<in> keys f2\<close> have "y = lp f2" by simp
    from mpa \<open>t \<in> keys g\<close> have "\<not> lp f2 adds t" by (rule membership_problem_assms_lp_f2_nadds)
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
    have keys_f1: "keys f1 = {lp f1, tp f1}"
      by (rule punit.keys_binomial, rule membership_problem_assmsD, fact)
    from \<open>y \<in> keys f1\<close> have "y = tp f1" unfolding keys_f1
    proof
      assume "y = lp f1"
      from mpa \<open>t \<in> keys g\<close> have "\<not> lp f1 adds t" by (rule membership_problem_assms_lp_f1_nadds)
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
      and *: "\<forall>t\<in>(keys g). \<exists>v\<in>(keys q1). t = v + tp f1" by (rule thm_3_2_1_aux_2)
      
    have **: "\<And>t. t \<in> keys g \<Longrightarrow> monomial 1 t \<in> ideal {f1, f2}"
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
        show "q1' * f1 + ?q2 * f2 \<in> ideal {f1, f2}" by (rule in_idealI_2)
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
    and *: "\<forall>t\<in>(keys g). \<exists>v\<in>(keys q1). t = v + tp f1" by (rule thm_3_2_1_aux_2)
  have "g \<noteq> 0" by (rule binomial_not_0, rule membership_problem_assmsD, fact)
  hence "lp g \<in> keys g" by (rule punit.lt_in_keys)
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

theorem thm_3_2_2:
  "membership_problem_concl f1 f2 g
          (to_nat (max (rat (deg_pm (lp g))) (deg_pm (of_nat_pm (lp g) + (rat (step (lp g)) + 1) \<cdot> vect f1 + vect f2))))"
  sorry

end

end (* two_polys *)

end (* theory *)
