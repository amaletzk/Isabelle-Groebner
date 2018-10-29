section \<open>Dub\'{e}'s General Degree-Bound for Gr\"obner Bases\<close>

theory Dube_Bound
  imports Cone_Decomposition Groebner_PM
begin

subsection \<open>Preliminaries\<close>

(* TODO: Move lemmas in this subsection into AFP. *)

context ordered_term
begin

lemma is_red_monom_mult:
  assumes "is_red F (monom_mult c 0 p)"
  shows "is_red F p"
proof -
  from assms obtain f u where "f \<in> F" and "u \<in> keys (monom_mult c 0 p)" and "f \<noteq> 0"
    and a: "lt f adds\<^sub>t u" by (rule is_red_addsE)
  from this(2) keys_monom_mult_subset have "u \<in> (\<oplus>) 0 ` keys p" ..
  hence "u \<in> keys p" by (auto simp: splus_zero)
  with \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> show ?thesis using a by (rule is_red_addsI)
qed

corollary is_irred_monom_mult: "\<not> is_red F p \<Longrightarrow> \<not> is_red F (monom_mult c 0 p)"
  by (auto dest: is_red_monom_mult)

lemma is_red_uminus: "is_red F (- p) \<longleftrightarrow> is_red F p"
  by (auto elim!: is_red_addsE simp: keys_uminus intro: is_red_addsI)

lemma is_red_plus:
  assumes "is_red F (p + q)"
  shows "is_red F p \<or> is_red F q"
proof -
  from assms obtain f u where "f \<in> F" and "u \<in> keys (p + q)" and "f \<noteq> 0"
    and a: "lt f adds\<^sub>t u" by (rule is_red_addsE)
  from this(2) keys_add_subset have "u \<in> keys p \<union> keys q" ..
  thus ?thesis
  proof
    assume "u \<in> keys p"
    with \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> have "is_red F p" using a by (rule is_red_addsI)
    thus ?thesis ..
  next
    assume "u \<in> keys q"
    with \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> have "is_red F q" using a by (rule is_red_addsI)
    thus ?thesis ..
  qed
qed

lemma is_irred_plus: "\<not> is_red F p \<Longrightarrow> \<not> is_red F q \<Longrightarrow> \<not> is_red F (p + q)"
  by (auto dest: is_red_plus)

lemma is_red_minus:
  assumes "is_red F (p - q)"
  shows "is_red F p \<or> is_red F q"
proof -
  from assms have "is_red F (p + (- q))" by simp
  hence "is_red F p \<or> is_red F (- q)" by (rule is_red_plus)
  thus ?thesis by (simp only: is_red_uminus)
qed

lemma is_irred_minus: "\<not> is_red F p \<Longrightarrow> \<not> is_red F q \<Longrightarrow> \<not> is_red F (p - q)"
  by (auto dest: is_red_minus)

end

subsection \<open>Standard Decompositions for Leading Power-Products of Ideals\<close>

context pm_powerprod
begin

definition normal_form :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field)"
  where "normal_form F p = (SOME q. (punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q \<and> \<not> punit.is_red (punit.reduced_GB F) q)"

text \<open>Of course, @{const normal_form} could be defined in a much more general context.\<close>

context
  fixes X :: "'x::countable set"
  assumes fin_X: "finite X"
begin

context
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) set"
  assumes F_sub: "F \<subseteq> P[X]"
begin

lemma normal_form:
  shows "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p (normal_form F p)" (is ?thesis1)
    and "\<not> punit.is_red (punit.reduced_GB F) (normal_form F p)" (is ?thesis2)
proof -
  from fin_X F_sub have "finite (punit.reduced_GB F)" by (rule finite_reduced_GB_Polys)
  hence "wfP (punit.red (punit.reduced_GB F))\<inverse>\<inverse>" by (rule punit.red_wf_finite)
  then obtain q where "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q"
    and "\<not> punit.is_red (punit.reduced_GB F) q" unfolding punit.is_red_def not_not
    by (rule relation.wf_imp_nf_ex)
  hence "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q \<and> \<not> punit.is_red (punit.reduced_GB F) q" ..
  hence "?thesis1 \<and> ?thesis2" unfolding normal_form_def by (rule someI)
  thus ?thesis1 and ?thesis2 by simp_all
qed

lemma normal_form_unique:
  assumes "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p q" and "\<not> punit.is_red (punit.reduced_GB F) q"
  shows "normal_form F p = q"
proof (rule relation.ChurchRosser_unique_final)
  from fin_X F_sub have "punit.is_Groebner_basis (punit.reduced_GB F)" by (rule reduced_GB_is_GB_Polys)
  thus "relation.is_ChurchRosser (punit.red (punit.reduced_GB F))"
    by (simp only: punit.is_Groebner_basis_def)
next
  show "(punit.red (punit.reduced_GB F))\<^sup>*\<^sup>* p (normal_form F p)" by (rule normal_form)
next
  have "\<not> punit.is_red (punit.reduced_GB F) (normal_form F p)" by (rule normal_form)
  thus "relation.is_final (punit.red (punit.reduced_GB F)) (normal_form F p)"
    by (simp add: punit.is_red_def)
next
  from assms(2) show "relation.is_final (punit.red (punit.reduced_GB F)) q"
    by (simp add: punit.is_red_def)
qed fact

lemma normal_form_id_iff: "normal_form F p = p \<longleftrightarrow> (\<not> punit.is_red (punit.reduced_GB F) p)"
proof
  assume "normal_form F p = p"
  with normal_form(2)[of p] show "\<not> punit.is_red (punit.reduced_GB F) p" by simp
next
  assume "\<not> punit.is_red (punit.reduced_GB F) p"
  with rtranclp.rtrancl_refl show "normal_form F p = p" by (rule normal_form_unique)
qed

lemma normal_form_normal_form: "normal_form F (normal_form F p) = normal_form F p"
  by (simp add: normal_form_id_iff normal_form)

lemma normal_form_zero: "normal_form F 0 = 0"
  by (simp add: normal_form_id_iff punit.irred_0)

lemma normal_form_monom_mult:
  "normal_form F (punit.monom_mult c 0 p) = punit.monom_mult c 0 (normal_form F p)"
  by (intro normal_form_unique punit.is_irred_monom_mult normal_form punit.red_rtrancl_mult)

lemma normal_form_uminus: "normal_form F (- p) = - normal_form F p"
  by (intro normal_form_unique punit.red_rtrancl_uminus normal_form)
      (simp add: punit.is_red_uminus normal_form)

lemma normal_form_plus_normal_form:
  "normal_form F (normal_form F p + normal_form F q) = normal_form F p + normal_form F q"
  by (intro normal_form_unique rtranclp.rtrancl_refl punit.is_irred_plus normal_form)

lemma normal_form_minus_normal_form:
  "normal_form F (normal_form F p - normal_form F q) = normal_form F p - normal_form F q"
  by (intro normal_form_unique rtranclp.rtrancl_refl punit.is_irred_minus normal_form)

lemma normal_form_ideal: "p - normal_form F p \<in> ideal F"
proof -
  from normal_form(1) have "p - normal_form F p \<in> ideal (punit.reduced_GB F)"
    by (rule punit.red_rtranclp_diff_in_pmdl[simplified])
  also from fin_X F_sub have "\<dots> = ideal F" by (rule reduced_GB_ideal_Polys)
  finally show ?thesis .
qed

lemma normal_form_zero_iff: "normal_form F p = 0 \<longleftrightarrow> p \<in> ideal F"
proof
  assume "normal_form F p = 0"
  with normal_form_ideal[of p] show "p \<in> ideal F" by simp
next
  assume "p \<in> ideal F"
  hence "p - (p - normal_form F p) \<in> ideal F" using normal_form_ideal by (rule ideal.module_closed_minus)
  also from fin_X F_sub have "\<dots> = ideal (punit.reduced_GB F)" by (rule reduced_GB_ideal_Polys[symmetric])
  finally have *: "normal_form F p \<in> ideal (punit.reduced_GB F)" by simp
  show "normal_form F p = 0"
  proof (rule ccontr)
    from fin_X F_sub have "punit.is_Groebner_basis (punit.reduced_GB F)" by (rule reduced_GB_is_GB_Polys)
    moreover note *
    moreover assume "normal_form F p \<noteq> 0"
    ultimately obtain g where "g \<in> punit.reduced_GB F" and "g \<noteq> 0"
      and a: "punit.lt g adds punit.lt (normal_form F p)" by (rule punit.GB_adds_lt[simplified])
    note this(1, 2)
    moreover from \<open>normal_form F p \<noteq> 0\<close> have "punit.lt (normal_form F p) \<in> keys (normal_form F p)"
      by (rule punit.lt_in_keys)
    ultimately have "punit.is_red (punit.reduced_GB F) (normal_form F p)"
      using a by (rule punit.is_red_addsI[simplified])
    with normal_form(2) show False ..
  qed
qed

lemma normal_form_eq_iff: "normal_form F p = normal_form F q \<longleftrightarrow> p - q \<in> ideal F"
proof -
  have "p - q - (normal_form F p - normal_form F q) = (p - normal_form F p) - (q - normal_form F q)"
    by simp
  also from normal_form_ideal normal_form_ideal have "\<dots> \<in> ideal F" by (rule ideal.module_closed_minus)
  finally have *: "p - q - (normal_form F p - normal_form F q) \<in> ideal F" .
  show ?thesis
  proof
    assume "normal_form F p = normal_form F q"
    with * show "p - q \<in> ideal F" by simp
  next
    assume "p - q \<in> ideal F"
    hence "p - q - (p - q - (normal_form F p - normal_form F q)) \<in> ideal F" using *
      by (rule ideal.module_closed_minus)
    hence "normal_form F (normal_form F p - normal_form F q) = 0" by (simp add: normal_form_zero_iff)
    thus "normal_form F p = normal_form F q" by (simp add: normal_form_minus_normal_form)
  qed
qed

lemma Polys_closed_normal_form:
  assumes "p \<in> P[X]"
  shows "normal_form F p \<in> P[X]"
proof -
  from fin_X F_sub have "punit.reduced_GB F \<subseteq> P[X]" by (rule reduced_GB_Polys)
  with fin_X show ?thesis using assms normal_form(1)
    by (rule punit.dgrad_p_set_closed_red_rtrancl[OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt])
qed

end

qualified definition ideal_decomp_aux :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow>
                                          ((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) set \<times> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set)"
  where "ideal_decomp_aux F f =
              (let J = ideal F; L = {l. l \<in> P[X] \<and> f * l \<in> J};
                    F' = (\<lambda>s. punit.lt s - punit.lt f) ` punit.reduced_GB F in
                 ((*) f ` normal_form L ` P[X], apfst ((+) (punit.lt f)) ` snd (split 0 X F')))"

(* The last three subgoals of the following lemma do not hold.
  As it seems, it is necessary to generalize certain concepts from theory "Cone_Decomposition" to
  sets of polynomials (e.g. (exact, standard) cone decompositions, Hilbert functions), because
  we can only prove the existence of a "d"-standard exact cone decomposition of the ideal generated
  by "F", but not of the leading-term ideal generated by "F" (which is what the last three subgoals
  below state).
  Note that function "split" does not need to be generalized, since it is applied to monomial ideals
  only. *)

lemma ideal_decomp_aux:
  assumes "finite F" and "F \<subseteq> P[X]" and "f \<in> P[X]"
  shows "fst (ideal_decomp_aux F f) \<subseteq> ideal {f}" (is ?thesis1)
    and "\<And>h. h \<in> ideal (insert f F) \<Longrightarrow> h \<in> P[X] \<Longrightarrow> (\<exists>a\<in>ideal F. \<exists>b\<in>fst (ideal_decomp_aux F f). h = a + b)"
    and "ideal F \<inter> fst (ideal_decomp_aux F f) = {0}" (is ?thesis2)

    and "cone_decomp (punit.lt ` (fst (ideal_decomp_aux F f) - {0})) (snd (ideal_decomp_aux F f))" (is ?thesis3)
    and "standard_decomp (poly_deg f) (snd (ideal_decomp_aux F f))" (is ?thesis4)
    and "finite_decomp (snd (ideal_decomp_aux F f))" (is ?thesis5)
proof -
  define J where "J = ideal F"
  define L where "L = {l. l \<in> P[X] \<and> f * l \<in> J}"
  define S where "S = (*) f ` normal_form L ` P[X]"
  define F' where "F' = (\<lambda>s. punit.lt s - punit.lt f) ` punit.reduced_GB F"

  have eq: "ideal_decomp_aux F f = (S, apfst ((+) (punit.lt f)) ` snd (split 0 X F'))"
    by (simp add: J_def ideal_decomp_aux_def Let_def L_def F'_def S_def)

  have L_sub: "L \<subseteq> P[X]" by (auto simp: L_def)

  show ?thesis1 unfolding eq fst_conv
  proof
    fix s
    assume "s \<in> S"
    then obtain q where "s = normal_form L q * f" by (auto simp: S_def mult.commute)
    also have "\<dots> \<in> ideal {f}" by (intro ideal.module_closed_smult ideal.generator_in_module singletonI)
    finally show "s \<in> ideal {f}" .
  qed

  {
    fix h
    assume "h \<in> ideal (insert f F)"
    from assms(2, 3) have "insert f F \<subseteq> P[X]" by simp
    moreover assume "h \<in> P[X]"
    ultimately obtain A q0 where "A \<subseteq> insert f F" and "finite A" and "\<And>a. q0 a \<in> P[X]"
      and h: "h = (\<Sum>a\<in>A. q0 a * a)"
      using \<open>h \<in> ideal (insert f F)\<close> by (rule in_idealE_Polys) blast
    obtain q h' where h': "h' \<in> ideal F" and "q \<in> P[X]" and h: "h = q * f + h'"
    proof (cases "f \<in> A")
      case True
      with \<open>A \<subseteq> insert f F\<close> have "A - {f} \<subseteq> F" by blast
      show ?thesis
      proof
        have "(\<Sum>a\<in>A - {f}. q0 a * a) \<in> ideal (A - {f})" by (rule ideal.sum_in_moduleI)
        also from \<open>A - {f} \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.module_mono)
        finally show "(\<Sum>a\<in>A - {f}. q0 a * a) \<in> ideal F" .
      next
        from \<open>finite A\<close> True show "h = q0 f * f + (\<Sum>a\<in>A - {f}. q0 a * a)" by (simp only: h sum.remove)
      qed fact
    next
      case False
      with \<open>A \<subseteq> insert f F\<close> have "A \<subseteq> F" by blast
      show ?thesis
      proof
        have "h \<in> ideal A" unfolding h by (rule ideal.sum_in_moduleI)
        also from \<open>A \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.module_mono)
        finally show "h \<in> ideal F" .
      next
        show "h = 0 * f + h" by simp
      qed (fact zero_in_Polys)
    qed
    show "\<exists>a\<in>ideal F. \<exists>b\<in>fst (ideal_decomp_aux F f). h = a + b"
    proof (intro bexI)
      show "h = (h - normal_form L q * f) + normal_form L q * f" by simp
    next
      from L_sub have "q - normal_form L q \<in> ideal L" by (rule normal_form_ideal)
      also have "\<dots> \<subseteq> {l. f * l \<in> J}"
      proof
        fix l
        assume "l \<in> ideal L"
        hence "f * l \<in> ideal F"
        proof (induct l rule: ideal.module_induct)
          case module_0
          thus ?case by (simp add: ideal.module_0)
        next
          case (module_plus a q p)
          from module_plus(3) have "f * p \<in> ideal F" by (simp add: L_def J_def)
          hence "q * (f * p) \<in> ideal F" by (rule ideal.module_closed_smult)
          hence "f * (q * p) \<in> ideal F" by (simp only: ac_simps)
          with module_plus(2) have "f * a + f * (q * p) \<in> ideal F" by (rule ideal.module_closed_plus)
          thus ?case by (simp only: algebra_simps)
        qed
        thus "l \<in> {l. f * l \<in> J}" by (simp add: J_def)
      qed
      finally have "(q - normal_form L q) * f \<in> J" by (simp add: mult.commute)
      hence "(q - normal_form L q) * f + h' \<in> ideal F"
        using h' unfolding J_def by (rule ideal.module_closed_plus)
      thus "h - normal_form L q * f \<in> ideal F" by (simp add: h algebra_simps)
    next
      have "normal_form L q * f = f * normal_form L q" by (fact mult.commute)
      also have "\<dots> \<in> fst (ideal_decomp_aux F f)" unfolding eq fst_conv S_def by (intro imageI \<open>q \<in> P[X]\<close>)
      finally show "normal_form L q * f \<in> fst (ideal_decomp_aux F f)" .
    qed
  }

  show ?thesis2
  proof (rule set_eqI)
    fix h
    show "h \<in> ideal F \<inter> fst (ideal_decomp_aux F f) \<longleftrightarrow> h \<in> {0}"
    proof
      assume "h \<in> ideal F \<inter> fst (ideal_decomp_aux F f)"
      hence "h \<in> J" and "h \<in> S" by (simp_all add: J_def S_def eq)
      from this(2) obtain q where "q \<in> P[X]" and h: "h = f * normal_form L q" by (auto simp: S_def)
      from L_sub this(1) have "normal_form L q \<in> P[X]" by (rule Polys_closed_normal_form)
      moreover from \<open>h \<in> J\<close> have "f * normal_form L q \<in> J" by (simp add: h)
      ultimately have "normal_form L q \<in> L" by (simp add: L_def)
      hence "normal_form L q \<in> ideal L" by (rule ideal.generator_in_module)
      with normal_form_ideal[OF L_sub] have "(q - normal_form L q) + normal_form L q \<in> ideal L"
        by (rule ideal.module_closed_plus)
      hence "normal_form L q = 0" using L_sub by (simp add: normal_form_zero_iff)
      thus "h \<in> {0}" by (simp add: h)
    next
      assume "h \<in> {0}"
      moreover have "0 \<in> (*) f ` normal_form L ` P[X]"
      proof (intro image_eqI)
        from L_sub show "0 = normal_form L 0" by (simp only: normal_form_zero)
      qed (simp_all add: zero_in_Polys)
      ultimately show "h \<in> ideal F \<inter> fst (ideal_decomp_aux F f)" by (simp add: ideal.module_0 eq S_def)
    qed
  qed

  note fin_X
  moreover have "finite F'" unfolding F'_def using assms(1) by (rule finite_imageI)
  moreover have "F' \<subseteq> .[X]" using assms(2, 3) by (auto simp: F'_def intro: PPs_closed_minus)
  moreover have "L = (\<Union>f\<in>F'. cone f X)" by (simp add: F'_def L_def J_def image_UN image_minus_cone)
  ultimately have std: "standard_decomp 0 (snd (split 0 X F'))"
    and "cone_decomp (.[X] - L) (snd (split 0 X F'))" by (rule standard_cone_decomp_snd_split)+
  from this(2) show ?thesis3 unfolding eq fst_conv snd_conv by (rule cone_decomp_plus)

  from std have "standard_decomp (0 + deg_pm f) (apfst ((+) f) ` snd (split 0 X F'))"
    by (rule standard_decomp_plus)
  thus ?thesis4 by (simp add: eq)

  from fin_X subset_refl \<open>finite F'\<close> have "finite_decomp (snd (split 0 X F'))"
    by (rule finite_decomp_split)
  thus ?thesis5 unfolding eq snd_conv by (rule finite_decomp_image)
qed

lemma ideal_decompE:
  assumes "finite F" and "F \<subseteq> .[X]" and "f0 \<in> .[X]" and "I = (\<Union>f\<in>insert f0 F. cone f X)"
    and "\<And>g. g \<in> F \<Longrightarrow> deg_pm g \<le> deg_pm f0"
  obtains T P where "finite_decomp P" and "standard_decomp (deg_pm f0) P" and "cone_decomp T P"
    and "I = cone f0 X \<union> T" and "cone f0 X \<inter> T = {}"
  using assms(1, 2, 4-)
proof (induct F arbitrary: I thesis)
  case empty
  show ?case
  proof (rule empty.prems)
    show "finite_decomp {}" by (rule finite_decompI) simp_all
  next
    show "standard_decomp (deg_pm f0) {}" by (rule standard_decompI) simp_all
  next
    show "cone_decomp {} {}" by (rule cone_decompI) simp_all
  next
    from empty.prems(3) show "I = cone f0 X \<union> {}" by simp
  next
    show "cone f0 X \<inter> {} = {}" by simp
  qed
next
  case (insert f F)
  define J where "J = (\<Union>f\<in>insert f0 F. cone f X)"
  with insert.prems(3) have I: "I = J \<union> cone f X" by (simp add: ac_simps)
  from insert.prems(2) have "f \<in> .[X]" and "F \<subseteq> .[X]" by simp_all
  from insert.prems(4) have "deg_pm f \<le> deg_pm f0" and 1: "\<And>g. g \<in> F \<Longrightarrow> deg_pm g \<le> deg_pm f0"
    by auto
  from \<open>F \<subseteq> .[X]\<close> J_def 1 obtain T P
    where finP: "finite_decomp P" and stdP: "standard_decomp (deg_pm f0) P" and cnP: "cone_decomp T P"
    and J: "J = cone f0 X \<union> T" and dsjnt1: "cone f0 X \<inter> T = {}"
    using insert.hyps(3) by blast

  let ?D = "ideal_decomp_aux (insert f0 F) f"
  from insert.hyps(1) have f0F_fin: "finite (insert f0 F)" by simp
  moreover from \<open>F \<subseteq> .[X]\<close> assms(3) have f0F_sub: "insert f0 F \<subseteq> .[X]" by simp
  ultimately have "finite_decomp (snd ?D)" and "cone_decomp (fst ?D) (snd ?D)"
    and "standard_decomp (deg_pm f) (snd ?D)" and dsjnt2: "J \<inter> fst ?D = {}"
    unfolding J_def using \<open>f \<in> .[X]\<close> by (rule ideal_decomp_aux)+
  from this(1-3) obtain Q where finQ: "finite_decomp Q" and cnQ: "cone_decomp (fst ?D) Q"
    and stdQ: "standard_decomp (deg_pm f0) Q"
    using \<open>deg_pm f \<le> deg_pm f0\<close> by (rule standard_decomp_geE)
  let ?T = "T \<union> fst ?D"
  let ?P = "P \<union> Q"
  show ?case
  proof (rule insert.prems)
    from finP finQ show "finite_decomp ?P" by (rule finite_decomp_Un)
  next
    from stdP stdQ show "standard_decomp (deg_pm f0) ?P" by (rule standard_decomp_Un)
  next
    from dsjnt2 have "T \<inter> fst ?D = {}" unfolding J by blast
    thus "cone_decomp ?T ?P" using cnP cnQ by (rule cone_decomp_Un)
  next
    have "I = (\<Union>g\<in>insert f (insert f0 F). cone g X)" by (simp add: insert.prems(3) ac_simps)
    also have "\<dots> = J \<union> fst ?D" unfolding J_def using f0F_fin f0F_sub \<open>f \<in> .[X]\<close>
      by (rule ideal_decomp_aux)
    also have "\<dots> = cone f0 X \<union> ?T" by (simp add: J Un_assoc)
    finally show "I = cone f0 X \<union> ?T" .
  next
    from dsjnt1 dsjnt2 show "cone f0 X \<inter> ?T = {}" unfolding J by blast
  qed
qed

lemma ideal_exact_decompE:
  assumes "finite F" and "F \<subseteq> .[X]" and "f \<in> F" and "\<And>g. g \<in> F \<Longrightarrow> deg_pm g \<le> deg_pm f"
    and "I = (\<Union>g\<in>F. cone g X)"
  obtains T P where "standard_decomp (deg_pm f) P" and "cone_decomp T P" and "exact_decomp X 0 P"
    and "I = cone f X \<union> T" and "cone f X \<inter> T = {}"
proof -
  from assms(3) have eq: "insert f F = F" by blast
  note assms(1, 2)
  moreover from assms(3, 2) have "f \<in> .[X]" ..
  moreover have "I = (\<Union>g\<in>insert f F. cone g X)" by (simp only: eq assms(5))
  ultimately obtain T P where "finite_decomp P" and std: "standard_decomp (deg_pm f) P"
    and cn: "cone_decomp T P" and I: "I = cone f X \<union> T" and dsjnt: "cone f X \<inter> T = {}"
    using assms(4) by (rule ideal_decompE)
  from this(1) have fin: "finite P" by (rule finite_decompD)
  have "cone g X \<subseteq> .[X]" if "g \<in> F" for g
  proof -
    from that assms(2) have "g \<in> .[X]" ..
    with zero_adds have "cone g X \<subseteq> cone 0 X" by (rule cone_mono_1')
    thus ?thesis by simp
  qed
  hence "I \<subseteq> .[X]" by (auto simp: assms(5))
  hence "T \<subseteq> .[X]" by (auto simp: I)
  moreover from cn have "T = (\<Union>(t, U)\<in>P. cone t U)" by (rule cone_decompD)
  ultimately have "cone t U \<subseteq> .[X]" if "(t, U) \<in> P" for t U using that by blast
  hence 1: "\<And>t U. (t, U) \<in> P \<Longrightarrow> t \<in> .[X]" and 2: "\<And>t U. (t, U) \<in> P \<Longrightarrow> U \<subseteq> X"
    by (auto dest: cone_indets)
  let ?P = "exact X (deg_pm f) P"
  from fin_X fin std 1 2 have "standard_decomp (deg_pm f) ?P" by (rule exact)
  moreover from fin_X std cn 1 2 have "cone_decomp T ?P" by (rule cone_decomp_exact)
  moreover from fin_X fin std 1 2 have "exact_decomp X 0 ?P" by (rule exact)
  ultimately show ?thesis using I dsjnt ..
qed

end

end (* theory *)
