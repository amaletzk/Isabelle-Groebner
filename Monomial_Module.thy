section \<open>Monomial Modules\<close>

theory Monomial_Module
  imports Groebner_Bases.Reduced_GB
begin

text \<open>Properties of modules generated by sets of monomials, and (reduced) Gr\"obner bases thereof.\<close>

lemma subset_imageE_inj:
  assumes "B \<subseteq> f ` A"
  obtains C where "C \<subseteq> A" and "B = f ` C" and "inj_on f C"
proof -
  define g where "g = (\<lambda>x. SOME a. a \<in> A \<and> f a = x)"
  have "g b \<in> A \<and> f (g b) = b" if "b \<in> B" for b
  proof -
    from that assms have "b \<in> f ` A" ..
    then obtain a where "a \<in> A" and "b = f a" ..
    hence "a \<in> A \<and> f a = b" by simp
    thus ?thesis unfolding g_def by (rule someI)
  qed
  hence 1: "\<And>b. b \<in> B \<Longrightarrow> g b \<in> A" and 2: "\<And>b. b \<in> B \<Longrightarrow> f (g b) = b" by simp_all
  let ?C = "g ` B"
  show ?thesis
  proof
    show "?C \<subseteq> A" by (auto intro: 1)
  next
    show "B = f ` ?C"
    proof (rule set_eqI)
      fix b
      show "b \<in> B \<longleftrightarrow> b \<in> f ` ?C"
      proof
        assume "b \<in> B"
        moreover from this have "f (g b) = b" by (rule 2)
        ultimately show "b \<in> f ` ?C" by force
      next
        assume "b \<in> f ` ?C"
        then obtain b' where "b' \<in> B" and "b = f (g b')" unfolding image_image ..
        moreover from this(1) have "f (g b') = b'" by (rule 2)
        ultimately show "b \<in> B" by simp
      qed
    qed
  next
    show "inj_on f ?C"
    proof
      fix x y
      assume "x \<in> ?C"
      then obtain bx where "bx \<in> B" and x: "x = g bx" ..
      moreover from this(1) have "f (g bx) = bx" by (rule 2)
      ultimately have *: "f x = bx" by simp
      assume "y \<in> ?C"
      then obtain "by" where "by \<in> B" and y: "y = g by" ..
      moreover from this(1) have "f (g by) = by" by (rule 2)
      ultimately have "f y = by" by simp
      moreover assume "f x = f y"
      ultimately have "bx = by" using * by simp
      thus "x = y" by (simp only: x y)
    qed
  qed
qed

lemma (in ordered_term) lt_eq_min_term_monomial:
  assumes "lt p = min_term"
  shows "monomial (lc p) min_term = p"
proof (rule poly_mapping_eqI)
  fix v
  from min_term_min[of v] have "v = min_term \<or> min_term \<prec>\<^sub>t v" by auto
  thus "lookup (monomial (lc p) min_term) v = lookup p v"
  proof
    assume "v = min_term"
    thus ?thesis by (simp add: lookup_single lc_def assms)
  next
    assume "min_term \<prec>\<^sub>t v"
    moreover have "v \<notin> keys p"
    proof
      assume "v \<in> keys p"
      hence "v \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
      with \<open>min_term \<prec>\<^sub>t v\<close> show False by (simp add: assms)
    qed
    ultimately show ?thesis by (simp add: lookup_single in_keys_iff)
  qed
qed

subsection \<open>Sets of Monomials\<close>

definition is_monomial_set :: "('a \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool"
  where "is_monomial_set A \<longleftrightarrow> (\<forall>p\<in>A. is_monomial p)"

lemma is_monomial_setI: "(\<And>p. p \<in> A \<Longrightarrow> is_monomial p) \<Longrightarrow> is_monomial_set A"
  by (simp add: is_monomial_set_def)

lemma is_monomial_setD: "is_monomial_set A \<Longrightarrow> p \<in> A \<Longrightarrow> is_monomial p"
  by (simp add: is_monomial_set_def)

lemma is_monomial_set_subset: "is_monomial_set B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> is_monomial_set A"
  by (auto simp: is_monomial_set_def)

lemma is_monomial_set_Un: "is_monomial_set (A \<union> B) \<longleftrightarrow> (is_monomial_set A \<and> is_monomial_set B)"
  by (auto simp: is_monomial_set_def)

subsection \<open>Modules\<close>

context term_powerprod
begin

lemma monomial_pmdl:
  assumes "is_monomial_set B" and "p \<in> pmdl B"
  shows "monomial (lookup p v) v \<in> pmdl B"
  using assms(2)
proof (induct p rule: pmdl_induct)
  case base: module_0
  show ?case by (simp add: pmdl.span_zero)
next
  case step: (module_plus p b c t)
  have eq: "monomial (lookup (p + monom_mult c t b) v) v =
            monomial (lookup p v) v + monomial (lookup (monom_mult c t b) v) v"
    by (simp only: single_add lookup_add)
  from assms(1) step.hyps(3) have "is_monomial b" by (rule is_monomial_setD)
  then obtain d u where b: "b = monomial d u" by (rule is_monomial_monomial)
  have "monomial (lookup (monom_mult c t b) v) v \<in> pmdl B"
  proof (simp add: b monom_mult_monomial lookup_single when_def pmdl.span_zero, intro impI)
    assume "t \<oplus> u = v"
    hence "monomial (c * d) v = monom_mult c t b" by (simp add: b monom_mult_monomial)
    also from step.hyps(3) have "\<dots> \<in> pmdl B" by (rule monom_mult_in_pmdl)
    finally show "monomial (c * d) v \<in> pmdl B" .
  qed
  with step.hyps(2) show ?case unfolding eq by (rule pmdl.span_add)
qed

lemma monomial_pmdl_field:
  assumes "is_monomial_set B" and "p \<in> pmdl B" and "v \<in> keys (p::_ \<Rightarrow>\<^sub>0 'b::field)"
  shows "monomial c v \<in> pmdl B"
proof -
  from assms(1, 2) have "monomial (lookup p v) v \<in> pmdl B" by (rule monomial_pmdl)
  hence "monom_mult (c / lookup p v) 0 (monomial (lookup p v) v) \<in> pmdl B"
    by (rule pmdl_closed_monom_mult)
  with assms(3) show ?thesis by (simp add: monom_mult_monomial splus_zero in_keys_iff)
qed

end (* term_powerprod *)

context ordered_term
begin

lemma keys_monomial_pmdl:
  assumes "is_monomial_set F" and "p \<in> pmdl F" and "t \<in> keys p"
  obtains f where "f \<in> F" and "f \<noteq> 0" and "lt f adds\<^sub>t t"
  using assms(2) assms(3)
proof (induct arbitrary: thesis rule: pmdl_induct)
  case module_0
  from this(2) show ?case by simp
next
  case step: (module_plus p f0 c s)
  from assms(1) step(3) have "is_monomial f0" unfolding is_monomial_set_def ..
  hence "keys f0 = {lt f0}" and "f0 \<noteq> 0" by (rule keys_monomial, rule monomial_not_0)
  from Poly_Mapping.keys_add step(6) have "t \<in> keys p \<union> keys (monom_mult c s f0)" ..
  thus ?case
  proof
    assume "t \<in> keys p"
    from step(2)[OF _ this] obtain f where "f \<in> F" and "f \<noteq> 0" and "lt f adds\<^sub>t t" by blast
    thus ?thesis by (rule step(5))
  next
    assume "t \<in> keys (monom_mult c s f0)"
    with keys_monom_mult_subset have "t \<in> (\<oplus>) s ` keys f0" ..
    hence "t = s \<oplus> lt f0" by (simp add: \<open>keys f0 = {lt f0}\<close>)
    hence "lt f0 adds\<^sub>t t" by (simp add: term_simps)
    with \<open>f0 \<in> F\<close> \<open>f0 \<noteq> 0\<close> show ?thesis by (rule step(5))
  qed
qed

lemma image_lt_monomial_lt: "lt ` monomial (1::'b::zero_neq_one) ` lt ` F = lt ` F"
  by (auto simp: lt_monomial intro!: image_eqI)

subsection \<open>Reduction\<close>

lemma red_setE2:
  assumes "red B p q"
  obtains b where "b \<in> B" and "b \<noteq> 0" and "red {b} p q"
proof -
  from assms obtain b t where "b \<in> B" and "red_single p q b t" by (rule red_setE)
  from this(2) have "b \<noteq> 0" by (simp add: red_single_def)
  have "red {b} p q" by (rule red_setI, simp, fact)
  show ?thesis by (rule, fact+)
qed

lemma red_monomial_keys:
  assumes "is_monomial r" and "red {r} p q"
  shows "card (keys p) = Suc (card (keys q))"
proof -
  from assms(2) obtain s where rs: "red_single p q r s" unfolding red_singleton ..
  hence cp0: "lookup p (s \<oplus> lt r) \<noteq> 0" and q_def0: "q = p - monom_mult (lookup p (s \<oplus> lt r) / lc r) s r"
    unfolding red_single_def by simp_all
  from assms(1) obtain c t where "c \<noteq> 0" and r_def: "r = monomial c t" by (rule is_monomial_monomial)
  have ltr: "lt r = t" unfolding r_def by (rule lt_monomial, fact)
  have lcr: "lc r = c" unfolding r_def by (rule lc_monomial)
  define u where "u = s \<oplus> t"
  from q_def0 have "q = p - monom_mult (lookup p u / c) s r" unfolding u_def ltr lcr .
  also have "... = p - monomial ((lookup p u / c) * c) u" unfolding u_def r_def monom_mult_monomial ..
  finally have q_def: "q = p - monomial (lookup p u) u" using \<open>c \<noteq> 0\<close> by simp
  from cp0 have "lookup p u \<noteq> 0" unfolding u_def ltr .
  hence "u \<in> keys p" by (simp add: in_keys_iff)
      
  have "keys q = keys p - {u}" unfolding q_def
  proof (rule, rule)
    fix x
    assume "x \<in> keys (p - monomial (lookup p u) u)"
    hence "lookup (p - monomial (lookup p u) u) x \<noteq> 0" by (simp add: in_keys_iff)
    hence a: "lookup p x - lookup (monomial (lookup p u) u) x \<noteq> 0" unfolding lookup_minus .
    hence "x \<noteq> u" unfolding lookup_single by auto
    with a have "lookup p x \<noteq> 0" unfolding lookup_single by auto
    show "x \<in> keys p - {u}"
    proof
      from \<open>lookup p x \<noteq> 0\<close> show "x \<in> keys p" by (simp add: in_keys_iff)
    next
      from \<open>x \<noteq> u\<close> show "x \<notin> {u}" by simp
    qed
  next
    show "keys p - {u} \<subseteq> keys (p - monomial (lookup p u) u)"
    proof
      fix x
      assume "x \<in> keys p - {u}"
      hence "x \<in> keys p" and "x \<noteq> u" by auto
      from \<open>x \<in> keys p\<close> have "lookup p x \<noteq> 0" by (simp add: in_keys_iff)
      with \<open>x \<noteq> u\<close> have "lookup (p - monomial (lookup p u) u) x \<noteq> 0" by (simp add: lookup_minus lookup_single)
      thus "x \<in> keys (p - monomial (lookup p u) u)" by (simp add: in_keys_iff)
    qed
  qed
      
  have "Suc (card (keys q)) = card (keys p)" unfolding \<open>keys q = keys p - {u}\<close>
    by (rule card_Suc_Diff1, rule finite_keys, fact)
  thus ?thesis by simp
qed

lemma red_monomial_monomial_setD:
  assumes "is_monomial p" and "is_monomial_set B" and "red B p q"
  shows "q = 0"
proof -
  from assms(3) obtain b where "b \<in> B" and "b \<noteq> 0" and *: "red {b} p q" by (rule red_setE2)
  from assms(2) this(1) have "is_monomial b" by (rule is_monomial_setD)
  hence "card (keys p) = Suc (card (keys q))" using * by (rule red_monomial_keys)
  with assms(1) show ?thesis by (simp add: is_monomial_def)
qed

corollary is_red_monomial_monomial_setD:
  assumes "is_monomial p" and "is_monomial_set B" and "is_red B p"
  shows "red B p 0"
proof -
  from assms(3) obtain q where "red B p q" by (rule is_redE)
  moreover from assms(1, 2) this have "q = 0" by (rule red_monomial_monomial_setD)
  ultimately show ?thesis by simp
qed

corollary is_red_monomial_monomial_set_in_pmdl:
  "is_monomial p \<Longrightarrow> is_monomial_set B \<Longrightarrow> is_red B p \<Longrightarrow> p \<in> pmdl B"
  by (intro red_rtranclp_0_in_pmdl r_into_rtranclp is_red_monomial_monomial_setD)

corollary red_rtrancl_monomial_monomial_set_cases:
  assumes "is_monomial p" and "is_monomial_set B" and "(red B)\<^sup>*\<^sup>* p q"
  obtains "q = p" | "q = 0"
  using assms(3)
proof (induct q arbitrary: thesis rule: rtranclp_induct)
  case base
  from refl show ?case by (rule base)
next
  case (step y z)
  show ?case
  proof (rule step.hyps)
    assume "y = p"
    with step.hyps(2) have "red B p z" by simp
    with assms(1, 2) have "z = 0" by (rule red_monomial_monomial_setD)
    thus ?thesis by (rule step.prems)
  next
    assume "y = 0"
    from step.hyps(2) have "is_red B 0" unfolding \<open>y = 0\<close> by (rule is_redI)
    with irred_0 show ?thesis ..
  qed
qed

lemma is_red_monomial_lt:
  assumes "0 \<notin> B"
  shows "is_red (monomial (1::'b::field) ` lt ` B) = is_red B"
proof
  fix p
  let ?B = "monomial (1::'b) ` lt ` B"
  show "is_red ?B p \<longleftrightarrow> is_red B p"
  proof
    assume "is_red ?B p"
    then obtain f v where "f \<in> ?B" and "v \<in> keys p" and adds: "lt f adds\<^sub>t v" by (rule is_red_addsE)
    from this(1) have "lt f \<in> lt ` ?B" by (rule imageI)
    also have "\<dots> = lt ` B" by (fact image_lt_monomial_lt)
    finally obtain b where "b \<in> B" and eq: "lt f = lt b" ..
    note this(1)
    moreover from this assms have "b \<noteq> 0" by blast
    moreover note \<open>v \<in> keys p\<close>
    moreover from adds have "lt b adds\<^sub>t v" by (simp only: eq)
    ultimately show "is_red B p" by (rule is_red_addsI)
  next
    assume "is_red B p"
    then obtain b v where "b \<in> B" and "v \<in> keys p" and adds: "lt b adds\<^sub>t v" by (rule is_red_addsE)
    from this(1) have "lt b \<in> lt ` B" by (rule imageI)
    also from image_lt_monomial_lt have "\<dots> = lt ` ?B" by (rule sym)
    finally obtain f where "f \<in> ?B" and eq: "lt b = lt f" ..
    note this(1)
    moreover from this have "f \<noteq> 0" by (auto simp: monomial_0_iff)
    moreover note \<open>v \<in> keys p\<close>
    moreover from adds have "lt f adds\<^sub>t v" by (simp only: eq)
    ultimately show "is_red ?B p" by (rule is_red_addsI)
  qed
qed

end (* ordered_term *)

subsection \<open>Gr\"obner Bases\<close>

context gd_term
begin

lemma monomial_set_is_GB:
  assumes "is_monomial_set G"
  shows "is_Groebner_basis G"
  unfolding GB_alt_1
proof
  fix f
  assume "f \<in> pmdl G"
  thus "(red G)\<^sup>*\<^sup>* f 0"
  proof (induct f rule: poly_mapping_plus_induct)
    case 1
    show ?case ..
  next
    case (2 f c t)
    let ?f = "monomial c t + f"
    from 2(1) have "t \<in> keys (monomial c t)" by simp
    from this 2(2) have "t \<in> keys ?f" by (rule in_keys_plusI1)
    with assms \<open>?f \<in> pmdl G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t t"
      by (rule keys_monomial_pmdl)
    from this(1) have "red G ?f f"
    proof (rule red_setI)
      from \<open>lt g adds\<^sub>t t\<close> have "component_of_term (lt g) = component_of_term t" and "lp g adds pp_of_term t"
        by (simp_all add: adds_term_def)
      from this have eq: "(pp_of_term t - lp g) \<oplus> lt g = t"
        by (simp add: adds_minus splus_def term_of_pair_pair)
      moreover from 2(2) have "lookup ?f t = c" by (simp add: lookup_add in_keys_iff)
      ultimately show "red_single (monomial c t + f) f g (pp_of_term t - lp g)"
      proof (simp add: red_single_def \<open>g \<noteq> 0\<close> \<open>t \<in> keys ?f\<close> 2(1))
        from \<open>g \<noteq> 0\<close> have "lc g \<noteq> 0" by (rule lc_not_0)
        hence "monomial c t = monom_mult (c / lc g) (pp_of_term t - lp g) (monomial (lc g) (lt g))"
          by (simp add: monom_mult_monomial eq)
        moreover from assms \<open>g \<in> G\<close> have "is_monomial g" unfolding is_monomial_set_def ..
        ultimately show "monomial c t = monom_mult (c / lc g) (pp_of_term t - lp g) g"
          by (simp only: monomial_eq_itself)
      qed
    qed
    have "f \<in> pmdl G" by (rule pmdl_closed_red, fact subset_refl, fact+)
    hence "(red G)\<^sup>*\<^sup>* f 0" by (rule 2(3))
    with \<open>red G ?f f\<close> show ?case by simp
  qed
qed

context
  fixes d
  assumes dgrad: "dickson_grading (d::'a \<Rightarrow> nat)"
begin

context
  fixes F m
  assumes fin_comps: "finite (component_of_term ` Keys F)"
    and F_sub: "F \<subseteq> dgrad_p_set d m"
    and F_monom: "is_monomial_set (F::(_ \<Rightarrow>\<^sub>0 'b::field) set)"
begin

text \<open>The proof of the following lemma could be simplified, analogous to homogeneous ideals.\<close>

lemma reduced_GB_subset_monic_dgrad_p_set: "reduced_GB F \<subseteq> monic ` F"
proof -
  from subset_refl obtain F' where "F' \<subseteq> F - {0}" and "lt ` (F - {0}) = lt ` F'" and "inj_on lt F'"
    by (rule subset_imageE_inj)
  define G where "G = {f \<in> F'. \<forall>f'\<in>F'. lt f' adds\<^sub>t lt f \<longrightarrow> f' = f}"
  have "G \<subseteq> F'" by (simp add: G_def)
  hence "G \<subseteq> F - {0}" using \<open>F' \<subseteq> F - {0}\<close> by (rule subset_trans)
  also have "\<dots> \<subseteq> F" by blast
  finally have "G \<subseteq> F" .
  have 1: thesis if "f \<in> F" and "f \<noteq> 0" and "\<And>g. g \<in> G \<Longrightarrow> lt g adds\<^sub>t lt f \<Longrightarrow> thesis" for thesis f
  proof -
    let ?K = "component_of_term ` Keys F"
    let ?A = "{t. pp_of_term t \<in> dgrad_set d m \<and> component_of_term t \<in> ?K}"
    let ?Q = "{f' \<in> F'. lt f' adds\<^sub>t lt f}"
    from dgrad fin_comps have "almost_full_on (adds\<^sub>t) ?A" by (rule Dickson_term)
    moreover have "transp_on (adds\<^sub>t) ?A" by (auto intro: transp_onI dest: adds_term_trans)
    ultimately have "wfp_on (strict (adds\<^sub>t)) ?A" by (rule af_trans_imp_wf)
    moreover have "lt f \<in> lt ` ?Q"
    proof -
      from that(1, 2) have "f \<in> F - {0}" by simp
      hence "lt f \<in> lt ` (F - {0})" by (rule imageI)
      also have "\<dots> = lt ` F'" by fact
      finally have "lt f \<in> lt ` F'" .
      with adds_term_refl show ?thesis by fastforce
    qed
    moreover have "lt ` ?Q \<subseteq> ?A"
    proof
      fix s
      assume "s \<in> lt ` ?Q"
      then obtain q where "q \<in> ?Q" and s: "s = lt q" ..
      from this(1) have "q \<in> F'" by simp
      hence "q \<in> F - {0}" using \<open>F' \<subseteq> F - {0}\<close> ..
      hence "q \<in> F" and "q \<noteq> 0" by simp_all
      from this(1) F_sub have "q \<in> dgrad_p_set d m" ..
      from \<open>q \<noteq> 0\<close> have "lt q \<in> keys q" by (rule lt_in_keys)
      hence "pp_of_term (lt q) \<in> pp_of_term ` keys q" by (rule imageI)
      also from \<open>q \<in> dgrad_p_set d m\<close> have "\<dots> \<subseteq> dgrad_set d m" by (simp add: dgrad_p_set_def)
      finally have 1: "pp_of_term s \<in> dgrad_set d m" by (simp only: s)
      from \<open>lt q \<in> keys q\<close> \<open>q \<in> F\<close> have "lt q \<in> Keys F" by (rule in_KeysI)
      hence "component_of_term s \<in> ?K" unfolding s by (rule imageI)
      with 1 show "s \<in> ?A" by simp
    qed
    ultimately obtain t where "t \<in> lt ` ?Q" and t_min: "\<And>s. strict (adds\<^sub>t) s t \<Longrightarrow> s \<notin> lt ` ?Q"
      by (rule wfp_onE_min) blast
    from this(1) obtain g where "g \<in> ?Q" and t: "t = lt g" ..
    from this(1) have "g \<in> F'" and adds: "lt g adds\<^sub>t lt f" by simp_all
    show ?thesis
    proof (rule that)
      {
        fix f'
        assume "f' \<in> F'"
        assume "lt f' adds\<^sub>t lt g"
        hence "lt f' adds\<^sub>t lt f" using adds by (rule adds_term_trans)
        with \<open>f' \<in> F'\<close> have "f' \<in> ?Q" by simp
        hence "lt f' \<in> lt ` ?Q" by (rule imageI)
        with t_min have "\<not> strict (adds\<^sub>t) (lt f') (lt g)" unfolding t by blast
        with \<open>lt f' adds\<^sub>t lt g\<close> have "lt g adds\<^sub>t lt f'" by blast
        with \<open>lt f' adds\<^sub>t lt g\<close> have "lt f' = lt g" by (rule adds_term_antisym)
        with \<open>inj_on lt F'\<close> have "f' = g" using \<open>f' \<in> F'\<close> \<open>g \<in> F'\<close> by (rule inj_onD)
      }
      with \<open>g \<in> F'\<close> show "g \<in> G" by (simp add: G_def)
    qed fact
  qed
  have 2: "is_red G q" if "q \<in> pmdl F" and "q \<noteq> 0" for q
  proof -
    from that(2) have "keys q \<noteq> {}" by simp
    then obtain t where "t \<in> keys q" by blast
    with F_monom that(1) obtain f where "f \<in> F" and "f \<noteq> 0" and *: "lt f adds\<^sub>t t"
      by (rule keys_monomial_pmdl)
    from this(1, 2) obtain g where "g \<in> G" and "lt g adds\<^sub>t lt f" by (rule 1)
    from this(2) have **: "lt g adds\<^sub>t t" using * by (rule adds_term_trans)
    from \<open>g \<in> G\<close> \<open>G \<subseteq> F - {0}\<close> have "g \<in> F - {0}" ..
    hence "g \<noteq> 0" by simp
    with \<open>g \<in> G\<close> show ?thesis using \<open>t \<in> keys q\<close> ** by (rule is_red_addsI)
  qed
  from \<open>G \<subseteq> F - {0}\<close> have "G \<subseteq> F" by blast
  hence "pmdl G \<subseteq> pmdl F" by (rule pmdl.span_mono)
  note dgrad fin_comps F_sub
  moreover have "is_reduced_GB (monic ` G)" unfolding is_reduced_GB_def GB_image_monic
  proof (intro conjI image_monic_is_auto_reduced image_monic_is_monic_set)
    from dgrad show "is_Groebner_basis G"
    proof (rule isGB_I_is_red)
      from \<open>G \<subseteq> F\<close> F_sub show "G \<subseteq> dgrad_p_set d m" by (rule subset_trans)
    next
      fix f
      assume "f \<in> pmdl G"
      hence "f \<in> pmdl F" using \<open>pmdl G \<subseteq> pmdl F\<close> ..
      moreover assume "f \<noteq> 0"
      ultimately show "is_red G f" by (rule 2)
    qed
  next
    show "is_auto_reduced G" unfolding is_auto_reduced_def
    proof (intro ballI notI)
      fix g
      assume "g \<in> G"
      hence "g \<in> F" using \<open>G \<subseteq> F\<close> ..
      with F_monom have "is_monomial g" by (rule is_monomial_setD)
      hence keys_g: "keys g = {lt g}" by (rule keys_monomial)
      assume "is_red (G - {g}) g"
      then obtain g' t where "g' \<in> G - {g}" and "t \<in> keys g" and adds: "lt g' adds\<^sub>t t" by (rule is_red_addsE)
      from this(1) have "g' \<in> F'" and "g' \<noteq> g" by (simp_all add: G_def)
      from \<open>t \<in> keys g\<close> have "t = lt g" by (simp add: keys_g)
      with \<open>g \<in> G\<close> \<open>g' \<in> F'\<close> adds have "g' = g" by (simp add: G_def)
      with \<open>g' \<noteq> g\<close> show False ..
    qed
  next
    show "0 \<notin> monic ` G"
    proof
      assume "0 \<in> monic ` G"
      then obtain g where "0 = monic g" and "g \<in> G" ..
      moreover from this(2) \<open>G \<subseteq> F - {0}\<close> have "g \<noteq> 0" by blast
      ultimately show False by (simp add: monic_0_iff)
    qed
  qed
  moreover have "pmdl (monic ` G) = pmdl F" unfolding pmdl_image_monic
  proof
    show "pmdl F \<subseteq> pmdl G"
    proof (rule pmdl.span_subset_spanI, rule)
      fix f
      assume "f \<in> F"
      hence "f \<in> pmdl F" by (rule pmdl.span_base)
      note dgrad
      moreover from \<open>G \<subseteq> F\<close> F_sub have "G \<subseteq> dgrad_p_set d m" by (rule subset_trans)
      moreover note \<open>pmdl G \<subseteq> pmdl F\<close> 2 \<open>f \<in> pmdl F\<close>
      moreover from \<open>f \<in> F\<close> F_sub have "f \<in> dgrad_p_set d m" ..
      ultimately have "(red G)\<^sup>*\<^sup>* f 0" by (rule is_red_implies_0_red_dgrad_p_set)
      thus "f \<in> pmdl G" by (rule red_rtranclp_0_in_pmdl)
    qed
  qed fact
  ultimately have "reduced_GB F = monic ` G" by (rule reduced_GB_unique_dgrad_p_set)
  also from \<open>G \<subseteq> F\<close> have "\<dots> \<subseteq> monic ` F" by (rule image_mono)
  finally show ?thesis .
qed

corollary reduced_GB_is_monomial_set_dgrad_p_set: "is_monomial_set (reduced_GB F)"
proof (rule is_monomial_setI)
  fix g
  assume "g \<in> reduced_GB F"
  also have "\<dots> \<subseteq> monic ` F" by (fact reduced_GB_subset_monic_dgrad_p_set)
  finally obtain f where "f \<in> F" and g: "g = monic f" ..
  from F_monom this(1) have "is_monomial f" by (rule is_monomial_setD)
  hence "card (keys f) = 1" by (simp only: is_monomial_def)
  hence "f \<noteq> 0" by auto
  hence "lc f \<noteq> 0" by (rule lc_not_0)
  hence "1 / lc f \<noteq> 0" by simp
  hence "keys g = (\<oplus>) 0 ` keys f" by (simp add: keys_monom_mult monic_def g)
  also from refl have "\<dots> = (\<lambda>x. x) ` keys f" by (rule image_cong) (simp only: splus_zero)
  finally show "is_monomial g" using \<open>card (keys f) = 1\<close> by (simp only: is_monomial_def image_ident)
qed

end

lemma is_red_reduced_GB_monomial_dgrad_set:
  assumes "finite (component_of_term ` S)" and "pp_of_term ` S \<subseteq> dgrad_set d m"
  shows "is_red (reduced_GB (monomial 1 ` S)) = is_red (monomial (1::'b::field) ` S)"
proof
  fix p
  let ?F = "monomial (1::'b) ` S"
  from assms(1) have 1: "finite (component_of_term ` Keys ?F)" by (simp add: Keys_def)
  moreover from assms(2) have 2: "?F \<subseteq> dgrad_p_set d m" by (auto simp: dgrad_p_set_def)
  moreover have "is_monomial_set ?F" by (auto intro!: is_monomial_setI monomial_is_monomial)
  ultimately have "reduced_GB ?F \<subseteq> monic ` ?F" by (rule reduced_GB_subset_monic_dgrad_p_set)
  also have "\<dots> = ?F" by (auto simp: monic_def intro!: image_eqI)
  finally have 3: "reduced_GB ?F \<subseteq> ?F" .
  show "is_red (reduced_GB ?F) p \<longleftrightarrow> is_red ?F p"
  proof
    assume "is_red (reduced_GB ?F) p"
    thus "is_red ?F p" using 3 by (rule is_red_subset)
  next
    assume "is_red ?F p"
    then obtain f v where "f \<in> ?F" and "v \<in> keys p" and "f \<noteq> 0" and adds1: "lt f adds\<^sub>t v"
      by (rule is_red_addsE)
    from this(1) have "f \<in> pmdl ?F" by (rule pmdl.span_base)
    from dgrad 1 2 have "is_Groebner_basis (reduced_GB ?F)" by (rule reduced_GB_is_GB_dgrad_p_set)
    moreover from \<open>f \<in> pmdl ?F\<close> dgrad 1 2 have "f \<in> pmdl (reduced_GB ?F)"
      by (simp only: reduced_GB_pmdl_dgrad_p_set)
    ultimately obtain g where "g \<in> reduced_GB ?F" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f"
      using \<open>f \<noteq> 0\<close> by (rule GB_adds_lt)
    from this(3) adds1 have "lt g adds\<^sub>t v" by (rule adds_term_trans)
    with \<open>g \<in> reduced_GB ?F\<close> \<open>g \<noteq> 0\<close> \<open>v \<in> keys p\<close> show "is_red (reduced_GB ?F) p"
      by (rule is_red_addsI)
  qed
qed

corollary is_red_reduced_GB_monomial_lt_GB_dgrad_p_set:
  assumes "finite (component_of_term ` Keys G)" and "G \<subseteq> dgrad_p_set d m" and "0 \<notin> G"
  shows "is_red (reduced_GB (monomial (1::'b::field) ` lt ` G)) = is_red G"
proof -
  let ?S = "lt ` G"
  let ?G = "monomial (1::'b) ` ?S"
  from assms(3) have "?S \<subseteq> Keys G" by (auto intro: lt_in_keys in_KeysI)
  hence "component_of_term ` ?S \<subseteq> component_of_term ` Keys G"
    and *: "pp_of_term ` ?S \<subseteq> pp_of_term ` Keys G" by (rule image_mono)+
  from this(1) have "finite (component_of_term ` ?S)" using assms(1) by (rule finite_subset)
  moreover from * have "pp_of_term ` ?S \<subseteq> dgrad_set d m"
  proof (rule subset_trans)
    from assms(2) show "pp_of_term ` Keys G \<subseteq> dgrad_set d m" by (auto simp: dgrad_p_set_def Keys_def)
  qed
  ultimately have "is_red (reduced_GB ?G) = is_red ?G" by (rule is_red_reduced_GB_monomial_dgrad_set)
  also from assms(3) have "\<dots> = is_red G" by (rule is_red_monomial_lt)
  finally show ?thesis .
qed

lemma reduced_GB_monomial_lt_reduced_GB_dgrad_p_set:
  assumes "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "reduced_GB (monomial 1 ` lt ` reduced_GB F) = monomial (1::'b::field) ` lt ` reduced_GB F"
proof (rule reduced_GB_unique)
  let ?G = "reduced_GB F"
  let ?F = "monomial (1::'b) ` lt ` ?G"

  from dgrad assms have "0 \<notin> ?G" and ar: "is_auto_reduced ?G" and "finite ?G"
    by (rule reduced_GB_nonzero_dgrad_p_set, rule reduced_GB_is_auto_reduced_dgrad_p_set,
        rule finite_reduced_GB_dgrad_p_set)
  from this(3) show "finite ?F" by (intro finite_imageI)

  show "is_reduced_GB ?F" unfolding is_reduced_GB_def
  proof (intro conjI monomial_set_is_GB)
    show "is_monomial_set ?F" by (auto intro!: is_monomial_setI monomial_is_monomial)
  next
    show "is_monic_set ?F" by (simp add: is_monic_set_def)
  next
    show "0 \<notin> ?F" by (auto simp: monomial_0_iff)
  next
    show "is_auto_reduced ?F" unfolding is_auto_reduced_def
    proof (intro ballI notI)
      fix f
      assume "f \<in> ?F"
      then obtain g where "g \<in> ?G" and f: "f = monomial 1 (lt g)" by blast
      assume "is_red (?F - {f}) f"
      then obtain f' v where "f' \<in> ?F - {f}" and "v \<in> keys f" and "f' \<noteq> 0" and adds1: "lt f' adds\<^sub>t v"
        by (rule is_red_addsE)
      from this(1) have "f' \<in> ?F" and "f' \<noteq> f" by simp_all
      from this(1) obtain g' where "g' \<in> ?G" and f': "f' = monomial 1 (lt g')" by blast
      from \<open>v \<in> keys f\<close> have v: "v = lt g" by (simp add: f)
      from ar \<open>g \<in> ?G\<close> have "\<not> is_red (?G - {g}) g" by (rule is_auto_reducedD)
      moreover have "is_red (?G - {g}) g"
      proof (rule is_red_addsI)
        from \<open>g' \<in> ?G\<close> \<open>f' \<noteq> f\<close> show "g' \<in> ?G - {g}" by (auto simp: f f')
      next
        from \<open>g' \<in> ?G\<close> \<open>0 \<notin> ?G\<close> show "g' \<noteq> 0" by blast
      next
        from \<open>g \<in> ?G\<close> \<open>0 \<notin> ?G\<close> have "g \<noteq> 0" by blast
        thus "lt g \<in> keys g" by (rule lt_in_keys)
      next
        from adds1 show adds2: "lt g' adds\<^sub>t lt g" by (simp add: v f' lt_monomial)
      qed
      ultimately show False ..
    qed
  qed
qed (fact refl)

end

end (* gd_term *)

end (* theory *)
