(* Author: Alexander Maletzky *)

section \<open>Elimination Property\<close>

theory Elimination_Property
  imports Lex_Order_PP MPoly_PM Groebner_Bases.Syzygy
begin

text \<open>We prove the so-called \<^emph>\<open>elimination property\<close> of Gr\"obner bases: Roughly, if \<open>G\<close> is a
  Gr\"obner basis, then under certain restrictions \<open>G \<inter> P[X]\<close> is a Gr\"obner basis, too. This does
  not only hold for intersections with sets of the form \<open>P[X]\<close>, but also for the component-analog of
  \<open>P[X]\<close> (called \<open>PolysC\<close> below).\<close>

subsection \<open>Eliminating Components\<close>

context gd_term
begin

definition PolysC :: "'k \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) set"
  where "PolysC k = {p. component_of_term ` keys p \<subseteq> {..<k}}"

context
  assumes pot: is_pot_ord
begin

lemma PolysC_I_pot_ord:
  assumes "component_of_term (lt p) < k"
  shows "p \<in> PolysC k"
proof -
  {
    fix u
    assume "u \<in> keys p"
    hence "u \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
    with pot have "component_of_term u \<le> component_of_term (lt p)" by (rule is_pot_ordD2)
    also have "\<dots> < k" by fact
    finally have "component_of_term u < k" .
  }
  thus ?thesis by (auto simp: PolysC_def)
qed

lemma ex_pmdl_Int_PolysC_adds_lt:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "is_Groebner_basis G"
    and "f \<in> pmdl (pmdl G \<inter> PolysC k)" and "f \<noteq> 0"
  shows "\<exists>g\<in>G \<inter> PolysC k. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f"
proof -
  have "pmdl (pmdl G \<inter> PolysC k) \<subseteq> pmdl G" by (rule pmdl.span_subset_spanI) simp
  with assms(4) have "f \<in> pmdl G" ..
  with assms(3, 5) obtain g where "g \<in> G" and "g \<noteq> 0"
    and adds: "lt g adds\<^sub>t lt f" unfolding GB_alt_3_dgrad_p_set[OF assms(1, 2)] by blast
  show ?thesis
  proof (intro bexI conjI)
    from adds have "lt g \<preceq>\<^sub>t lt f" by (rule ord_adds_term)
    with pot have "component_of_term (lt g) \<le> component_of_term (lt f)" by (rule is_pot_ordD2)
    also from assms(4, 5) have "\<dots> < k"
    proof (induct f rule: pmdl_induct)
      case module_0
      thus ?case by simp
    next
      case (module_plus a p c t)
      from module_plus.hyps(3) have "p \<in> PolysC k" ..
      let ?q = "a + monom_mult c t p"
      from module_plus.prems have "lt ?q \<in> keys ?q" by (rule lt_in_keys)
      also have "\<dots> \<subseteq> keys a \<union> keys (monom_mult c t p)" by (rule keys_add_subset)
      finally show ?case
      proof
        assume *: "lt ?q \<in> keys a"
        hence "a \<noteq> 0" by auto
        from * have "lt ?q \<preceq>\<^sub>t lt a" by (rule lt_max_keys)
        with pot have "component_of_term (lt ?q) \<le> component_of_term (lt a)" by (rule is_pot_ordD2)
        also from \<open>a \<noteq> 0\<close> have "\<dots> < k" by (rule module_plus.hyps)
        finally show ?thesis .
      next
        assume "lt ?q \<in> keys (monom_mult c t p)"
        also have "\<dots> \<subseteq> (\<oplus>) t ` keys p" by (rule keys_monom_mult_subset)
        finally have "component_of_term (lt ?q) \<in> component_of_term ` (\<oplus>) t ` keys p" by (rule imageI)
        also have "\<dots> = component_of_term ` keys p" by (simp add: image_image term_simps)
        also from \<open>p \<in> PolysC k\<close> have "\<dots> \<subseteq> {..<k}" by (simp add: PolysC_def)
        finally show ?thesis by simp
      qed
    qed
    finally have "g \<in> PolysC k" by (rule PolysC_I_pot_ord)
    with \<open>g \<in> G\<close> show "g \<in> G \<inter> PolysC k" ..
  qed fact+
qed

lemma pmdl_Int_PolysC_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "is_Groebner_basis G"
  shows "pmdl (G \<inter> PolysC k) = pmdl (pmdl G \<inter> PolysC k)"
  using assms(1)
proof (rule pmdl_eqI_adds_lt_dgrad_p_set')
  have "G \<inter> PolysC k \<subseteq> G" by simp
  also have "\<dots> \<subseteq> dgrad_p_set d m" by fact
  finally show "G \<inter> PolysC k \<subseteq> dgrad_p_set d m" .
next
  show "pmdl (G \<inter> PolysC k) \<subseteq> pmdl (pmdl G \<inter> PolysC k)" by (auto intro!: pmdl.span_base pmdl.span_mono)
next
  fix f
  assume "f \<in> pmdl (pmdl G \<inter> PolysC k)" and "f \<noteq> 0"
  with assms show "\<exists>g\<in>G \<inter> PolysC k. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f" by (rule ex_pmdl_Int_PolysC_adds_lt)
qed

lemma Int_PolysC_isGB_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "is_Groebner_basis G"
  shows "is_Groebner_basis (G \<inter> PolysC k)"
  using assms(1)
proof (rule isGB_I_adds_lt)
  have "G \<inter> PolysC k \<subseteq> G" by simp
  also have "\<dots> \<subseteq> dgrad_p_set d m" by fact
  finally show "G \<inter> PolysC k \<subseteq> dgrad_p_set d m" .
next
  fix f::"'t \<Rightarrow>\<^sub>0 'b"
  assume "f \<noteq> 0"
  assume "f \<in> pmdl (G \<inter> PolysC k)"
  also have "\<dots> \<subseteq> pmdl (pmdl G \<inter> PolysC k)" by (auto intro!: pmdl.span_base pmdl.span_mono)
  finally have "f \<in> pmdl (pmdl G \<inter> PolysC k)" .
  with assms show "\<exists>g\<in>G \<inter> PolysC k. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f" using \<open>f \<noteq> 0\<close>
    by (rule ex_pmdl_Int_PolysC_adds_lt)
qed

lemmas pmdl_Int_PolysC_finite =
  pmdl_Int_PolysC_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas Int_PolysC_isGB_finite =
  Int_PolysC_isGB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

end

end (* gd_term *)

subsection \<open>TOP Orders\<close>

context ordered_term
begin

definition is_top_ord :: bool
  where "is_top_ord \<longleftrightarrow> (\<forall>u v. pp_of_term u \<prec> pp_of_term v \<longrightarrow> u \<prec>\<^sub>t v)"

lemma is_top_ordI: "(\<And>u v. pp_of_term u \<prec> pp_of_term v \<Longrightarrow> u \<prec>\<^sub>t v) \<Longrightarrow> is_top_ord"
  by (simp add: is_top_ord_def)

lemma is_top_ordD: "is_top_ord \<Longrightarrow> pp_of_term u \<prec> pp_of_term v \<Longrightarrow> u \<prec>\<^sub>t v"
  by (simp add: is_top_ord_def)

lemma is_top_ordD2:
  assumes "is_top_ord" and "u \<preceq>\<^sub>t v"
  shows "pp_of_term u \<preceq> pp_of_term v"
proof (rule ccontr)
  assume "\<not> pp_of_term u \<preceq> pp_of_term v"
  hence "pp_of_term v \<prec> pp_of_term u" by simp
  with assms(1) have "v \<prec>\<^sub>t u" by (rule is_top_ordD)
  with assms(2) show False by simp
qed

lemma is_top_ord:
  assumes "is_top_ord"
  shows "u \<preceq>\<^sub>t v \<longleftrightarrow> (pp_of_term u \<prec> pp_of_term v \<or>
                    (pp_of_term u = pp_of_term v \<and> component_of_term u \<le> component_of_term v))"
      (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  with assms have "pp_of_term u \<preceq> pp_of_term v" by (rule is_top_ordD2)
  hence "pp_of_term u \<prec> pp_of_term v \<or> pp_of_term u = pp_of_term v" by auto
  thus ?r
  proof
    assume "pp_of_term u \<prec> pp_of_term v"
    thus ?r ..
  next
    assume 1: "pp_of_term u = pp_of_term v"
    moreover have "component_of_term u \<le> component_of_term v"
    proof (rule ccontr)
      assume "\<not> component_of_term u \<le> component_of_term v"
      hence 2: "component_of_term v \<le> component_of_term u"
        and 3: "component_of_term u \<noteq> component_of_term v" by simp_all
      from 1 have "pp_of_term v \<preceq> pp_of_term u" by simp
      hence "v \<preceq>\<^sub>t u" using 2 by (rule ord_termI)
      with \<open>?l\<close> have "u = v" by simp
      with 3 show False by simp
    qed
    ultimately show ?r by simp
  qed
next
  assume ?r
  thus ?l
  proof
    assume "pp_of_term u \<prec> pp_of_term v"
    with assms have "u \<prec>\<^sub>t v" by (rule is_top_ordD)
    thus ?l by simp
  next
    assume "pp_of_term u = pp_of_term v \<and> component_of_term u \<le> component_of_term v"
    hence "pp_of_term u \<preceq> pp_of_term v" and "component_of_term u \<le> component_of_term v" by simp_all
    thus ?l by (rule ord_termI)
  qed
qed

end (* ordered_term *)

subsection \<open>Elimination Orders\<close>

definition is_elim_ord :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool) \<Rightarrow> 'x set \<Rightarrow> bool"
  where "is_elim_ord ord X \<longleftrightarrow> (\<forall>s t. s \<in> .[X] \<longrightarrow> ord t s \<longrightarrow> t \<in> .[X])"

lemma is_elim_ordI: "(\<And>s t. s \<in> .[X] \<Longrightarrow> ord t s \<Longrightarrow> t \<in> .[X]) \<Longrightarrow> is_elim_ord ord X"
  by (simp add: is_elim_ord_def)

lemma is_elim_ordD: "is_elim_ord ord X \<Longrightarrow> s \<in> .[X] \<Longrightarrow> ord t s \<Longrightarrow> t \<in> .[X]"
  by (simp add: is_elim_ord_def)

lemma is_elim_ord_UNIV: "is_elim_ord ord UNIV"
  by (simp add: is_elim_ord_def PPs_def)

lemma lex_is_elim_ord: "is_elim_ord (lex_pm::('x::linorder \<Rightarrow>\<^sub>0 nat) \<Rightarrow> _) {x..}"
proof (intro is_elim_ordI PPsI subsetI)
  fix s t :: "'x \<Rightarrow>\<^sub>0 nat" and y
  assume "lex_pm t s" and "y \<in> keys t"
  then obtain z where "z \<in> keys s" and "z \<le> y" by (rule lex_pm_keys_leE)
  moreover assume "s \<in> .[{x..}]"
  ultimately show "y \<in> {x..}" by (auto dest!: PPsD)
qed

lemma lex_is_elim_ord': "is_elim_ord (lex_pm::('x::linorder \<Rightarrow>\<^sub>0 nat) \<Rightarrow> _) {x<..}"
proof (intro is_elim_ordI PPsI subsetI)
  fix s t :: "'x \<Rightarrow>\<^sub>0 nat" and y
  assume "lex_pm t s" and "y \<in> keys t"
  then obtain z where "z \<in> keys s" and "z \<le> y" by (rule lex_pm_keys_leE)
  moreover assume "s \<in> .[{x<..}]"
  ultimately show "y \<in> {x<..}" by (auto dest!: PPsD)
qed

subsection \<open>Eliminating Indeterminates\<close>

locale pm_term =
  ordered_term pair_of_term term_of_pair ord ord_strict ord_term ord_term_strict
  for pair_of_term::"'t \<Rightarrow> (('x::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<times> 'k::{the_min,wellorder})"
  and term_of_pair::"(('x \<Rightarrow>\<^sub>0 nat) \<times> 'k) \<Rightarrow> 't"
  and ord :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
  and ord_term::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<preceq>\<^sub>t" 50)
  and ord_term_strict::"'t \<Rightarrow> 't \<Rightarrow> bool" (infixl "\<prec>\<^sub>t" 50)
begin

sublocale gd_term ..

definition PolysV :: "'x set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) set"
  where "PolysV X = {p. pp_of_term ` keys p \<subseteq> .[X]}"

lemma dgrad_p_set_varnum_wrt_PolysV: "dgrad_p_set (varnum_wrt X) 0 = PolysV X"
  by (simp add: dgrad_p_set_def dgrad_set_varnum_wrt PolysV_def)

context
  fixes Y :: "'x set"
  assumes top: is_top_ord
  assumes elim: "is_elim_ord (\<preceq>) Y"
  assumes fin: "finite Y"
begin

lemma PolysV_I_top_ord:
  assumes "lp p \<in> .[Y]"
  shows "p \<in> PolysV Y"
proof -
  {
    fix u
    assume "u \<in> keys p"
    hence "u \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
    note elim assms
    moreover from top \<open>u \<preceq>\<^sub>t lt p\<close> have "pp_of_term u \<preceq> lp p" by (rule is_top_ordD2)
    ultimately have "pp_of_term u \<in> .[Y]" by (rule is_elim_ordD)
  }
  thus ?thesis by (auto simp: PolysV_def)
qed

lemma ex_pmdl_Int_PolysV_adds_lt:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "is_Groebner_basis G"
    and "f \<in> PolysV Y" and "f \<in> pmdl (pmdl G \<inter> PolysV Y)" and "f \<noteq> 0"
  shows "\<exists>g\<in>G \<inter> PolysV Y. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f"
proof -
  have "pmdl (pmdl G \<inter> PolysV Y) \<subseteq> pmdl G" by (rule pmdl.span_subset_spanI) simp
  with assms(5) have "f \<in> pmdl G" ..
  with assms(3, 6) obtain g where "g \<in> G" and "g \<noteq> 0"
    and adds: "lt g adds\<^sub>t lt f" unfolding GB_alt_3_dgrad_p_set[OF assms(1, 2)] by blast
  show ?thesis
  proof (intro bexI conjI)
    from adds have "lt g \<preceq>\<^sub>t lt f" by (rule ord_adds_term)
    note elim
    moreover from assms(4, 6) have "lp f \<in> .[Y]" by (auto simp: PolysV_def dest: lt_in_keys)
    moreover from top \<open>lt g \<preceq>\<^sub>t lt f\<close> have "lp g \<preceq> lp f" by (rule is_top_ordD2)
    ultimately have "lp g \<in> .[Y]" by (rule is_elim_ordD)
    hence "g \<in> PolysV Y" by (rule PolysV_I_top_ord)
    with \<open>g \<in> G\<close> show "g \<in> G \<inter> PolysV Y" ..
  qed fact+
qed

lemma pmdl_Int_PolysV_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "is_Groebner_basis G"
  shows "pmdl (G \<inter> PolysV Y) = pmdl (pmdl G \<inter> PolysV Y)"
  using dickson_grading_varnum_wrt[OF fin]
proof (rule pmdl_eqI_adds_lt_dgrad_p_set)
  show "G \<inter> PolysV Y \<subseteq> dgrad_p_set (varnum_wrt Y) 0"
    and "pmdl G \<inter> PolysV Y \<subseteq> dgrad_p_set (varnum_wrt Y) 0" by (simp_all add: dgrad_p_set_varnum_wrt_PolysV)
next
  show "pmdl (G \<inter> PolysV Y) \<subseteq> pmdl (pmdl G \<inter> PolysV Y)" by (auto intro!: pmdl.span_base pmdl.span_mono)
next
  fix f :: "'t \<Rightarrow>\<^sub>0 'a"
  assume "f \<in> dgrad_p_set (varnum_wrt Y) 0"
  hence "f \<in> PolysV Y" by (simp only: dgrad_p_set_varnum_wrt_PolysV)
  assume "f \<in> pmdl (pmdl G \<inter> PolysV Y)" and "f \<noteq> 0"
  with assms \<open>f \<in> PolysV Y\<close> show "\<exists>g\<in>G \<inter> PolysV Y. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f"
    by (rule ex_pmdl_Int_PolysV_adds_lt)
qed

lemma Int_PolysV_isGB_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "is_Groebner_basis G"
  shows "is_Groebner_basis (G \<inter> PolysV Y)"
  using dickson_grading_varnum_wrt[OF fin]
proof (rule isGB_I_adds_lt)
  show "G \<inter> PolysV Y \<subseteq> dgrad_p_set (varnum_wrt Y) 0" by (simp add: dgrad_p_set_varnum_wrt_PolysV)
next
  fix f::"'t \<Rightarrow>\<^sub>0 'a"
  assume "f \<noteq> 0"
  assume "f \<in> dgrad_p_set (varnum_wrt Y) 0"
  hence "f \<in> PolysV Y" by (simp only: dgrad_p_set_varnum_wrt_PolysV)
  assume "f \<in> pmdl (G \<inter> PolysV Y)"
  also have "\<dots> \<subseteq> pmdl (pmdl G \<inter> PolysV Y)" by (auto intro!: pmdl.span_base pmdl.span_mono)
  finally have "f \<in> pmdl (pmdl G \<inter> PolysV Y)" .
  with assms \<open>f \<in> PolysV Y\<close> show "\<exists>g\<in>G \<inter> PolysV Y. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f" using \<open>f \<noteq> 0\<close>
    by (rule ex_pmdl_Int_PolysV_adds_lt)
qed

lemmas pmdl_Int_PolysV_PolysV =
  pmdl_Int_PolysV_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt_PolysV]
lemmas Int_PolysV_isGB_PolysV =
  Int_PolysV_isGB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt_PolysV]

lemmas pmdl_Int_PolysV_finite =
  pmdl_Int_PolysV_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas Int_PolysV_isGB_finite =
  Int_PolysV_isGB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

end

end (* pm_term *)

subsection \<open>Translating Results into @{locale pm_powerprod}\<close>

context pm_powerprod
begin

sublocale punit: pm_term to_pair_unit fst "(\<preceq>)" "(\<prec>)" "(\<preceq>)" "(\<prec>)" ..

lemma PolysV_eq_Polys [simp]: "punit.PolysV X = P[X]"
  by (simp add: punit.PolysV_def Polys_def)

lemma punit_is_top_ord: "punit.is_top_ord"
  by (simp add: punit.is_top_ord_def)

lemmas ideal_Int_Polys_Polys =
  punit.pmdl_Int_PolysV_PolysV[OF punit_is_top_ord, simplified]
lemmas Int_Polys_isGB_Polys =
  punit.Int_PolysV_isGB_PolysV[OF punit_is_top_ord, simplified]
lemmas ideal_Int_Polys_finite =
  punit.pmdl_Int_PolysV_finite[OF punit_is_top_ord, simplified]
lemmas Int_Polys_isGB_finite =
  punit.Int_PolysV_isGB_finite[OF punit_is_top_ord, simplified]

end (* pm_powerprod *)

end (* theory *)
