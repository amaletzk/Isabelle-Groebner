(* Author: Alexander Maletzky *)

section \<open>Hilbert's Nullstellensatz\<close>

theory Nullstellensatz
  imports "HOL-Computational_Algebra.Fundamental_Theorem_Algebra" Univariate_PM
begin

text \<open>We prove the geometric version of Hilbert's Nullstellensatz, i.e. the precise correspondence
  between algebraic varieties and radical ideals.\<close>

subsection \<open>Preliminaries\<close>

context gd_term
begin

lemma ord_term_minimum_dgrad_set:
  assumes "dickson_grading d" and "v \<in> V" and "pp_of_term ` V \<subseteq> dgrad_set d m"
  obtains u where "u \<in> V" and "\<And>w. w \<prec>\<^sub>t u \<Longrightarrow> w \<notin> V"
proof -
  from assms(1) have "wfP (dickson_less_v d m)" by (rule wf_dickson_less_v)
  then obtain u where "u \<in> V" and *: "\<And>w. dickson_less_v d m w u \<Longrightarrow> w \<notin> V" using assms(2)
    by (rule wfE_min[to_pred]) blast
  from this(1) have "pp_of_term u \<in> pp_of_term ` V" by (rule imageI)
  with assms(3) have "pp_of_term u \<in> dgrad_set d m" ..
  hence "d (pp_of_term u) \<le> m" by (rule dgrad_setD)
  from \<open>u \<in> V\<close> show ?thesis
  proof
    fix w
    assume "w \<prec>\<^sub>t u"
    show "w \<notin> V"
    proof
      assume "w \<in> V"
      hence "pp_of_term w \<in> pp_of_term ` V" by (rule imageI)
      with assms(3) have "pp_of_term w \<in> dgrad_set d m" ..
      hence "d (pp_of_term w) \<le> m" by (rule dgrad_setD)
      from this \<open>d (pp_of_term u) \<le> m\<close> \<open>w \<prec>\<^sub>t u\<close> have "dickson_less_v d m w u"
        by (rule dickson_less_vI)
      hence "w \<notin> V" by (rule *)
      from this \<open>w \<in> V\<close> show False ..
    qed
  qed
qed

definition spoly_rep :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> bool"
  where "spoly_rep d m G g1 g2 \<longleftrightarrow> (\<exists>q. spoly g1 g2 = (\<Sum>g\<in>G. q g \<odot> g) \<and>
                (\<forall>g. q g \<in> punit.dgrad_p_set d m \<and>
                        (q g \<odot> g \<noteq> 0 \<longrightarrow> lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2),
                                                                      component_of_term (lt g2)))))"

lemma spoly_repI:
  "spoly g1 g2 = (\<Sum>g\<in>G. q g \<odot> g) \<Longrightarrow> (\<And>g. q g \<in> punit.dgrad_p_set d m) \<Longrightarrow>
    (\<And>g. q g \<odot> g \<noteq> 0 \<Longrightarrow> lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2),
                                                        component_of_term (lt g2))) \<Longrightarrow>
    spoly_rep d m G g1 g2"
  by (auto simp: spoly_rep_def)

lemma spoly_repI_zero:
  assumes "spoly g1 g2 = 0"
  shows "spoly_rep d m G g1 g2"
proof (rule spoly_repI)
  show "spoly g1 g2 = (\<Sum>g\<in>G. 0 \<odot> g)" by (simp add: assms)
qed (simp_all add: punit.zero_in_dgrad_p_set)

lemma spoly_repE:
  assumes "spoly_rep d m G g1 g2"
  obtains q where "spoly g1 g2 = (\<Sum>g\<in>G. q g \<odot> g)" and "\<And>g. q g \<in> punit.dgrad_p_set d m"
    and "\<And>g. q g \<odot> g \<noteq> 0 \<Longrightarrow> lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2),
                                                             component_of_term (lt g2))"
  using assms by (auto simp: spoly_rep_def)

lemma red_rtrancl_repE:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "finite G" and "p \<in> dgrad_p_set d m"
    and "(red G)\<^sup>*\<^sup>* p r"
  obtains q where "p = r + (\<Sum>g\<in>G. q g \<odot> g)" and "\<And>g. q g \<in> punit.dgrad_p_set d m"
    and "\<And>g. lt (q g \<odot> g) \<preceq>\<^sub>t lt p"
  using assms(5)
proof (induct r arbitrary: thesis)
  case base
  show ?case
  proof (rule base)
    show "p = p + (\<Sum>g\<in>G. 0 \<odot> g)" by simp
  qed (simp_all add: punit.zero_in_dgrad_p_set min_term_min)
next
  case (step r' r)
  from step.hyps(2) obtain g t where "g \<in> G" and rs: "red_single r' r g t" by (rule red_setE)
  from this(2) have "r' = r + monomial (lookup r' (t \<oplus> lt g) / lc g) t \<odot> g"
    by (simp add: red_single_def mult_scalar_monomial)
  moreover define q0 where "q0 = monomial (lookup r' (t \<oplus> lt g) / lc g) t"
  ultimately have r': "r' = r + q0 \<odot> g" by simp
  obtain q' where p: "p = r' + (\<Sum>g\<in>G. q' g \<odot> g)" and 1: "\<And>g. q' g \<in> punit.dgrad_p_set d m"
    and 2: "\<And>g. lt (q' g \<odot> g) \<preceq>\<^sub>t lt p" by (rule step.hyps) blast
  define q where "q = q'(g := q0 + q' g)"
  show ?case
  proof (rule step.prems)
    from assms(3) \<open>g \<in> G\<close> have "p = (r + q0 \<odot> g) + (q' g \<odot> g + (\<Sum>g\<in>G - {g}. q' g \<odot> g))"
      by (simp add: p r' sum.remove)
    also have "\<dots> = r + (q g \<odot> g + (\<Sum>g\<in>G - {g}. q' g \<odot> g))"
      by (simp add: q_def mult_scalar_distrib_right)
    also from refl have "(\<Sum>g\<in>G - {g}. q' g \<odot> g) = (\<Sum>g\<in>G - {g}. q g \<odot> g)"
      by (rule sum.cong) (simp add: q_def)
    finally show "p = r + (\<Sum>g\<in>G. q g \<odot> g)" using assms(3) \<open>g \<in> G\<close> by (simp only: sum.remove)
  next
    fix g0
    have "q g0 \<in> punit.dgrad_p_set d m \<and> lt (q g0 \<odot> g0) \<preceq>\<^sub>t lt p"
    proof (cases "g0 = g")
      case True
      have eq: "q g = q0 + q' g" by (simp add: q_def)
      show ?thesis unfolding True eq
      proof
        from assms(1, 2, 4) step.hyps(1) have "r' \<in> dgrad_p_set d m"
          by (rule dgrad_p_set_closed_red_rtrancl)
        with assms(1) have "d t \<le> m" using rs by (rule dgrad_p_set_red_single_pp)
        hence "q0 \<in> punit.dgrad_p_set d m" by (simp add: q0_def punit.dgrad_p_set_def dgrad_set_def)
        thus "q0 + q' g \<in> punit.dgrad_p_set d m" by (intro punit.dgrad_p_set_closed_plus 1)
      next
        have "lt (q0 \<odot> g + q' g \<odot> g) \<preceq>\<^sub>t ord_term_lin.max (lt (q0 \<odot> g)) (lt (q' g \<odot> g))"
          by (fact lt_plus_le_max)
        also have "\<dots> \<preceq>\<^sub>t lt p"
        proof (intro ord_term_lin.max.boundedI 2)
          have "lt (q0 \<odot> g) \<preceq>\<^sub>t t \<oplus> lt g" by (simp add: q0_def mult_scalar_monomial lt_monom_mult_le)
          also from rs have "\<dots> \<preceq>\<^sub>t lt r'" by (intro lt_max) (simp add: red_single_def)
          also from step.hyps(1) have "\<dots> \<preceq>\<^sub>t lt p" by (intro ord_p_lt red_rtrancl_ord)
          finally show "lt (q0 \<odot> g) \<preceq>\<^sub>t lt p" .
        qed
        finally show "lt ((q0 + q' g) \<odot> g) \<preceq>\<^sub>t lt p" by (simp only: mult_scalar_distrib_right)
      qed
    next
      case False
      hence "q g0 = q' g0" by (simp add: q_def)
      thus ?thesis by (simp add: 1 2)
    qed
    thus "q g0 \<in> punit.dgrad_p_set d m" and "lt (q g0 \<odot> g0) \<preceq>\<^sub>t lt p" by simp_all
  qed
qed

corollary isGB_D_spoly_rep:
  assumes "dickson_grading d" and "is_Groebner_basis G" and "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "g1 \<in> G" and "g2 \<in> G" and "g1 \<noteq> 0" and "g2 \<noteq> 0"
  shows "spoly_rep d m G g1 g2"
proof (cases "spoly g1 g2 = 0")
  case True
  thus ?thesis by (rule spoly_repI_zero)
next
  case False
  let ?v = "term_of_pair (lcs (lp g1) (lp g2), component_of_term (lt g1))"
  let ?h = "crit_pair g1 g2"
  from assms(7, 8) have eq: "spoly g1 g2 = fst ?h + (- snd ?h)" by (simp add: spoly_alt)
  have "fst ?h \<prec>\<^sub>p monomial 1 ?v" by (fact fst_crit_pair_below_lcs)
  hence d1: "fst ?h = 0 \<or> lt (fst ?h) \<prec>\<^sub>t ?v" by (simp only: ord_strict_p_monomial_iff)
  have "snd ?h \<prec>\<^sub>p monomial 1 ?v" by (fact snd_crit_pair_below_lcs)
  hence d2: "snd ?h = 0 \<or> lt (- snd ?h) \<prec>\<^sub>t ?v" by (simp only: ord_strict_p_monomial_iff lt_uminus)
  note assms(1)
  moreover from assms(5, 3) have "g1 \<in> dgrad_p_set d m" ..
  moreover from assms(6, 3) have "g2 \<in> dgrad_p_set d m" ..
  ultimately have "spoly g1 g2 \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_spoly)
  from assms(5) have "g1 \<in> pmdl G" by (rule pmdl.span_base)
  moreover from assms(6) have "g2 \<in> pmdl G" by (rule pmdl.span_base)
  ultimately have "spoly g1 g2 \<in> pmdl G" by (rule pmdl_closed_spoly)
  with assms(2) have "(red G)\<^sup>*\<^sup>* (spoly g1 g2) 0" by (rule GB_imp_zero_reducibility)
  with assms(1, 3, 4) \<open>spoly _ _ \<in> dgrad_p_set _ _\<close> obtain q
    where 1: "spoly g1 g2 = 0 + (\<Sum>g\<in>G. q g \<odot> g)" and 2: "\<And>g. q g \<in> punit.dgrad_p_set d m"
      and "\<And>g. lt (q g \<odot> g) \<preceq>\<^sub>t lt (spoly g1 g2)" by (rule red_rtrancl_repE) blast
  show ?thesis
  proof (rule spoly_repI)
    fix g
    note \<open>lt (q g \<odot> g) \<preceq>\<^sub>t lt (spoly g1 g2)\<close>
    also from d1 have "lt (spoly g1 g2) \<prec>\<^sub>t ?v"
    proof
      assume "fst ?h = 0"
      hence eq: "spoly g1 g2 = - snd ?h" by (simp add: eq)
      also from d2 have "lt \<dots> \<prec>\<^sub>t ?v"
      proof
        assume "snd ?h = 0"
        with False show ?thesis by (simp add: eq)
      qed
      finally show ?thesis .
    next
      assume *: "lt (fst ?h) \<prec>\<^sub>t ?v"
      from d2 show ?thesis
      proof
        assume "snd ?h = 0"
        with * show ?thesis by (simp add: eq)
      next
        assume **: "lt (- snd ?h) \<prec>\<^sub>t ?v"
        have "lt (spoly g1 g2) \<preceq>\<^sub>t ord_term_lin.max (lt (fst ?h)) (lt (- snd ?h))" unfolding eq
          by (fact lt_plus_le_max)
        also from * ** have "\<dots> \<prec>\<^sub>t ?v" by (simp only: ord_term_lin.max_less_iff_conj)
        finally show ?thesis .
      qed
    qed
    also from False have "\<dots> = term_of_pair (lcs (lp g1) (lp g2), component_of_term (lt g2))"
      by (simp add: spoly_def Let_def split: if_split_asm)
    finally show "lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2), component_of_term (lt g2))" .
  qed (simp_all add: 1 2)
qed

text \<open>The finiteness assumption on \<open>G\<close> in the following theorem could be dropped, but it makes the
  proof a lot easier (although it is still fairly complicated).\<close>

lemma isGB_I_spoly_rep:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "\<And>g1 g2. g1 \<in> G \<Longrightarrow> g2 \<in> G \<Longrightarrow> g1 \<noteq> 0 \<Longrightarrow> g2 \<noteq> 0 \<Longrightarrow> spoly g1 g2 \<noteq> 0 \<Longrightarrow> spoly_rep d m G g1 g2"
  shows "is_Groebner_basis G"
proof (rule ccontr)
  assume "\<not> is_Groebner_basis G"
  then obtain p where "p \<in> pmdl G" and p_in: "p \<in> dgrad_p_set d m" and "\<not> (red G)\<^sup>*\<^sup>* p 0"
    by (auto simp: GB_alt_1_dgrad_p_set[OF assms(1, 2)])
  from \<open>\<not> is_Groebner_basis G\<close> have "G \<noteq> {}" by (auto simp: is_Groebner_basis_empty)

  obtain r where p_red: "(red G)\<^sup>*\<^sup>* p r" and r_irred: "\<not> is_red G r"
  proof -
    define A where "A = {q. (red G)\<^sup>*\<^sup>* p q}"
    from assms(1, 2) have "wfP (red G)\<inverse>\<inverse>" by (rule red_wf_dgrad_p_set)
    moreover have "p \<in> A" by (simp add: A_def)
    ultimately obtain r where "r \<in> A" and r_min: "\<And>z. (red G)\<inverse>\<inverse> z r \<Longrightarrow> z \<notin> A"
      by (rule wfE_min[to_pred]) blast
    show ?thesis
    proof
      from \<open>r \<in> A\<close> show *: "(red G)\<^sup>*\<^sup>* p r" by (simp add: A_def)

      show "\<not> is_red G r"
      proof
        assume "is_red G r"
        then obtain z where "(red G) r z" by (rule is_redE)
        hence "(red G)\<inverse>\<inverse> z r" by simp
        hence "z \<notin> A" by (rule r_min)
        hence "\<not> (red G)\<^sup>*\<^sup>* p z" by (simp add: A_def)
        moreover from * \<open>(red G) r z\<close> have "(red G)\<^sup>*\<^sup>* p z" ..
        ultimately show False ..
      qed
    qed
  qed
  from assms(1, 2) p_in p_red have r_in: "r \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red_rtrancl)
  from p_red \<open>\<not> (red G)\<^sup>*\<^sup>* p 0\<close> have "r \<noteq> 0" by blast
  from p_red have "p - r \<in> pmdl G" by (rule red_rtranclp_diff_in_pmdl)
  with \<open>p \<in> pmdl G\<close> have "p - (p - r) \<in> pmdl G" by (rule pmdl.span_diff)
  hence "r \<in> pmdl G" by simp
  with assms(3) obtain q0 where r: "r = (\<Sum>g\<in>G. q0 g \<odot> g)" by (rule pmdl.span_finiteE)
  from assms(3) have "finite (q0 ` G)" by (rule finite_imageI)
  then obtain m0 where "q0 ` G \<subseteq> punit.dgrad_p_set d m0" by (rule punit.dgrad_p_set_exhaust)
  define m' where "m' = ord_class.max m m0"
  have "dgrad_p_set d m \<subseteq> dgrad_p_set d m'" by (rule dgrad_p_set_subset) (simp add: m'_def)
  with assms(2) have G_sub: "G \<subseteq> dgrad_p_set d m'" by (rule subset_trans)
  have "punit.dgrad_p_set d m0 \<subseteq> punit.dgrad_p_set d m'"
    by (rule punit.dgrad_p_set_subset) (simp add: m'_def)
  with \<open>q0 ` G \<subseteq> _\<close> have "q0 ` G \<subseteq> punit.dgrad_p_set d m'" by (rule subset_trans)

  define mlt where "mlt = (\<lambda>q. ord_term_lin.Max (lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}))"
  define mnum where "mnum = (\<lambda>q. card {g\<in>G. q g \<odot> g \<noteq> 0 \<and> lt (q g \<odot> g) = mlt q})"
  define rel where "rel = (\<lambda>q1 q2. mlt q1 \<prec>\<^sub>t mlt q2 \<or> (mlt q1 = mlt q2 \<and> mnum q1 < mnum q2))"
  define rel_dom where "rel_dom = {q. q ` G \<subseteq> punit.dgrad_p_set d m' \<and> r = (\<Sum>g\<in>G. q g \<odot> g)}"

  have mlt_in: "mlt q \<in> lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}" if "q \<in> rel_dom" for q
    unfolding mlt_def
  proof (rule ord_term_lin.Max_in, simp_all add: assms(3), rule ccontr)
    assume "\<nexists>g. g \<in> G \<and> q g \<odot> g \<noteq> 0"
    hence "q g \<odot> g = 0" if "g \<in> G" for g using that by simp
    with that have "r = 0" by (simp add: rel_dom_def)
    with \<open>r \<noteq> 0\<close> show False ..
  qed
  
  have rel_dom_dgrad_set: "pp_of_term ` mlt ` rel_dom \<subseteq> dgrad_set d m'"
  proof (rule subsetI, elim imageE)
    fix q v t
    assume "q \<in> rel_dom" and v: "v = mlt q" and t: "t = pp_of_term v"
    from this(1) have "v \<in> lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}" unfolding v by (rule mlt_in)
    then obtain g where "g \<in> G" and "q g \<odot> g \<noteq> 0" and v: "v = lt (q g \<odot> g)" by blast
    from this(2) have "q g \<noteq> 0" and "g \<noteq> 0" by auto
    hence "v = lpp (q g) \<oplus> lt g" unfolding v by (rule lt_mult_scalar)
    hence "t = lpp (q g) + lp g" by (simp add: t pp_of_term_splus)
    also from assms(1) have "d \<dots> = ord_class.max (d (lpp (q g))) (d (lp g))"
      by (rule dickson_gradingD1)
    also have "\<dots> \<le> m'"
    proof (rule max.boundedI)
      from \<open>g \<in> G\<close> \<open>q \<in> rel_dom\<close> have "q g \<in> punit.dgrad_p_set d m'" by (auto simp: rel_dom_def)
      moreover from \<open>q g \<noteq> 0\<close> have "lpp (q g) \<in> keys (q g)" by (rule punit.lt_in_keys)
      ultimately show "d (lpp (q g)) \<le> m'" by (rule punit.dgrad_p_setD[simplified])
    next
      from \<open>g \<in> G\<close> G_sub have "g \<in> dgrad_p_set d m'" ..
      moreover from \<open>g \<noteq> 0\<close> have "lt g \<in> keys g" by (rule lt_in_keys)
      ultimately show "d (lp g) \<le> m'" by (rule dgrad_p_setD)
    qed
    finally show "t \<in> dgrad_set d m'" by (simp add: dgrad_set_def)
  qed

  obtain q where "q \<in> rel_dom" and q_min: "\<And>q'. rel q' q \<Longrightarrow> q' \<notin> rel_dom"
  proof -
    from \<open>q0 ` G \<subseteq> punit.dgrad_p_set d m'\<close> have "q0 \<in> rel_dom" by (simp add: rel_dom_def r)
    hence "mlt q0 \<in> mlt ` rel_dom" by (rule imageI)
    with assms(1) obtain u where "u \<in> mlt ` rel_dom" and u_min: "\<And>w. w \<prec>\<^sub>t u \<Longrightarrow> w \<notin> mlt ` rel_dom"
      using rel_dom_dgrad_set by (rule ord_term_minimum_dgrad_set) blast
    from this(1) obtain q' where "q' \<in> rel_dom" and u: "u = mlt q'" ..
    hence "q' \<in> rel_dom \<inter> {q. mlt q = u}" (is "_ \<in> ?A") by simp
    hence "mnum q' \<in> mnum ` ?A" by (rule imageI)
    with wf[to_pred] obtain k where "k \<in> mnum ` ?A" and k_min: "\<And>l. l < k \<Longrightarrow> l \<notin> mnum ` ?A"
      by (rule wfE_min[to_pred]) blast
    from this(1) obtain q'' where "q'' \<in> rel_dom" and mlt'': "mlt q'' = u" and k: "k = mnum q''"
      by blast
    from this(1) show ?thesis
    proof
      fix q0
      assume "rel q0 q''"
      show "q0 \<notin> rel_dom"
      proof
        assume "q0 \<in> rel_dom"
        from \<open>rel q0 q''\<close> show False unfolding rel_def
        proof (elim disjE conjE)
          assume "mlt q0 \<prec>\<^sub>t mlt q''"
          hence "mlt q0 \<notin> mlt ` rel_dom" unfolding mlt'' by (rule u_min)
          moreover from \<open>q0 \<in> rel_dom\<close> have "mlt q0 \<in> mlt ` rel_dom" by (rule imageI)
          ultimately show ?thesis ..
        next
          assume "mlt q0 = mlt q''"
          with \<open>q0 \<in> rel_dom\<close> have "q0 \<in> ?A" by (simp add: mlt'')
          assume "mnum q0 < mnum q''"
          hence "mnum q0 \<notin> mnum ` ?A" unfolding k[symmetric] by (rule k_min)
          with \<open>q0 \<in> ?A\<close> show ?thesis by blast
        qed
      qed
    qed
  qed
  from this(1) have q_in: "\<And>g. g \<in> G \<Longrightarrow> q g \<in> punit.dgrad_p_set d m'"
    and r: "r = (\<Sum>g\<in>G. q g \<odot> g)" by (auto simp: rel_dom_def)

  define v where "v = mlt q"
  from \<open>q \<in> rel_dom\<close> have "v \<in> lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}" unfolding v_def
    by (rule mlt_in)
  then obtain g1 where "g1 \<in> G" and "q g1 \<odot> g1 \<noteq> 0" and v1: "v = lt (q g1 \<odot> g1)" by blast
  moreover define M where "M = {g\<in>G. q g \<odot> g \<noteq> 0 \<and> lt (q g \<odot> g) = v}"
  ultimately have "g1 \<in> M" by simp
  have v_max: "lt (q g \<odot> g) \<prec>\<^sub>t v" if "g \<in> G" and "g \<notin> M" and "q g \<odot> g \<noteq> 0" for g
  proof -
    from that have "lt (q g \<odot> g) \<noteq> v" by (auto simp: M_def)
    moreover have "lt (q g \<odot> g) \<preceq>\<^sub>t v" unfolding v_def mlt_def
      by (rule ord_term_lin.Max_ge) (auto simp: assms(3) \<open>q g \<odot> g \<noteq> 0\<close> intro!: imageI \<open>g \<in> G\<close>)
    ultimately show ?thesis by simp
  qed
  from \<open>q g1 \<odot> g1 \<noteq> 0\<close> have "q g1 \<noteq> 0" and "g1 \<noteq> 0" by auto
  hence v1': "v = lpp (q g1) \<oplus> lt g1" unfolding v1 by (rule lt_mult_scalar)
  have "M - {g1} \<noteq> {}"
  proof
    assume "M - {g1} = {}"
    have "v \<in> keys (q g1 \<odot> g1)" unfolding v1 using \<open>q g1 \<odot> g1 \<noteq> 0\<close> by (rule lt_in_keys)
    moreover have "v \<notin> keys (\<Sum>g\<in>G-{g1}. q g \<odot> g)"
    proof
      assume "v \<in> keys (\<Sum>g\<in>G-{g1}. q g \<odot> g)"
      also have "\<dots> \<subseteq> (\<Union>g\<in>G-{g1}. keys (q g \<odot> g))" by (fact keys_sum_subset)
      finally obtain g where "g \<in> G - {g1}" and "v \<in> keys (q g \<odot> g)" ..
      from this(2) have "q g \<odot> g \<noteq> 0" and "v \<preceq>\<^sub>t lt (q g \<odot> g)" by (auto intro: lt_max_keys)
      from \<open>g \<in> G - {g1}\<close> \<open>M - {g1} = {}\<close> have "g \<in> G" and "g \<notin> M" by blast+
      hence "lt (q g \<odot> g) \<prec>\<^sub>t v" by (rule v_max) fact
      with \<open>v \<preceq>\<^sub>t _\<close> show False by simp
    qed
    ultimately have "v \<in> keys (q g1 \<odot> g1 + (\<Sum>g\<in>G-{g1}. q g \<odot> g))" by (rule in_keys_plusI1)
    also from \<open>g1 \<in> G\<close> assms(3) have "\<dots> = keys r" by (simp add: r sum.remove)
    finally have "v \<in> keys r" .
    with \<open>g1 \<in> G\<close> \<open>g1 \<noteq> 0\<close> have "is_red G r" by (rule is_red_addsI) (simp add: v1' term_simps)
    with r_irred show False ..
  qed
  then obtain g2 where "g2 \<in> M" and "g1 \<noteq> g2" by blast
  from this(1) have "g2 \<in> G" and "q g2 \<odot> g2 \<noteq> 0" and v2: "v = lt (q g2 \<odot> g2)" by (simp_all add: M_def)
  from this(2) have "q g2 \<noteq> 0" and "g2 \<noteq> 0" by auto
  hence v2': "v = lpp (q g2) \<oplus> lt g2" unfolding v2 by (rule lt_mult_scalar)
  hence "component_of_term (lpp (q g1) \<oplus> lt g1) = component_of_term (lpp (q g2) \<oplus> lt g2)"
    by (simp only: v1' flip: v2')
  hence cmp_eq: "component_of_term (lt g1) = component_of_term (lt g2)" by (simp add: term_simps)

  have "M \<subseteq> G" by (simp add: M_def)
  have "r = q g1 \<odot> g1 + (\<Sum>g\<in>G - {g1}. q g \<odot> g)"
    using assms(3) \<open>g1 \<in> G\<close> by (simp add: r sum.remove)
  also have "\<dots> = q g1 \<odot> g1 + q g2 \<odot> g2 + (\<Sum>g\<in>G - {g1} - {g2}. q g \<odot> g)"
    using assms(3) \<open>g2 \<in> G\<close> \<open>g1 \<noteq> g2\<close>
    by (metis (no_types, lifting) add.assoc finite_Diff insert_Diff insert_Diff_single insert_iff
                sum.insert_remove)
  finally have r: "r = q g1 \<odot> g1 + q g2 \<odot> g2 + (\<Sum>g\<in>G - {g1, g2}. q g \<odot> g)"
    by (simp flip: Diff_insert2)

  let ?l = "lcs (lp g1) (lp g2)"
  let ?v = "term_of_pair (?l, component_of_term (lt g2))"
  have "lp g1 adds lp (q g1 \<odot> g1)" by (simp add: v1' pp_of_term_splus flip: v1)
  moreover have "lp g2 adds lp (q g1 \<odot> g1)" by (simp add: v2' pp_of_term_splus flip: v1)
  ultimately have l_adds: "?l adds lp (q g1 \<odot> g1)" by (rule lcs_adds)

  have "spoly_rep d m G g1 g2"
  proof (cases "spoly g1 g2 = 0")
    case True
    thus ?thesis by (rule spoly_repI_zero)
  next
    case False
    with \<open>g1 \<in> G\<close> \<open>g2 \<in> G\<close> \<open>g1 \<noteq> 0\<close> \<open>g2 \<noteq> 0\<close> show ?thesis by (rule assms(4))
  qed
  then obtain q' where spoly: "spoly g1 g2 = (\<Sum>g\<in>G. q' g \<odot> g)"
    and "\<And>g. q' g \<in> punit.dgrad_p_set d m" and "\<And>g. q' g \<odot> g \<noteq> 0 \<Longrightarrow> lt (q' g \<odot> g) \<prec>\<^sub>t ?v"
    by (rule spoly_repE) blast
  note this(2)
  also have "punit.dgrad_p_set d m \<subseteq> punit.dgrad_p_set d m'"
    by (rule punit.dgrad_p_set_subset) (simp add: m'_def)
  finally have q'_in: "\<And>g. q' g \<in> punit.dgrad_p_set d m'" .

  define mu where "mu = monomial (lc (q g1 \<odot> g1)) (lp (q g1 \<odot> g1) - ?l)"
  define mu1 where "mu1 = monomial (1 / lc g1) (?l - lp g1)"
  define mu2 where "mu2 = monomial (1 / lc g2) (?l - lp g2)"
    define q'' where "q'' = (\<lambda>g. q g + mu * q' g)
                              (g1:=punit.tail (q g1) + mu * q' g1, g2:=q g2 + mu * q' g2 + mu * mu2)"
  from \<open>q g1 \<odot> g1 \<noteq> 0\<close> have "mu \<noteq> 0" by (simp add: mu_def monomial_0_iff lc_eq_zero_iff)
  from \<open>g1 \<noteq> 0\<close> l_adds have mu_times_mu1: "mu * mu1 = monomial (lcf (q g1)) (lpp (q g1))"
    by (simp add: mu_def mu1_def times_monomial_monomial lc_mult_scalar lc_eq_zero_iff
              minus_plus_minus_cancel adds_lcs v1' pp_of_term_splus flip: v1)
  from l_adds have mu_times_mu2: "mu * mu2 = monomial (lc (q g1 \<odot> g1) / lc g2) (lpp (q g2))"
    by (simp add: mu_def mu2_def times_monomial_monomial lc_mult_scalar minus_plus_minus_cancel
              adds_lcs_2 v2' pp_of_term_splus flip: v1)
  have "mu1 \<odot> g1 - mu2 \<odot> g2 = spoly g1 g2"
    by (simp add: spoly_def Let_def cmp_eq lc_def mult_scalar_monomial mu1_def mu2_def)
  also have "\<dots> = q' g1 \<odot> g1 + (\<Sum>g\<in>G - {g1}. q' g \<odot> g)"
    using assms(3) \<open>g1 \<in> G\<close> by (simp add: spoly sum.remove)
  also have "\<dots> = q' g1 \<odot> g1 + q' g2 \<odot> g2 + (\<Sum>g\<in>G - {g1} - {g2}. q' g \<odot> g)"
    using assms(3) \<open>g2 \<in> G\<close> \<open>g1 \<noteq> g2\<close>
    by (metis (no_types, lifting) add.assoc finite_Diff insert_Diff insert_Diff_single insert_iff
                sum.insert_remove)
  finally have "(q' g1 - mu1) \<odot> g1 + (q' g2 + mu2) \<odot> g2 + (\<Sum>g\<in>G - {g1, g2}. q' g \<odot> g) = 0"
    by (simp add: algebra_simps flip: Diff_insert2)
  hence "0 = mu \<odot> ((q' g1 - mu1) \<odot> g1 + (q' g2 + mu2) \<odot> g2 + (\<Sum>g\<in>G - {g1, g2}. q' g \<odot> g))" by simp
  also have "\<dots> = (mu * q' g1 - mu * mu1) \<odot> g1 + (mu * q' g2 + mu * mu2) \<odot> g2 +
                    (\<Sum>g\<in>G - {g1, g2}. (mu * q' g) \<odot> g)"
    by (simp add: mult_scalar_distrib_left sum_mult_scalar_distrib_left distrib_left right_diff_distrib
            flip: mult_scalar_assoc)
  finally have "r = r + (mu * q' g1 - mu * mu1) \<odot> g1 + (mu * q' g2 + mu * mu2) \<odot> g2 +
                          (\<Sum>g\<in>G - {g1, g2}. (mu * q' g) \<odot> g)" by simp
  also have "\<dots> = (q g1 - mu * mu1 + mu * q' g1) \<odot> g1 + (q g2 + mu * q' g2 + mu * mu2) \<odot> g2 +
                    (\<Sum>g\<in>G - {g1, g2}. (q g + mu * q' g) \<odot> g)"
    by (simp add: r algebra_simps flip: sum.distrib)
  also have "q g1 - mu * mu1 = punit.tail (q g1)"
    by (simp only: mu_times_mu1 punit.leading_monomial_tail diff_eq_eq add.commute[of "punit.tail (q g1)"])
  finally have "r = q'' g1 \<odot> g1 + q'' g2 \<odot> g2 + (\<Sum>g\<in>G - {g1} - {g2}. q'' g \<odot> g)"
    using \<open>g1 \<noteq> g2\<close> by (simp add: q''_def flip: Diff_insert2)
  also from \<open>finite G\<close> \<open>g1 \<noteq> g2\<close> \<open>g1 \<in> G\<close> \<open>g2 \<in> G\<close> have "\<dots> = (\<Sum>g\<in>G. q'' g \<odot> g)"
    by (simp add: sum.remove) (metis (no_types, lifting) finite_Diff insert_Diff insert_iff sum.remove)
  finally have r: "r = (\<Sum>g\<in>G. q'' g \<odot> g)" .

  have 1: "lt ((mu * q' g) \<odot> g) \<prec>\<^sub>t v" if "(mu * q' g) \<odot> g \<noteq> 0" for g
  proof -
    from that have "q' g \<odot> g \<noteq> 0" by (auto simp: mult_scalar_assoc)
    hence *: "lt (q' g \<odot> g) \<prec>\<^sub>t ?v" by fact
    from \<open>q' g \<odot> g \<noteq> 0\<close> \<open>mu \<noteq> 0\<close> have "lt ((mu * q' g) \<odot> g) = (lp (q g1 \<odot> g1) - ?l) \<oplus> lt (q' g \<odot> g)"
      by (simp add: mult_scalar_assoc lt_mult_scalar) (simp add: mu_def punit.lt_monomial monomial_0_iff)
    also from * have "\<dots> \<prec>\<^sub>t (lp (q g1 \<odot> g1) - ?l) \<oplus> ?v" by (rule splus_mono_strict)
    also from l_adds have "\<dots> = v" by (simp add: splus_def minus_plus term_simps v1' flip: cmp_eq v1)
    finally show ?thesis .
  qed

  have 2: "lt (q'' g1 \<odot> g1) \<prec>\<^sub>t v" if "q'' g1 \<odot> g1 \<noteq> 0" using that
  proof (rule lt_less)
    fix u
    assume "v \<preceq>\<^sub>t u"
    have "u \<notin> keys (q'' g1 \<odot> g1)"
    proof
      assume "u \<in> keys (q'' g1 \<odot> g1)"
      also from \<open>g1 \<noteq> g2\<close> have "\<dots> = keys ((punit.tail (q g1) + mu * q' g1) \<odot> g1)"
        by (simp add: q''_def)
      also have "\<dots> \<subseteq> keys (punit.tail (q g1) \<odot> g1) \<union> keys ((mu * q' g1) \<odot> g1)"
        unfolding mult_scalar_distrib_right by (fact keys_add_subset)
      finally show False
      proof
        assume "u \<in> keys (punit.tail (q g1) \<odot> g1)"
        hence "u \<preceq>\<^sub>t lt (punit.tail (q g1) \<odot> g1)" by (rule lt_max_keys)
        also have "\<dots> \<preceq>\<^sub>t lpp (punit.tail (q g1)) \<oplus> lt g1"
          by (metis in_keys_mult_scalar_le lt_def lt_in_keys min_term_min)
        also have "\<dots> \<prec>\<^sub>t lpp (q g1) \<oplus> lt g1"
        proof (intro splus_mono_strict_left punit.lt_tail notI)
          assume "punit.tail (q g1) = 0"
          with \<open>u \<in> keys (punit.tail (q g1) \<odot> g1)\<close> show False by simp
        qed
        also have "\<dots> = v" by (simp only: v1')
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      next
        assume "u \<in> keys ((mu * q' g1) \<odot> g1)"
        hence "(mu * q' g1) \<odot> g1 \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g1) \<odot> g1)" by (auto intro: lt_max_keys)
        note this(2)
        also from \<open>(mu * q' g1) \<odot> g1 \<noteq> 0\<close> have "lt ((mu * q' g1) \<odot> g1) \<prec>\<^sub>t v" by (rule 1)
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      qed
    qed
    thus "lookup (q'' g1 \<odot> g1) u = 0" by simp
  qed

  have 3: "lt (q'' g2 \<odot> g2) \<preceq>\<^sub>t v"
  proof (rule lt_le)
    fix u
    assume "v \<prec>\<^sub>t u"
    have "u \<notin> keys (q'' g2 \<odot> g2)"
    proof
      assume "u \<in> keys (q'' g2 \<odot> g2)"
      also have "\<dots> = keys ((q g2 + mu * q' g2 + mu * mu2) \<odot> g2)" by (simp add: q''_def)
      also have "\<dots> \<subseteq> keys (q g2 \<odot> g2 + (mu * q' g2) \<odot> g2) \<union> keys ((mu * mu2) \<odot> g2)"
        unfolding mult_scalar_distrib_right by (fact keys_add_subset)
      finally show False
      proof
        assume "u \<in> keys (q g2 \<odot> g2 + (mu * q' g2) \<odot> g2)"
        also have "\<dots> \<subseteq> keys (q g2 \<odot> g2) \<union> keys ((mu * q' g2) \<odot> g2)" by (fact keys_add_subset)
        finally show ?thesis
        proof
          assume "u \<in> keys (q g2 \<odot> g2)"
          hence "u \<preceq>\<^sub>t lt (q g2 \<odot> g2)" by (rule lt_max_keys)
          with \<open>v \<prec>\<^sub>t u\<close> show ?thesis by (simp add: v2)
        next
          assume "u \<in> keys ((mu * q' g2) \<odot> g2)"
          hence "(mu * q' g2) \<odot> g2 \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g2) \<odot> g2)" by (auto intro: lt_max_keys)
          note this(2)
          also from \<open>(mu * q' g2) \<odot> g2 \<noteq> 0\<close> have "lt ((mu * q' g2) \<odot> g2) \<prec>\<^sub>t v" by (rule 1)
          finally show ?thesis using \<open>v \<prec>\<^sub>t u\<close> by simp
        qed
      next
        assume "u \<in> keys ((mu * mu2) \<odot> g2)"
        hence "(mu * mu2) \<odot> g2 \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * mu2) \<odot> g2)" by (auto intro: lt_max_keys)
        from this(1) have "(mu * mu2) \<noteq> 0" by auto
        note \<open>u \<preceq>\<^sub>t _\<close>
        also from \<open>mu * mu2 \<noteq> 0\<close> \<open>g2 \<noteq> 0\<close> have "lt ((mu * mu2) \<odot> g2) = lpp (q g2) \<oplus> lt g2"
          by (simp add: lt_mult_scalar) (simp add: mu_times_mu2 punit.lt_monomial monomial_0_iff)
        finally show ?thesis using \<open>v \<prec>\<^sub>t u\<close> by (simp add: v2')
      qed
    qed
    thus "lookup (q'' g2 \<odot> g2) u = 0" by simp
  qed

  have 4: "lt (q'' g \<odot> g) \<preceq>\<^sub>t v" if "g \<in> M" for g
  proof (cases "g \<in> {g1, g2}")
    case True
    hence "g = g1 \<or> g = g2" by simp
    thus ?thesis
    proof
      assume "g = g1"
      show ?thesis
      proof (cases "q'' g1 \<odot> g1 = 0")
        case True
        thus ?thesis by (simp add: \<open>g = g1\<close> min_term_min)
      next
        case False
        hence "lt (q'' g \<odot> g) \<prec>\<^sub>t v" unfolding \<open>g = g1\<close> by (rule 2)
        thus ?thesis by simp
      qed
    next
      assume "g = g2"
      with 3 show ?thesis by simp
    qed
  next
    case False
    hence q'': "q'' g = q g + mu * q' g" by (simp add: q''_def)
    show ?thesis
    proof (rule lt_le)
      fix u
      assume "v \<prec>\<^sub>t u"
      have "u \<notin> keys (q'' g \<odot> g)"
      proof
        assume "u \<in> keys (q'' g \<odot> g)"
        also have "\<dots> \<subseteq> keys (q g \<odot> g) \<union> keys ((mu * q' g) \<odot> g)"
          unfolding q'' mult_scalar_distrib_right by (fact keys_add_subset)
        finally show False
        proof
          assume "u \<in> keys (q g \<odot> g)"
          hence "u \<preceq>\<^sub>t lt (q g \<odot> g)" by (rule lt_max_keys)
          with \<open>g \<in> M\<close> \<open>v \<prec>\<^sub>t u\<close> show ?thesis by (simp add: M_def)
        next
          assume "u \<in> keys ((mu * q' g) \<odot> g)"
          hence "(mu * q' g) \<odot> g \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g) \<odot> g)" by (auto intro: lt_max_keys)
          note this(2)
          also from \<open>(mu * q' g) \<odot> g \<noteq> 0\<close> have "lt ((mu * q' g) \<odot> g) \<prec>\<^sub>t v" by (rule 1)
          finally show ?thesis using \<open>v \<prec>\<^sub>t u\<close> by simp
        qed
      qed
      thus "lookup (q'' g \<odot> g) u = 0" by simp
    qed
  qed

  have 5: "lt (q'' g \<odot> g) \<prec>\<^sub>t v" if "g \<in> G" and "g \<notin> M" and "q'' g \<odot> g \<noteq> 0" for g using that(3)
  proof (rule lt_less)
    fix u
    assume "v \<preceq>\<^sub>t u"
    from that(2) \<open>g1 \<in> M\<close> \<open>g2 \<in> M\<close> have "g \<noteq> g1" and "g \<noteq> g2" by blast+
    hence q'': "q'' g = q g + mu * q' g" by (simp add: q''_def)
    have "u \<notin> keys (q'' g \<odot> g)"
    proof
      assume "u \<in> keys (q'' g \<odot> g)"
      also have "\<dots> \<subseteq> keys (q g \<odot> g) \<union> keys ((mu * q' g) \<odot> g)"
        unfolding q'' mult_scalar_distrib_right by (fact keys_add_subset)
      finally show False
      proof
        assume "u \<in> keys (q g \<odot> g)"
        hence "q g \<odot> g \<noteq> 0" and "u \<preceq>\<^sub>t lt (q g \<odot> g)" by (auto intro: lt_max_keys)
        note this(2)
        also from that(1, 2) \<open>q g \<odot> g \<noteq> 0\<close> have "\<dots> \<prec>\<^sub>t v" by (rule v_max)
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      next
        assume "u \<in> keys ((mu * q' g) \<odot> g)"
        hence "(mu * q' g) \<odot> g \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g) \<odot> g)" by (auto intro: lt_max_keys)
        note this(2)
        also from \<open>(mu * q' g) \<odot> g \<noteq> 0\<close> have "lt ((mu * q' g) \<odot> g) \<prec>\<^sub>t v" by (rule 1)
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      qed
    qed
    thus "lookup (q'' g \<odot> g) u = 0" by simp
  qed

  define u where "u = mlt q''"
  have u_in: "u \<in> lt ` {q'' g \<odot> g | g. g \<in> G \<and> q'' g \<odot> g \<noteq> 0}" unfolding u_def mlt_def
  proof (rule ord_term_lin.Max_in, simp_all add: assms(3), rule ccontr)
    assume "\<nexists>g. g \<in> G \<and> q'' g \<odot> g \<noteq> 0"
    hence "q'' g \<odot> g = 0" if "g \<in> G" for g using that by simp
    hence "r = 0" by (simp add: r)
    with \<open>r \<noteq> 0\<close> show False ..
  qed
  have u_max: "lt (q'' g \<odot> g) \<preceq>\<^sub>t u" if "g \<in> G" for g
  proof (cases "q'' g \<odot> g = 0")
    case True
    thus ?thesis by (simp add: min_term_min)
  next
    case False
    show ?thesis unfolding u_def mlt_def
      by (rule ord_term_lin.Max_ge) (auto simp: assms(3) False intro!: imageI \<open>g \<in> G\<close>)
  qed
  have "q'' \<in> rel_dom"
  proof (simp add: rel_dom_def r, intro subsetI, elim imageE)
    fix g
    assume "g \<in> G"
    from assms(1) l_adds have "d (lp (q g1 \<odot> g1) - ?l) \<le> d (lp (q g1 \<odot> g1))"
      by (rule dickson_grading_minus)
    also have "\<dots> = d (lpp (q g1) + lp g1)" by (simp add: v1' term_simps flip: v1)
    also from assms(1) have "\<dots> = ord_class.max (d (lpp (q g1))) (d (lp g1))"
      by (rule dickson_gradingD1)
    also have "\<dots> \<le> m'"
    proof (rule max.boundedI)
      from \<open>g1 \<in> G\<close> have "q g1 \<in> punit.dgrad_p_set d m'" by (rule q_in)
      moreover from \<open>q g1 \<noteq> 0\<close> have "lpp (q g1) \<in> keys (q g1)" by (rule punit.lt_in_keys)
      ultimately show "d (lpp (q g1)) \<le> m'" by (rule punit.dgrad_p_setD[simplified])
    next
      from \<open>g1 \<in> G\<close> G_sub have "g1 \<in> dgrad_p_set d m'" ..
      moreover from \<open>g1 \<noteq> 0\<close> have "lt g1 \<in> keys g1" by (rule lt_in_keys)
      ultimately show "d (lp g1) \<le> m'" by (rule dgrad_p_setD)
    qed
    finally have d1: "d (lp (q g1 \<odot> g1) - ?l) \<le> m'" .
    have "d (?l - lp g2) \<le> ord_class.max (d (lp g2)) (d (lp g1))"
      unfolding lcs_comm[of "lp g1"] using assms(1) by (rule dickson_grading_lcs_minus)
    also have "\<dots> \<le> m'"
    proof (rule max.boundedI)
      from \<open>g2 \<in> G\<close> G_sub have "g2 \<in> dgrad_p_set d m'" ..
      moreover from \<open>g2 \<noteq> 0\<close> have "lt g2 \<in> keys g2" by (rule lt_in_keys)
      ultimately show "d (lp g2) \<le> m'" by (rule dgrad_p_setD)
    next
      from \<open>g1 \<in> G\<close> G_sub have "g1 \<in> dgrad_p_set d m'" ..
      moreover from \<open>g1 \<noteq> 0\<close> have "lt g1 \<in> keys g1" by (rule lt_in_keys)
      ultimately show "d (lp g1) \<le> m'" by (rule dgrad_p_setD)
    qed
    finally have mu2: "mu2 \<in> punit.dgrad_p_set d m'"
      by (simp add: mu2_def punit.dgrad_p_set_def dgrad_set_def)
    fix z
    assume z: "z = q'' g"
    have "g = g1 \<or> g = g2 \<or> (g \<noteq> g1 \<and> g \<noteq> g2)" by blast
    thus "z \<in> punit.dgrad_p_set d m'"
    proof (elim disjE conjE)
      assume "g = g1"
      with \<open>g1 \<noteq> g2\<close> have "q'' g = punit.tail (q g1) + mu * q' g1" by (simp add: q''_def)
      also have "\<dots> \<in> punit.dgrad_p_set d m'" unfolding mu_def times_monomial_left
        by (intro punit.dgrad_p_set_closed_plus punit.dgrad_p_set_closed_tail
                punit.dgrad_p_set_closed_monom_mult d1 assms(1) q_in q'_in \<open>g1 \<in> G\<close>)
      finally show ?thesis by (simp only: z)
    next
      assume "g = g2"
      hence "q'' g = q g2 + mu * q' g2 + mu * mu2" by (simp add: q''_def)
      also have "\<dots> \<in> punit.dgrad_p_set d m'" unfolding mu_def times_monomial_left
        by (intro punit.dgrad_p_set_closed_plus punit.dgrad_p_set_closed_monom_mult
                d1 mu2 q_in q'_in assms(1) \<open>g2 \<in> G\<close>)
      finally show ?thesis by (simp only: z)
    next
      assume "g \<noteq> g1" and "g \<noteq> g2"
      hence "q'' g = q g + mu * q' g" by (simp add: q''_def)
      also have "\<dots> \<in> punit.dgrad_p_set d m'" unfolding mu_def times_monomial_left
        by (intro punit.dgrad_p_set_closed_plus punit.dgrad_p_set_closed_monom_mult
                d1 assms(1) q_in q'_in \<open>g \<in> G\<close>)
      finally show ?thesis by (simp only: z)
    qed
  qed
  with q_min have "\<not> rel q'' q" by blast
  hence "v \<preceq>\<^sub>t u" and "u \<noteq> v \<or> mnum q \<le> mnum q''" by (auto simp: v_def u_def rel_def)
  moreover have "u \<preceq>\<^sub>t v"
  proof -
    from u_in obtain g where "g \<in> G" and "q'' g \<odot> g \<noteq> 0" and u: "u = lt (q'' g \<odot> g)" by blast
    show ?thesis
    proof (cases "g \<in> M")
      case True
      thus ?thesis unfolding u by (rule 4)
    next
      case False
      with \<open>g \<in> G\<close> have "lt (q'' g \<odot> g) \<prec>\<^sub>t v" using \<open>q'' g \<odot> g \<noteq> 0\<close> by (rule 5)
      thus ?thesis by (simp add: u)
    qed
  qed
  ultimately have u_v: "u = v" and "mnum q \<le> mnum q''" by simp_all
  note this(2)
  also have "mnum q'' < card M" unfolding mnum_def
  proof (rule psubset_card_mono)
    from \<open>M \<subseteq> G\<close> \<open>finite G\<close> show "finite M" by (rule finite_subset)
  next
    have "{g\<in>G. q'' g \<odot> g \<noteq> 0 \<and> lt (q'' g \<odot> g) = v} \<subseteq> M - {g1}"
    proof
      fix g
      assume "g \<in> {g\<in>G. q'' g \<odot> g \<noteq> 0 \<and> lt (q'' g \<odot> g) = v}"
      hence "g \<in> G" and "q'' g \<odot> g \<noteq> 0" and "lt (q'' g \<odot> g) = v" by simp_all
      with 2 5 show "g \<in> M - {g1}" by blast
    qed
    also from \<open>g1 \<in> M\<close> have "\<dots> \<subset> M" by blast
    finally show "{g\<in>G. q'' g \<odot> g \<noteq> 0 \<and> lt (q'' g \<odot> g) = mlt q''} \<subset> M"
      by (simp only: u_v flip: u_def)
  qed
  also have "\<dots> = mnum q" by (simp only: M_def mnum_def v_def)
  finally show False ..
qed

end

subsection \<open>Algebraically Closed Fields\<close>

lemma prod_eq_zeroE:
  assumes "prod f I = (0::'a::{semiring_no_zero_divisors,comm_monoid_mult,zero_neq_one})"
  obtains i where "finite I" and "i \<in> I" and "f i = 0"
proof -
  have "finite I"
  proof (rule ccontr)
    assume "infinite I"
    with assms show False by simp
  qed
  moreover from this assms obtain i where "i \<in> I" and "f i = 0"
  proof (induct I arbitrary: thesis)
    case empty
    from empty(2) show ?case by simp
  next
    case (insert j I)
    from insert.hyps(1, 2) have "f j * prod f I = prod f (insert j I)" by simp
    also have "\<dots> = 0" by fact
    finally have "f j = 0 \<or> prod f I = 0" by simp
    thus ?case
    proof
      assume "f j = 0"
      with _ show ?thesis by (rule insert.prems) simp
    next
      assume "prod f I = 0"
      then obtain i where "i \<in> I" and "f i = 0" using insert.hyps(3) by blast
      from _ this(2) show ?thesis by (rule insert.prems) (simp add: \<open>i \<in> I\<close>)
    qed
  qed
  ultimately show ?thesis ..
qed

lemma degree_prod_eq:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> f i \<noteq> 0"
  shows "Polynomial.degree (prod f I :: _::semiring_no_zero_divisors poly) = (\<Sum>i\<in>I. Polynomial.degree (f i))"
  using assms
proof (induct I)
  case empty
  show ?case by simp
next
  case (insert j J)
  have 1: "f i \<noteq> 0" if "i \<in> J" for i
  proof (rule insert.prems)
    from that show "i \<in> insert j J" by simp
  qed
  hence eq: "Polynomial.degree (prod f J) = (\<Sum>i\<in>J. Polynomial.degree (f i))" by (rule insert.hyps)
  from insert.hyps(1, 2) have "Polynomial.degree (prod f (insert j J)) = Polynomial.degree (f j * prod f J)"
    by simp
  also have "\<dots> = Polynomial.degree (f j) + Polynomial.degree (prod f J)"
  proof (rule degree_mult_eq)
    show "f j \<noteq> 0" by (rule insert.prems) simp
  next
    show "prod f J \<noteq> 0"
    proof
      assume "prod f J = 0"
      then obtain i where "i \<in> J" and "f i = 0" by (rule prod_eq_zeroE)
      from this(1) have "f i \<noteq> 0" by (rule 1)
      thus False using \<open>f i = 0\<close> ..
    qed
  qed
  also from insert.hyps(1, 2) have "\<dots> = (\<Sum>i\<in>insert j J. Polynomial.degree (f i))" by (simp add: eq)
  finally show ?case .
qed

class alg_closed_field =
  assumes alg_closed_field_axiom: "\<And>p::'a::field poly. 0 < Polynomial.degree p \<Longrightarrow> \<exists>z. poly p z = 0"
begin

lemma rootE:
  assumes "0 < Polynomial.degree p"
  obtains z where "poly p z = (0::'a)"
proof -
  from assms have "\<exists>z. poly p z = 0" by (rule alg_closed_field_axiom)
  then obtain z where "poly p z = 0" ..
  thus ?thesis ..
qed

lemma infinite_UNIV: "infinite (UNIV::'a set)"
proof
  assume fin: "finite (UNIV::'a set)"
  define p where "p = (\<Prod>a\<in>UNIV. [:- a, 1::'a:]) + [:-1:]"
  have "Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:]) = (\<Sum>a\<in>UNIV. Polynomial.degree [:- a, 1::'a:])"
    using fin by (rule degree_prod_eq) simp
  also have "\<dots> = (\<Sum>a\<in>(UNIV::'a set). 1)" by simp
  also have "\<dots> = card (UNIV::'a set)" by simp
  also from fin have "\<dots> > 0" by (rule finite_UNIV_card_ge_0)
  finally have "0 < Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" .
  hence "Polynomial.degree [:-1:] < Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" by simp
  hence "Polynomial.degree p = Polynomial.degree (\<Prod>a\<in>UNIV. [:- a, 1::'a:])" unfolding p_def
    by (rule degree_add_eq_left)
  also have "\<dots> > 0" by fact
  finally have "0 < Polynomial.degree p" .
  then obtain z where "poly p z = 0" by (rule rootE)
  hence "(\<Prod>a\<in>UNIV. (z - a)) = 1" by (simp add: p_def poly_prod)
  thus False by (metis UNIV_I cancel_comm_monoid_add_class.diff_cancel fin one_neq_zero prod_zero_iff)
qed

lemma linear_factorsE:
  fixes p :: "'a poly"
  obtains c A m where "finite A" and "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A" and "c = 0 \<longleftrightarrow> p = 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)"
proof -
  obtain c A m where fin: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and *: "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A"
  proof (induct p arbitrary: thesis rule: poly_root_induct[where P="\<lambda>_. True"])
    case 0
    show ?case
    proof (rule 0)
      show "0 = Polynomial.smult 0 (\<Prod>a\<in>{}. [:- a, 1:] ^ (\<lambda>_. 0) a)" by simp
    qed simp_all
  next
    case (no_roots p)
    have "Polynomial.degree p = 0"
    proof (rule ccontr)
      assume "Polynomial.degree p \<noteq> 0"
      hence "0 < Polynomial.degree p" by simp
      then obtain z where "poly p z = 0" by (rule rootE)
      moreover have "poly p z \<noteq> 0" by (rule no_roots) blast
      ultimately show False by simp
    qed
    then obtain c where p: "p = [:c:]" by (rule degree_eq_zeroE)
    show ?case
    proof (rule no_roots)
      show "p = Polynomial.smult c (\<Prod>a\<in>{}. [:- a, 1:] ^ (\<lambda>_. 0) a)" by (simp add: p)
    qed simp_all
  next
    case (root a p)
    obtain A c m where 1: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
      and 2: "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A" by (rule root.hyps) blast
    define m' where "m' = (\<lambda>x. if x = a then Suc (m x) else m x)"
    show ?case
    proof (rule root.prems)
      from 1 show "finite (insert a A)" by simp
    next
      have "[:a, - 1:] * p = [:- a, 1:] * (- p)" by simp
      also have "\<dots> = [:- a, 1:] * (Polynomial.smult (- c) (\<Prod>a\<in>A. [:- a, 1:] ^ m a))"
        by (simp add: p)
      also have "\<dots> = Polynomial.smult (- c) ([:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a))"
        by (simp only: mult_smult_right ac_simps)
      also have "[:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a) = (\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a)"
      proof (cases "a \<in> A")
        case True
        with 1 have "(\<Prod>a\<in>A. [:- a, 1:] ^ m a) = [:- a, 1:] ^ m a * (\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m a)"
          by (simp add: prod.remove)
        also from refl have "(\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m a) = (\<Prod>a\<in>A-{a}. [:- a, 1:] ^ m' a)"
          by (rule prod.cong) (simp add: m'_def)
        finally have "[:- a, 1:] * (\<Prod>a\<in>A. [:- a, 1:] ^ m a) =
                          ([:- a, 1:] * [:- a, 1:] ^ m a) * (\<Prod>a\<in>A - {a}. [:- a, 1:] ^ m' a)"
          by (simp only: mult.assoc)
        also have "[:- a, 1:] * [:- a, 1:] ^ m a = [:- a, 1:] ^ m' a" by (simp add: m'_def)
        finally show ?thesis using 1 by (simp add: prod.insert_remove)
      next
        case False
        with 1 have "(\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a) = [:- a, 1:] ^ m' a * (\<Prod>a\<in>A. [:- a, 1:] ^ m' a)"
          by simp
        also from refl have "(\<Prod>a\<in>A. [:- a, 1:] ^ m' a) = (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
        proof (rule prod.cong)
          fix x
          assume "x \<in> A"
          with False have "x \<noteq> a" by blast
          thus "[:- x, 1:] ^ m' x = [:- x, 1:] ^ m x" by (simp add: m'_def)
        qed
        finally have "(\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a) = [:- a, 1:] ^ m' a * (\<Prod>a\<in>A. [:- a, 1:] ^ m a)" .
        also from False have "m' a = 1" by (simp add: m'_def 2)
        finally show ?thesis by simp
      qed
      finally show "[:a, - 1:] * p = Polynomial.smult (- c) (\<Prod>a\<in>insert a A. [:- a, 1:] ^ m' a)" .
    next
      fix x
      show "m' x = 0 \<longleftrightarrow> x \<notin> insert a A" by (simp add: m'_def 2)
    qed
  qed
  moreover have "c = 0 \<longleftrightarrow> p = 0"
  proof
    assume "p = 0"
    hence "[:c:] = 0 \<or> (\<Prod>a\<in>A. [:- a, 1:] ^ m a) = 0" by (simp add: p)
    thus "c = 0"
    proof
      assume "[:c:] = 0"
      thus ?thesis by simp
    next
      assume "(\<Prod>a\<in>A. [:- a, 1:] ^ m a) = 0"
      then obtain a where "[:- a, 1:] ^ m a = 0" by (rule prod_eq_zeroE)
      thus ?thesis by simp
    qed
  qed (simp add: p)
  moreover {
    fix z
    have "0 < m z" if "z \<in> A" by (rule ccontr) (simp add: * that)
    hence "poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)" by (auto simp: p poly_prod * fin elim: prod_eq_zeroE)
  }
  ultimately show ?thesis ..
qed

end (* alg_closed_field *)

instance complex :: alg_closed_field
  by standard (rule fundamental_theorem_of_algebra, simp add: constant_degree)

subsection \<open>Ideals and Varieties\<close>

definition variety_of :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> ('x \<Rightarrow> 'a::comm_semiring_1) set"
  where "variety_of F = {a. \<forall>f\<in>F. eval_pm a f = 0}"

definition ideal_of :: "('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set"
  where "ideal_of A = {f. \<forall>a\<in>A. eval_pm a f = 0}"

definition radical :: "('a \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('a::comm_powerprod \<Rightarrow>\<^sub>0 'b::semiring_1) set" ("\<surd>(_)" [999] 999)
  where "radical F = {f. \<exists>m. f ^ m \<in> F}"

abbreviation "\<V> \<equiv> variety_of"
abbreviation "\<I> \<equiv> ideal_of"

lemma variety_ofI: "(\<And>f. f \<in> F \<Longrightarrow> eval_pm a f = 0) \<Longrightarrow> a \<in> \<V> F"
  by (simp add: variety_of_def)

lemma variety_ofD: "a \<in> \<V> F \<Longrightarrow> f \<in> F \<Longrightarrow> eval_pm a f = 0"
  by (simp add: variety_of_def)

lemma variety_of_antimono: "F \<subseteq> G \<Longrightarrow> \<V> G \<subseteq> \<V> F"
  by (auto simp: variety_of_def)

lemma variety_of_ideal [simp]: "\<V> (ideal F) = \<V> F"
proof
  show "\<V> (ideal F) \<subseteq> \<V> F" by (intro variety_of_antimono ideal.span_superset)
next
  show "\<V> F \<subseteq> \<V> (ideal F)"
  proof (intro subsetI variety_ofI)
    fix a f
    assume "a \<in> \<V> F" and "f \<in> ideal F"
    from this(2) show "eval_pm a f = 0"
    proof (induct f rule: ideal.span_induct_alt)
      case base
      show ?case by simp
    next
      case (step c f g)
      with \<open>a \<in> \<V> F\<close> show ?case by (auto simp: eval_pm_plus eval_pm_times dest: variety_ofD)
    qed
  qed
qed

lemma ideal_ofI: "(\<And>a. a \<in> A \<Longrightarrow> eval_pm a f = 0) \<Longrightarrow> f \<in> \<I> A"
  by (simp add: ideal_of_def)

lemma ideal_ofD: "f \<in> \<I> A \<Longrightarrow> a \<in> A \<Longrightarrow> eval_pm a f = 0"
  by (simp add: ideal_of_def)

lemma ideal_of_antimono: "A \<subseteq> B \<Longrightarrow> \<I> B \<subseteq> \<I> A"
  by (auto simp: ideal_of_def)

lemma ideal_ideal_of [simp]: "ideal (\<I> A) = \<I> A"
  unfolding ideal.span_eq_iff
proof (rule ideal.subspaceI)
  show "0 \<in> \<I> A" by (rule ideal_ofI) simp
next
  fix f g
  assume "f \<in> \<I> A"
  hence f: "eval_pm a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  assume "g \<in> \<I> A"
  hence g: "eval_pm a g = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "f + g \<in> \<I> A" by (rule ideal_ofI) (simp add: eval_pm_plus f g)
next
  fix c f
  assume "f \<in> \<I> A"
  hence f: "eval_pm a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "c * f \<in> \<I> A" by (rule ideal_ofI) (simp add: eval_pm_times f)
qed

lemma variety_of_ideal_of_variety [simp]: "\<V> (\<I> (\<V> F)) = \<V> F" (is "_ = ?V")
proof
  have "F \<subseteq> \<I> (\<V> F)" by (auto intro!: ideal_ofI dest: variety_ofD)
  thus "\<V> (\<I> ?V) \<subseteq> ?V" by (rule variety_of_antimono)
next
  show "?V \<subseteq> \<V> (\<I> ?V)" by (auto intro!: variety_ofI dest: ideal_ofD)
qed

lemma ideal_of_inj_on: "inj_on \<I> (range (\<V>::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_semiring_1) set \<Rightarrow> _))"
proof (rule inj_onI)
  fix A B :: "('x \<Rightarrow> 'a) set"
  assume "A \<in> range \<V>"
  then obtain F where A: "A = \<V> F" ..
  assume "B \<in> range \<V>"
  then obtain G where B: "B = \<V> G" ..
  assume "\<I> A = \<I> B"
  hence "\<V> (\<I> A) = \<V> (\<I> B)" by simp
  thus "A = B" by (simp add: A B)
qed

lemma ideal_of_variety_of_ideal [simp]: "\<I> (\<V> (\<I> A)) = \<I> A" (is "_ = ?I")
proof
  have "A \<subseteq> \<V> (\<I> A)" by (auto intro!: variety_ofI dest: ideal_ofD)
  thus "\<I> (\<V> ?I) \<subseteq> ?I" by (rule ideal_of_antimono)
next
  show "?I \<subseteq> \<I> (\<V> ?I)" by (auto intro!: ideal_ofI dest: variety_ofD)
qed

lemma variety_of_inj_on: "inj_on \<V> (range (\<I>::('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> _))"
proof (rule inj_onI)
  fix F G :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set"
  assume "F \<in> range \<I>"
  then obtain A where F: "F = \<I> A" ..
  assume "G \<in> range \<I>"
  then obtain B where G: "G = \<I> B" ..
  assume "\<V> F = \<V> G"
  hence "\<I> (\<V> F) = \<I> (\<V> G)" by simp
  thus "F = G" by (simp add: F G)
qed

lemma radicalI: "f ^ m \<in> F \<Longrightarrow> f \<in> \<surd>F"
  by (auto simp: radical_def)

lemma radicalE:
  assumes "f \<in> \<surd>F"
  obtains m where "f ^ m \<in> F"
  using assms by (auto simp: radical_def)

lemma radical_mono: "F \<subseteq> G \<Longrightarrow> \<surd>F \<subseteq> \<surd>G"
  by (auto elim!: radicalE intro: radicalI)

lemma radical_superset: "F \<subseteq> \<surd>F"
proof
  fix f
  assume "f \<in> F"
  hence "f ^ 1 \<in> F" by simp
  thus "f \<in> \<surd>F" by (rule radicalI)
qed

lemma radical_idem [simp]: "\<surd>\<surd>F = \<surd>F"
proof
  show "\<surd>\<surd>F \<subseteq> \<surd>F" by (auto elim!: radicalE intro: radicalI simp flip: power_mult)
qed (fact radical_superset)

lemma ideal_radical_ideal [simp]: "ideal (\<surd>ideal F) = \<surd>ideal F" (is "_ = ?R")
  unfolding ideal.span_eq_iff
proof (rule ideal.subspaceI)
  have "0 ^ 1 \<in> ideal F" by (simp add: ideal.span_zero)
  thus "0 \<in> ?R" by (rule radicalI)
next
  fix a b
  assume "a \<in> ?R"
  then obtain m where "a ^ m \<in> ideal F" by (rule radicalE)
  have a: "a ^ k \<in> ideal F" if "m \<le> k" for k
  proof -
    from \<open>a ^ m \<in> _\<close> have "a ^ (k - m + m) \<in> ideal F" by (simp only: power_add ideal.span_scale)
    with that show ?thesis by simp
  qed
  assume "b \<in> ?R"
  then obtain n where "b ^ n \<in> ideal F" by (rule radicalE)
  have b: "b ^ k \<in> ideal F" if "n \<le> k" for k
  proof -
    from \<open>b ^ n \<in> _\<close> have "b ^ (k - n + n) \<in> ideal F" by (simp only: power_add ideal.span_scale)
    with that show ?thesis by simp
  qed
  have "(a + b) ^ (m + n) \<in> ideal F" unfolding binomial_ring
  proof (rule ideal.span_sum)
    fix k
    show "of_nat (m + n choose k) * a ^ k * b ^ (m + n - k) \<in> ideal F"
    proof (cases "k \<le> m")
      case True
      hence "n \<le> m + n - k" by simp
      hence "b ^ (m + n - k) \<in> ideal F" by (rule b)
      thus ?thesis by (rule ideal.span_scale)
    next
      case False
      hence "m \<le> k" by simp
      hence "a ^ k \<in> ideal F" by (rule a)
      hence "of_nat (m + n choose k) * b ^ (m + n - k) * a ^ k \<in> ideal F" by (rule ideal.span_scale)
      thus ?thesis by (simp only: ac_simps)
    qed
  qed
  thus "a + b \<in> ?R" by (rule radicalI)
next
  fix c a
  assume "a \<in> ?R"
  then obtain m where "a ^ m \<in> ideal F" by (rule radicalE)
  hence "(c * a) ^ m \<in> ideal F" by (simp only: power_mult_distrib ideal.span_scale)
  thus "c * a \<in> ?R" by (rule radicalI)
qed

lemma radical_ideal_of [simp]: "\<surd>\<I> A = \<I> (A::(_ \<Rightarrow> _::semiring_1_no_zero_divisors) set)"
proof
  show "\<surd>\<I> A \<subseteq> \<I> A" by (auto elim!: radicalE dest!: ideal_ofD intro!: ideal_ofI simp: eval_pm_power)
qed (fact radical_superset)

lemma variety_of_radical_ideal [simp]: "\<V> (\<surd>ideal F) = \<V> (F::(_ \<Rightarrow>\<^sub>0 _::semiring_1_no_zero_divisors) set)"
proof
  have "F \<subseteq> ideal F" by (rule ideal.span_superset)
  also have "\<dots> \<subseteq> \<surd>ideal F" by (rule radical_superset)
  finally show "\<V> (\<surd>ideal F) \<subseteq> \<V> F" by (rule variety_of_antimono)
next
  show "\<V> F \<subseteq> \<V> (\<surd>ideal F)"
  proof (intro subsetI variety_ofI)
    fix a f
    assume "a \<in> \<V> F"
    hence "a \<in> \<V> (ideal F)" by simp
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    with \<open>a \<in> \<V> (ideal F)\<close> have "eval_pm a (f ^ m) = 0" by (rule variety_ofD)
    thus "eval_pm a f = 0" by (simp add: eval_pm_power)
  qed
qed

subsection \<open>Nullstellensatz\<close>

lemma weak_Nullstellensatz_aux:
  assumes "F \<subseteq> P[insert x X]" and "x \<notin> X" and "1 \<notin> ideal F"
  obtains a::"'a::alg_closed_field" where "1 \<notin> eval_pm (\<lambda>_. monomial a 0) ` focus {x} ` ideal F"
proof (cases "ideal F \<inter> P[{x}] \<subseteq> {0}")
  case True
  then show ?thesis sorry
next
  case False
  then obtain f where "f \<in> ideal F" and "f \<in> P[{x}]" and "f \<noteq> 0" by blast
  then show ?thesis sorry
qed

thm indets_eval_pm_focus_subset

theorem weak_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]" and "\<V> F = {}"
  shows "(1::_ \<Rightarrow>\<^sub>0 'a::alg_closed_field) \<in> ideal F"
  sorry

thm ideal_eq_UNIV_iff_contains_one

theorem Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]" and "(f::_ \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<I> (\<V> F)"
  shows "f \<in> \<surd>ideal F"
  sorry

theorem strong_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "\<I> (\<V> F) = \<surd>ideal (F::(_ \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
proof (intro subset_antisym subsetI)
  fix f
  assume "f \<in> \<I> (\<V> F)"
  with assms show "f \<in> \<surd>ideal F" by (rule Nullstellensatz)
qed (metis ideal_ofI variety_ofD variety_of_radical_ideal)

lemma radical_ideal_iff:
  assumes "finite X" and "F \<subseteq> P[X]" and "y \<notin> X" and "y \<notin> indets f"
  shows "f \<in> \<surd>ideal F \<longleftrightarrow> 1 \<in> ideal (insert (1 - punit.monom_mult 1 (Poly_Mapping.single y 1) f) F)"
  sorry

end (* theory *)
