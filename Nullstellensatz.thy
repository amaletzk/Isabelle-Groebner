(* Author: Alexander Maletzky *)

section \<open>Hilbert's Nullstellensatz\<close>

theory Nullstellensatz
  imports Algebraically_Closed_Fields
          "HOL-Computational_Algebra.Fraction_Field"
          Lex_Order_PP
          Univariate_PM
          Groebner_PM
begin

text \<open>We prove the geometric version of Hilbert's Nullstellensatz, i.e. the precise correspondence
  between algebraic varieties and radical ideals.\<close>

subsection \<open>Preliminaries\<close>

lemma finite_linorder_induct [consumes 1, case_names empty insert]:
  assumes "finite (A::'a::linorder set)" and "P {}"
    and "\<And>a A. finite A \<Longrightarrow> A \<subseteq> {..<a} \<Longrightarrow> P A \<Longrightarrow> P (insert a A)"
  shows "P A"
proof -
  define k where "k = card A"
  thus ?thesis using assms(1)
  proof (induct k arbitrary: A)
    case 0
    with assms(2) show ?case by simp
  next
    case (Suc k)
    define a where "a = Max A"
    from Suc.prems(1) have "A \<noteq> {}" by auto
    with Suc.prems(2) have "a \<in> A" unfolding a_def by (rule Max_in)
    with Suc.prems have "k = card (A - {a})" by simp
    moreover from Suc.prems(2) have "finite (A - {a})" by simp
    ultimately have "P (A - {a})" by (rule Suc.hyps)
    with \<open>finite (A - {a})\<close> _ have "P (insert a (A - {a}))"
    proof (rule assms(3))
      show "A - {a} \<subseteq> {..<a}"
      proof
        fix b
        assume "b \<in> A - {a}"
        hence "b \<in> A" and "b \<noteq> a" by simp_all
        moreover from Suc.prems(2) this(1) have "b \<le> a" unfolding a_def by (rule Max_ge)
        ultimately show "b \<in> {..<a}" by simp
      qed
    qed
    with \<open>a \<in> A\<close> show ?case by (simp add: insert_absorb)
  qed
qed

lemma Fract_same: "Fract a a = (1 when a \<noteq> 0)"
  by (simp add: One_fract_def Zero_fract_def eq_fract when_def)

lemma Fract_eq_zero_iff: "Fract a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (metis (no_types, lifting) Zero_fract_def eq_fract(1) eq_fract(2) mult_eq_0_iff one_neq_zero)

lemma poly_plus_rightE:
  obtains c where "poly p (x + y) = poly p x + c * y"
proof (induct p arbitrary: thesis)
  case 0
  have "poly 0 (x + y) = poly 0 x + 0 * y" by simp
  thus ?case by (rule 0)
next
  case (pCons a p)
  obtain c where "poly p (x + y) = poly p x + c * y" by (rule pCons.hyps)
  hence "poly (pCons a p) (x + y) = a + (x + y) * (poly p x + c * y)" by simp
  also have "\<dots> = poly (pCons a p) x + (x * c + (poly p x + c * y)) * y" by (simp add: algebra_simps)
  finally show ?case by (rule pCons.prems)
qed

lemma poly_minus_rightE:
  obtains c where "poly p (x - y) = poly p x - c * (y::_::comm_ring)"
  by (metis (no_types, hide_lams) add_uminus_conv_diff linordered_field_class.sign_simps(5)
      mult_minus_left poly_plus_rightE)

lemma map_poly_plus:
  assumes "f 0 = 0" and "\<And>a b. f (a + b) = f a + f b"
  shows "map_poly f (p + q) = map_poly f p + map_poly f q"
  by (rule Polynomial.poly_eqI) (simp add: coeff_map_poly assms)

lemma map_poly_minus:
  assumes "f 0 = 0" and "\<And>a b. f (a - b) = f a - f b"
  shows "map_poly f (p - q) = map_poly f p - map_poly f q"
  by (rule Polynomial.poly_eqI) (simp add: coeff_map_poly assms)

lemma map_poly_sum:
  assumes "f 0 = 0" and "\<And>a b. f (a + b) = f a + f b"
  shows "map_poly f (sum g A) = (\<Sum>a\<in>A. map_poly f (g a))"
  by (induct A rule: infinite_finite_induct) (simp_all add: map_poly_plus assms)

lemma map_poly_times:
  assumes "f 0 = 0" and "\<And>a b. f (a + b) = f a + f b" and "\<And>a b. f (a * b) = f a * f b"
  shows "map_poly f (p * q) = map_poly f p * map_poly f q"
proof (induct p)
  case 0
  show ?case by simp
next
  case (pCons c p)
  show ?case by (simp add: assms map_poly_plus map_poly_smult map_poly_pCons pCons)
qed

lemma poly_Fract:
  assumes "set (Polynomial.coeffs p) \<subseteq> range (\<lambda>x. Fract x 1)"
  obtains q m where "poly p (Fract a b) = Fract q (b ^ m)"
  using assms
proof (induct p arbitrary: thesis)
  case 0
  have "poly 0 (Fract a b) = Fract 0 (b ^ 1)" by (simp add: fract_collapse)
  thus ?case by (rule 0)
next
  case (pCons c p)
  from pCons.hyps(1) have "insert c (set (Polynomial.coeffs p)) = set (Polynomial.coeffs (pCons c p))"
    by auto
  with pCons.prems(2) have "c \<in> range (\<lambda>x. Fract x 1)" and "set (Polynomial.coeffs p) \<subseteq> range (\<lambda>x. Fract x 1)"
    by blast+
  from this(2) obtain q0 m0 where poly_p: "poly p (Fract a b) = Fract q0 (b ^ m0)"
    using pCons.hyps(2) by blast
  from \<open>c \<in> _\<close> obtain c0 where c: "c = Fract c0 1" ..
  show ?case
  proof (cases "b = 0")
    case True
    hence "poly (pCons c p) (Fract a b) = Fract c0 (b ^ 0)" by (simp add: c fract_collapse)
    thus ?thesis by (rule pCons.prems)
  next
    case False
    hence "poly (pCons c p) (Fract a b) = Fract (c0 * b ^ Suc m0 + a * q0) (b ^ Suc m0)"
      by (simp add: poly_p c)
    thus ?thesis by (rule pCons.prems)
  qed
qed

lemma (in ordered_term) lt_sum_le_Max: "lt (sum f A) \<preceq>\<^sub>t ord_term_lin.Max {lt (f a) | a. a \<in> A}"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  thus ?case by (simp add: min_term_min)
next
  case empty
  thus ?case by (simp add: min_term_min)
next
  case (insert a A)
  show ?case
  proof (cases "A = {}")
    case True
    thus ?thesis by simp
  next
    case False
    from insert.hyps(1, 2) have "lt (sum f (insert a A)) = lt (f a + sum f A)" by simp
    also have "\<dots> \<preceq>\<^sub>t ord_term_lin.max (lt (f a)) (lt (sum f A))" by (rule lt_plus_le_max)
    also have "\<dots> \<preceq>\<^sub>t ord_term_lin.max (lt (f a)) (ord_term_lin.Max {lt (f a) |a. a \<in> A})"
      using insert.hyps(3) ord_term_lin.max.mono by blast
    also from insert.hyps(1) False have "\<dots> = ord_term_lin.Max (insert (lt (f a)) {lt (f x) |x. x \<in> A})"
      by simp
    also have "\<dots> = ord_term_lin.Max {lt (f x) |x. x \<in> insert a A}"
      by (rule arg_cong[where f=ord_term_lin.Max]) blast
    finally show ?thesis .
  qed
qed

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
        unfolding mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
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
    thus "lookup (q'' g1 \<odot> g1) u = 0" by (simp add: in_keys_iff)
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
        unfolding mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
      finally show False
      proof
        assume "u \<in> keys (q g2 \<odot> g2 + (mu * q' g2) \<odot> g2)"
        also have "\<dots> \<subseteq> keys (q g2 \<odot> g2) \<union> keys ((mu * q' g2) \<odot> g2)" by (fact Poly_Mapping.keys_add)
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
    thus "lookup (q'' g2 \<odot> g2) u = 0" by (simp add: in_keys_iff)
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
          unfolding q'' mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
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
      thus "lookup (q'' g \<odot> g) u = 0" by (simp add: in_keys_iff)
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
        unfolding q'' mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
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
    thus "lookup (q'' g \<odot> g) u = 0" by (simp add: in_keys_iff)
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

subsection \<open>Ideals and Varieties\<close>

definition variety_of :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> ('x \<Rightarrow> 'a::comm_semiring_1) set"
  where "variety_of F = {a. \<forall>f\<in>F. poly_eval a f = 0}"

definition ideal_of :: "('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set"
  where "ideal_of A = {f. \<forall>a\<in>A. poly_eval a f = 0}"

abbreviation "\<V> \<equiv> variety_of"
abbreviation "\<I> \<equiv> ideal_of"

lemma variety_ofI: "(\<And>f. f \<in> F \<Longrightarrow> poly_eval a f = 0) \<Longrightarrow> a \<in> \<V> F"
  by (simp add: variety_of_def)

lemma variety_ofI_alt: "poly_eval a ` F \<subseteq> {0} \<Longrightarrow> a \<in> \<V> F"
  by (auto intro: variety_ofI)

lemma variety_ofD: "a \<in> \<V> F \<Longrightarrow> f \<in> F \<Longrightarrow> poly_eval a f = 0"
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
    from this(2) show "poly_eval a f = 0"
    proof (induct f rule: ideal.span_induct_alt)
      case base
      show ?case by simp
    next
      case (step c f g)
      with \<open>a \<in> \<V> F\<close> show ?case by (auto simp: poly_eval_plus poly_eval_times dest: variety_ofD)
    qed
  qed
qed

lemma ideal_ofI: "(\<And>a. a \<in> A \<Longrightarrow> poly_eval a f = 0) \<Longrightarrow> f \<in> \<I> A"
  by (simp add: ideal_of_def)

lemma ideal_ofD: "f \<in> \<I> A \<Longrightarrow> a \<in> A \<Longrightarrow> poly_eval a f = 0"
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
  hence f: "poly_eval a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  assume "g \<in> \<I> A"
  hence g: "poly_eval a g = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "f + g \<in> \<I> A" by (rule ideal_ofI) (simp add: poly_eval_plus f g)
next
  fix c f
  assume "f \<in> \<I> A"
  hence f: "poly_eval a f = 0" if "a \<in> A" for a using that by (rule ideal_ofD)
  show "c * f \<in> \<I> A" by (rule ideal_ofI) (simp add: poly_eval_times f)
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

subsection \<open>Radical Ideals\<close>

definition radical :: "'a::monoid_mult set \<Rightarrow> 'a set" ("\<surd>(_)" [999] 999)
  where "radical F = {f. \<exists>m. f ^ m \<in> F}"

lemma radicalI: "f ^ m \<in> F \<Longrightarrow> f \<in> \<surd>F"
  by (auto simp: radical_def)

lemma radicalE:
  assumes "f \<in> \<surd>F"
  obtains m where "f ^ m \<in> F"
  using assms by (auto simp: radical_def)

lemma radical_empty [simp]: "\<surd>{} = {}"
  by (simp add: radical_def)

lemma radical_UNIV [simp]: "\<surd>UNIV = UNIV"
  by (simp add: radical_def)

lemma zero_in_radical_ideal [simp]: "0 \<in> \<surd>ideal F"
proof (rule radicalI)
  show "0 ^ 1 \<in> ideal F" by (simp add: ideal.span_zero)
qed

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
  show "\<surd>\<I> A \<subseteq> \<I> A" by (auto elim!: radicalE dest!: ideal_ofD intro!: ideal_ofI simp: poly_eval_power)
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
    with \<open>a \<in> \<V> (ideal F)\<close> have "poly_eval a (f ^ m) = 0" by (rule variety_ofD)
    thus "poly_eval a f = 0" by (simp add: poly_eval_power)
  qed
qed

subsection \<open>Nullstellensatz\<close>

lemma weak_Nullstellensatz_aux_1:
  assumes "\<And>i. i \<in> I \<Longrightarrow> g i \<in> ideal B"
  obtains c where "c \<in> ideal B" and "(\<Prod>i\<in>I. (f i + g i) ^ m i) = (\<Prod>i\<in>I. f i ^ m i) + c"
  using assms
proof (induct I arbitrary: thesis rule: infinite_finite_induct)
  case (infinite I)
  from ideal.span_zero show ?case by (rule infinite) (simp add: infinite(1))
next
  case empty
  from ideal.span_zero show ?case by (rule empty) simp
next
  case (insert j I)
  have "g i \<in> ideal B" if "i \<in> I" for i by (rule insert.prems) (simp add: that)
  with insert.hyps(3) obtain c where c: "c \<in> ideal B"
    and 1: "(\<Prod>i\<in>I. (f i + g i) ^ m i) = (\<Prod>i\<in>I. f i ^ m i) + c" by blast
  define k where "k = m j"
  obtain d where 2: "(f j + g j) ^ m j = f j ^ m j + d * g j" unfolding k_def[symmetric]
  proof (induct k arbitrary: thesis)
    case 0
    have "(f j + g j) ^ 0 = f j ^ 0 + 0 * g j" by simp
    thus ?case by (rule 0)
  next
    case (Suc k)
    obtain d where "(f j + g j) ^ k = f j ^ k + d * g j" by (rule Suc.hyps)
    hence "(f j + g j) ^ Suc k = (f j ^ k + d * g j) * (f j + g j)" by simp
    also have "\<dots> = f j ^ Suc k + (f j ^ k + d * (f j + g j)) * g j" by (simp add: algebra_simps)
    finally show ?case by (rule Suc.prems)
  qed
  from c have *: "f j ^ m j * c + (((\<Prod>i\<in>I. f i ^ m i) + c) * d) * g j \<in> ideal B" (is "?c \<in> _")
    by (intro ideal.span_add ideal.span_scale insert.prems insertI1)
  from insert.hyps(1, 2) have "(\<Prod>i\<in>insert j I. (f i + g i) ^ m i) =
                                (f j ^ m j + d * g j) * ((\<Prod>i\<in>I. f i ^ m i) + c)"
    by (simp add: 1 2)
  also from insert.hyps(1, 2) have "\<dots> = (\<Prod>i\<in>insert j I. f i ^ m i) + ?c" by (simp add: algebra_simps)
  finally have "(\<Prod>i\<in>insert j I. (f i + g i) ^ m i) = (\<Prod>i\<in>insert j I. f i ^ m i) + ?c" .
  with * show ?case by (rule insert.prems)
qed

lemma weak_Nullstellensatz_aux_2:
  assumes "finite X" and "F \<subseteq> P[insert x X]" and "X \<subseteq> {..<x::'x::{countable,linorder}}"
    and "1 \<notin> ideal F" and "ideal F \<inter> P[{x}] \<subseteq> {0}"
  obtains a::"'a::alg_closed_field" where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)"
proof -
  let ?x = "monomial 1 (Poly_Mapping.single x 1)"
  from assms(3) have "x \<notin> X" by blast
  hence eq1: "insert x X - {x} = X" and eq2: "insert x X - X = {x}" by blast+

  interpret i: pm_powerprod lex_pm "lex_pm_strict::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> _"
    unfolding lex_pm_def lex_pm_strict_def
    by standard (simp_all add: lex_pm_zero_min lex_pm_plus_monotone flip: lex_pm_def)
  have lpp_focus: "i.lpp (focus X g) = except (i.lpp g) {x}" if "g \<in> P[insert x X]" for g::"_ \<Rightarrow>\<^sub>0 'a"
  proof (cases "g = 0")
    case True
    thus ?thesis by simp
  next
    case False
    have keys_focus_g: "keys (focus X g) = (\<lambda>t. except t {x}) ` keys g"
      unfolding keys_focus using refl
    proof (rule image_cong)
      fix t
      assume "t \<in> keys g"
      also from that have "\<dots> \<subseteq> .[insert x X]" by (rule PolysD)
      finally have "keys t \<subseteq> insert x X" by (rule PPsD)
      hence "except t (- X) = except t (insert x X \<inter> - X)"
        by (metis (no_types, lifting) Int_commute except_keys_Int inf.orderE inf_left_commute)
      also from \<open>x \<notin> X\<close> have "insert x X \<inter> - X = {x}" by simp
      finally show "except t (- X) = except t {x}" .
    qed
    show ?thesis
    proof (rule i.punit.lt_eqI_keys)
      from False have "i.lpp g \<in> keys g" by (rule i.punit.lt_in_keys)
      thus "except (i.lpp g) {x} \<in> keys (focus X g)" unfolding keys_focus_g by (rule imageI)

      fix t
      assume "t \<in> keys (focus X g)"
      then obtain s where "s \<in> keys g" and t: "t = except s {x}" unfolding keys_focus_g ..
      from this(1) have "lex_pm s (i.lpp g)" by (rule i.punit.lt_max_keys)
      moreover have "keys s \<union> keys (i.lpp g) \<subseteq> {..x}"
      proof (rule Un_least)
        from \<open>g \<in> P[_]\<close> have "keys g \<subseteq> .[insert x X]" by (rule PolysD)
        with \<open>s \<in> keys g\<close> have "s \<in> .[insert x X]" ..
        hence "keys s \<subseteq> insert x X" by (rule PPsD)
        thus "keys s \<subseteq> {..x}" using assms(3) by auto

        from \<open>i.lpp g \<in> keys g\<close> \<open>keys g \<subseteq> _\<close> have "i.lpp g \<in> .[insert x X]" ..
        hence "keys (i.lpp g) \<subseteq> insert x X" by (rule PPsD)
        thus "keys (i.lpp g) \<subseteq> {..x}" using assms(3) by auto
      qed
      ultimately show "lex_pm t (except (i.lpp g) {x})" unfolding t by (rule lex_pm_except_max)
    qed
  qed

  define G where "G = i.punit.reduced_GB F"
  from assms(1) have "finite (insert x X)" by simp
  hence fin_G: "finite G" and G_sub: "G \<subseteq> P[insert x X]" and ideal_G: "ideal G = ideal F"
    and "0 \<notin> G" and G_isGB: "i.punit.is_Groebner_basis G" unfolding G_def using assms(2)
    by (rule i.finite_reduced_GB_Polys, rule i.reduced_GB_Polys, rule i.reduced_GB_ideal_Polys,
        rule i.reduced_GB_nonzero_Polys, rule i.reduced_GB_is_GB_Polys)
  define G' where "G' = focus X ` G"
  from fin_G \<open>0 \<notin> G\<close> have fin_G': "finite G'" and "0 \<notin> G'" by (auto simp: G'_def)
  have G'_sub: "G' \<subseteq> P[X]" by (auto simp: G'_def intro: focus_in_Polys)
  define G'' where "G'' = i.lcf ` G'"
  from \<open>0 \<notin> G'\<close> have "0 \<notin> G''" by (auto simp: G''_def i.punit.lc_eq_zero_iff)
  have lookup_focus_in: "lookup (focus X g) t \<in> P[{x}]" if "g \<in> G" for g t
  proof -
    have "lookup (focus X g) t \<in> range (lookup (focus X g))" by (rule rangeI)
    from that G_sub have "g \<in> P[insert x X]" ..
    hence "range (lookup (focus X g)) \<subseteq> P[insert x X - X]" by (rule focus_coeffs_subset_Polys')
    with \<open>_ \<in> range _\<close> have "lookup (focus X g) t \<in> P[insert x X - X]" ..
    also have "insert x X - X = {x}" by (simp only: eq2)
    finally show ?thesis .
  qed
  hence lcf_in: "i.lcf (focus X g) \<in> P[{x}]" if "g \<in> G" for g
    unfolding i.punit.lc_def using that by blast
  have G''_sub: "G'' \<subseteq> P[{x}]"
  proof
    fix c
    assume "c \<in> G''"
    then obtain g' where "g' \<in> G'" and c: "c = i.lcf g'" unfolding G''_def ..
    from \<open>g' \<in> G'\<close> obtain g where "g \<in> G" and g': "g' = focus X g" unfolding G'_def ..
    from this(1) show "c \<in> P[{x}]" unfolding c g' by (rule lcf_in)
  qed
  define P where "P = poly_of_pm x ` G''"
  from fin_G' have fin_P: "finite P" by (simp add: P_def G''_def)
  have "0 \<notin> P"
  proof
    assume "0 \<in> P"
    then obtain g'' where "g'' \<in> G''" and "0 = poly_of_pm x g''" unfolding P_def ..
    from this(2) have *: "keys g'' \<inter> .[{x}] = {}" by (simp add: poly_of_pm_eq_zero_iff)
    from \<open>g'' \<in> G''\<close> G''_sub have "g'' \<in> P[{x}]" ..
    hence "keys g'' \<subseteq> .[{x}]" by (rule PolysD)
    with * have "keys g'' = {}" by blast
    with \<open>g'' \<in> G''\<close> \<open>0 \<notin> G''\<close> show False by simp
  qed
  define Z where "Z = (\<Union>p\<in>P. {z. poly p z = 0})"
  have "finite Z" unfolding Z_def using fin_P
  proof (rule finite_UN_I)
    fix p
    assume "p \<in> P"
    with \<open>0 \<notin> P\<close> have "p \<noteq> 0" by blast
    thus "finite {z. poly p z = 0}" by (rule poly_roots_finite)
  qed
  with infinite_UNIV[where 'a='a] have "- Z \<noteq> {}" using finite_compl by fastforce
  then obtain a where "a \<notin> Z" by blast

  have a_nz: "poly_eval (\<lambda>_. a) (i.lcf (focus X g)) \<noteq> 0" if "g \<in> G" for g
  proof -
    from that G_sub have "g \<in> P[insert x X]" ..
    have "poly_eval (\<lambda>_. a) (i.lcf (focus X g)) = poly (poly_of_pm x (i.lcf (focus X g))) a"
      by (rule sym, intro poly_eq_poly_eval' lcf_in that)
    moreover have "poly_of_pm x (i.lcf (focus X g)) \<in> P"
      by (auto simp: P_def G''_def G'_def that intro!: imageI)
    ultimately show ?thesis using \<open>a \<notin> Z\<close> by (simp add: Z_def)
  qed

  let ?e = "poly_eval (\<lambda>_. monomial a 0)"
  have lookup_e_focus: "lookup (?e (focus {x} g)) t = poly_eval (\<lambda>_. a) (lookup (focus X g) t)"
    if "g \<in> P[insert x X]" for g t
  proof -
    have "focus (- {x}) g = focus (- {x} \<inter> insert x X) g" by (rule sym) (rule focus_Int, fact)
    also have "\<dots> = focus X g" by (simp add: Int_commute eq1 flip: Diff_eq)
    finally show ?thesis by (simp add: lookup_poly_eval_focus)
  qed
  have lpp_e_focus: "i.lpp (?e (focus {x} g)) = except (i.lpp g) {x}" if "g \<in> G" for g
  proof (rule i.punit.lt_eqI_keys)
    from that G_sub have "g \<in> P[insert x X]" ..
    hence "lookup (?e (focus {x} g)) (except (i.lpp g) {x}) = poly_eval (\<lambda>_. a) (i.lcf (focus X g))"
      by (simp only: lookup_e_focus lpp_focus i.punit.lc_def)
    also from that have "\<dots> \<noteq> 0" by (rule a_nz)
    finally show "except (i.lpp g) {x} \<in> keys (?e (focus {x} g))" by (simp add: in_keys_iff)

    fix t
    assume "t \<in> keys (?e (focus {x} g))"
    hence "0 \<noteq> lookup (?e (focus {x} g)) t" by (simp add: in_keys_iff)
    also from \<open>g \<in> P[_]\<close> have "lookup (?e (focus {x} g)) t = poly_eval (\<lambda>_. a) (lookup (focus X g) t)"
      by (rule lookup_e_focus)
    finally have "t \<in> keys (focus X g)" by (auto simp flip: lookup_not_eq_zero_eq_in_keys)
    hence "lex_pm t (i.lpp (focus X g))" by (rule i.punit.lt_max_keys)
    with \<open>g \<in> P[_]\<close> show "lex_pm t (except (i.lpp g) {x})" by (simp only: lpp_focus)
  qed

  show ?thesis
  proof
    define G3 where "G3 = ?e ` focus {x} ` G"
    have "G3 \<subseteq> P[X]"
    proof
      fix h
      assume "h \<in> G3"
      then obtain h0 where "h0 \<in> G" and h: "h = ?e (focus {x} h0)" by (auto simp: G3_def)
      from this(1) G_sub have "h0 \<in> P[insert x X]" ..
      hence "h \<in> P[insert x X - {x}]" unfolding h by (rule poly_eval_focus_in_Polys)
      thus "h \<in> P[X]" by (simp only: eq1)
    qed
    from fin_G have "finite G3" by (simp add: G3_def)
    
    have "ideal G3 \<inter> P[- {x}] = ?e ` focus {x} ` ideal G"
      by (simp only: G3_def image_poly_eval_focus_ideal)
    also have "\<dots> = ideal (?e ` focus {x} ` F) \<inter> P[- {x}]"
      by (simp only: ideal_G image_poly_eval_focus_ideal)
    finally have eq3: "ideal G3 \<inter> P[- {x}] = ideal (?e ` focus {x} ` F) \<inter> P[- {x}]" .
    from assms(1) \<open>G3 \<subseteq> P[X]\<close> \<open>finite G3\<close> have G3_isGB: "i.punit.is_Groebner_basis G3"
    proof (rule i.punit.isGB_I_spoly_rep[simplified, OF dickson_grading_varnum_wrt,
                                          where m=0, simplified i.dgrad_p_set_varnum_wrt])
      fix g1 g2
      assume "g1 \<in> G3"
      then obtain g1' where "g1' \<in> G" and g1: "g1 = ?e (focus {x} g1')"
        unfolding G3_def by blast
      from this(1) have lpp1: "i.lpp g1 = except (i.lpp g1') {x}" unfolding g1 by (rule lpp_e_focus)
      from \<open>g1' \<in> G\<close> G_sub have "g1' \<in> P[insert x X]" ..
      assume "g2 \<in> G3"
      then obtain g2' where "g2' \<in> G" and g2: "g2 = ?e (focus {x} g2')"
        unfolding G3_def by blast
      from this(1) have lpp2: "i.lpp g2 = except (i.lpp g2') {x}" unfolding g2 by (rule lpp_e_focus)
      from \<open>g2' \<in> G\<close> G_sub have "g2' \<in> P[insert x X]" ..

      define l where "l = lcs (except (i.lpp g1') {x}) (except (i.lpp g2') {x})"
      define c1 where "c1 = i.lcf (focus X g1')"
      define c2 where "c2 = i.lcf (focus X g2')"
      define c where "c = poly_eval (\<lambda>_. a) c1 * poly_eval (\<lambda>_. a) c2"
      define s where "s = c2 * punit.monom_mult 1 (l - except (i.lpp g1') {x}) g1' -
                          c1 * punit.monom_mult 1 (l - except (i.lpp g2') {x}) g2'"
      have "c1 \<in> P[{x}]" unfolding c1_def using \<open>g1' \<in> G\<close> by (rule lcf_in)
      hence eval_c1: "poly_eval (\<lambda>_. monomial a 0) (focus {x} c1) = monomial (poly_eval (\<lambda>_. a) c1) 0"
        by (simp add: focus_Polys poly_eval_sum poly_eval_monomial monomial_power_map_scale
                  times_monomial_monomial flip: punit.monomial_prod_sum monomial_sum)
           (simp add: poly_eval_alt)
      have "c2 \<in> P[{x}]" unfolding c2_def using \<open>g2' \<in> G\<close> by (rule lcf_in)
      hence eval_c2: "poly_eval (\<lambda>_. monomial a 0) (focus {x} c2) = monomial (poly_eval (\<lambda>_. a) c2) 0"
        by (simp add: focus_Polys poly_eval_sum poly_eval_monomial monomial_power_map_scale
                  times_monomial_monomial flip: punit.monomial_prod_sum monomial_sum)
           (simp add: poly_eval_alt)

      assume spoly_nz: "i.punit.spoly g1 g2 \<noteq> 0"
      assume "g1 \<noteq> 0" and "g2 \<noteq> 0"
      hence "g1' \<noteq> 0" and "g2' \<noteq> 0" by (auto simp: g1 g2)
      have c1_nz: "poly_eval (\<lambda>_. a) c1 \<noteq> 0" unfolding c1_def using \<open>g1' \<in> G\<close> by (rule a_nz)
      moreover have c2_nz: "poly_eval (\<lambda>_. a) c2 \<noteq> 0" unfolding c2_def using \<open>g2' \<in> G\<close> by (rule a_nz)
      ultimately have "c \<noteq> 0" by (simp add: c_def)
      hence "inverse c \<noteq> 0" by simp
      from \<open>g1' \<in> P[_]\<close> have "except (i.lpp g1') {x} \<in> .[insert x X - {x}]"
        by (intro PPs_closed_except' i.PPs_closed_lpp)
      moreover from \<open>g2' \<in> P[_]\<close> have "except (i.lpp g2') {x} \<in> .[insert x X - {x}]"
        by (intro PPs_closed_except' i.PPs_closed_lpp)
      ultimately have "l \<in> .[insert x X - {x}]" unfolding l_def by (rule PPs_closed_lcs)
      hence "l \<in> .[X]" by (simp only: eq1)
      hence "l \<in> .[insert x X]" by rule (rule PPs_mono, blast)
      moreover from \<open>c1 \<in> P[{x}]\<close> have "c1 \<in> P[insert x X]" by rule (intro Polys_mono, simp)
      moreover from \<open>c2 \<in> P[{x}]\<close> have "c2 \<in> P[insert x X]" by rule (intro Polys_mono, simp)
      ultimately have "s \<in> P[insert x X]" using \<open>g1' \<in> P[_]\<close> \<open>g2' \<in> P[_]\<close> unfolding s_def
        by (intro Polys_closed_minus Polys_closed_times Polys_closed_monom_mult PPs_closed_minus)
      have "s \<in> ideal G" unfolding s_def times_monomial_left[symmetric]
        by (intro ideal.span_diff ideal.span_scale ideal.span_base \<open>g1' \<in> G\<close> \<open>g2' \<in> G\<close>)
      with G_isGB have "(i.punit.red G)\<^sup>*\<^sup>* s 0" by (rule i.punit.GB_imp_zero_reducibility[simplified])
      with \<open>finite (insert x X)\<close> G_sub fin_G \<open>s \<in> P[_]\<close>
      obtain q0 where 1: "s = 0 + (\<Sum>g\<in>G. q0 g * g)" and 2: "\<And>g. q0 g \<in> P[insert x X]"
        and 3: "\<And>g. lex_pm (i.lpp (q0 g * g)) (i.lpp s)"
        by (rule i.punit.red_rtrancl_repE[simplified, OF dickson_grading_varnum_wrt, where m=0,
                                            simplified i.dgrad_p_set_varnum_wrt]) blast

      define q where "q = (\<lambda>g. inverse c \<cdot> (\<Sum>h\<in>{y\<in>G. ?e (focus {x} y) = g}. ?e (focus {x} (q0 h))))"

      have eq4: "?e (focus {x} (monomial 1 (l - t))) = monomial 1 (l - t)" for t
      proof -
        have "focus {x} (monomial (1::'a) (l - t)) = monomial (monomial 1 (l - t)) 0"
        proof (intro focus_Polys_Compl Polys_closed_monomial PPs_closed_minus)
          from \<open>x \<notin> X\<close> have "X \<subseteq> - {x}" by simp
          hence ".[X] \<subseteq> .[- {x}]" by (rule PPs_mono)
          with \<open>l \<in> .[X]\<close> show "l \<in> .[- {x}]" ..
        qed
        thus ?thesis by (simp add: poly_eval_monomial)
      qed
      from c2_nz have eq5: "inverse c * poly_eval (\<lambda>_. a) c2 = 1 / lookup g1 (i.lpp g1)"
        unfolding lpp1 using \<open>g1' \<in> P[_]\<close>
        by (simp add: c_def mult.assoc divide_inverse_commute g1 lookup_e_focus
                flip: lpp_focus i.punit.lc_def c1_def)
      from c1_nz have eq6: "inverse c * poly_eval (\<lambda>_. a) c1 = 1 / lookup g2 (i.lpp g2)"
        unfolding lpp2 using \<open>g2' \<in> P[_]\<close>
        by (simp add: c_def mult.assoc mult.left_commute[of "inverse (poly_eval (\<lambda>_. a) c1)"]
                    divide_inverse_commute g2 lookup_e_focus flip: lpp_focus i.punit.lc_def c2_def)
      have l_alt: "l = lcs (i.lpp g1) (i.lpp g2)" by (simp only: l_def lpp1 lpp2)
      have spoly_eq: "i.punit.spoly g1 g2 = (inverse c) \<cdot> ?e (focus {x} s)"
        by (simp add: s_def focus_minus focus_times poly_eval_minus poly_eval_times eval_c1 eval_c2
                      eq4 eq5 eq6 map_scale_eq_times times_monomial_monomial right_diff_distrib
                      i.punit.spoly_def Let_def
                 flip: mult.assoc times_monomial_left g1 g2 lpp1 lpp2 l_alt)
      also have "\<dots> = (\<Sum>g\<in>G. inverse c \<cdot> (?e (focus {x} (q0 g)) * ?e (focus {x} g)))"
        by (simp add: 1 focus_sum poly_eval_sum focus_times poly_eval_times map_scale_sum_distrib_left)
      also have "\<dots> = (\<Sum>g\<in>G3. \<Sum>h\<in>{y\<in>G. ?e (focus{x} y) = g}.
                                      inverse c \<cdot> (?e (focus {x} (q0 h)) * ?e (focus {x} h)))"
        unfolding G3_def image_image using fin_G by (rule sum.image_gen)
      also have "\<dots> = (\<Sum>g\<in>G3. inverse c \<cdot> (\<Sum>h\<in>{y\<in>G. ?e (focus{x} y) = g}. ?e (focus {x} (q0 h))) * g)"
        by (intro sum.cong refl) (simp add: map_scale_eq_times sum_distrib_left sum_distrib_right mult.assoc)
      also from refl have "\<dots> = (\<Sum>g\<in>G3. q g * g)" by (rule sum.cong) (simp add: q_def sum_distrib_right)
      finally have "i.punit.spoly g1 g2 = (\<Sum>g\<in>G3. q g * g)" .
      thus "i.punit.spoly_rep (varnum_wrt X) 0 G3 g1 g2"
      proof (rule i.punit.spoly_repI[simplified, where m=0 and d="varnum_wrt X",
                                        simplified i.dgrad_p_set_varnum_wrt])
        fix g
        show "q g \<in> P[X]" unfolding q_def
        proof (intro Polys_closed_map_scale Polys_closed_sum)
          fix g0
          from \<open>q0 g0 \<in> P[insert x X]\<close> have "?e (focus {x} (q0 g0)) \<in> P[insert x X - {x}]"
            by (rule poly_eval_focus_in_Polys)
          thus "?e (focus {x} (q0 g0)) \<in> P[X]" by (simp only: eq1)
        qed

        assume "q g \<noteq> 0 \<and> g \<noteq> 0"
        hence "q g \<noteq> 0" ..
        have "i.lpp (q g * g) = i.lpp (\<Sum>h\<in>{y\<in>G. ?e (focus {x} y) = g}. inverse c \<cdot> ?e (focus {x} (q0 h)) * g)"
          by (simp add: q_def map_scale_sum_distrib_left sum_distrib_right)
        also have "lex_pm \<dots> (i.ordered_powerprod_lin.Max
                {i.lpp (inverse c \<cdot> ?e (focus {x} (q0 h)) * g) | h. h \<in> {y\<in>G. ?e (focus {x} y) = g}})"
          (is "lex_pm _ (i.ordered_powerprod_lin.Max ?A)") by (fact i.punit.lt_sum_le_Max)
        also have "lex_pm \<dots> (i.lpp s)"
        proof (rule i.ordered_powerprod_lin.Max.boundedI)
          from fin_G show "finite ?A" by simp
        next
          show "?A \<noteq> {}"
          proof
            assume "?A = {}"
            hence "{h \<in> G. ?e (focus {x} h) = g} = {}" by simp
            hence "q g = 0" by (simp only: q_def sum.empty map_scale_zero_right)
            with \<open>q g \<noteq> 0\<close> show False ..
          qed
        next
          fix t
          assume "t \<in> ?A"
          then obtain h where "h \<in> G" and g[symmetric]: "?e (focus {x} h) = g"
            and "t = i.lpp (inverse c \<cdot> ?e (focus {x} (q0 h)) * g)" by blast
          note this(3)
          also have "i.lpp (inverse c \<cdot> ?e (focus {x} (q0 h)) * g) =
                      i.lpp (inverse c \<cdot> (?e (focus {x} (q0 h * h))))"
            by (simp only: map_scale_eq_times mult.assoc g poly_eval_times focus_times)
          also from \<open>inverse c \<noteq> 0\<close> have "\<dots> = i.lpp (?e (focus {x} (q0 h * h)))"
            by (rule i.punit.lt_map_scale)
          also have "lex_pm \<dots> (i.lpp (q0 h * h))"
          proof (rule i.punit.lt_le, rule ccontr)
            fix u
            assume "lookup (?e (focus {x} (q0 h * h))) u \<noteq> 0"
            hence "u \<in> keys (?e (focus {x} (q0 h * h)))" by (simp add: in_keys_iff)
            with keys_poly_eval_focus_subset have "u \<in> (\<lambda>v. except v {x}) ` keys (q0 h * h)" ..
            then obtain v where "v \<in> keys (q0 h * h)" and u: "u = except v {x}" ..
            have "lex_pm u (Poly_Mapping.single x (lookup v x) + u)"
              by (metis add.commute add.right_neutral i.plus_monotone_left lex_pm_zero_min)
            also have "\<dots> = v" by (simp only: u flip: plus_except)
            also from \<open>v \<in> _\<close> have "lex_pm v (i.lpp (q0 h * h))" by (rule i.punit.lt_max_keys)
            finally have "lex_pm u (i.lpp (q0 h * h))" .
            moreover assume "lex_pm_strict (i.lpp (q0 h * h)) u"
            ultimately show False by simp
          qed
          also have "lex_pm \<dots> (i.lpp s)" by fact
          finally show "lex_pm t (i.lpp s)" .
        qed
        also have "lex_pm_strict \<dots> l"
        proof (rule i.punit.lt_less)
          from spoly_nz show "s \<noteq> 0" by (auto simp: spoly_eq)
        next
          fix t
          assume "lex_pm l t"

          have "g1' = flatten (focus X g1')" by simp
          also have "\<dots> = flatten (monomial c1 (i.lpp (focus X g1')) + i.punit.tail (focus X g1'))"
            by (simp only: c1_def flip: i.punit.leading_monomial_tail)
          also from \<open>g1' \<in> P[_]\<close> have "\<dots> = punit.monom_mult 1 (except (i.lpp g1') {x}) c1 +
                                              flatten (i.punit.tail (focus X g1'))"
            by (simp only: flatten_plus flatten_monomial lpp_focus)
          finally have "punit.monom_mult 1 (except (i.lpp g1') {x}) c1 +
                              flatten (i.punit.tail (focus X g1')) = g1'" (is "?l = _") by (rule sym)
          moreover have "c2 * punit.monom_mult 1 (l - except (i.lpp g1') {x}) ?l =
                          punit.monom_mult 1 l (c1 * c2) +
                          c2 * punit.monom_mult 1 (l - i.lpp (focus X g1'))
                                                  (flatten (i.punit.tail (focus X g1')))"
            (is "_ = punit.monom_mult 1 l (c1 * c2) + ?a")
            by (simp add: punit.monom_mult_dist_right punit.monom_mult_assoc l_def minus_plus adds_lcs)
               (simp add: distrib_left lpp_focus \<open>g1' \<in> P[_]\<close> flip: times_monomial_left)
          ultimately have a: "c2 * punit.monom_mult 1 (l - except (i.lpp g1') {x}) g1' =
                                punit.monom_mult 1 l (c1 * c2) + ?a" by simp

          have "g2' = flatten (focus X g2')" by simp
          also have "\<dots> = flatten (monomial c2 (i.lpp (focus X g2')) + i.punit.tail (focus X g2'))"
            by (simp only: c2_def flip: i.punit.leading_monomial_tail)
          also from \<open>g2' \<in> P[_]\<close> have "\<dots> = punit.monom_mult 1 (except (i.lpp g2') {x}) c2 +
                                              flatten (i.punit.tail (focus X g2'))"
            by (simp only: flatten_plus flatten_monomial lpp_focus)
          finally have "punit.monom_mult 1 (except (i.lpp g2') {x}) c2 +
                              flatten (i.punit.tail (focus X g2')) = g2'" (is "?l = _") by (rule sym)
          moreover have "c1 * punit.monom_mult 1 (l - except (i.lpp g2') {x}) ?l =
                          punit.monom_mult 1 l (c1 * c2) +
                          c1 * punit.monom_mult 1 (l - i.lpp (focus X g2'))
                                                  (flatten (i.punit.tail (focus X g2')))"
            (is "_ = punit.monom_mult 1 l (c1 * c2) + ?b")
            by (simp add: punit.monom_mult_dist_right punit.monom_mult_assoc l_def minus_plus adds_lcs_2)
               (simp add: distrib_left lpp_focus \<open>g2' \<in> P[_]\<close> flip: times_monomial_left)
          ultimately have b: "c1 * punit.monom_mult 1 (l - except (i.lpp g2') {x}) g2' =
                                punit.monom_mult 1 l (c1 * c2) + ?b" by simp

          have lex_pm_strict_t: "lex_pm_strict t (l - i.lpp (focus X h) + i.lpp (focus X h))"
            if "t \<in> keys (d * punit.monom_mult 1 (l - i.lpp (focus X h))
                                            (flatten (i.punit.tail (focus X h))))"
            and "h \<in> G" and "d \<in> P[{x}]" for d h
          proof -
            have 0: "lex_pm_strict (u + v) w" if "lex_pm_strict v w" and "w \<in> .[X]" and "u \<in> .[{x}]"
              for u v w using that(1)
            proof (rule lex_pm_strict_plus_left)
              fix y z
              assume "y \<in> keys w"
              also from that(2) have "\<dots> \<subseteq> X" by (rule PPsD)
              also have "\<dots> \<subseteq> {..<x}" by fact
              finally have "y < x" by simp
              assume "z \<in> keys u"
              also from that(3) have "\<dots> \<subseteq> {x}" by (rule PPsD)
              finally show "y < z" using \<open>y < x\<close> by simp
            qed
            let ?h = "focus X h"
            from that(2) have "?h \<in> G'" by (simp add: G'_def)
            with \<open>G' \<subseteq> P[X]\<close> have "?h \<in> P[X]" ..
            hence "i.lpp ?h \<in> .[X]" by (rule i.PPs_closed_lpp)
            from that(1) obtain t1 t2 where "t1 \<in> keys d"
              and "t2 \<in> keys (punit.monom_mult 1 (l - i.lpp ?h) (flatten (i.punit.tail ?h)))"
              and t: "t = t1 + t2" by (rule in_keys_timesE)
            from this(2) obtain t3 where "t3 \<in> keys (flatten (i.punit.tail ?h))"
              and t2: "t2 = l - i.lpp ?h + t3" by (auto simp: punit.keys_monom_mult)
            from this(1) obtain t4 t5 where "t4 \<in> keys (i.punit.tail ?h)"
              and t5_in: "t5 \<in> keys (lookup (i.punit.tail ?h) t4)" and t3: "t3 = t4 + t5"
              using keys_flatten_subset by blast
            from this(1) have 1: "lex_pm_strict t4 (i.lpp ?h)" by (rule i.punit.keys_tail_less_lt)
            from that(2) have "lookup ?h t4 \<in> P[{x}]" by (rule lookup_focus_in)
            hence "keys (lookup ?h t4) \<subseteq> .[{x}]" by (rule PolysD)
            moreover from t5_in have t5_in: "t5 \<in> keys (lookup ?h t4)"
              by (simp add: i.punit.lookup_tail split: if_split_asm)
            ultimately have "t5 \<in> .[{x}]" ..
            with 1 \<open>i.lpp ?h \<in> _\<close> have "lex_pm_strict (t5 + t4) (i.lpp ?h)" by (rule 0)
            hence "lex_pm_strict t3 (i.lpp ?h)" by (simp only: t3 add.commute)
            hence "lex_pm_strict t2 (l - i.lpp ?h + i.lpp ?h)" unfolding t2
              by (rule i.plus_monotone_strict_left)
            moreover from \<open>l \<in> .[X]\<close> \<open>i.lpp ?h \<in> .[X]\<close> have "l - i.lpp ?h + i.lpp ?h \<in> .[X]"
              by (intro PPs_closed_plus PPs_closed_minus)
            moreover from \<open>t1 \<in> keys d\<close> that(3) have "t1 \<in> .[{x}]" by (auto dest: PolysD)
            ultimately show ?thesis unfolding t by (rule 0)
          qed
          show "lookup s t = 0"
          proof (rule ccontr)
            assume "lookup s t \<noteq> 0"
            hence "t \<in> keys s" by (simp add: in_keys_iff)
            also have "\<dots> = keys (?a - ?b)" by (simp add: s_def a b)
            also have "\<dots> \<subseteq> keys ?a \<union> keys ?b" by (fact keys_minus)
            finally show False
            proof
              assume "t \<in> keys ?a"
              hence "lex_pm_strict t (l - i.lpp (focus X g1') + i.lpp (focus X g1'))"
                using \<open>g1' \<in> G\<close> \<open>c2 \<in> P[{x}]\<close> by (rule lex_pm_strict_t)
              with \<open>g1' \<in> P[_]\<close> have "lex_pm_strict t l"
                by (simp add: lpp_focus l_def minus_plus adds_lcs)
              with \<open>lex_pm l t\<close> show ?thesis by simp
            next
              assume "t \<in> keys ?b"
              hence "lex_pm_strict t (l - i.lpp (focus X g2') + i.lpp (focus X g2'))"
                using \<open>g2' \<in> G\<close> \<open>c1 \<in> P[{x}]\<close> by (rule lex_pm_strict_t)
              with \<open>g2' \<in> P[_]\<close> have "lex_pm_strict t l"
                by (simp add: lpp_focus l_def minus_plus adds_lcs_2)
              with \<open>lex_pm l t\<close> show ?thesis by simp
            qed
          qed
        qed
        also have "\<dots> = lcs (i.lpp g1) (i.lpp g2)" by (simp only: l_def lpp1 lpp2)
        finally show "lex_pm_strict (i.lpp (q g * g)) (lcs (i.lpp g1) (i.lpp g2))" .
      qed
    qed
    have "1 \<in> ideal (?e ` focus {x} ` F) \<longleftrightarrow> 1 \<in> ideal (?e ` focus {x} ` F) \<inter> P[- {x}]"
      by (simp add: one_in_Polys)
    also have "\<dots> \<longleftrightarrow> 1 \<in> ideal G3" by (simp add: one_in_Polys flip: eq3)
    also have "\<not> \<dots>"
    proof
      note G3_isGB
      moreover assume "1 \<in> ideal G3"
      moreover have "1 \<noteq> (0::_ \<Rightarrow>\<^sub>0 'a)" by simp
      ultimately obtain g where "g \<in> G3" and "g \<noteq> 0" and "i.lpp g adds i.lpp (1::_ \<Rightarrow>\<^sub>0 'a)"
        by (rule i.punit.GB_adds_lt[simplified])
      from this(3) have "i.lpp g = 0" by (simp add: i.punit.lt_monomial adds_zero flip: single_one)
      hence "monomial (i.lcf g) 0 = g" by (rule i.punit.lt_eq_min_term_monomial[simplified])
      from \<open>g \<in> G3\<close> obtain g' where "g' \<in> G" and g: "g = ?e (focus {x} g')" by (auto simp: G3_def)
      from this(1) have "i.lpp g = except (i.lpp g') {x}" unfolding g by (rule lpp_e_focus)
      hence "keys (i.lpp g') \<subseteq> {x}" by (simp add: \<open>i.lpp g = 0\<close> except_eq_zero_iff)
      have "g' \<in> P[{x}]"
      proof (intro PolysI subsetI PPsI)
        fix t y
        assume "t \<in> keys g'"
        hence "lex_pm t (i.lpp g')" by (rule i.punit.lt_max_keys)
        moreover assume "y \<in> keys t"
        ultimately obtain z where "z \<in> keys (i.lpp g')" and "z \<le> y" by (rule lex_pm_keys_leE)
        with \<open>keys (i.lpp g') \<subseteq> {x}\<close> have "x \<le> y" by blast
        from \<open>g' \<in> G\<close> G_sub have "g' \<in> P[insert x X]" ..
        hence "indets g' \<subseteq> insert x X" by (rule PolysD)
        moreover from \<open>y \<in> _\<close> \<open>t \<in> _\<close> have "y \<in> indets g'" by (rule in_indetsI)
        ultimately have "y \<in> insert x X" ..
        thus "y \<in> {x}"
        proof
          assume "y \<in> X"
          with assms(3) have "y \<in> {..<x}" ..
          with \<open>x \<le> y\<close> show ?thesis by simp
        qed simp
      qed
      moreover from \<open>g' \<in> G\<close> have "g' \<in> ideal G" by (rule ideal.span_base)
      ultimately have "g' \<in> ideal F \<inter> P[{x}]" by (simp add: ideal_G)
      with assms(5) have "g' = 0" by blast
      hence "g = 0" by (simp add: g)
      with \<open>g \<noteq> 0\<close> show False ..
    qed
    finally show "1 \<notin> ideal (?e ` focus {x} ` F)" .
  qed
qed

lemma weak_Nullstellensatz_aux_3:
  assumes "F \<subseteq> P[insert x X]" and "x \<notin> X" and "1 \<notin> ideal F" and "\<not> ideal F \<inter> P[{x}] \<subseteq> {0}"
  obtains a::"'a::alg_closed_field" where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)"
proof -
  let ?x = "monomial 1 (Poly_Mapping.single x 1)"
  from assms(4) obtain f where "f \<in> ideal F" and "f \<in> P[{x}]" and "f \<noteq> 0" by blast
  define p where "p = poly_of_pm x f"
  from \<open>f \<in> P[{x}]\<close> \<open>f \<noteq> 0\<close> have "p \<noteq> 0"
    by (auto simp: p_def poly_of_pm_eq_zero_iff simp flip: keys_eq_empty dest!: PolysD(1))
  obtain c A m where A: "finite A" and p: "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and "\<And>x. m x = 0 \<longleftrightarrow> x \<notin> A" and "c = 0 \<longleftrightarrow> p = 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)"
    by (rule linear_factorsE) blast
  from this(4, 5) have "c \<noteq> 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> z \<in> A" by (simp_all add: \<open>p \<noteq> 0\<close>)
  have "\<exists>a\<in>A. 1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)"
  proof (rule ccontr)
    assume asm: "\<not> (\<exists>a\<in>A. 1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F))"
    obtain g h where "g a \<in> ideal F" and 1: "h a * (?x - monomial a 0) + g a = 1"
      if "a \<in> A" for a
    proof -
      define P where "P = (\<lambda>gh a. fst gh \<in> ideal F \<and> fst gh + snd gh * (?x - monomial a 0) = 1)"
      define gh where "gh = (\<lambda>a. SOME gh. P gh a)"
      show ?thesis
      proof
        fix a
        assume "a \<in> A"
        with asm have "1 \<in> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)" by blast
        hence "1 \<in> poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` ideal F"
          by (simp add: image_poly_eval_focus_ideal one_in_Polys)
        then obtain g where "g \<in> ideal F" and "1 = poly_eval (\<lambda>_. monomial a 0) (focus {x} g)"
          unfolding image_image ..
        note this(2)
        also have "poly_eval (\<lambda>_. monomial a 0) (focus {x} g) = poly (poly_of_focus x g) (monomial a 0)"
          by (simp only: poly_poly_of_focus)
        also have "\<dots> = poly (poly_of_focus x g) (?x - (?x - monomial a 0))" by simp
        also obtain h where "\<dots> = poly (poly_of_focus x g) ?x - h * (?x - monomial a 0)"
          by (rule poly_minus_rightE)
        also have "\<dots> = g - h * (?x - monomial a 0)" by (simp only: poly_poly_of_focus_monomial)
        finally have "g - h * (?x - monomial a 0) = 1" by (rule sym)
        with \<open>g \<in> ideal F\<close> have "P (g, - h) a" by (simp add: P_def)
        hence "P (gh a) a" unfolding gh_def by (rule someI)
        thus "fst (gh a) \<in> ideal F" and "snd (gh a) * (?x - monomial a 0) + fst (gh a) = 1"
          by (simp_all only: P_def add.commute)
      qed
    qed
    from this(1) obtain g' where "g' \<in> ideal F"
      and 2: "(\<Prod>a\<in>A. (h a * (?x - monomial a 0) + g a) ^ m a) =
                (\<Prod>a\<in>A. (h a * (?x - monomial a 0)) ^ m a) + g'"
      by (rule weak_Nullstellensatz_aux_1)
    have "1 = (\<Prod>a\<in>A. (h a * (?x - monomial a 0) + g a) ^ m a)"
      by (rule sym) (intro prod.neutral ballI, simp only: 1 power_one)
    also have "\<dots> = (\<Prod>a\<in>A. h a ^ m a) * (\<Prod>a\<in>A. (?x - monomial a 0) ^ m a) + g'"
      by (simp only: 2 power_mult_distrib prod.distrib)
    also have "(\<Prod>a\<in>A. (?x - monomial a 0) ^ m a) = pm_of_poly x (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
      by (simp add: pm_of_poly_prod pm_of_poly_pCons single_uminus punit.monom_mult_monomial
              flip: single_one)
    also from \<open>c \<noteq> 0\<close> have "\<dots> = monomial (inverse c) 0 * pm_of_poly x p"
      by (simp add: p map_scale_assoc flip: map_scale_eq_times)
    also from \<open>f \<in> P[{x}]\<close> have "\<dots> = monomial (inverse c) 0 * f"
      by (simp only: \<open>p = poly_of_pm x f\<close> pm_of_poly_of_pm)
    finally have "1 = ((\<Prod>a\<in>A. h a ^ m a) * monomial (inverse c) 0) * f + g'"
      by (simp only: mult.assoc)
    also from \<open>f \<in> ideal F\<close> \<open>g' \<in> ideal F\<close> have "\<dots> \<in> ideal F" by (intro ideal.span_add ideal.span_scale)
    finally have "1 \<in> ideal F" .
    with assms(3) show False ..
  qed
  then obtain a where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a 0) ` focus {x} ` F)" ..
  thus ?thesis ..
qed

theorem weak_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]" and "\<V> F = ({}::('x::{countable,linorder} \<Rightarrow> 'a::alg_closed_field) set)"
  shows "ideal F = UNIV"
  unfolding ideal_eq_UNIV_iff_contains_one
proof (rule ccontr)
  assume "1 \<notin> ideal F"
  with assms(1, 2) obtain a where "1 \<notin> ideal (poly_eval a ` F)"
  proof (induct X arbitrary: F thesis rule: finite_linorder_induct)
    case empty
    have "F \<subseteq> {0}"
    proof
      fix f
      assume "f \<in> F"
      with empty.prems(2) have "f \<in> P[{}]" ..
      then obtain c where f: "f = monomial c 0" unfolding Polys_empty ..
      also have "c = 0"
      proof (rule ccontr)
        assume "c \<noteq> 0"
        from \<open>f \<in> F\<close> have "f \<in> ideal F" by (rule ideal.span_base)
        hence "monomial (inverse c) 0 * f \<in> ideal F" by (rule ideal.span_scale)
        with \<open>c \<noteq> 0\<close> have "1 \<in> ideal F" by (simp add: f times_monomial_monomial)
        with empty.prems(3) show False ..
      qed
      finally show "f \<in> {0}" by simp
    qed
    hence "poly_eval 0 ` F \<subseteq> {0}" by auto
    hence "ideal (poly_eval 0 ` F) = {0}" by simp
    hence "1 \<notin> ideal (poly_eval 0 ` F)" by (simp del: ideal_eq_zero_iff)
    thus ?case by (rule empty.prems)
  next
    case (insert x X)
    obtain a0 where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a0 0) ` focus {x} ` F)" (is "_ \<notin> ideal ?F")
    proof (cases "ideal F \<inter> P[{x}] \<subseteq> {0}")
      case True
      with insert.hyps(1) insert.prems(2) insert.hyps(2) insert.prems(3) obtain a0
        where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a0 0) ` focus {x} ` F)"
        by (rule weak_Nullstellensatz_aux_2)
      thus ?thesis ..
    next
      case False
      from insert.hyps(2) have "x \<notin> X" by blast
      with insert.prems(2) obtain a0 where "1 \<notin> ideal (poly_eval (\<lambda>_. monomial a0 0) ` focus {x} ` F)"
        using insert.prems(3) False by (rule weak_Nullstellensatz_aux_3)
      thus ?thesis ..
    qed
    moreover have "?F \<subseteq> P[X]"
    proof -
      {
        fix f
        assume "f \<in> F"
        with insert.prems(2) have "f \<in> P[insert x X]" ..
        hence "poly_eval (\<lambda>_. monomial a0 0) (focus {x} f) \<in> P[insert x X - {x}]"
          by (rule poly_eval_focus_in_Polys)
        also have "\<dots> \<subseteq> P[X]" by (rule Polys_mono) simp
        finally have "poly_eval (\<lambda>_. monomial a0 0) (focus {x} f) \<in> P[X]" .
      }
      thus ?thesis by blast
    qed
    ultimately obtain a1 where "1 \<notin> ideal (poly_eval a1 ` ?F)" using insert.hyps(3) by blast
    also have "poly_eval a1 ` ?F = poly_eval (a1(x := poly_eval a1 (monomial a0 0))) ` F"
      by (simp add: image_image poly_eval_poly_eval_focus fun_upd_def)
    finally show ?case by (rule insert.prems)
  qed
  hence "ideal (poly_eval a ` F) \<noteq> UNIV" by (simp add: ideal_eq_UNIV_iff_contains_one)
  hence "ideal (poly_eval a ` F) = {0}" using ideal_field_disj[of "poly_eval a ` F"] by blast
  hence "poly_eval a ` F \<subseteq> {0}" by simp
  hence "a \<in> \<V> F" by (rule variety_ofI_alt)
  thus False by (simp add: assms(3))
qed

lemma radical_idealI:
  assumes "finite X" and "F \<subseteq> P[X]" and "f \<in> P[X]" and "x \<notin> X"
    and "\<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single x 1) f) F) = {}"
  shows "(f::('x::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::alg_closed_field) \<in> \<surd>ideal F"
proof (cases "f = 0")
  case True
  thus ?thesis by simp
next
  case False
  from assms(4) have "P[X] \<subseteq> P[- {x}]" by (auto simp: Polys_alt)
  with assms(3) have "f \<in> P[- {x}]" ..
  let ?x = "Poly_Mapping.single x 1"
  let ?f = "punit.monom_mult 1 ?x f"
  from assms(1) have "finite (insert x X)" by simp
  moreover have "insert (1 - ?f) F \<subseteq> P[insert x X]" unfolding insert_subset
  proof (intro conjI Polys_closed_minus one_in_Polys Polys_closed_monom_mult PPs_closed_single)
    have "P[X] \<subseteq> P[insert x X]" by (rule Polys_mono) blast
    with assms(2, 3) show "f \<in> P[insert x X]" and "F \<subseteq> P[insert x X]" by blast+
  qed simp
  ultimately have "ideal (insert (1 - ?f) F) = UNIV"
    using assms(5) by (rule weak_Nullstellensatz)
  hence "1 \<in> ideal (insert (1 - ?f) F)" by simp
  then obtain F' q where fin': "finite F'" and F'_sub: "F' \<subseteq> insert (1 - ?f) F"
    and eq: "1 = (\<Sum>f'\<in>F'. q f' * f')" by (rule ideal.spanE)
  show "f \<in> \<surd>ideal F"
  proof (cases "1 - ?f \<in> F'")
    case True
    define g where "g = (\<lambda>x::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a. Fract x 1)"
    define F'' where "F'' = F' - {1 - ?f}"
    define q0 where "q0 = q (1 - ?f)"
    have g_0: "g 0 = 0" by (simp add: g_def fract_collapse)
    have g_1: "g 1 = 1" by (simp add: g_def fract_collapse)
    have g_plus: "g (a + b) = g a + g b" for a b by (simp add: g_def)
    have g_minus: "g (a - b) = g a - g b" for a b by (simp add: g_def)
    have g_times: "g (a * b) = g a * g b" for a b by (simp add: g_def)
    from fin' have fin'': "finite F''" by (simp add: F''_def)
    from F'_sub have F''_sub: "F'' \<subseteq> F" by (auto simp: F''_def)

    have "focus {x} ?f = monomial 1 ?x * focus {x} f"
      by (simp add: focus_times focus_monomial except_single flip: times_monomial_left)
    also from \<open>f \<in> P[- {x}]\<close> have "focus {x} f = monomial f 0" by (rule focus_Polys_Compl)
    finally have "focus {x} ?f = monomial f ?x" by (simp add: times_monomial_monomial)
    hence eq1: "poly (map_poly g (poly_of_focus x (1 - ?f))) (Fract 1 f) = 0"
      by (simp add: poly_of_focus_def focus_minus poly_of_pm_minus poly_of_pm_monomial
                PPs_closed_single map_poly_minus g_0 g_1 g_minus map_poly_monom poly_monom)
         (simp add: g_def Fract_same \<open>f \<noteq> 0\<close>)
    have eq2: "poly (map_poly g (poly_of_focus x f')) (Fract 1 f) = Fract f' 1" if "f' \<in> F''" for f'
    proof -
      from that F''_sub have "f' \<in> F" ..
      with assms(2) have "f' \<in> P[X]" ..
      with \<open>P[X] \<subseteq> _\<close> have "f' \<in> P[- {x}]" ..
      hence "focus {x} f' = monomial f' 0" by (rule focus_Polys_Compl)
      thus ?thesis
        by (simp add: poly_of_focus_def focus_minus poly_of_pm_minus poly_of_pm_monomial
                zero_in_PPs map_poly_minus g_0 g_1 g_minus map_poly_monom poly_monom)
           (simp only: g_def)
    qed

    define p0m0 where "p0m0 = (\<lambda>f'. SOME z. poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) =
                                              Fract (fst z) (f ^ snd z))"
    define p0 where "p0 = fst \<circ> p0m0"
    define m0 where "m0 = snd \<circ> p0m0"
    define m where "m = Max (m0 ` F'')"
    have eq3: "poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) = Fract (p0 f') (f ^ m0 f')"
      for f'
    proof -
      have "g a = 0 \<longleftrightarrow> a = 0" for a by (simp add: g_def Fract_eq_zero_iff)
      hence "set (Polynomial.coeffs (map_poly g (poly_of_focus x (q f')))) \<subseteq> range (\<lambda>x. Fract x 1)"
        by (auto simp: set_coeffs_map_poly g_def)
      then obtain p m' where "poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) = Fract p (f ^ m')"
        by (rule poly_Fract)
      hence "poly (map_poly g (poly_of_focus x (q f'))) (Fract 1 f) = Fract (fst (p, m')) (f ^ snd (p, m'))"
        by simp
      thus ?thesis unfolding p0_def m0_def p0m0_def o_def by (rule someI)
    qed
    
    note eq
    also from True fin' have "(\<Sum>f'\<in>F'. q f' * f') = q0 * (1 - ?f) + (\<Sum>f'\<in>F''. q f' * f')"
      by (simp add: q0_def F''_def sum.remove)
    finally have "poly_of_focus x 1 = poly_of_focus x (q0 * (1 - ?f) + (\<Sum>f'\<in>F''. q f' * f'))"
      by (rule arg_cong)
    hence "1 = poly (map_poly g (poly_of_focus x (q0 * (1 - ?f) + (\<Sum>f'\<in>F''. q f' * f')))) (Fract 1 f)"
      by (simp add: g_1)
    also have "\<dots> = poly (map_poly g (poly_of_focus x (\<Sum>f'\<in>F''. q f' * f'))) (Fract 1 f)"
      by (simp only: poly_of_focus_plus map_poly_plus g_0 g_plus g_times poly_add
                poly_of_focus_times map_poly_times poly_mult eq1 mult_zero_right add_0_left)
    also have "\<dots> = (\<Sum>f'\<in>F''. Fract (p0 f') (f ^ m0 f') * Fract f' 1)"
      by (simp only: poly_of_focus_sum poly_of_focus_times map_poly_sum map_poly_times
                g_0 g_plus g_times poly_sum poly_mult eq2 eq3 cong: sum.cong)
    finally have "Fract (f ^ m) 1 = Fract (f ^ m) 1 * (\<Sum>f'\<in>F''. Fract (p0 f' * f') (f ^ m0 f'))"
      by simp
    also have "\<dots> = (\<Sum>f'\<in>F''. Fract (f ^ m * (p0 f' * f')) (f ^ m0 f'))"
      by (simp add: sum_distrib_left)
    also from refl have "\<dots> = (\<Sum>f'\<in>F''. Fract ((f ^ (m - m0 f') * p0 f') * f') 1)"
    proof (rule sum.cong)
      fix f'
      assume "f' \<in> F''"
      hence "m0 f' \<in> m0 ` F''" by (rule imageI)
      with _ have "m0 f' \<le> m" unfolding m_def by (rule Max_ge) (simp add: fin'')
      hence "f ^ m = f ^ (m0 f') * f ^ (m - m0 f')" by (simp flip: power_add)
      hence "Fract (f ^ m * (p0 f' * f')) (f ^ m0 f') = Fract (f ^ m0 f') (f ^ m0 f') *
                                                        Fract (f ^ (m - m0 f') * (p0 f' * f')) 1"
        by (simp add: ac_simps)
      also from \<open>f \<noteq> 0\<close> have "Fract (f ^ m0 f') (f ^ m0 f') = 1" by (simp add: Fract_same)
      finally show "Fract (f ^ m * (p0 f' * f')) (f ^ m0 f') = Fract (f ^ (m - m0 f') * p0 f' * f') 1"
        by (simp add: ac_simps)
    qed
    also from fin'' have "\<dots> = Fract (\<Sum>f'\<in>F''. (f ^ (m - m0 f') * p0 f') * f') 1"
      by (induct F'') (simp_all add: fract_collapse)
    finally have "f ^ m = (\<Sum>f'\<in>F''. (f ^ (m - m0 f') * p0 f') * f')"
      by (simp add: eq_fract)
    also have "\<dots> \<in> ideal F''" by (rule ideal.sum_in_spanI)
    also from \<open>F'' \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.span_mono)
    finally show "f \<in> \<surd>ideal F" by (rule radicalI)
  next
    case False
    with F'_sub have "F' \<subseteq> F" by blast
    have "1 \<in> ideal F'" unfolding eq by (rule ideal.sum_in_spanI)
    also from \<open>F' \<subseteq> F\<close> have "\<dots> \<subseteq> ideal F" by (rule ideal.span_mono)
    finally have "ideal F = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one)
    thus ?thesis by simp
  qed
qed

corollary radical_idealI_extend_indets:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "\<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single None 1) (extend_indets f))
                            (extend_indets ` F)) = {}"
  shows "(f::(_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<surd>ideal F"
proof -
  define Y where "Y = X \<union> indets f"
  from assms(1) have fin_Y: "finite Y" by (simp add: Y_def finite_indets)
  have "P[X] \<subseteq> P[Y]" by (rule Polys_mono) (simp add: Y_def)
  with assms(2) have F_sub: "F \<subseteq> P[Y]" by (rule subset_trans)
  have f_in: "f \<in> P[Y]" by (simp add: Y_def Polys_alt)

  let ?F = "extend_indets ` F"
  let ?f = "extend_indets f"
  let ?X = "Some ` Y"
  from fin_Y have "finite ?X" by (rule finite_imageI)
  moreover from F_sub have "?F \<subseteq> P[?X]"
    by (auto simp: indets_extend_indets intro!: PolysI_alt imageI dest!: PolysD(2) subsetD[of F])
  moreover from f_in have "?f \<in> P[?X]"
    by (auto simp: indets_extend_indets intro!: PolysI_alt imageI dest!: PolysD(2))
  moreover have "None \<notin> ?X" by simp
  ultimately have "?f \<in> \<surd>ideal ?F" using assms(3) by (rule radical_idealI)
  also have "?f \<in> \<surd>ideal ?F \<longleftrightarrow> f \<in> \<surd>ideal F"
  proof
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    hence "extend_indets (f ^ m) \<in> extend_indets ` ideal F" by (rule imageI)
    with extend_indets_ideal_subset have "?f ^ m \<in> ideal ?F" unfolding extend_indets_power ..
    thus "?f \<in> \<surd>ideal ?F" by (rule radicalI)
  next
    assume "?f \<in> \<surd>ideal ?F"
    then obtain m where "?f ^ m \<in> ideal ?F" by (rule radicalE)
    moreover have "?f ^ m \<in> P[- {None}]"
      by (rule Polys_closed_power) (auto intro!: PolysI_alt simp: indets_extend_indets)
    ultimately have "extend_indets (f ^ m) \<in> extend_indets ` ideal F"
      by (simp add: extend_indets_ideal extend_indets_power)
    hence "f ^ m \<in> ideal F" by (simp only: inj_image_mem_iff[OF inj_extend_indets])
    thus "f \<in> \<surd>ideal F" by (rule radicalI)
  qed
  finally show ?thesis .
qed

theorem Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "(f::(_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<I> (\<V> F)"
  shows "f \<in> \<surd>ideal F"
  using assms(1, 2)
proof (rule radical_idealI_extend_indets)
  let ?f = "punit.monom_mult 1 (monomial 1 None) (extend_indets f)"
  show "\<V> (insert (1 - ?f) (extend_indets ` F)) = {}"
  proof (intro subset_antisym subsetI)
    fix a
    assume "a \<in> \<V> (insert (1 - ?f) (extend_indets ` F))"
    moreover have "1 - ?f \<in> insert (1 - ?f) (extend_indets ` F)" by simp
    ultimately have "poly_eval a (1 - ?f) = 0" by (rule variety_ofD)
    hence "poly_eval a (extend_indets f) \<noteq> 0"
      by (auto simp: poly_eval_minus poly_eval_times simp flip: times_monomial_left)
    hence "poly_eval (a \<circ> Some) f \<noteq> 0" by (simp add: poly_eval_extend_indets)
    have "a \<circ> Some \<in> \<V> F"
    proof (rule variety_ofI)
      fix f'
      assume "f' \<in> F"
      hence "extend_indets f' \<in> insert (1 - ?f) (extend_indets ` F)" by simp
      with \<open>a \<in> _\<close> have "poly_eval a (extend_indets f') = 0" by (rule variety_ofD)
      thus "poly_eval (a \<circ> Some) f' = 0" by (simp only: poly_eval_extend_indets)
    qed
    with assms(3) have "poly_eval (a \<circ> Some) f = 0" by (rule ideal_ofD)
    with \<open>poly_eval (a \<circ> Some) f \<noteq> 0\<close> show "a \<in> {}" ..
  qed simp
qed

theorem strong_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "\<I> (\<V> F) = \<surd>ideal (F::((_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
proof (intro subset_antisym subsetI)
  fix f
  assume "f \<in> \<I> (\<V> F)"
  with assms show "f \<in> \<surd>ideal F" by (rule Nullstellensatz)
qed (metis ideal_ofI variety_ofD variety_of_radical_ideal)

text \<open>The following lemma can be used for actually \<^emph>\<open>deciding\<close> whether a polynomial is contained in
  the radical of an ideal or not.\<close>

lemma radical_ideal_iff:
  assumes "finite X" and "F \<subseteq> P[X]" and "f \<in> P[X]" and "x \<notin> X"
  shows "(f::(_::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<surd>ideal F \<longleftrightarrow>
            1 \<in> ideal (insert (1 - punit.monom_mult 1 (Poly_Mapping.single x 1) f) F)"
proof -
  let ?f = "punit.monom_mult 1 (Poly_Mapping.single x 1) f"
  show ?thesis
  proof
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    from assms(1) have "finite (insert x X)" by simp
    moreover have "insert (1 - ?f) F \<subseteq> P[insert x X]" unfolding insert_subset
    proof (intro conjI Polys_closed_minus one_in_Polys Polys_closed_monom_mult PPs_closed_single)
      have "P[X] \<subseteq> P[insert x X]" by (rule Polys_mono) blast
      with assms(2, 3) show "f \<in> P[insert x X]" and "F \<subseteq> P[insert x X]" by blast+
    qed simp
    moreover have "\<V> (insert (1 - ?f) F) = {}"
    proof (intro subset_antisym subsetI)
      fix a
      assume "a \<in> \<V> (insert (1 - ?f) F)"
      moreover have "1 - ?f \<in> insert (1 - ?f) F" by simp
      ultimately have "poly_eval a (1 - ?f) = 0" by (rule variety_ofD)
      hence "poly_eval a (f ^ m) \<noteq> 0"
        by (auto simp: poly_eval_minus poly_eval_times poly_eval_power simp flip: times_monomial_left)
      from \<open>a \<in> _\<close> have "a \<in> \<V> (ideal (insert (1 - ?f) F))" by (simp only: variety_of_ideal)
      moreover from \<open>f ^ m \<in> ideal F\<close> ideal.span_mono have "f ^ m \<in> ideal (insert (1 - ?f) F)"
        by (rule rev_subsetD) blast
      ultimately have "poly_eval a (f ^ m) = 0" by (rule variety_ofD)
      with \<open>poly_eval a (f ^ m) \<noteq> 0\<close> show "a \<in> {}" ..
    qed simp
    ultimately have "ideal (insert (1 - ?f) F) = UNIV" by (rule weak_Nullstellensatz)
    thus "1 \<in> ideal (insert (1 - ?f) F)" by simp
  next
    assume "1 \<in> ideal (insert (1 - ?f) F)"
    have "\<V> (insert (1 - ?f) F) = {}"
    proof (intro subset_antisym subsetI)
      fix a
      assume "a \<in> \<V> (insert (1 - ?f) F)"
      hence "a \<in> \<V> (ideal (insert (1 - ?f) F))" by (simp only: variety_of_ideal)
      hence "poly_eval a 1 = 0" using \<open>1 \<in> _\<close> by (rule variety_ofD)
      thus "a \<in> {}" by simp
    qed simp
    with assms show "f \<in> \<surd>ideal F" by (rule radical_idealI)
  qed
qed

end (* theory *)
