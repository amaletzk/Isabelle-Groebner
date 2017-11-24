section \<open>New Bounds for the Membership Problem for Binomial Ideals\<close>

theory Membership_Bound_Binomials
imports Binomials Power_Products_Fun Poly_Multiplication
begin

subsection \<open>Structure of Binomial Ideals\<close>
  
context od_powerprod
begin

lemma rem_3_1_4_aux_1:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and "g' \<in> reduced_GB F" and "t \<in> supp g"
    and "lp g' dvd t"
  shows "g' = g"
proof (rule ccontr)
  let ?G = "reduced_GB F"
  assume "g' \<noteq> g"
  with \<open>g' \<in> ?G\<close> have "g' \<in> (remove g ?G)" by (rule in_removeI)
  have "\<not> is_red (remove g ?G) g" by (rule is_auto_reducedD, rule reduced_GB_is_auto_reduced, fact+)
  moreover have "is_red (remove g ?G) g"
  proof (rule is_red_singletonD, rule is_red_dvdI, rule)
    from reduced_GB_nonzero[OF fin] \<open>g' \<in> ?G\<close> show "g' \<noteq> 0" by auto
  qed fact+
  ultimately show False ..
qed

lemma rem_3_1_4_aux_2:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and "g' \<in> reduced_GB F" and "t \<in> supp g"
    and "lp g' dvd t"
  shows "t = lp g"
proof -
  from assms have "g' = g" by (rule rem_3_1_4_aux_1)
  from \<open>lp g' dvd t\<close> have "lp g \<preceq> t" unfolding \<open>g' = g\<close> by (rule ord_dvd)
  with lp_max_supp[OF \<open>t \<in> supp g\<close>] show ?thesis by simp
qed
  
text \<open>The following two lemmas are contained in Remark 3.1.4. of @{cite WW2015}.\<close>
  
lemma rem_3_1_4_1:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and lp_notin: "lp g \<notin> lp_set F"
  shows "\<not> is_red F g"
proof
  let ?G = "reduced_GB F"
  assume "is_red F g"
  then obtain f t where "f \<in> F" and "t \<in> supp g" and "f \<noteq> 0" and lpf: "lp f dvd t" by (rule is_red_dvdE)
  have "f \<in> pideal ?G" unfolding reduced_GB_pideal[OF fin]
    by (rule, fact \<open>f \<in> F\<close>, rule generator_subset_pideal)
  from reduced_GB_is_GB[OF fin] this \<open>f \<noteq> 0\<close> obtain g'
    where "g' \<in> ?G" and "g' \<noteq> 0" and lpg': "lp g' dvd lp f" by (rule GB_dvd_lp)
  from lpg' lpf have lpg'': "lp g' dvd t" by (rule dvd_trans)
  from _ \<open>g' \<noteq> 0\<close> \<open>t \<in> supp g\<close> this have red: "is_red {g'} g" by (rule is_red_dvdI, simp)
  from fin \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> \<open>t \<in> supp g\<close> lpg'' have "g' = g" and "t = lp g"
    by (rule rem_3_1_4_aux_1, rule rem_3_1_4_aux_2)
  from lpg' lpf have "lp g = lp f" unfolding \<open>t = lp g\<close> \<open>g' = g\<close> by (rule dvd_antisym)
  from \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> have "lp g \<in> lp_set F" unfolding \<open>lp g = lp f\<close> by (rule lp_setI)
  with lp_notin show False ..
qed

lemma rem_3_1_4_2:
  assumes fin: "finite F" and "g \<in> reduced_GB F" and bin: "is_proper_binomial g"
  shows "mpoly_of_pp`(supp g) \<inter> pideal F = {}"
  unfolding disjoint_eq_subset_Compl
proof (rule, rule)
  let ?G = "reduced_GB F"
  fix x
  assume xin1: "x \<in> mpoly_of_pp`(supp g)" and xin2: "x \<in> pideal F"
  from bin obtain c d s t where obd: "is_obd c s d t" and g: "g = binom c s d t"
    by (rule is_proper_binomial_binom_od)
  from obd have pbd: "is_pbd c s d t" by (rule obd_imp_pbd)
  have suppg: "supp g = {s, t}" unfolding g by (rule supp_binom_pbd, fact pbd)
  
  have a: "mpoly_of_pp t \<notin> pideal F"
  proof
    assume "mpoly_of_pp t \<in> pideal F" (is "?p \<in> pideal F")
    hence "?p \<in> pideal ?G" unfolding reduced_GB_pideal[OF fin] .
    have "?p \<noteq> 0" by (rule mpoly_of_pp_nonzero)
    from reduced_GB_is_GB[OF fin] \<open>?p \<in> pideal ?G\<close> this obtain g'
      where "g' \<in> ?G" and "g' \<noteq> 0" and lpg': "lp g' dvd lp ?p" by (rule GB_dvd_lp)
    from lpg' have lpg'': "lp g' dvd t" unfolding lp_mpoly_of_pp .
    have "t \<in> supp g" unfolding suppg by simp
    from fin \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> this lpg'' have "t = lp g" by (rule rem_3_1_4_aux_2)
    also have "... = s" unfolding g lp_binom[OF obd] ..
    finally show False using obd unfolding is_obd_def by simp
  qed

  from xin1 have "x = mpoly_of_pp s \<or> x = mpoly_of_pp t" unfolding suppg by simp
  thus False
  proof
    assume x: "x = mpoly_of_pp s"
    from pbd have "d \<noteq> 0" by (rule is_pbdE2)
    have "g \<in> pideal F" unfolding reduced_GB_pideal[OF fin, symmetric]
      by (rule, fact \<open>g \<in> ?G\<close>, rule generator_subset_pideal)
    from xin2 have "monom 1 s \<in> pideal F" unfolding x mpoly_of_pp_def .
    hence "monom_mult c 1 (monom 1 s) \<in> pideal F" by (rule pideal_closed_monom_mult)
    hence "monom c s \<in> pideal F" by (simp add: monom_mult_monom)
    with \<open>g \<in> pideal F\<close> have "g - monom c s \<in> pideal F" by (rule pideal_closed_minus)
    hence "monom d t \<in> pideal F" unfolding g binom_def by simp
    hence "monom_mult (1 / d) 1 (monom d t) \<in> pideal F" by (rule pideal_closed_monom_mult)
    hence "monom 1 t \<in> pideal F" using \<open>d \<noteq> 0\<close> by (simp add: monom_mult_monom)
    hence "mpoly_of_pp t \<in> pideal F" unfolding mpoly_of_pp_def .
    with a show False ..
  next
    assume x: "x = mpoly_of_pp t"
    from a xin2 show False unfolding x ..
  qed
qed

end (* od_powerprod *)

subsection \<open>Preliminaries\<close>
  
context ordered_powerprod
begin
  
text \<open>Unfortunately, @{term is_red} is only defined in locale @{locale od_powerprod}, so we have to
  define @{term is_red'} here, in context @{locale ordered_powerprod}.\<close>
definition is_red' :: "('a, 'b::zero) mpoly set \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> bool" where
  "is_red' F g = (\<exists>f\<in>F. \<exists>t\<in>supp g. f \<noteq> 0 \<and> lp f dvd t)"
  
lemma is_red'I:
  assumes "f \<in> F" and "f \<noteq> 0" and "t \<in> (supp p)" and "lp f dvd t"
  shows "is_red' F p"
  unfolding is_red'_def by (intro bexI conjI, fact \<open>f \<noteq> 0\<close>, fact \<open>lp f dvd t\<close>, fact+)

lemma is_red'E:
  assumes "is_red' F p"
  obtains f t where "f \<in> F" and "t \<in> (supp p)" and "f \<noteq> 0" and "lp f dvd t"
  using assms unfolding is_red'_def by auto

lemma rem_3_1_7_aux:
  assumes "g \<in> pideal F" and "t \<in> supp g"
  obtains f s where "f \<in> F" and "s \<in> supp f" and "s dvd t"
  using assms
proof (induct g arbitrary: thesis)
  case base: pideal_0
  from base(2) show ?case unfolding supp_of_0 ..
next
  case ind: (pideal_plus g f' c u)
  from ind(5) supp_plus have "t \<in> supp g \<union> supp (monom_mult c u f')" ..
  thus ?case
  proof
    assume "t \<in> supp g"
    obtain f s where "f \<in> F" and "s \<in> supp f" and "s dvd t"
    proof (rule ind(2))
      show "t \<in> supp g" by fact
    qed
    thus ?thesis by (rule ind(4))
  next
    assume "t \<in> supp (monom_mult c u f')"
    then obtain s where "s \<in> supp f'" and "t = u * s" by (rule supp_monom_multE)
    from \<open>f' \<in> F\<close> \<open>s \<in> supp f'\<close> show ?thesis
    proof (rule ind(4))
      show "s dvd t" unfolding \<open>t = u * s\<close> by simp
    qed
  qed
qed

lemma rem_3_1_7:
  assumes "is_binomial_set F" and gin: "g \<in> pideal F" and "\<not> is_red' F g" and tin: "t \<in> supp g"
  obtains f where "f \<in> F" and "is_proper_binomial f" and "tp f dvd t"
proof -
  from gin tin obtain f s where "f \<in> F" and "s \<in> supp f" and "s dvd t" by (rule rem_3_1_7_aux)
  have "s \<noteq> lp f"
  proof
    assume "s = lp f"
    from \<open>f \<in> F\<close> have "is_red' F g"
    proof (rule is_red'I)
      show "f \<noteq> 0"
      proof
        assume "f = 0"
        from \<open>s \<in> supp f\<close> show False unfolding \<open>f = 0\<close> supp_of_0 ..
      qed
    next
      from \<open>s dvd t\<close> show "lp f dvd t" unfolding \<open>s = lp f\<close> .
    qed fact
    with \<open>\<not> is_red' F g\<close> show False ..
  qed
  from \<open>is_binomial_set F\<close> \<open>f \<in> F\<close> have "is_binomial f" by (rule is_binomial_setD)
  hence "is_monomial f \<or> is_proper_binomial f" unfolding is_binomial_alt .
  hence "is_proper_binomial f"
  proof
    assume "is_monomial f"
    hence "supp f = {lp f}" by (rule supp_monomial)
    with \<open>s \<in> supp f\<close> \<open>s \<noteq> lp f\<close> show ?thesis by simp
  qed
  with \<open>f \<in> F\<close> show ?thesis
  proof
    from \<open>is_binomial f\<close> have "supp f = {lp f, tp f}" by (rule supp_binomial)
    with \<open>s \<in> supp f\<close> \<open>s \<noteq> lp f\<close> have "s = tp f" by simp
    with \<open>s dvd t\<close> show "tp f dvd t" by simp
  qed
qed

end (* od_powerprod *)
  
definition maxdeg :: "('n \<Rightarrow> 'a::add_linorder) set \<Rightarrow> 'a" where
  "maxdeg A = Max (deg ` A)"
  
definition mindeg :: "('n \<Rightarrow> 'a::add_linorder) set \<Rightarrow> 'a" where
  "mindeg A = Min (deg ` A)"
  
definition poly_deg :: "('n \<Rightarrow> 'a::add_linorder, 'b::zero) mpoly \<Rightarrow> 'a" where
  "poly_deg p = maxdeg (supp p)"

class finite_nat = finite + linorder + zero +
  assumes zero_min: "0 \<le> n"

locale fun_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"('n \<Rightarrow> 'a) \<Rightarrow> ('n::finite_nat \<Rightarrow> 'a::number_dom) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

definition overlap :: "('n \<Rightarrow> 'a, 'b::zero) mpoly \<Rightarrow> ('n \<Rightarrow> 'a, 'b) mpoly \<Rightarrow> ('n \<Rightarrow> 'a)"
  where "overlap f1 f2 = lub (glb (lp f1) (tp f1)) (glb (lp f2) (tp f2))"
    
definition vect :: "('n \<Rightarrow> 'a, 'b::zero) mpoly \<Rightarrow> ('n \<Rightarrow> 'a)"
  where "vect f = (lp f) - (tp f)"

definition membership_problem_assms ::
    "('n \<Rightarrow> 'a, 'b) mpoly \<Rightarrow> ('n \<Rightarrow> 'a, 'b) mpoly \<Rightarrow> ('n \<Rightarrow> 'a, 'b::semiring_1) mpoly \<Rightarrow> bool"
    where "membership_problem_assms f1 f2 g =
        (is_binomial f1 \<and> is_binomial f2 \<and> is_binomial g \<and> g \<in> pideal {f1, f2} \<and>
          \<not> is_red' {f1, f2} g \<and> (is_proper_binomial g \<longrightarrow> \<not> (mpoly_of_pp ` supp g) \<subseteq> pideal {f1, f2}))"

definition membership_problem_concl ::
    "('n \<Rightarrow> 'a, 'b) mpoly \<Rightarrow> ('n \<Rightarrow> 'a, 'b) mpoly \<Rightarrow> ('n \<Rightarrow> 'a, 'b::semiring_1) mpoly \<Rightarrow> (('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow>
      ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> bool"
  where "membership_problem_concl f1 f2 g d =
        (\<exists>q1 q2. g = q1 \<star> f1 + q2 \<star> f2 \<and>
          (q1 \<noteq> 0 \<longrightarrow> poly_deg (q1 \<star> f1) \<le> (d (lp f1) (tp f1) (lp f2) (tp f2) (lp g) (tp g))) \<and>
          (q2 \<noteq> 0 \<longrightarrow> poly_deg (q2 \<star> f2) \<le> (d (lp f1) (tp f1) (lp f2) (tp f2) (lp g) (tp g))))"

definition membership_problem ::
    "('b::semiring_1 itself) \<Rightarrow> (('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> bool"
  where "membership_problem _ d =
      (\<forall>f1 f2 g::('n \<Rightarrow> 'a, 'b) mpoly. membership_problem_assms f1 f2 g \<longrightarrow>
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
  shows "\<not> is_red' {f1, f2} g"
  using assms unfolding membership_problem_assms_def by simp

lemma membership_problem_assmsD6:
  assumes "membership_problem_assms f1 f2 g" and "is_proper_binomial g"
  shows "\<not> (mpoly_of_pp ` supp g) \<subseteq> pideal {f1, f2}"
  using assms unfolding membership_problem_assms_def by simp

lemma membership_problemI:
  assumes "\<And>f1 f2 g::('n \<Rightarrow> 'a, 'b::semiring_1) mpoly. membership_problem_assms f1 f2 g \<Longrightarrow>
            membership_problem_concl f1 f2 g d"
  shows "membership_problem TYPE('b) d"
  unfolding membership_problem_def using assms by auto

end (* fun_powerprod *)

locale two_binoms =
  fun_powerprod ord ord_strict
  for ord::"('n \<Rightarrow> 'a) \<Rightarrow> ('n::finite_nat \<Rightarrow> 'a::number_dom) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50) +
  (* The reason why we have to name the order relations again is that otherwise we cannot call the
    type variables 'n, 'a and 'b. *)
  fixes f1 f2 :: "('n \<Rightarrow> 'a, 'b::field) mpoly"
  assumes f1_binomial: "is_binomial f1"
  assumes f2_binomial: "is_binomial f2"
begin
  
lemma is_binomial_set: "is_binomial_set {f1, f2}"
  unfolding is_binomial_set_def using f1_binomial f2_binomial by simp

lemma lem_3_1_13:
  assumes "(tp f1) \<le> p" and "(tp f2) \<le> p"
  shows "overlap f1 f2 \<le> p"
  unfolding overlap_def
proof (rule lub_min_fun)
  have "glb (lp f1) (tp f1) \<le> (tp f1)" by (fact geq_glb_fun2)
  also from assms(1) have "... \<le> p" .
  finally show "glb (lp f1) (tp f1) \<le> p" .
next
  have "glb (lp f2) (tp f2) \<le> (tp f2)" by (fact geq_glb_fun2)
  also from assms(2) have "... \<le> p" .
  finally show "glb (lp f2) (tp f2) \<le> p" .
qed

definition step' :: "('n \<Rightarrow> 'a, 'b) mpoly \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "step' f p = Max ({div_ceil (overlap f1 f2 j - p j) (vect f j) | j::'n. vect f j \<noteq> 0 \<and> overlap f1 f2 j > p j} \<union> {0})"

definition step :: "('n \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "step p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<le> p) then
      step' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<le> p) p
    else
      0
    )"

lemma step'_above_overlap:
  assumes "overlap f1 f2 \<le> p"
  shows "step' f p = 0"
proof -
  let ?A = "{div_ceil (overlap f1 f2 j - p j) (vect f j) | j::'n. vect f j \<noteq> 0 \<and> overlap f1 f2 j > p j}"
  have eq: "?A = {}"
  proof (simp, intro allI)
    fix j
    show "vect f j = 0 \<or> \<not> p j < overlap f1 f2 j"
    proof (intro disjI2)
      from assms have "overlap f1 f2 j \<le> p j" unfolding le_fun_def ..
      thus "\<not> p j < overlap f1 f2 j" by simp
    qed
  qed
  show ?thesis unfolding step'_def eq by simp
qed

lemma step_welldefined:
  assumes "tp f1 \<le> p" and "tp f2 \<le> p"
  shows "step p = 0"
  unfolding step_def
proof (split if_split, intro conjI impI)
  from assms have "overlap f1 f2 \<le> p" by (rule lem_3_1_13)
  thus "step' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<le> p) p = 0"
    by (rule step'_above_overlap)
qed rule

lemma some_step_eqI:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<le> p" and "\<exists>g\<in>{f1,f2}. \<not> tp g \<le> p"
  shows "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<le> p) = f"
proof (rule some_equality)
  from assms show "f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<le> p" by simp
next
  fix f'
  assume "f' \<in> {f1, f2} \<and> is_proper_binomial f' \<and> tp f' \<le> p"
  hence "f' \<in> {f1, f2}" and "tp f' \<le> p" by simp_all
  show "f' = f"
  proof (rule ccontr)
    assume "f' \<noteq> f"
    have "\<forall>g\<in>{f1, f2}. tp g \<le> p"
    proof
      fix g
      assume "g \<in> {f1, f2}"
      with \<open>f \<in> {f1, f2}\<close> \<open>f' \<in> {f1, f2}\<close> \<open>f' \<noteq> f\<close> have "g = f \<or> g = f'" by auto
      with \<open>tp f \<le> p\<close> \<open>tp f' \<le> p\<close> show "tp g \<le> p" by auto
    qed
    with assms(4) show False by simp
  qed
qed

lemma step_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<le> p"
  shows "step p = step' f p"
proof (cases "\<forall>g\<in>{f1, f2}. tp g \<le> p")
  case True
  hence "tp f1 \<le> p" and "tp f2 \<le> p" by simp_all
  hence "step p = 0" and "overlap f1 f2 \<le> p" by (rule step_welldefined, rule lem_3_1_13)
  from this(2) have "step' f p = 0" by (rule step'_above_overlap)
  with \<open>step p = 0\<close> show ?thesis by simp
next
  case False
  hence "\<exists>g\<in>{f1,f2}. \<not> tp g \<le> p" by simp
  with assms have eq: "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<le> p) = f" by (rule some_step_eqI)
  show ?thesis unfolding step_def eq
  proof (split if_split, intro conjI impI, rule)
    assume "\<not> (\<exists>f\<in>{f1, f2}.is_proper_binomial f \<and> tp f \<le> p)"
    hence "\<forall>f\<in>{f1,f2}. (\<not> is_proper_binomial f) \<or> \<not> tp f \<le> p" by simp
    from this \<open>f \<in> {f1, f2}\<close> have "(\<not> is_proper_binomial f) \<or> \<not> tp f \<le> p" ..
    with assms(2) assms(3) show "0 = step' f p" by simp
  qed
qed

lemma step_alt2:
  assumes "(\<not> is_proper_binomial f1) \<or> p < tp f1" and "(\<not> is_proper_binomial f2) \<or> p < tp f2"
  shows "step p = 0"
proof -
  from assms have "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<le> p)" by auto
  thus ?thesis unfolding step_def by auto
qed

definition overlapshift' :: "('n \<Rightarrow> 'a, 'b) mpoly \<Rightarrow> ('n \<Rightarrow> 'a) \<Rightarrow> 'n \<Rightarrow> 'a" where
  "overlapshift' f p = p + (step' f p) \<cdot> (vect f)"

definition overlapshift :: "('n \<Rightarrow> 'a) \<Rightarrow> 'n \<Rightarrow> 'a" where
  "overlapshift p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<le> p) then
      overlapshift' (SOME f. f \<in> {f1,f2} \<and> is_proper_binomial f \<and> (tp f) \<le> p) p
    else
      p
    )"

lemma overlapshift'_above_overlap:
  assumes "overlap f1 f2 \<le> p"
  shows "overlapshift' f p = p"
  unfolding overlapshift'_def step'_above_overlap[OF assms] by (simp add: scalar_zero_left)

lemma overlapshift_welldefined:
  assumes "tp f1 \<le> p" and "tp f2 \<le> p"
  shows "overlapshift p = p"
  unfolding overlapshift_def
proof (split if_split, intro conjI impI)
  from assms have "overlap f1 f2 \<le> p" by (rule lem_3_1_13)
  thus "overlapshift' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<le> p) p = p"
    by (rule overlapshift'_above_overlap)
qed rule

lemma overlapshift_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<le> p"
  shows "overlapshift p = p + (step p) \<cdot> (vect f)"
proof (cases "\<forall>g\<in>{f1, f2}. tp g \<le> p")
  case True
  hence "tp f1 \<le> p" and "tp f2 \<le> p" by simp_all
  hence "overlapshift p = p" and "step p = 0" by (rule overlapshift_welldefined, rule step_welldefined)
  thus ?thesis by (simp add: scalar_zero_left)
next
  case False
  hence "\<exists>g\<in>{f1,f2}. \<not> tp g \<le> p" by simp
  with assms have eq: "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<le> p) = f" by (rule some_step_eqI)
  show ?thesis unfolding overlapshift_def eq
  proof (split if_split, intro conjI impI)
    from assms have "step p = step' f p" by (rule step_alt1)
    thus "overlapshift' f p = p + step p \<cdot> vect f" unfolding overlapshift'_def by simp
  next
    assume "\<not> (\<exists>f\<in>{f1, f2}. is_proper_binomial f \<and> tp f \<le> p)"
    hence "\<forall>f\<in>{f1,f2}. (\<not> is_proper_binomial f) \<or> \<not> tp f \<le> p" by simp
    from this \<open>f \<in> {f1, f2}\<close> have "(\<not> is_proper_binomial f) \<or> \<not> tp f \<le> p" ..
    with assms(2) assms(3) show "p = p + step p \<cdot> vect f" by simp
  qed
qed

lemma overlapshift_alt2:
  assumes "(\<not> is_proper_binomial f1) \<or> p < tp f1" and "(\<not> is_proper_binomial f2) \<or> p < tp f2"
  shows "overlapshift p = p"
proof -
  from assms have "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<le> p)" by auto
  thus ?thesis unfolding overlapshift_def by auto
qed
  
end (* two_binoms *)

subsection \<open>Degree Bounds on the Shifts for Generating a Monomial\<close>

locale binom_monom =
  fun_powerprod ord ord_strict
  for ord::"('n \<Rightarrow> 'a) \<Rightarrow> ('n::finite_nat \<Rightarrow> 'a::number_dom) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50) +
  fixes f1 f2 :: "('n \<Rightarrow> 'a, 'b::field) mpoly"
  assumes f1_proper_binomial: "is_proper_binomial f1"
  assumes f2_monomial: "is_monomial f2"
begin

sublocale two_binoms
proof
  from f1_proper_binomial show "is_binomial f1" by (rule proper_binomial_imp_binomial)
next
  from f2_monomial show "is_binomial f2" by (rule monomial_imp_binomial)
qed
  
lemma thm_3_2_1_aux_1:
  assumes "membership_problem_assms f1 f2 g" and "t \<in> supp g"
  shows "tp f1 dvd t"
proof-
  from assms(1) have "g \<in> pideal {f1, f2}" and "\<not> is_red' {f1, f2} g"
    by (rule membership_problem_assmsD4, rule membership_problem_assmsD5)
  from is_binomial_set this assms(2) obtain f where "f \<in> {f1, f2}" and "is_proper_binomial f"
    and "tp f dvd t" by (rule rem_3_1_7)
  from \<open>f \<in> {f1, f2}\<close> have "f = f1 \<or> f = f2" by simp
  thus ?thesis
  proof
    assume "f = f1"
    with \<open>tp f dvd t\<close> show ?thesis by simp
  next
    from \<open>is_proper_binomial f\<close> have "\<not> is_monomial f" by (rule proper_binomial_no_monomial)
    assume "f = f2"
    with \<open>\<not> is_monomial f\<close> f2_monomial show ?thesis by simp
  qed
qed

lemma thm_3_2_1_aux_1':
  assumes "membership_problem_assms f1 f2 g"
  shows "tp f1 dvd lp g"
  sorry

text \<open>The proof of the following lemma seems to require a significant amount of additional work
  (unless there is a simpler proof?). It goes along the following lines:
  - Because of the form of f1 and f2, applying Buchberger's algorithm to {f1, f2} yields a set of
    the form G = {f1, f2, h1, ..., hn} (where n could be 0), where each of the hi is a monomial
    multiple of tp(f1).
  - Since g is in pideal{f1, f2}, it must be reducible modulo G. But, since g is irreducible modulo
    f1 and f2, it must be reducible modulo H = {h1, ..., hn}.
  - Reducing g modulo H once only cancels one monomial but leaves the rest unchanged. So, also the
    rest must be reducible modulo H and so on, which eventually allows us to conclude that every
    monomial in supp(g) must be divisible by some hi.
  - Since every hi is in pideal{f1, f2}, this also holds for all monomials in g. Thus, if g contained
    more than one monomial, it would contradict the last part of "membership_problem_assms f1 f2 g".\<close>
lemma thm_3_2_1_aux_2:
  assumes "membership_problem_assms f1 f2 g"
  shows "is_monomial g"
proof -
  from assms have "is_binomial g" and "g \<in> pideal {f1, f2}"
    by (rule membership_problem_assmsD3, rule membership_problem_assmsD4)
  hence "is_monomial g \<or> is_proper_binomial g" unfolding is_binomial_alt by simp
  thus ?thesis
  proof
    assume "is_proper_binomial g"
    show ?thesis sorry
  qed
qed

lemma thm_3_2_1_aux_3:
  assumes "membership_problem_assms f1 f2 g"
  shows "0 < step (lp g)"
proof -
  from assms have "tp f1 dvd lp g" by (rule thm_3_2_1_aux_1')
  hence "tp f1 \<le> lp g" unfolding dvd_fun_min'
  oops

lemma thm_3_2_1_aux_4:
  assumes "membership_problem_assms f1 f2 g"
  shows "lp f2 \<le> lp g + (step (lp g)) \<cdot> (lp f1 - tp f1)"
  sorry

theorem thm_3_2_1:
  assumes "membership_problem_assms f1 f2 g"
  defines "k \<equiv> (SOME l::'a. 0 < l \<and> lp f2 \<le> lp g + l \<cdot> (lp f1 - tp f1))"
  shows "membership_problem_concl f1 f2 g (\<lambda>r r' s s' t t'. maxdeg {t, t + k \<cdot> (r - r')})"
  sorry

end

(*
subsection \<open>Standard Power-Products in Finitely Many Indeterminates\<close>

locale standard_powerprod =
  od_powerprod ord ord_strict
  for ord::"('n \<Rightarrow> 'a) \<Rightarrow> ('n::{finite,linorder} \<Rightarrow> 'a::add_wellorder) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin
  
lemma card_nonzero: "card (UNIV::'n set) \<noteq> 0"
  using finite_UNIV by simp
    
thm ord_canc
thm exists_unique_reduced_GB
  
end (* standard_powerprod *)
*)

end (* theory *)