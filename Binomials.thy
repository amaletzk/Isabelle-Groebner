(* Author: Alexander Maletzky *)

theory Binomials
  imports Reduced_GB "Groebner_Bases/Buchberger"
begin

context ordered_term
begin

section \<open>Monomial Ideals\<close>

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
  from keys_add_subset step(6) have "t \<in> keys p \<union> keys (monom_mult c s f0)" ..
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
  
section \<open>Reduction Modulo Monomials and Binomials\<close>

lemma red_setE2:
  assumes "red B p q"
  obtains b where "b \<in> B" and "red {b} p q"
proof -
  from assms obtain b t where "b \<in> B" and "red_single p q b t" by (rule red_setE)
  have "red {b} p q" by (rule red_setI, simp, fact)
  show ?thesis by (rule, fact+)
qed

lemma red_monomial_keys:
  assumes mon: "is_monomial r" and red: "red {r} p q"
  shows "card (keys p) = Suc (card (keys q))"
proof -
  from red obtain s where rs: "red_single p q r s" unfolding red_singleton ..
  hence cp0: "lookup p (s \<oplus> lt r) \<noteq> 0" and q_def0: "q = p - monom_mult (lookup p (s \<oplus> lt r) / lc r) s r"
    unfolding red_single_def by simp_all
  from mon obtain c t where "c \<noteq> 0" and r_def: "r = monomial c t" by (rule is_monomial_monomial)
  have ltr: "lt r = t" unfolding r_def by (rule lt_monomial, fact)
  have lcr: "lc r = c" unfolding r_def by (rule lc_monomial)
  define u where "u = s \<oplus> t"
  from q_def0 have "q = p - monom_mult (lookup p u / c) s r" unfolding u_def ltr lcr .
  also have "... = p - monomial ((lookup p u / c) * c) u" unfolding u_def r_def monom_mult_monomial ..
  finally have q_def: "q = p - monomial (lookup p u) u" using \<open>c \<noteq> 0\<close> by simp
  from cp0 have "lookup p u \<noteq> 0" unfolding u_def ltr .
  hence "u \<in> keys p" by simp
      
  have "keys q = keys p - {u}" unfolding q_def
  proof (rule, rule)
    fix x
    assume "x \<in> keys (p - monomial (lookup p u) u)"
    hence "lookup (p - monomial (lookup p u) u) x \<noteq> 0" by simp
    hence a: "lookup p x - lookup (monomial (lookup p u) u) x \<noteq> 0" unfolding lookup_minus .
    hence "x \<noteq> u" unfolding lookup_single by auto
    with a have "lookup p x \<noteq> 0" unfolding lookup_single by auto
    show "x \<in> keys p - {u}"
    proof
      from \<open>lookup p x \<noteq> 0\<close> show "x \<in> keys p" by simp
    next
      from \<open>x \<noteq> u\<close> show "x \<notin> {u}" by simp
    qed
  next
    show "keys p - {u} \<subseteq> keys (p - monomial (lookup p u) u)"
    proof
      fix x
      assume "x \<in> keys p - {u}"
      hence "x \<in> keys p" and "x \<noteq> u" by auto
      from \<open>x \<in> keys p\<close> have "lookup p x \<noteq> 0" by simp
      with \<open>x \<noteq> u\<close> have "lookup (p - monomial (lookup p u) u) x \<noteq> 0" by (simp add: lookup_minus lookup_single)
      thus "x \<in> keys (p - monomial (lookup p u) u)" by simp
    qed
  qed
      
  have "Suc (card (keys q)) = card (keys p)" unfolding \<open>keys q = keys p - {u}\<close>
    by (rule card_Suc_Diff1, rule finite_keys, fact)
  thus ?thesis by simp
qed
  
lemma red_binomial_keys:
  assumes "is_obd c s d t" and red: "red {binomial c s d t} p q"
  shows "card (keys q) \<le> card (keys p)"
proof -
  have pbd: "is_pbd c s d t" by (rule obd_imp_pbd, fact)
  have "c \<noteq> 0" by (rule is_pbdE1, fact)
      
  define r where "r = binomial c s d t"
  have sr: "keys r = {s, t}" unfolding r_def by (rule keys_binomial_pbd, rule obd_imp_pbd, fact)
  hence "r \<noteq> 0" using keys_eq_empty_iff[of r] by simp
  have ltr: "lt r = s" unfolding r_def by (rule lt_binomial, fact)
  have lcr: "lc r = c" unfolding r_def by (rule lc_binomial, fact)
  
  from red obtain u where rs: "red_single p q r u" unfolding r_def red_singleton ..
  hence cp0: "lookup p (u \<oplus> lt r) \<noteq> 0" and q_def0: "q = p - monom_mult (lookup p (u \<oplus> lt r) / lc r) u r"
    unfolding red_single_def by simp_all
  define v where "v = u \<oplus> s"
  define w where "w = u \<oplus> t"
  define cpv where "cpv = lookup p v"
  define r' where "r' = binomial cpv v ((cpv / c) * d) w"
  from cp0 have "cpv \<noteq> 0" unfolding cpv_def v_def ltr .
  with \<open>c \<noteq> 0\<close> have "cpv / c \<noteq> 0" by simp
  from \<open>cpv \<noteq> 0\<close> have "v \<in> keys p" unfolding cpv_def by simp
  from q_def0 have "q = p - monom_mult (cpv / c) u r" unfolding cpv_def ltr lcr v_def .
  also have "... = p - binomial ((cpv / c) * c) v ((cpv / c) * d) w"
    unfolding r_def monom_mult_binomial v_def w_def ..
  finally have q_def: "q = p - r'" using \<open>c \<noteq> 0\<close> unfolding r'_def by simp
      
  have "is_obd ((cpv / c) * c) v ((cpv / c) * d) w" unfolding v_def w_def by (rule is_obd_mult, fact+)
  hence obd_r': "is_obd cpv v ((cpv / c) * d) w" using \<open>c \<noteq> 0\<close> by simp
  have pbd_r': "is_pbd cpv v ((cpv / c) * d) w" by (rule obd_imp_pbd, fact)
      
  have sr': "keys r' = {v, w}" unfolding r'_def by (rule keys_binomial_pbd, rule obd_imp_pbd, fact)
  hence "r' \<noteq> 0" using keys_eq_empty_iff[of r'] by simp
  have ltr': "lt r' = v" unfolding r'_def by (rule lt_binomial, fact)
  have lcr': "lc r' = cpv" unfolding r'_def by (rule lc_binomial, fact)
      
  have "keys q \<subseteq> (keys p - {v}) \<union> {w}"
  proof
    fix x
    assume "x \<in> keys q"
    hence "lookup q x \<noteq> 0" by simp
    hence "lookup p x - lookup r' x \<noteq> 0" unfolding q_def by (simp add: lookup_minus)
    hence "lookup p x \<noteq> lookup r' x" by simp
    have "x \<noteq> v"
    proof
      assume "x = v"
      hence "lookup p x = cpv" unfolding cpv_def by simp
      also have "... = lookup r' x" unfolding r'_def lookup_binomial[OF pbd_r'] unfolding \<open>x = v\<close> by simp
      finally have "lookup p x = lookup r' x" .
      with \<open>lookup p x \<noteq> lookup r' x\<close> show False ..
    qed
    have "x \<in> keys p \<or> x = w"
    proof (intro disjCI)
      assume "x \<noteq> w"
      with \<open>x \<noteq> v\<close> have "x \<notin> keys r'" unfolding sr' by simp
      hence "lookup r' x = 0" by simp
      with \<open>lookup p x \<noteq> lookup r' x\<close> have "lookup p x \<noteq> 0" by simp
      thus "x \<in> keys p" by simp
    qed
    thus "x \<in> (keys p - {v}) \<union> {w}"
    proof
      assume "x \<in> keys p"
      with \<open>x \<noteq> v\<close> have "x \<in> (keys p) - {v}" by simp
      thus ?thesis by simp
    next
      assume "x = w"
      thus ?thesis by simp
    qed
  qed
  hence "card (keys q) \<le> card ((keys p - {v}) \<union> {w})" by (simp add: card_mono)
  also have "... \<le> card (keys p - {v}) + card {w}" using card_Un_le[of "keys p - {v}" "{w}"] .
  also have "... = Suc (card (keys p - {v}))" by simp
  also have "... = card (keys p)" using \<open>v \<in> keys p\<close> by (metis card_Suc_Diff1 finite_keys)
  finally show ?thesis .
qed
  
lemma red_binomial_keys':
  assumes bin: "is_binomial r" and red: "red {r} p q"
  shows "card (keys q) \<le> card (keys p)"
proof -
  from bin have "is_monomial r \<or> is_proper_binomial r" by (simp add: is_binomial_alt)
  thus ?thesis
  proof
    assume "is_monomial r"
    have "card (keys p) = Suc (card (keys q))" by (rule red_monomial_keys, fact+)
    thus ?thesis by simp
  next
    assume "is_proper_binomial r"
    then obtain c s d t where pbd: "is_pbd c s d t" and r_def: "r = binomial c s d t" by (rule is_proper_binomial_binomial)
    from pbd have "is_obd c s d t \<or> is_obd d t c s" by (rule pbd_imp_obd)
    thus ?thesis
    proof
      assume "is_obd c s d t"
      thus ?thesis proof (rule red_binomial_keys)
        from red show "red {binomial c s d t} p q" unfolding r_def .
      qed
    next
      assume "is_obd d t c s"
      thus ?thesis proof (rule red_binomial_keys)
        from red show "red {binomial d t c s} p q" unfolding r_def by (simp add: binomial_comm)
      qed
    qed
  qed
qed
  
lemma red_rtrancl_binomial_keys:
  fixes p q B
  assumes bin: "is_binomial_set B" and red: "(red B)\<^sup>*\<^sup>* p q"
  shows "card (keys q) \<le> card (keys p)"
  using red
proof (induct q rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from \<open>red B y z\<close> obtain r where "r \<in> B" and "red {r} y z" by (rule red_setE2)
  have "card (keys z) \<le> card (keys y)" by (rule red_binomial_keys', rule is_binomial_setD, fact+)
  with \<open>card (keys y) \<le> card (keys p)\<close> show ?case by simp
qed
  
lemma has_bounded_keys_red:
  assumes p: "has_bounded_keys n p" and B: "has_bounded_keys_set m B" and "m \<le> 2" and "red B p q"
  shows "has_bounded_keys n q"
proof -
  from \<open>red B p q\<close> obtain b where "b \<in> B" and "red {b} p q" by (rule red_setE2)
  from B \<open>b \<in> B\<close> have "has_bounded_keys m b" by (rule has_bounded_keys_setD)
  hence "card (keys b) \<le> m" unfolding has_bounded_keys_def .
  also have "... \<le> 2" by fact
  finally have "card (keys b) \<le> 2" .
  hence "card (keys b) = 0 \<or> card (keys b) = 1 \<or> card (keys b) = 2" by linarith
  thus ?thesis
  proof
    assume "card (keys b) = 0"
    hence "keys b = {}" using finite_keys[of b] by simp
    hence "b = 0" using keys_eq_empty_iff[of b] by simp
    with \<open>red {b} p q\<close> have "red {0} p q" by simp
    thus ?thesis unfolding red_singleton by (metis red_single_nonzero2)
  next
    assume "card (keys b) = 1 \<or> card (keys b) = 2"
    hence "is_binomial b" unfolding is_binomial_def .
    from this \<open>red {b} p q\<close> have "card (keys q) \<le> card (keys p)" by (rule red_binomial_keys')
    also from p have "... \<le> n" unfolding has_bounded_keys_def .
    finally show ?thesis unfolding has_bounded_keys_def .
  qed
qed
    
lemma has_bounded_keys_red_rtrancl:
  assumes "(red B)\<^sup>*\<^sup>* p q" and "has_bounded_keys n p" and "has_bounded_keys_set m B" and "m \<le> 2"
  shows "has_bounded_keys n q"
  using assms(1) assms(2)
proof (induct q)
  case base
  thus ?case .
next
  case ind: (step y z)
  show ?case by (rule has_bounded_keys_red, rule ind(3), fact+)
qed

end (* ordered_term *)

context gd_term
begin

lemma has_bounded_keys_trd:
  assumes "has_bounded_keys n p" and "has_bounded_keys_set m (set xs)" and "m \<le> 2"
  shows "has_bounded_keys n (trd xs p)"
  by (rule has_bounded_keys_red_rtrancl, rule trd_red_rtrancl, fact+)
  
section \<open>Gr\"obner Bases\<close>

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
      moreover from 2(2) have "lookup ?f t = c" by (simp add: lookup_add)
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
  
section \<open>Functions @{const gb} and \<open>rgb\<close>\<close>

lemma comp_red_monic_basis_of_gb_is_reduced_GB:
  "is_reduced_GB (set (comp_red_monic_basis (map fst (gb xs ()))))"
  by (rule comp_red_monic_basis_is_reduced_GB, simp, rule gb_isGB)
    
lemma comp_red_monic_basis_of_gb_pmdl:
  "pmdl (set (comp_red_monic_basis (map fst (gb xs ())))) = pmdl (fst ` set xs)" (is "?l = ?r")
proof -
  have "?l = pmdl (set (map fst (gb xs ())))"
    by (rule comp_red_monic_basis_pmdl, simp, rule gb_isGB)
  also have "... = pmdl (fst ` set (gb xs ()))" by simp
  also have "... = ?r" by (rule gb_pmdl)
  finally show ?thesis .
qed

definition rgb :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
  where "rgb bs = comp_red_monic_basis (map fst (gb (map (\<lambda>b. (b, ())) bs) ()))"

lemma reduced_GB_comp: "reduced_GB (set xs) = set (rgb xs)"
  apply (rule reduced_GB_unique_finite)
  subgoal by (fact finite_set)
  subgoal by (simp add: rgb_def, rule comp_red_monic_basis_of_gb_is_reduced_GB)
  subgoal by (simp add: rgb_def comp_red_monic_basis_of_gb_pmdl image_image)
  done

subsection \<open>Monomials\<close>

lemma spoly_monom:
  assumes "c \<noteq> 0" and "d \<noteq> 0"
  shows "spoly (monomial c s) (monomial d t) = 0"
proof -
  define p where "p = monomial c s"
  define q where "q = monomial d t"
  define u where "u = lcs (lp p) (lp q)"
 
  from \<open>c \<noteq> 0\<close> have ltp: "lt p = s" and lcp: "lc p = c" unfolding p_def
    by (rule lt_monomial, intro lc_monomial)
  from \<open>d \<noteq> 0\<close> have ltq: "lt q = t" and lcq: "lc q = d" unfolding q_def
    by (rule lt_monomial, intro lc_monomial)

  show ?thesis
  proof (cases "component_of_term s = component_of_term t")
    case True
    have "(pp_of_term s) adds u" unfolding u_def ltp by (rule adds_lcs)
    have "(pp_of_term t) adds u" unfolding u_def ltq by (rule adds_lcs_2)
    
    have "monom_mult (1 / lc p) (lcs (lp p) (lp q) - lp p) p =
          monom_mult (1 / c) (u - (pp_of_term s)) p" unfolding u_def ltp lcp ..
    also have "... = monomial 1 (term_of_pair (u, component_of_term s))"
      unfolding p_def monom_mult_monomial adds_minus_splus[OF \<open>(pp_of_term s) adds u\<close>]
      using \<open>c \<noteq> 0\<close> by simp
    finally have eq1: "monom_mult (1 / lc p) (lcs (lp p) (lp q) - lp p) p =
                        monomial 1 (term_of_pair (u, component_of_term s))" .
        
    have "monom_mult (1 / lc q) (lcs (lp p) (lp q) - lp q) q =
          monom_mult (1 / d) (u - (pp_of_term t)) q" unfolding u_def ltq lcq ..
    also have "... = monomial 1 (term_of_pair (u, component_of_term s))"
      unfolding q_def monom_mult_monomial adds_minus_splus[OF \<open>(pp_of_term t) adds u\<close>] True
      using \<open>d \<noteq> 0\<close> by simp
    finally have eq2: "monom_mult (1 / lc q) (lcs (lp p) (lp q) - lp q) q =
                        monomial 1 (term_of_pair (u, component_of_term s))" .
        
    have "spoly p q = 0" by (simp add: spoly_def eq1 eq2 Let_def lc_def[symmetric])
    thus ?thesis unfolding p_def q_def .
  next
    case False
    thus ?thesis by (simp add: spoly_def ltp ltq p_def[symmetric] q_def[symmetric])
  qed
qed

lemma spoly_monomial:
  assumes "is_monomial p" and "is_monomial q"
  shows "spoly p q = 0"
proof -
  from \<open>is_monomial p\<close> obtain c s where "c \<noteq> 0" and p_def: "p = monomial c s" by (rule is_monomial_monomial)
  from \<open>is_monomial q\<close> obtain d t where "d \<noteq> 0" and q_def: "q = monomial d t" by (rule is_monomial_monomial)
  show ?thesis unfolding p_def q_def by (rule spoly_monom, fact+)
qed

lemma gb_red_monomial_set:
  assumes "\<And>p q. (p, q) \<in> set sps \<Longrightarrow> is_monomial (fst p) \<and> is_monomial (fst q)"
  shows "fst (gb_red gs bs ps sps data) = []"
proof -
  have "fst ` set (fst (gb_red gs bs ps sps data)) = {}"
  proof (simp only: fst_set_fst_gb_red set_gb_red_aux Diff_eq_empty_iff, rule)
    fix h
    assume "h \<in> trdsp (map fst (gs @ bs)) ` set sps"
    then obtain p q where "(p, q) \<in> set sps" and h: "h = trdsp (map fst (gs @ bs)) (p, q)"
      by fastforce
    from this(1) have "is_monomial (fst p)" and "is_monomial (fst q)" by (simp_all add: assms)
    hence spoly: "spoly (fst p) (fst q) = 0" by (rule spoly_monomial)
    have "h = 0" unfolding h trdsp_alt spoly using rtrancl_0 trd_red_rtrancl by blast
    thus "h \<in> {0}" by simp
  qed
  thus ?thesis by simp
qed

lemma gb_schema_aux_induct [consumes 1, case_names base rec1 rec2]:
  assumes "struct_spec sel ap ab compl"
  assumes base: "\<And>bs data. P data bs [] (gs @ bs)"
    and rec1: "\<And>bs ps sps data. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                fst (data) \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data))) \<Longrightarrow>
                P data bs ps (full_gb (gs @ bs))"
    and rec2: "\<And>bs ps sps aux hs rc data data'. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                aux = compl gs bs (ps -- sps) sps (snd data) \<Longrightarrow> (hs, data') = add_indices aux (snd data) \<Longrightarrow>
                rc = fst data - count_const_lt_components (fst aux) \<Longrightarrow> 0 < rc \<Longrightarrow>
                P (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_aux sel ap ab compl gs (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')) \<Longrightarrow>
                P data bs ps (gb_schema_aux sel ap ab compl gs (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
  shows "P data bs ps (gb_schema_aux sel ap ab compl gs data bs ps)"
proof -
  from assms(1) have "gb_schema_aux_dom sel ap ab compl gs (data, bs, ps)" by (rule gb_schema_aux_domI2)
  thus ?thesis
  proof (induct data bs ps rule: gb_schema_aux.pinduct)
    case (1 data bs ps)
    show ?case
    proof (cases "ps = []")
      case True
      show ?thesis by (simp add: True, rule base)
    next
      case False
      show ?thesis
      proof (simp add: gb_schema_aux_simps[OF assms(1), of gs data bs ps] False Let_def split: if_split,
            intro conjI impI)
        define sps where "sps = sel gs bs ps (snd data)"
        assume "fst data \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data)))"
        with False sps_def show "P data bs ps (full_gb (gs @ bs))" by (rule rec1)
      next
        define sps where "sps = sel gs bs ps (snd data)"
        define aux where "aux = compl gs bs (ps -- sps) sps (snd data)"
        define hs where "hs = fst (add_indices aux (snd data))"
        define data' where "data' = snd (add_indices aux (snd data))"
        define rc where "rc = fst data - count_const_lt_components (fst aux)"
        have eq: "add_indices aux (snd data) = (hs, data')" by (simp add: hs_def data'_def)
        assume "\<not> fst data \<le> count_const_lt_components (fst aux)"
        hence "0 < rc" by (simp add: rc_def)
        hence "rc \<noteq> 0" by simp
        show "P data bs ps
           (case add_indices aux (snd data) of
            (hs, data') \<Rightarrow>
              gb_schema_aux sel ap ab compl gs (rc, data')
               (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
          unfolding eq prod.case using False sps_def aux_def eq[symmetric] rc_def \<open>0 < rc\<close>
        proof (rule rec2)
          show "P (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_aux sel ap ab compl gs (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
            using False sps_def refl aux_def rc_def \<open>rc \<noteq> 0\<close> eq[symmetric] refl by (rule 1)
        qed
      qed
    qed
  qed
qed

lemma gb_aux_monomial_set:
  assumes "\<And>p q. (p, q) \<in> (set ps) \<Longrightarrow> is_monomial (fst p) \<and> is_monomial (fst q)"
  assumes "gb_aux gs data bs ps = gs @ bs \<Longrightarrow> thesis"
    and "gb_aux gs data bs ps = full_gb (gs @ bs) \<Longrightarrow> thesis"
  shows thesis
  using struct_spec_gb assms unfolding gb_aux_def
proof (induct data bs ps arbitrary: thesis rule: gb_schema_aux_induct)
  case (base bs data)
  from refl show ?case by (rule base.prems(2))
next
  case (rec1 bs ps sps data)
  from refl show ?case by (rule rec1.prems(3))
next
  case (rec2 bs ps sps aux hs rc data data')
  have *: "fst (gb_red gs bs (ps -- sps) sps (snd data)) = []"
  proof (rule gb_red_monomial_set, rule rec2.prems)
    fix p q
    assume "(p, q) \<in> set sps"
    also from sel_spec_gb_sel rec2(1) have "... \<subseteq> set ps" unfolding rec2(2) by (rule sel_specD2)
    finally show "(p, q) \<in> set ps" .
  qed
  have "hs = fst (add_indices (gb_red gs bs (ps -- sps) sps (snd data)) (snd data))"
    by (simp add: rec2(4)[symmetric] rec2(3)[symmetric])
  also have "... = []" by (simp add: add_indices_def *)
  finally have "hs = []" .
  hence eq: "add_basis_canon gs bs hs data' = bs" by (simp add: add_basis_sorted_def)
  show ?case
  proof (rule rec2.hyps)
    define ps1 where "ps1 = apply_ncrit chain_ncrit data' gs bs hs
        (apply_icrit component_crit data' gs bs hs (new_pairs_sorted canon_pair_order gs bs hs data'))"
    have "ps1 = []" by (simp add: ps1_def \<open>hs = []\<close> new_pairs_sorted_def apply_icrit_def apply_ncrit_def)
    fix p q
    assume "(p, q) \<in> set (add_pairs_canon gs bs (ps -- sps) hs data')"
    hence "(False, p, q) \<in> set ps1 \<or> ((p, q) \<in> set (ps -- sps) \<and> \<not> chain_ocrit data' hs ps1 p q)"
      by (simp add: set_add_pairs_iff[of canon_pair_comb ps1 chain_ncrit data' gs bs hs component_crit
            "new_pairs_sorted canon_pair_order", OF set_merge_wrt ps1_def])
    hence "(p, q) \<in> set ps" by (simp add: set_diff_list \<open>ps1 = []\<close>)
    thus "is_monomial (fst p) \<and> is_monomial (fst q)" by (rule rec2.prems(1))
  qed (simp_all add: eq rec2.prems(2, 3))
qed

lemma gb_is_monomial_set:
  assumes "is_monomial_set (fst ` set bs0)"
  shows "is_monomial_set (fst ` set (gb bs0 ()))"
proof (simp add: gb_simps Let_def fst_set_drop_indices)
  define data0 where "data0 = (length bs0, ())"
  define data where "data = (count_rem_components (add_basis_canon [] [] (fst (add_indices (bs0, ()) (0, ()))) data0), data0)"
  define bs where "bs = fst (add_indices (bs0, ()) (0, ()))"
  define bs' where "bs' = add_basis_canon [] [] bs data0"
  define ps where "ps = add_pairs_canon [] [] [] bs data0"
  have bs: "fst ` set bs = fst ` set bs0" by (simp add: bs_def fst_set_add_indices)
  show "is_monomial_set (fst ` set (gb_aux [] data bs' ps))"
  proof (rule gb_aux_monomial_set)
    fix p q
    assume "(p, q) \<in> set ps"
    also from ap_spec_add_pairs_canon have "... \<subseteq> set [] \<union> set bs \<times> (set [] \<union> set [] \<union> set bs)"
      unfolding ps_def by (rule ap_specD1)
    also have "... = set bs \<times> set bs" by simp
    finally have "(p, q) \<in> set bs \<times> set bs" .
    hence "fst p \<in> fst ` set bs" and "fst q \<in> fst ` set bs" by simp_all
    hence "fst p \<in> fst ` set bs0" and "fst q \<in> fst ` set bs0" by (simp_all only: bs)
    thus "is_monomial (fst p) \<and> is_monomial (fst q)"
      using assms unfolding is_monomial_set_def by auto
  next
    assume "gb_aux [] data bs' ps = [] @ bs'"
    moreover have "fst ` set bs' = fst ` set bs0"
      by (simp add: bs'_def ab_specD1[OF ab_spec_add_basis_sorted] bs)
    ultimately show ?thesis by (simp add: assms)
  next
    assume eq: "gb_aux [] data bs' ps = full_gb ([] @ bs')"
    show ?thesis
      by (simp add: eq full_gb_def is_monomial_set_def monomial_is_monomial)
  qed
qed

subsection \<open>Binomials\<close>

lemma spoly_binomial_monom:
  fixes tp
  assumes obd: "is_obd cp sp dp tp" and "cq \<noteq> 0" and "component_of_term sp = component_of_term sq"
  shows "spoly (binomial cp sp dp tp) (monomial cq sq) =
            monomial (dp / cp) (((lcs (pp_of_term sp) (pp_of_term sq)) - (pp_of_term sp)) \<oplus> tp)"
proof (simp add: spoly_def lt_binomial[OF obd] lt_monomial[OF \<open>cq \<noteq> 0\<close>] assms(3) Let_def
      lookup_binomial obd obd_imp_pbd)
  define u where "u = lcs (pp_of_term sp) (pp_of_term sq)"
  have "(pp_of_term sp) adds u" unfolding u_def by (rule adds_lcs)
  have "(pp_of_term sq) adds u" unfolding u_def by (rule adds_lcs_2)
  from obd have "cp \<noteq> 0" unfolding is_obd_def ..
  from \<open>(pp_of_term sp) adds u\<close> have eq1: "monom_mult (1 / cp) (u - (pp_of_term sp)) (binomial cp sp dp tp) =
                        binomial 1 (term_of_pair (u, component_of_term sp)) (dp / cp) ((u - (pp_of_term sp)) \<oplus> tp)"
    unfolding monom_mult_binomial by (simp add: \<open>cp \<noteq> 0\<close> adds_minus_splus)
  from \<open>(pp_of_term sq) adds u\<close> have eq2: "monom_mult (1 / cq) (u - (pp_of_term sq)) (monomial cq sq) =
                        monomial 1 (term_of_pair (u, component_of_term sp))"
    unfolding monom_mult_monomial by (simp add: \<open>cq \<noteq> 0\<close> adds_minus_splus assms(3))
  have "monom_mult (1 / cp) (u - (pp_of_term sp)) (binomial cp sp dp tp) -
        monom_mult (1 / cq) (u - (pp_of_term sq)) (monomial cq sq) =
        monomial (dp / cp) ((u - (pp_of_term sp)) \<oplus> tp)" unfolding eq1 eq2 unfolding binomial_def by simp
  thus "monom_mult (1 / cp) (lcs (pp_of_term sp) (pp_of_term sq) - pp_of_term sp) (binomial cp sp dp tp) -
    monom_mult (1 / cq) (lcs (pp_of_term sp) (pp_of_term sq) - pp_of_term sq) (monomial cq sq) =
    monomial (dp / cp) ((lcs (pp_of_term sp) (pp_of_term sq) - pp_of_term sp) \<oplus> tp)" unfolding u_def .
qed

lemma spoly_binomial:
  fixes tp
  assumes obdp: "is_obd cp sp dp tp" and obdq: "is_obd cq sq dq tq"
     and "component_of_term sp = component_of_term sq"
  shows "spoly (binomial cp sp dp tp) (binomial cq sq dq tq) =
         binomial (dp / cp) (((lcs (pp_of_term sp) (pp_of_term sq)) - (pp_of_term sp)) \<oplus> tp)
               (-dq / cq) (((lcs (pp_of_term sp) (pp_of_term sq)) - (pp_of_term sq)) \<oplus> tq)"
proof (simp add: spoly_def lt_binomial[OF obdp] lt_binomial[OF obdq] assms(3) Let_def
        lookup_binomial obdp obdq obd_imp_pbd)
  define u where "u = lcs (pp_of_term sp) (pp_of_term sq)"
  have "(pp_of_term sp) adds u" unfolding u_def by (rule adds_lcs)
  have "(pp_of_term sq) adds u" unfolding u_def by (rule adds_lcs_2)
  from obdp have "cp \<noteq> 0" unfolding is_obd_def ..
  from obdq have "cq \<noteq> 0" unfolding is_obd_def ..
  from \<open>(pp_of_term sp) adds u\<close> have eq1: "monom_mult (1 / cp) (u - (pp_of_term sp)) (binomial cp sp dp tp) =
                        binomial 1 (term_of_pair (u, component_of_term sp)) (dp / cp) ((u - (pp_of_term sp)) \<oplus> tp)"
    unfolding monom_mult_binomial by (simp add: \<open>cp \<noteq> 0\<close> adds_minus_splus)
  from \<open>(pp_of_term sq) adds u\<close> have eq2: "monom_mult (1 / cq) (u - (pp_of_term sq)) (binomial cq sq dq tq) =
                        binomial 1 (term_of_pair (u, component_of_term sp)) (dq / cq) ((u - (pp_of_term sq)) \<oplus> tq)"
    unfolding monom_mult_binomial by (simp add: \<open>cq \<noteq> 0\<close> adds_minus_splus assms(3))
  have eq3: "monomial (- (dq / cq)) ((u - pp_of_term sq) \<oplus> tq) =
                      - monomial (dq / cq) ((u - pp_of_term sq) \<oplus> tq)" by (simp only: monomial_uminus)
  have "monom_mult (1 / cp) (u - pp_of_term sp) (binomial cp sp dp tp) -
        monom_mult (1 / cq) (u - pp_of_term sq) (binomial cq sq dq tq) =
        binomial (dp / cp) ((u - pp_of_term sp) \<oplus> tp)
              (- (dq / cq)) ((u - pp_of_term sq) \<oplus> tq)" unfolding eq1 eq2 unfolding binomial_def eq3
    by simp
  thus "monom_mult (1 / cp) (lcs (pp_of_term sp) (pp_of_term sq) - pp_of_term sp) (binomial cp sp dp tp) -
      monom_mult (1 / cq) (lcs (pp_of_term sp) (pp_of_term sq) - pp_of_term sq) (binomial cq sq dq tq) =
       binomial (dp / cp) ((lcs (pp_of_term sp) (pp_of_term sq) - pp_of_term sp) \<oplus> tp) (- (dq / cq))
       ((lcs (pp_of_term sp) (pp_of_term sq) - pp_of_term sq) \<oplus> tq)" unfolding u_def .
qed
  
lemma spoly_binomial_monomial:
  assumes "is_proper_binomial p" and "is_monomial q"
  shows "is_monomial (spoly p q) \<or> spoly p q = 0"
proof (rule disjCI)
  assume "spoly p q \<noteq> 0"
  from \<open>is_proper_binomial p\<close> obtain cp sp dp tp where obd: "is_obd cp sp dp tp"
    and p_def: "p = binomial cp sp dp tp" by (rule is_proper_binomial_binomial_od)
  from \<open>is_monomial q\<close> obtain cq sq where "cq \<noteq> 0" and q_def: "q = monomial cq sq" by (rule is_monomial_monomial)
  have *: "component_of_term sp = component_of_term sq"
  proof (rule ccontr)
    assume "component_of_term sp \<noteq> component_of_term sq"
    moreover have "lt q = sq" unfolding q_def using \<open>cq \<noteq> 0\<close> by (rule lt_monomial)
    moreover have "lt p = sp" unfolding p_def using obd by (rule lt_binomial)
    ultimately have "spoly p q = 0" by (simp add: spoly_def)
    with \<open>spoly p q \<noteq> 0\<close> show False ..
  qed
  show "is_monomial (spoly p q)" unfolding p_def q_def spoly_binomial_monom[OF obd \<open>cq \<noteq> 0\<close> *]
  proof (rule monomial_is_monomial)
    from obd show "dp / cp \<noteq> 0" unfolding is_obd_def by simp
  qed
qed
    
lemma spoly_monomial_binomial:
  assumes "is_monomial p" and "is_proper_binomial q"
  shows "is_monomial (spoly p q) \<or> spoly p q = 0"
proof -
  from \<open>is_proper_binomial q\<close> \<open>is_monomial p\<close> have "is_monomial (spoly q p) \<or> spoly q p = 0"
    by (rule spoly_binomial_monomial)
  hence "is_monomial (- spoly p q) \<or> - spoly p q = 0" unfolding spoly_swap[of q p] .
  thus ?thesis by (simp add: is_monomial_uminus)
qed

lemma spoly_binomial_keys:
  assumes "is_binomial p" and "is_binomial q"
  shows "card (keys (spoly p q)) \<le> 2"
proof -
  from \<open>is_binomial p\<close> show ?thesis unfolding is_binomial_alt
  proof
    assume "is_monomial p"
    from \<open>is_binomial q\<close> show ?thesis unfolding is_binomial_alt
    proof
      assume "is_monomial q"
      with \<open>is_monomial p\<close> have "spoly p q = 0" by (rule spoly_monomial)
      thus ?thesis by simp
    next
      assume "is_proper_binomial q"
      with \<open>is_monomial p\<close> have "is_monomial (spoly p q) \<or> spoly p q = 0"
        by (rule spoly_monomial_binomial)
      thus ?thesis by (auto simp add: is_monomial_def)
    qed
  next
    assume "is_proper_binomial p"
    from \<open>is_binomial q\<close> show ?thesis unfolding is_binomial_alt
    proof
      assume "is_monomial q"
      with \<open>is_proper_binomial p\<close> have "is_monomial (spoly p q) \<or> spoly p q = 0"
        by (rule spoly_binomial_monomial)
      thus ?thesis by (auto simp add: is_monomial_def)
    next
      assume "is_proper_binomial q"
      from \<open>is_proper_binomial p\<close> obtain cp sp dp tp where obdp: "is_obd cp sp dp tp"
        and p_def: "p = binomial cp sp dp tp" by (rule is_proper_binomial_binomial_od)
      from \<open>is_proper_binomial q\<close> obtain cq sq dq tq where obdq: "is_obd cq sq dq tq"
        and q_def: "q = binomial cq sq dq tq" by (rule is_proper_binomial_binomial_od)
      show ?thesis
      proof (cases "component_of_term sp = component_of_term sq")
        case True
        show ?thesis unfolding p_def q_def spoly_binomial[OF obdp obdq True] by (rule card_keys_binomial)
      next
        case False
        moreover have "lt p = sp" unfolding p_def using obdp by (rule lt_binomial)
        moreover have "lt q = sq" unfolding q_def using obdq by (rule lt_binomial)
        ultimately show ?thesis by (simp add: spoly_def)
      qed
    qed
  qed
qed

lemma gb_red_binomial_set:
  assumes "\<And>p q. (p, q) \<in> set sps \<Longrightarrow> is_binomial (fst p) \<and> is_binomial (fst q)"
    and "is_binomial_set (fst ` set gs)" and "is_binomial_set (fst ` set bs)"
  shows "is_binomial_set (fst ` set (fst (gb_red gs bs ps sps data)))"
proof (simp only: fst_set_fst_gb_red set_gb_red_aux is_binomial_set_def, rule)
  fix h
  assume "h \<in> trdsp (map fst (gs @ bs)) ` set sps - {0}"
  hence "h \<in> trdsp (map fst (gs @ bs)) ` set sps" and "h \<noteq> 0" by simp_all
  from this(1) obtain p q where "(p, q) \<in> set sps" and h: "h = trdsp (map fst (gs @ bs)) (p, q)"
    by fastforce
  from this(1) have "is_binomial (fst p)" and "is_binomial (fst q)" by (simp_all add: assms(1))
  from assms(2, 3) have "is_binomial_set (set (map fst (gs @ bs)))"
    by (auto simp add: is_binomial_set_def)
  moreover have "(red (set (map fst (gs @ bs))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) h"
    unfolding h trdsp_alt by (rule trd_red_rtrancl)
  ultimately have "card (keys h) \<le> card (keys (spoly (fst p) (fst q)))"
    by (rule red_rtrancl_binomial_keys)
  also from \<open>is_binomial (fst p)\<close> \<open>is_binomial (fst q)\<close> have "... \<le> 2" by (rule spoly_binomial_keys)
  finally have "card (keys h) \<le> 2" .
  moreover from \<open>h \<noteq> 0\<close> have "card (keys h) \<noteq> 0" by simp
  ultimately show "is_binomial h" unfolding is_binomial_def by linarith
qed

lemma gb_aux_binomial_set:
  assumes "\<And>p q. (p, q) \<in> (set ps) \<Longrightarrow> is_binomial (fst p) \<and> is_binomial (fst q)"
    and "is_binomial_set (fst ` set gs)" and "is_binomial_set (fst ` set bs)"
  shows "is_binomial_set (fst ` set (gb_aux gs data bs ps))"
   unfolding gb_aux_def using struct_spec_gb assms(1, 3)
proof (induct gs data bs ps rule: gb_schema_aux_induct)
  case (base bs data)
  from assms(2) base(2) show ?case by (auto simp add: is_binomial_set_def)
next
  case (rec1 bs ps sps data)
  show ?case by (simp add: is_binomial_set_def is_binomial_def full_gb_def)
next
  case (rec2 bs ps sps aux hs rc data data')
  have "is_binomial_set (fst ` set (fst (gb_red gs bs (ps -- sps) sps (snd data))))"
  proof (rule gb_red_binomial_set, rule rec2.prems)
    fix p q
    assume "(p, q) \<in> set sps"
    also from sel_spec_gb_sel rec2(1) have "... \<subseteq> set ps" unfolding rec2(2) by (rule sel_specD2)
    finally show "(p, q) \<in> set ps" .
  qed fact+
  moreover have "hs = fst (add_indices (gb_red gs bs (ps -- sps) sps (snd data)) (snd data))"
    by (simp add: rec2(3, 4)[symmetric])
  ultimately have hs: "is_binomial_set (fst ` set hs)" by (simp add: fst_set_add_indices)
  show ?case
  proof (rule rec2.hyps)
    fix p q
    assume "(p, q) \<in> set (add_pairs_canon gs bs (ps -- sps) hs data')"
    also from ap_spec_add_pairs_canon have "... \<subseteq> set (ps -- sps) \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      by (rule ap_specD1)
    also have "... \<subseteq> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (auto simp add: set_diff_list)
    finally show "is_binomial (fst p) \<and> is_binomial (fst q)"
    proof
      assume "(p, q) \<in> set ps"
      thus ?thesis by (rule rec2.prems(1))
    next
      assume "(p, q) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      hence "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" by simp_all
      hence "fst p \<in> fst ` set hs" and disj: "fst q \<in> fst ` set gs \<union> fst ` set bs \<union> fst ` set hs"
        by auto
      from hs this(1) have "is_binomial (fst p)" unfolding is_binomial_set_def ..
      moreover from disj have "is_binomial (fst q)"
      proof (elim UnE)
        assume "fst q \<in> fst ` set gs"
        with assms(2) show ?thesis unfolding is_binomial_set_def ..
      next
        assume "fst q \<in> fst ` set bs"
        with rec2.prems(2) show ?thesis unfolding is_binomial_set_def ..
      next
        assume "fst q \<in> fst ` set hs"
        with hs show ?thesis unfolding is_binomial_set_def ..
      qed
      ultimately show ?thesis ..
    qed
  next
    from rec2.prems(2) hs show "is_binomial_set (fst ` set (add_basis_canon gs bs hs data'))"
      by (auto simp add: ab_specD1[OF ab_spec_add_basis_sorted] is_binomial_set_def)
  qed
qed

lemma gb_is_binomial_set:
  assumes "is_binomial_set (fst ` set bs0)"
  shows "is_binomial_set (fst ` set (gb bs0 ()))"
proof (simp add: gb_simps Let_def fst_set_drop_indices)
  define data0 where "data0 = (length bs0, ())"
  define data where "data = (count_rem_components (add_basis_canon [] [] (fst (add_indices (bs0, ()) (0, ()))) data0), data0)"
  define bs where "bs = fst (add_indices (bs0, ()) (0, ()))"
  define bs' where "bs' = add_basis_canon [] [] bs data0"
  define ps where "ps = add_pairs_canon [] [] [] bs data0"
  have bs: "fst ` set bs = fst ` set bs0" by (simp add: bs_def fst_set_add_indices)
  show "is_binomial_set (fst ` set (gb_aux [] data bs' ps))"
  proof (rule gb_aux_binomial_set)
    fix p q
    assume "(p, q) \<in> set ps"
    also from ap_spec_add_pairs_canon have "... \<subseteq> set [] \<union> set bs \<times> (set [] \<union> set [] \<union> set bs)"
      unfolding ps_def by (rule ap_specD1)
    also have "... = set bs \<times> set bs" by simp
    finally have "(p, q) \<in> set bs \<times> set bs" .
    hence "fst p \<in> fst ` set bs" and "fst q \<in> fst ` set bs" by simp_all
    hence "fst p \<in> fst ` set bs0" and "fst q \<in> fst ` set bs0" by (simp_all only: bs)
    thus "is_binomial (fst p) \<and> is_binomial (fst q)"
      using assms unfolding is_binomial_set_def by auto
  next
    show "is_binomial_set (fst ` set [])" by (simp add: is_binomial_set_def)
  next
    from assms show "is_binomial_set (fst ` set bs')"
      by (simp add: bs'_def ab_specD1[OF ab_spec_add_basis_sorted] bs)
  qed
qed

section \<open>Reduced Gr\"obner Bases\<close>
  
subsection \<open>Function @{term comp_red_basis}\<close>

lemma comp_red_basis_aux_has_bounded_keys_set:
  assumes major: "has_bounded_keys_set n (set (xs @ ys))" and "n \<le> 2"
  shows "has_bounded_keys_set n (set (comp_red_basis_aux xs ys))"
  using major
proof (induct xs arbitrary: ys)
  case base: Nil
  from base(1) show ?case unfolding comp_red_basis_aux_base by simp
next
  case ind: (Cons a xs)
  from ind(2) have "has_bounded_keys_set n ({a} \<union> set (xs @ ys))" by simp
  hence a: "has_bounded_keys n a" and b: "has_bounded_keys_set n (set (xs @ ys))"
    unfolding has_bounded_keys_set_union has_bounded_keys_set_singleton by simp_all
  let ?a = "trd (xs @ ys) a"
  have eq: "set (xs @ ?a # ys) = {?a} \<union> set (xs @ ys)" by simp
  show ?case unfolding comp_red_basis_aux_rec
  proof (rule ind.hyps, unfold eq has_bounded_keys_set_union has_bounded_keys_set_singleton, intro conjI)
    from a b \<open>n \<le> 2\<close> show "has_bounded_keys n ?a" by (rule has_bounded_keys_trd)
  qed fact
qed
  
lemma comp_red_basis_has_bounded_keys_set:
  assumes "has_bounded_keys_set n (set xs)" and "n \<le> 2"
  shows "has_bounded_keys_set n (set (comp_red_basis xs))"
  unfolding comp_red_basis_def
proof (rule comp_red_basis_aux_has_bounded_keys_set)
  have a: "has_bounded_keys_set n (set (comp_min_basis xs))"
    by (rule has_bounded_keys_set_subset, fact, fact comp_min_basis_subset)
  thus "has_bounded_keys_set n (set (comp_min_basis xs @ []))" by simp
qed fact
  
subsection \<open>Monicity\<close>
  
lemma comp_red_monic_basis_has_bounded_keys_set:
  assumes "has_bounded_keys_set n (set xs)" and "n \<le> 2"
  shows "has_bounded_keys_set n (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis
  by (rule monic_set_has_bounded_keys, rule comp_red_basis_has_bounded_keys_set, fact+)

subsection \<open>Monomials\<close>

lemma comp_red_monic_basis_is_monomial_set:
  assumes "is_monomial_set (set xs)"
  shows "is_monomial_set (set (comp_red_monic_basis xs))"
proof  (rule has_bounded_keys_set_1_D, rule comp_red_monic_basis_has_bounded_keys_set,
        rule has_bounded_keys_set_1_I1, fact assms, simp, rule)
  assume "0 \<in> set (comp_red_monic_basis xs)"
  hence "0 \<noteq> (0::'t \<Rightarrow>\<^sub>0 'b)" by (rule comp_red_monic_basis_nonzero)
  thus False by simp
qed
  
theorem reduced_GB_is_monomial_set:
  assumes "is_monomial_set B" and "finite B"
  shows "is_monomial_set (reduced_GB B)"
proof -
  from finite_list[OF \<open>finite B\<close>] obtain xs where set: "set xs = B" ..
  from assms(1) have a: "is_monomial_set (set xs)" unfolding set[symmetric] .
  show ?thesis unfolding set[symmetric] reduced_GB_comp rgb_def
    by (rule comp_red_monic_basis_is_monomial_set, simp, rule gb_is_monomial_set,
        simp add: image_image, fact a)
qed

subsection \<open>Binomials\<close>
  
lemma comp_red_monic_basis_is_binomial_set:
  assumes "is_binomial_set (set xs)"
  shows "is_binomial_set (set (comp_red_monic_basis xs))"
proof  (rule has_bounded_keys_set_2_D, rule comp_red_monic_basis_has_bounded_keys_set,
        rule has_bounded_keys_set_2_I1, fact assms, simp, rule)
  assume "0 \<in> set (comp_red_monic_basis xs)"
  hence "0 \<noteq> (0::'t \<Rightarrow>\<^sub>0 'b)" by (rule comp_red_monic_basis_nonzero)
  thus False by simp
qed
  
theorem reduced_GB_is_binomial_set:
  assumes "is_binomial_set B" and "finite B"
  shows "is_binomial_set (reduced_GB B)"
proof -
  from finite_list[OF \<open>finite B\<close>] obtain xs where set: "set xs = B" ..
  from assms(1) have a: "is_binomial_set (set xs)" unfolding set[symmetric] .
  show ?thesis unfolding set[symmetric] reduced_GB_comp rgb_def
    by (rule comp_red_monic_basis_is_binomial_set, simp, rule gb_is_binomial_set,
        simp add: image_image, fact a)
qed

end (* gd_term *)

end (* theory *)
