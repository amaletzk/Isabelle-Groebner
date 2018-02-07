(* Author: Alexander Maletzky *)

theory Binomials
  imports Reduced_GB Buchberger
begin

context ordered_powerprod
begin

section \<open>Monomial Ideals\<close>

lemma keys_monomial_pideal:
  assumes "is_monomial_set F" and "p \<in> pideal F" and "t \<in> keys p"
  obtains f where "f \<in> F" and "f \<noteq> 0" and "lp f adds t"
  using assms(2) assms(3)
proof (induct arbitrary: thesis rule: pideal_induct)
  case pideal_0
  from this(2) show ?case by simp
next
  case step: (pideal_plus p f0 c s)
  from assms(1) step(3) have "is_monomial f0" unfolding is_monomial_set_def ..
  hence "keys f0 = {lp f0}" and "f0 \<noteq> 0" by (rule keys_monomial, rule monomial_not_0)
  from keys_add_subset step(6) have "t \<in> keys p \<union> keys (monom_mult c s f0)" ..
  thus ?case
  proof
    assume "t \<in> keys p"
    from step(2)[OF _ this] obtain f where "f \<in> F" and "f \<noteq> 0" and "lp f adds t" by blast
    thus ?thesis by (rule step(5))
  next
    assume "t \<in> keys (monom_mult c s f0)"
    with keys_monom_mult_subset have "t \<in> plus s ` keys f0" ..
    hence "t = s + lp f0" by (simp add: \<open>keys f0 = {lp f0}\<close>)
    hence "lp f0 adds t" by simp
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
  hence cp0: "lookup p (s + lp r) \<noteq> 0" and q_def0: "q = p - monom_mult (lookup p (s + lp r) / lc r) s r"
    unfolding red_single_def by simp_all
  from mon obtain c t where "c \<noteq> 0" and r_def: "r = monomial c t" by (rule is_monomial_monomial)
  have lpr: "lp r = t" unfolding r_def by (rule lp_monomial, fact)
  have lcr: "lc r = c" unfolding r_def by (rule lc_monomial)
  define u where "u = s + t"
  from q_def0 have "q = p - monom_mult (lookup p u / c) s r" unfolding u_def lpr lcr .
  also have "... = p - monomial ((lookup p u / c) * c) u" unfolding u_def r_def monom_mult_monomial ..
  finally have q_def: "q = p - monomial (lookup p u) u" using \<open>c \<noteq> 0\<close> by simp
  from cp0 have "lookup p u \<noteq> 0" unfolding u_def lpr .
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
  have lpr: "lp r = s" unfolding r_def by (rule lp_binomial, fact)
  have lcr: "lc r = c" unfolding r_def by (rule lc_binomial, fact)
  
  from red obtain u where rs: "red_single p q r u" unfolding r_def red_singleton ..
  hence cp0: "lookup p (u + lp r) \<noteq> 0" and q_def0: "q = p - monom_mult (lookup p (u + lp r) / lc r) u r"
    unfolding red_single_def by simp_all
  define v where "v = u + s"
  define w where "w = u + t"
  define cpv where "cpv = lookup p v"
  define r' where "r' = binomial cpv v ((cpv / c) * d) w"
  from cp0 have "cpv \<noteq> 0" unfolding cpv_def v_def lpr .
  with \<open>c \<noteq> 0\<close> have "cpv / c \<noteq> 0" by simp
  from \<open>cpv \<noteq> 0\<close> have "v \<in> keys p" unfolding cpv_def by simp
  from q_def0 have "q = p - monom_mult (cpv / c) u r" unfolding cpv_def lpr lcr v_def .
  also have "... = p - binomial ((cpv / c) * c) v ((cpv / c) * d) w"
    unfolding r_def monom_mult_binomial v_def w_def ..
  finally have q_def: "q = p - r'" using \<open>c \<noteq> 0\<close> unfolding r'_def by simp
      
  have "is_obd ((cpv / c) * c) v ((cpv / c) * d) w" unfolding v_def w_def by (rule is_obd_mult, fact+)
  hence obd_r': "is_obd cpv v ((cpv / c) * d) w" using \<open>c \<noteq> 0\<close> by simp
  have pbd_r': "is_pbd cpv v ((cpv / c) * d) w" by (rule obd_imp_pbd, fact)
      
  have sr': "keys r' = {v, w}" unfolding r'_def by (rule keys_binomial_pbd, rule obd_imp_pbd, fact)
  hence "r' \<noteq> 0" using keys_eq_empty_iff[of r'] by simp
  have lpr': "lp r' = v" unfolding r'_def by (rule lp_binomial, fact)
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

end (* ordered_powerprod *)

context gd_powerprod
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
  assume "f \<in> pideal G"
  thus "(red G)\<^sup>*\<^sup>* f 0"
  proof (induct f rule: poly_mapping_plus_induct)
    case 1
    show ?case ..
  next
    case (2 f c t)
    let ?f = "monomial c t + f"
    from 2(1) have "t \<in> keys (monomial c t)" by simp
    from this 2(2) have "t \<in> keys ?f" by (rule in_keys_plusI1)
    with assms \<open>?f \<in> pideal G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds t"
      by (rule keys_monomial_pideal)
    from this(1) have "red G ?f f"
    proof (rule red_setI)
      from \<open>lp g adds t\<close> have eq: "t - lp g + lp g = t" by (rule adds_minus)
      moreover from 2(2) have "lookup ?f t = c" by (simp add: lookup_add)
      ultimately show "red_single (monomial c t + f) f g (t - lp g)"
      proof (simp add: red_single_def \<open>g \<noteq> 0\<close> \<open>t \<in> keys ?f\<close> 2(1))
        thm monom_mult_monomial
        from \<open>g \<noteq> 0\<close> have "lc g \<noteq> 0" by (rule lc_not_0)
        hence "monomial c t = monom_mult (c / lc g) (t - lp g) (monomial (lc g) (lp g))"
          by (simp add: monom_mult_monomial eq)
        moreover from assms \<open>g \<in> G\<close> have "is_monomial g" unfolding is_monomial_set_def ..
        ultimately show "monomial c t = monom_mult (c / lc g) (t - lp g) g"
          by (simp only: monomial_eq_itself)
      qed
    qed
    have "f \<in> pideal G" by (rule pideal_closed_red, fact subset_refl, fact+)
    hence "(red G)\<^sup>*\<^sup>* f 0" by (rule 2(3))
    with \<open>red G ?f f\<close> show ?case by simp
  qed
qed
  
section \<open>Functions @{const gb} and @{term rgb}\<close>

lemma comp_red_monic_basis_of_gb_is_reduced_GB:
  "is_reduced_GB (set (comp_red_monic_basis (map fst (gb xs ()))))"
  by (rule comp_red_monic_basis_is_reduced_GB, simp, rule gb_isGB)
    
lemma comp_red_monic_basis_of_gb_pideal:
  "pideal (set (comp_red_monic_basis (map fst (gb xs ())))) = pideal (fst ` set xs)" (is "?l = ?r")
proof -
  have "?l = pideal (set (map fst (gb xs ())))"
    by (rule comp_red_monic_basis_pideal, simp, rule gb_isGB)
  also have "... = pideal (fst ` set (gb xs ()))" by simp
  also have "... = ?r" by (rule gb_pideal)
  finally show ?thesis .
qed

definition rgb :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "rgb bs = comp_red_monic_basis (map fst (gb (map (\<lambda>b. (b, ())) bs) ()))"

lemma reduced_GB_comp: "reduced_GB (set xs) = set (rgb xs)"
  apply (rule reduced_GB_unique_finite)
  subgoal by (fact finite_set)
  subgoal by (simp add: rgb_def, rule comp_red_monic_basis_of_gb_is_reduced_GB)
  subgoal by (simp add: rgb_def comp_red_monic_basis_of_gb_pideal image_image)
  done

subsection \<open>Monomials\<close>

lemma spoly_monom:
  assumes "c \<noteq> 0" and "d \<noteq> 0"
  shows "spoly (monomial c s) (monomial d t) = 0"
proof -
  define p where "p = monomial c s"
  define q where "q = monomial d t"
  define u where "u = lcs_powerprod_class.lcs (lp p) (lp q)"
 
  from \<open>c \<noteq> 0\<close> have lpp: "lp p = s" and lcp: "lc p = c" unfolding p_def
    by (rule lp_monomial, intro lc_monomial)
  from \<open>d \<noteq> 0\<close> have lpq: "lp q = t" and lcq: "lc q = d" unfolding q_def
    by (rule lp_monomial, intro lc_monomial)
      
  have "s adds u" unfolding u_def lpp by (rule adds_lcs)
  have "t adds u" unfolding u_def lpq by (rule adds_lcs_2)
  
  have "monom_mult (1 / lc p) (lcs_powerprod_class.lcs (lp p) (lp q) - lp p) p =
        monom_mult (1 / c) (u - s) p" unfolding u_def lpp lcp ..
  also have "... = monomial 1 u" unfolding p_def monom_mult_monomial adds_minus[OF \<open>s adds u\<close>]
    using \<open>c \<noteq> 0\<close> by simp
  finally have eq1: "monom_mult (1 / lc p) (lcs_powerprod_class.lcs (lp p) (lp q) - lp p) p = monomial 1 u" .
      
  have "monom_mult (1 / lc q) (lcs_powerprod_class.lcs (lp p) (lp q) - lp q) q =
        monom_mult (1 / d) (u - t) q" unfolding u_def lpq lcq ..
  also have "... = monomial 1 u" unfolding q_def monom_mult_monomial adds_minus[OF \<open>t adds u\<close>]
    using \<open>d \<noteq> 0\<close> by simp
  finally have eq2: "monom_mult (1 / lc q) (lcs_powerprod_class.lcs (lp p) (lp q) - lp q) q = monomial 1 u" .
      
  have "spoly p q = 0" unfolding spoly_def eq1 eq2 by simp
  thus ?thesis unfolding p_def q_def .
qed
  
lemma spoly_monomial:
  assumes "is_monomial p" and "is_monomial q"
  shows "spoly p q = 0"
proof -
  from \<open>is_monomial p\<close> obtain c s where "c \<noteq> 0" and p_def: "p = monomial c s" by (rule is_monomial_monomial)
  from \<open>is_monomial q\<close> obtain d t where "d \<noteq> 0" and q_def: "q = monomial d t" by (rule is_monomial_monomial)
  show ?thesis unfolding p_def q_def by (rule spoly_monom, fact+)
qed

lemma gb_compl_monomial_set:
  assumes "\<And>p q. (p, q) \<in> set sps \<Longrightarrow> is_monomial (fst p) \<and> is_monomial (fst q)"
  shows "fst (gb_compl gs bs ps sps data) = []"
proof -
  have "fst ` set (fst (gb_compl gs bs ps sps data)) = {}"
  proof (simp only: discard_red_cp_def fst_set_fst_gb_red set_gb_red_aux Diff_eq_empty_iff)
    have "set (discard_crit_pairs pc_crit gs bs ps sps data) \<subseteq> set sps"
      by (simp add: set_discard_crit_pairs_partition[of sps pc_crit gs bs ps data])
    hence "trdsp (map fst (gs @ bs)) ` set (discard_crit_pairs pc_crit gs bs ps sps data) \<subseteq>
            trdsp (map fst (gs @ bs)) ` set sps" by (rule image_mono)
    also have "... \<subseteq> {0}"
    proof
      fix h
      assume "h \<in> trdsp (map fst (gs @ bs)) ` set sps"
      then obtain p q where "(p, q) \<in> set sps" and h: "h = trdsp (map fst (gs @ bs)) (p, q)"
        by fastforce
      from this(1) have "is_monomial (fst p)" and "is_monomial (fst q)" by (simp_all add: assms)
      hence spoly: "spoly (fst p) (fst q) = 0" by (rule spoly_monomial)
      have "h = 0" unfolding h trdsp_alt spoly using rtrancl_0 trd_red_rtrancl by blast
      thus "h \<in> {0}" by simp
    qed
    finally show "trdsp (map fst (gs @ bs)) ` set (discard_crit_pairs pc_crit gs bs ps sps data) \<subseteq> {0}" .
  qed
  thus ?thesis by simp
qed

lemma gb_aux_monomial_set:
  assumes "\<And>p q. (p, q) \<in> (set ps) \<Longrightarrow> is_monomial (fst p) \<and> is_monomial (fst q)"
  assumes "gb_aux data gs bs ps = gs @ bs \<Longrightarrow> thesis"
    and "gb_aux data gs bs ps = [(1, 0, default)] \<Longrightarrow> thesis"
  shows thesis
  using struct_spec_gb assms unfolding gb_aux_def
proof (induct data gs bs ps arbitrary: thesis rule: gb_schema_aux_induct)
  case (base bs data)
  from refl show ?case by (rule base.prems(2))
next
  case (rec1 bs ps sps h data)
  from refl show ?case by (rule rec1.prems(3))
next
  case (rec2 bs ps sps hs data data')
  have *: "fst (gb_compl gs bs (ps -- sps) sps data) = []"
  proof (rule gb_compl_monomial_set, rule rec2.prems)
    fix p q
    assume "(p, q) \<in> set sps"
    also from sel_spec_gb_sel rec2(1) have "... \<subseteq> set ps" unfolding rec2(2) by (rule sel_specD2)
    finally show "(p, q) \<in> set ps" .
  qed
  have "hs = fst (add_indices (gb_compl gs bs (ps -- sps) sps data) data)"
    by (simp add: rec2(3)[symmetric])
  also have "... = []" by (simp add: add_indices_def *)
  finally have "hs = []" .
  hence eq: "gb_ab gs bs hs data' = bs" by (simp add: add_basis_sorted_def)
  show ?case
  proof (rule rec2.hyps)
    fix p q
    assume "(p, q) \<in> set (gb_ap gs bs (ps -- sps) hs data')"
    hence "(p, q) \<in> set ps" by (simp add: \<open>hs = []\<close> set_add_pairs_sorted set_diff_list)
    thus "is_monomial (fst p) \<and> is_monomial (fst q)" by (rule rec2.prems(1))
  qed (simp_all add: eq rec2.prems(2, 3))
qed

lemma gb_is_monomial_set:
  assumes "is_monomial_set (fst ` set bs0)"
  shows "is_monomial_set (fst ` set (gb bs0 ()))"
proof (simp add: gb_simps Let_def fst_set_drop_indices)
  define data where "data = (length bs0, ())"
  define bs where "bs = fst (add_indices (bs0, ()) (0, ()))"
  define bs' where "bs' = gb_ab [] [] bs data"
  define ps where "ps = gb_ap [] [] [] bs data"
  have bs: "fst ` set bs = fst ` set bs0" by (simp add: bs_def fst_set_add_indices)
  show "is_monomial_set (fst ` set (gb_aux data [] bs' ps))"
  proof (rule gb_aux_monomial_set)
    fix p q
    assume "(p, q) \<in> set ps"
    also from ap_spec_add_pairs_sorted have "... \<subseteq> set [] \<union> set bs \<times> (set [] \<union> set [] \<union> set bs)"
      unfolding ps_def by (rule ap_specD1)
    also have "... = set bs \<times> set bs" by simp
    finally have "(p, q) \<in> set bs \<times> set bs" .
    hence "fst p \<in> fst ` set bs" and "fst q \<in> fst ` set bs" by simp_all
    hence "fst p \<in> fst ` set bs0" and "fst q \<in> fst ` set bs0" by (simp_all only: bs)
    thus "is_monomial (fst p) \<and> is_monomial (fst q)"
      using assms unfolding is_monomial_set_def by auto
  next
    assume "gb_aux data [] bs' ps = [] @ bs'"
    moreover have "fst ` set bs' = fst ` set bs0"
      by (simp add: bs'_def ab_specD1[OF ab_spec_add_basis_sorted] bs)
    ultimately show ?thesis by (simp add: assms)
  next
    assume eq: "gb_aux data [] bs' ps = [(1, 0, default)]"
    show ?thesis
      by (simp add: eq is_monomial_set_def single_one[symmetric] del: single_one,
          rule monomial_is_monomial, simp)
  qed
qed

subsection \<open>Binomials\<close>

lemma spoly_binomial_monom:
  fixes tp
  assumes obd: "is_obd cp sp dp tp" and "cq \<noteq> 0"
  shows "spoly (binomial cp sp dp tp) (monomial cq sq) =
         monomial (dp / cp) (((lcs_powerprod_class.lcs sp sq) - sp) + tp)"
  unfolding spoly_def lc_binomial[OF obd] lp_binomial[OF obd] lc_monomial lp_monomial[OF \<open>cq \<noteq> 0\<close>]
proof -
  define u where "u = lcs_powerprod_class.lcs sp sq"
  have "sp adds u" unfolding u_def by (rule adds_lcs)
  have "sq adds u" unfolding u_def by (rule adds_lcs_2)
  from obd have "cp \<noteq> 0" unfolding is_obd_def ..
  from \<open>sp adds u\<close> have eq1: "monom_mult (1 / cp) (u - sp) (binomial cp sp dp tp) =
                        binomial 1 u (dp / cp) ((u - sp) + tp)"
    unfolding monom_mult_binomial by (simp add: \<open>cp \<noteq> 0\<close> adds_minus)
  from \<open>sq adds u\<close> have eq2: "monom_mult (1 / cq) (u - sq) (monomial cq sq) = monomial 1 u"
    unfolding monom_mult_monomial by (simp add: \<open>cq \<noteq> 0\<close> adds_minus)
  have "monom_mult (1 / cp) (u - sp) (binomial cp sp dp tp) -
        monom_mult (1 / cq) (u - sq) (monomial cq sq) =
        monomial (dp / cp) (u - sp + tp)" unfolding eq1 eq2 unfolding binomial_def by simp
  thus "monom_mult (1 / cp) (lcs_powerprod_class.lcs sp sq - sp) (binomial cp sp dp tp) -
        monom_mult (1 / cq) (lcs_powerprod_class.lcs sp sq - sq) (monomial cq sq) =
        monomial (dp / cp) (lcs_powerprod_class.lcs sp sq - sp + tp)" unfolding u_def .
qed

lemma spoly_binomial:
  fixes tp
  assumes obdp: "is_obd cp sp dp tp" and obdq: "is_obd cq sq dq tq"
  shows "spoly (binomial cp sp dp tp) (binomial cq sq dq tq) =
         binomial (dp / cp) (((lcs_powerprod_class.lcs sp sq) - sp) + tp)
               (-dq / cq) (((lcs_powerprod_class.lcs sp sq) - sq) + tq)"
  unfolding spoly_def lc_binomial[OF obdp] lp_binomial[OF obdp] lc_binomial[OF obdq] lp_binomial[OF obdq]
proof -
  define u where "u = lcs_powerprod_class.lcs sp sq"
  have "sp adds u" unfolding u_def by (rule adds_lcs)
  have "sq adds u" unfolding u_def by (rule adds_lcs_2)
  from obdp have "cp \<noteq> 0" unfolding is_obd_def ..
  from obdq have "cq \<noteq> 0" unfolding is_obd_def ..
  from \<open>sp adds u\<close> have eq1: "monom_mult (1 / cp) (u - sp) (binomial cp sp dp tp) =
                        binomial 1 u (dp / cp) ((u - sp) + tp)"
    unfolding monom_mult_binomial by (simp add: \<open>cp \<noteq> 0\<close> adds_minus)
  from \<open>sq adds u\<close> have eq2: "monom_mult (1 / cq) (u - sq) (binomial cq sq dq tq) =
                        binomial 1 u (dq / cq) ((u - sq) + tq)"
    unfolding monom_mult_binomial by (simp add: \<open>cq \<noteq> 0\<close> adds_minus)
  have "monomial (- dq / cq) (u - sq + tq) = monomial (-(dq / cq)) (u - sq + tq)" by simp
  also have "... = - monomial (dq / cq) (u - sq + tq)" by (simp only: monomial_uminus)
  finally have eq3: "monomial (-dq / cq) (u - sq + tq) = - monomial (dq / cq) (u - sq + tq)" .
  have "monom_mult (1 / cp) (u - sp) (binomial cp sp dp tp) -
        monom_mult (1 / cq) (u - sq) (binomial cq sq dq tq) =
        binomial (dp / cp) (u - sp + tp)
              (-dq / cq) (u - sq + tq)" unfolding eq1 eq2 unfolding binomial_def eq3 by simp
  thus "monom_mult (1 / cp) (lcs_powerprod_class.lcs sp sq - sp) (binomial cp sp dp tp) -
        monom_mult (1 / cq) (lcs_powerprod_class.lcs sp sq - sq) (binomial cq sq dq tq) =
        binomial (dp / cp) (lcs_powerprod_class.lcs sp sq - sp + tp)
              (-dq / cq) (lcs_powerprod_class.lcs sp sq - sq + tq)" unfolding u_def .
qed
  
lemma spoly_binomial_monomial:
  assumes "is_proper_binomial p" and "is_monomial q"
  shows "is_monomial (spoly p q)"
proof -
  from \<open>is_proper_binomial p\<close> obtain cp sp dp tp where obd: "is_obd cp sp dp tp"
    and p_def: "p = binomial cp sp dp tp" by (rule is_proper_binomial_binomial_od)
  from \<open>is_monomial q\<close> obtain cq sq where "cq \<noteq> 0" and q_def: "q = monomial cq sq" by (rule is_monomial_monomial)
  show ?thesis unfolding p_def q_def spoly_binomial_monom[OF obd \<open>cq \<noteq> 0\<close>]
  proof (rule monomial_is_monomial)
    from obd show "dp / cp \<noteq> 0" unfolding is_obd_def by simp
  qed
qed
    
lemma spoly_monomial_binomial:
  assumes "is_monomial p" and "is_proper_binomial q"
  shows "is_monomial (spoly p q)"
proof -
  from \<open>is_proper_binomial q\<close> \<open>is_monomial p\<close> have "is_monomial (spoly q p)"
    by (rule spoly_binomial_monomial)
  hence "is_monomial (- spoly p q)" unfolding spoly_swap[of q p] .
  thus ?thesis unfolding is_monomial_uminus .
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
      with \<open>is_monomial p\<close> have "is_monomial (spoly p q)" by (rule spoly_monomial_binomial)
      thus ?thesis unfolding is_monomial_def by simp
    qed
  next
    assume "is_proper_binomial p"
    from \<open>is_binomial q\<close> show ?thesis unfolding is_binomial_alt
    proof
      assume "is_monomial q"
      with \<open>is_proper_binomial p\<close> have "is_monomial (spoly p q)" by (rule spoly_binomial_monomial)
      thus ?thesis unfolding is_monomial_def by simp
    next
      assume "is_proper_binomial q"
      from \<open>is_proper_binomial p\<close> obtain cp sp dp tp where obdp: "is_obd cp sp dp tp"
        and p_def: "p = binomial cp sp dp tp" by (rule is_proper_binomial_binomial_od)
      from \<open>is_proper_binomial q\<close> obtain cq sq dq tq where obdq: "is_obd cq sq dq tq"
        and q_def: "q = binomial cq sq dq tq" by (rule is_proper_binomial_binomial_od)
      show ?thesis unfolding p_def q_def spoly_binomial[OF obdp obdq] by (rule card_keys_binomial)
    qed
  qed
qed

lemma gb_compl_binomial_set:
  assumes "\<And>p q. (p, q) \<in> set sps \<Longrightarrow> is_binomial (fst p) \<and> is_binomial (fst q)"
    and "is_binomial_set (fst ` set gs)" and "is_binomial_set (fst ` set bs)"
  shows "is_binomial_set (fst ` set (fst (gb_compl gs bs ps sps data)))"
proof (simp only: discard_red_cp_def fst_set_fst_gb_red set_gb_red_aux is_binomial_set_def, rule)
  fix h
  assume "h \<in> trdsp (map fst (gs @ bs)) ` set (discard_crit_pairs pc_crit gs bs ps sps data) - {0}"
  hence "h \<in> trdsp (map fst (gs @ bs)) ` set sps" and "h \<noteq> 0"
    by (auto simp add: set_discard_crit_pairs_partition[of sps pc_crit gs bs ps data])
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
  shows "is_binomial_set (fst ` set (gb_aux data gs bs ps))"
   unfolding gb_aux_def using struct_spec_gb assms(1, 3)
proof (induct data gs bs ps rule: gb_schema_aux_induct)
  case (base bs data)
  from assms(2) base(2) show ?case by (auto simp add: is_binomial_set_def)
next
  case (rec1 bs ps sps h data)
  show ?case by (simp add: is_binomial_set_def is_binomial_def)
next
  case (rec2 bs ps sps hs data data')
  have "is_binomial_set (fst ` set (fst (gb_compl gs bs (ps -- sps) sps data)))"
  proof (rule gb_compl_binomial_set, rule rec2.prems)
    fix p q
    assume "(p, q) \<in> set sps"
    also from sel_spec_gb_sel rec2(1) have "... \<subseteq> set ps" unfolding rec2(2) by (rule sel_specD2)
    finally show "(p, q) \<in> set ps" .
  qed fact+
  moreover have "hs = fst (add_indices (gb_compl gs bs (ps -- sps) sps data) data)"
    by (simp add: rec2(3)[symmetric])
  ultimately have hs: "is_binomial_set (fst ` set hs)" by (simp add: fst_set_add_indices)
  show ?case
  proof (rule rec2.hyps)
    fix p q
    assume "(p, q) \<in> set (gb_ap gs bs (ps -- sps) hs data')"
    also from ap_spec_add_pairs_sorted have "... \<subseteq> set (ps -- sps) \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"
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
    from rec2.prems(2) hs show "is_binomial_set (fst ` set (gb_ab gs bs hs data'))"
      by (auto simp add: ab_specD1[OF ab_spec_add_basis_sorted] is_binomial_set_def)
  qed
qed

lemma gb_is_binomial_set:
  assumes "is_binomial_set (fst ` set bs0)"
  shows "is_binomial_set (fst ` set (gb bs0 ()))"
proof (simp add: gb_simps Let_def fst_set_drop_indices)
  define data where "data = (length bs0, ())"
  define bs where "bs = fst (add_indices (bs0, ()) (0, ()))"
  define bs' where "bs' = gb_ab [] [] bs data"
  define ps where "ps = gb_ap [] [] [] bs data"
  have bs: "fst ` set bs = fst ` set bs0" by (simp add: bs_def fst_set_add_indices)
  show "is_binomial_set (fst ` set (gb_aux data [] bs' ps))"
  proof (rule gb_aux_binomial_set)
    fix p q
    assume "(p, q) \<in> set ps"
    also from ap_spec_add_pairs_sorted have "... \<subseteq> set [] \<union> set bs \<times> (set [] \<union> set [] \<union> set bs)"
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
  hence "0 \<noteq> (0::('a, 'b) poly_mapping)" by (rule comp_red_monic_basis_nonzero)
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
  hence "0 \<noteq> (0::('a, 'b) poly_mapping)" by (rule comp_red_monic_basis_nonzero)
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

end (* gd_powerprod *)

end (* theory *)
