(* Author: Alexander Maletzky *)

theory Binomials
  imports Groebner_Bases.Buchberger Monomial_Module
begin

context ordered_term
begin
  
section \<open>Reduction Modulo Monomials and Binomials\<close>
  
lemma red_binomial_keys:
  assumes "is_obd c s d t" and red: "red {binomial c s d t} p q"
  shows "card (keys q) \<le> card (keys p)"
proof -
  from assms(1) have pbd: "is_pbd c s d t" by (rule obd_imp_pbd)
  hence "c \<noteq> 0" by (rule is_pbdD)
      
  define r where "r = binomial c s d t"
  have sr: "keys r = {s, t}" unfolding r_def by (rule keys_binomial_pbd, rule obd_imp_pbd, fact)
  hence "r \<noteq> 0" using keys_eq_empty[of r] by simp
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
  from \<open>cpv \<noteq> 0\<close> have "v \<in> keys p" unfolding cpv_def by (simp add: in_keys_iff)
  from q_def0 have "q = p - monom_mult (cpv / c) u r" unfolding cpv_def ltr lcr v_def .
  also have "... = p - binomial ((cpv / c) * c) v ((cpv / c) * d) w"
    unfolding r_def monom_mult_binomial v_def w_def ..
  finally have q_def: "q = p - r'" using \<open>c \<noteq> 0\<close> unfolding r'_def by simp
      
  have "is_obd ((cpv / c) * c) v ((cpv / c) * d) w" unfolding v_def w_def by (rule is_obd_mult, fact+)
  hence obd_r': "is_obd cpv v ((cpv / c) * d) w" using \<open>c \<noteq> 0\<close> by simp
  have pbd_r': "is_pbd cpv v ((cpv / c) * d) w" by (rule obd_imp_pbd, fact)
      
  have sr': "keys r' = {v, w}" unfolding r'_def by (rule keys_binomial_pbd, rule obd_imp_pbd, fact)
  hence "r' \<noteq> 0" using keys_eq_empty[of r'] by simp
  have ltr': "lt r' = v" unfolding r'_def by (rule lt_binomial, fact)
  have lcr': "lc r' = cpv" unfolding r'_def by (rule lc_binomial, fact)
      
  have "keys q \<subseteq> (keys p - {v}) \<union> {w}"
  proof
    fix x
    assume "x \<in> keys q"
    hence "lookup q x \<noteq> 0" by (simp add: in_keys_iff)
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
      hence "lookup r' x = 0" by (simp add: in_keys_iff)
      with \<open>lookup p x \<noteq> lookup r' x\<close> have "lookup p x \<noteq> 0" by simp
      thus "x \<in> keys p" by (simp add: in_keys_iff)
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
    then obtain c s d t where pbd: "is_pbd c s d t" and r_def: "r = binomial c s d t"
      by (rule is_proper_binomial_binomial)
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
    hence "b = 0" by simp
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

lemma red_rtrancl_has_bounded_keys_set_1:
  assumes "(red B)\<^sup>*\<^sup>* p q" and "has_bounded_keys_set 1 B"
  shows "q = p \<or> card (keys q) < card (keys p)"
  using assms(1)
proof (rule rtranclE[to_pred])
  fix r
  assume "red B r q"
  then obtain b where "b \<in> B" and "b \<noteq> 0" and red: "red {b} r q" by (rule red_setE2)
  from assms(2) this(1) have "has_bounded_keys 1 b" by (rule has_bounded_keys_setD)
  hence "b = 0 \<or> is_monomial b" by (rule has_bounded_keys_1_D)
  with \<open>b \<noteq> 0\<close> have "is_monomial b" by simp
  hence "card (keys r) = Suc (card (keys q))" using red by (rule red_monomial_keys)
  hence *: "card (keys q) < card (keys r)" by simp
  assume "(red B)\<^sup>*\<^sup>* p r"
  moreover have "has_bounded_keys (card (keys p)) p" by (simp add: has_bounded_keys_def)
  ultimately have "has_bounded_keys (card (keys p)) r"
    using assms(2) by (rule has_bounded_keys_red_rtrancl) simp
  hence "card (keys r) \<le> card (keys p)" by (simp only: has_bounded_keys_def)
  with * have "card (keys q) < card (keys p)" by (rule order_less_le_trans)
  thus ?thesis ..
qed simp

end (* ordered_term *)

context gd_term
begin

lemma has_bounded_keys_trd:
  assumes "has_bounded_keys n p" and "has_bounded_keys_set m (set xs)" and "m \<le> 2"
  shows "has_bounded_keys n (trd xs p)"
  using trd_red_rtrancl assms by (rule has_bounded_keys_red_rtrancl)

lemma trd_has_bounded_keys_set_1:
  assumes "has_bounded_keys_set 1 (set xs)"
  shows "trd xs p = p \<or> card (keys (trd xs p)) < card (keys p)"
  using trd_red_rtrancl assms by (rule red_rtrancl_has_bounded_keys_set_1)
  
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
  assumes "is_binomial p" and "is_monomial q"
  shows "is_monomial (spoly p q) \<or> spoly p q = 0"
proof (rule disjCI)
  assume "spoly p q \<noteq> 0"
  with assms(2) spoly_monomial have "\<not> is_monomial p" by blast
  with assms(1) have "is_proper_binomial p" by (simp add: is_binomial_alt)
  then obtain cp sp dp tp where obd: "is_obd cp sp dp tp" and p_def: "p = binomial cp sp dp tp"
    by (rule is_proper_binomial_binomial_od)
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
  assumes "is_monomial p" and "is_binomial q"
  shows "is_monomial (spoly p q) \<or> spoly p q = 0"
proof -
  from assms(2, 1) have "is_monomial (spoly q p) \<or> spoly q p = 0" by (rule spoly_binomial_monomial)
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
    hence "is_monomial (spoly p q) \<or> spoly p q = 0" using assms(2) by (rule spoly_monomial_binomial)
    thus ?thesis by (auto simp: is_monomial_def)
  next
    assume "is_proper_binomial p"
    from \<open>is_binomial q\<close> show ?thesis unfolding is_binomial_alt
    proof
      assume "is_monomial q"
      with assms(1) have "is_monomial (spoly p q) \<or> spoly p q = 0" by (rule spoly_binomial_monomial)
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

subsection \<open>Mixed Sets\<close>

lemma gb_red_binomial_monomial_set:
  assumes "\<And>p q. (p, q) \<in> set sps \<Longrightarrow> ((is_monomial (fst p) \<and> is_binomial (fst q)) \<or>
                                       (is_binomial (fst p) \<and> is_monomial (fst q)) \<or>
                                       fst p = fst q)"
    and "is_binomial_set (fst ` set gs)" and "is_binomial_set (fst ` set bs)"
  shows "is_monomial_set (fst ` set (fst (gb_red gs bs ps sps data)))"
proof (simp only: fst_set_fst_gb_red set_gb_red_aux, rule is_monomial_setI)
  fix h
  assume "h \<in> trdsp (map fst (gs @ bs)) ` set sps - {0}"
  hence "h \<in> trdsp (map fst (gs @ bs)) ` set sps" and "h \<noteq> 0" by simp_all
  from this(1) obtain p q where "(p, q) \<in> set sps" and h: "h = trdsp (map fst (gs @ bs)) (p, q)"
    by fastforce
  from this(1) have disj: "(is_monomial (fst p) \<and> is_binomial (fst q)) \<or>
                          (is_binomial (fst p) \<and> is_monomial (fst q)) \<or> fst p = fst q"
    by (rule assms(1))
  from assms(2, 3) have "is_binomial_set (set (map fst (gs @ bs)))"
    by (auto simp add: is_binomial_set_def)
  moreover have "(red (set (map fst (gs @ bs))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) h"
    unfolding h trdsp_alt by (rule trd_red_rtrancl)
  ultimately have "card (keys h) \<le> card (keys (spoly (fst p) (fst q)))"
    by (rule red_rtrancl_binomial_keys)
  also from disj have "\<dots> \<le> 1"
  proof (elim disjE conjE)
    assume "is_monomial (fst p)" and "is_binomial (fst q)"
    hence "is_monomial (spoly (fst p) (fst q)) \<or> spoly (fst p) (fst q) = 0"
      by (rule spoly_monomial_binomial)
    thus ?thesis by (auto simp: is_monomial_def)
  next
    assume "is_binomial (fst p)" and "is_monomial (fst q)"
    hence "is_monomial (spoly (fst p) (fst q)) \<or> spoly (fst p) (fst q) = 0"
      by (rule spoly_binomial_monomial)
    thus ?thesis by (auto simp: is_monomial_def)
  qed (simp add: spoly_same)
  finally have "card (keys h) \<le> 1" .
  moreover from \<open>h \<noteq> 0\<close> have "card (keys h) \<noteq> 0" by simp
  ultimately show "is_monomial h" unfolding is_monomial_def by linarith
qed

lemma gb_aux_binomial_monomial_set:
  assumes "\<And>p q. (p, q) \<in> set ps \<Longrightarrow> ((is_monomial (fst p) \<and> is_binomial (fst q)) \<or>
                                       (is_binomial (fst p) \<and> is_monomial (fst q)) \<or>
                                       fst p = fst q)"
    and "is_binomial_set (fst ` set gs)" and "is_binomial_set (fst ` set bs)"
  obtains B where "fst ` set (gb_aux gs data bs ps) \<subseteq> fst ` set (gs @ bs) \<union> B" and "is_monomial_set B"
  unfolding gb_aux_def using struct_spec_gb assms(1, 3)
proof (induct gs data bs ps arbitrary: thesis rule: gb_schema_aux_induct)
  case (base bs data)
  have "fst ` set (gs @ bs) \<subseteq> fst ` set (gs @ bs) \<union> {}" by simp
  moreover have "is_monomial_set {}" by (simp add: is_monomial_set_def)
  ultimately show ?case by (rule base)
next
  case (rec1 bs ps sps data)
  have "fst ` set (full_gb (gs @ bs)) \<subseteq> fst ` set (gs @ bs) \<union> fst ` set (full_gb (gs @ bs))" by simp
  moreover have "is_monomial_set (fst ` set (full_gb (gs @ bs)))"
    by (simp add: is_monomial_set_def is_monomial_def full_gb_def)
  ultimately show ?case by (rule rec1)
next
  case (rec2 bs ps sps aux hs rc data data')
  have "is_monomial_set (fst ` set (fst (gb_red gs bs (ps -- sps) sps (snd data))))"
  proof (rule gb_red_binomial_monomial_set, rule rec2.prems)
    fix p q
    assume "(p, q) \<in> set sps"
    also from sel_spec_gb_sel rec2(1) have "... \<subseteq> set ps" unfolding rec2(2) by (rule sel_specD2)
    finally show "(p, q) \<in> set ps" .
  qed fact+
  moreover have "hs = fst (add_indices (gb_red gs bs (ps -- sps) sps (snd data)) (snd data))"
    by (simp add: rec2(3, 4)[symmetric])
  ultimately have hs: "is_monomial_set (fst ` set hs)" by (simp add: fst_set_add_indices)
  hence hs': "is_binomial_set (fst ` set hs)"
    by (auto intro: is_binomial_setI monomial_imp_binomial dest: is_monomial_setD)
  obtain B where sub: "fst ` set (gb_schema_aux gb_sel add_pairs_canon add_basis_canon gb_red gs (rc, data')
                (add_basis_canon gs bs hs data') (add_pairs_canon gs bs (ps -- sps) hs data')) \<subseteq>
                fst ` set (gs @ add_basis_canon gs bs hs data') \<union> B" and "is_monomial_set B"
  proof (rule rec2.hyps)
    fix p q
    assume "(p, q) \<in> set (add_pairs_canon gs bs (ps -- sps) hs data')"
    also from ap_spec_add_pairs_canon have "... \<subseteq> set (ps -- sps) \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      by (rule ap_specD1)
    also have "\<dots> \<subseteq> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (auto simp add: set_diff_list)
    finally show "(is_monomial (fst p) \<and> is_binomial (fst q)) \<or>
                  (is_binomial (fst p) \<and> is_monomial (fst q)) \<or> fst p = fst q"
    proof
      assume "(p, q) \<in> set ps"
      thus ?thesis by (rule rec2.prems(2))
    next
      assume "(p, q) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      hence "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" by simp_all
      hence "fst p \<in> fst ` set hs" and disj: "fst q \<in> fst ` set gs \<union> fst ` set bs \<union> fst ` set hs"
        by auto
      from hs this(1) have "is_monomial (fst p)" by (rule is_monomial_setD)
      moreover from disj have "is_binomial (fst q)"
      proof (elim UnE)
        assume "fst q \<in> fst ` set gs"
        with assms(2) show ?thesis by (rule is_binomial_setD)
      next
        assume "fst q \<in> fst ` set bs"
        with rec2.prems(3) show ?thesis by (rule is_binomial_setD)
      next
        assume "fst q \<in> fst ` set hs"
        with hs' show ?thesis by (rule is_binomial_setD)
      qed
      ultimately have "is_monomial (fst p) \<and> is_binomial (fst q)" ..
      thus ?thesis ..
    qed
  next
    from rec2.prems(3) hs' show "is_binomial_set (fst ` set (add_basis_canon gs bs hs data'))"
      by (auto simp: ab_specD1[OF ab_spec_add_basis_sorted] is_binomial_set_def)
  qed
  show ?case
  proof (rule rec2.prems)
    show "fst ` set (gb_schema_aux gb_sel add_pairs_canon add_basis_canon gb_red gs (rc, data')
                (add_basis_canon gs bs hs data') (add_pairs_canon gs bs (ps -- sps) hs data')) \<subseteq>
          fst ` set (gs @ bs) \<union> (B \<union> fst ` (set (add_basis_canon gs bs hs data') - set bs))"
      using sub by auto
  next
    have "fst ` (set (add_basis_canon gs bs hs data') - set bs) \<subseteq> fst ` set hs"
      by (auto simp: ab_specD1[OF ab_spec_add_basis_sorted])
    with hs have "is_monomial_set (fst ` (set (add_basis_canon gs bs hs data') - set bs))"
      by (rule is_monomial_set_subset)
    with \<open>is_monomial_set B\<close> show "is_monomial_set (B \<union> fst ` (set (add_basis_canon gs bs hs data') - set bs))"
      by (simp only: is_monomial_set_Un)
  qed
qed

lemma gb_binomial_monomial_set:
  assumes "is_binomial (fst b0)" and "is_monomial_set (fst ` set bs0)"
  obtains B where "fst ` set (gb (b0 # bs0) ()) \<subseteq> insert (fst b0) B" and "is_monomial_set B"
proof -
  define data0 where "data0 = (Suc (length bs0), ())"
  define bs where "bs = fst (add_indices (b0 # bs0, ()) (0, ()))"
  define bs' where "bs' = add_basis_canon [] [] bs data0"
  define data where "data = (count_rem_components bs', data0)"
  define ps where "ps = add_pairs_canon [] [] [] bs data0"
  have bs: "fst ` set bs = insert (fst b0) (fst ` set bs0)" by (simp add: bs_def fst_set_add_indices)
  obtain B where "fst ` set (gb_aux [] data bs' ps) \<subseteq> fst ` set ([] @ bs') \<union> B" and "is_monomial_set B"
  proof (rule gb_aux_binomial_monomial_set)
    fix p q
    assume "(p, q) \<in> set ps"
    also from ap_spec_add_pairs_canon have "... \<subseteq> set [] \<union> set bs \<times> (set [] \<union> set [] \<union> set bs)"
      unfolding ps_def by (rule ap_specD1)
    also have "... = set bs \<times> set bs" by simp
    finally have "(p, q) \<in> set bs \<times> set bs" .
    hence "fst p \<in> fst ` set bs" and "fst q \<in> fst ` set bs" by simp_all
    hence "fst p = fst b0 \<or> fst p \<in> fst ` set bs0" and "fst q = fst b0 \<or> fst q \<in> fst ` set bs0"
      by (simp_all add: bs)
    thus "(is_monomial (fst p) \<and> is_binomial (fst q)) \<or>
            (is_binomial (fst p) \<and> is_monomial (fst q)) \<or> fst p = fst q"
      using assms by (auto simp: is_monomial_set_def dest!: monomial_imp_binomial[of "fst p"])
  next
    show "is_binomial_set (fst ` set [])" by (simp add: is_binomial_set_def)
  next
    from assms(1) have "is_binomial_set {fst b0}" by (simp add: is_binomial_set_def)
    moreover from assms(2) have "is_binomial_set (fst ` set bs0)"
      by (auto intro: is_binomial_setI monomial_imp_binomial dest: is_monomial_setD)
    ultimately have "is_binomial_set ({fst b0} \<union> fst ` set bs0)" by (simp only: is_binomial_set_Un)
    thus "is_binomial_set (fst ` set bs')"
      by (simp add: bs'_def ab_specD1[OF ab_spec_add_basis_sorted] bs)
  qed
  show ?thesis
  proof
    have "fst ` set (gb (b0 # bs0) ()) = fst ` set (gb_aux [] data bs' ps)"
      by (simp add: gb_simps Let_def fst_set_drop_indices data0_def data_def bs_def bs'_def ps_def)
    also have "\<dots> \<subseteq> fst ` set ([] @ bs') \<union> B" by fact
    also have "\<dots> = insert (fst b0) (fst ` set bs0 \<union> B)"
      by (simp add: bs'_def ab_specD1[OF ab_spec_add_basis_sorted] bs)
    finally show "fst ` set (gb (b0 # bs0) ()) \<subseteq> insert (fst b0) (fst ` set bs0 \<union> B)" .
  next
    from \<open>is_monomial_set B\<close> assms(2) show "is_monomial_set (fst ` set bs0 \<union> B)"
      by (simp only: is_monomial_set_Un)
  qed
qed

section \<open>Reduced Gr\"obner Bases\<close>
  
subsection \<open>Function @{const comp_red_basis}\<close>

lemma comp_red_basis_aux_has_bounded_keys_set:
  assumes "has_bounded_keys_set n (set (xs @ ys))" and "n \<le> 2"
  shows "has_bounded_keys_set n (set (comp_red_basis_aux xs ys))"
  using assms(1)
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

lemma comp_red_basis_aux_binomial_monomial_set_cases:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)" and "set (xs @ ys) \<subseteq> insert b B"
    and "is_binomial b" and "is_monomial_set B" and "g \<in> set (comp_red_basis_aux xs ys)"
  obtains "g = b" | "is_monomial g"
  using assms(1, 2, 3, 5, 6)
proof (induct xs arbitrary: thesis B ys)
  case Nil
  from Nil(5, 7) have "g = b \<or> g \<in> B" by auto
  thus ?case
  proof
    assume "g = b"
    thus ?thesis by (rule Nil(1))
  next
    assume "g \<in> B"
    with Nil(6) have "is_monomial g" by (rule is_monomial_setD)
    thus ?thesis by (rule Nil(2))
  qed
next
  case (Cons x xs)
  have eq: "(x # xs) @ ys = x # (xs @ ys)" by simp
  from Cons.prems(4) have x: "x \<notin> set (xs @ ys)" by simp
  let ?y = "trd (xs @ ys) x"
  let ?ys = "?y # ys"
  let ?B = "insert ?y B - {b}"
  from Cons.prems(3) x have 1: "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
    by (rule is_minimal_basis_trd_is_minimal_basis)
  from Cons.prems(3, 4) have 2: "distinct (xs @ ?ys)" unfolding distinct_reorder eq
    by (rule is_minimal_basis_trd_distinct)
  show ?case
  proof (rule Cons.hyps)
    assume "g = b"
    thus ?thesis by (rule Cons.prems)
  next
    assume "is_monomial g"
    thus ?thesis by (rule Cons.prems)
  next
    from Cons.prems(5) show "set (xs @ ?ys) \<subseteq> insert b ?B" by auto
  next
    show "is_monomial_set ?B"
    proof (rule is_monomial_setI, elim DiffE insertE)
      fix z
      assume "z \<notin> {b}"
      hence "z \<noteq> b" by simp
      assume z: "z = ?y"
      hence "z \<in> set ?ys" by simp
      with subset_comp_red_basis_aux have "z \<in> set (comp_red_basis_aux xs ?ys)" ..
      with 1 2 have "z \<noteq> 0" by (rule comp_red_basis_aux_nonzero)
      from Cons.prems(5) have "x = b \<or> x \<in> B" by simp
      thus "is_monomial z"
      proof
        assume "x = b"
        with x Cons.prems(5) have "set (xs @ ys) \<subseteq> B" by auto
        with Cons.prems(6) have "is_monomial_set (set (xs @ ys))" by (rule is_monomial_set_subset)
        hence "has_bounded_keys_set 1 (set (xs @ ys))" by (rule has_bounded_keys_set_1_I1)
        hence "z = x \<or> card (keys z) < card (keys x)" unfolding z by (rule trd_has_bounded_keys_set_1)
        with \<open>z \<noteq> b\<close> have "card (keys z) < card (keys b)" by (simp add: \<open>x = b\<close>)
        also from assms(4) have "\<dots> \<le> 2" by (auto simp: is_binomial_def)
        finally have "z = 0 \<or> is_monomial z" by (auto simp: is_monomial_def dest: less_2_cases)
        with \<open>z \<noteq> 0\<close> show ?thesis by simp
      next
        assume "x \<in> B"
        with Cons.prems(6) have "is_monomial x" by (rule is_monomial_setD)
        hence "has_bounded_keys 1 x" by (rule has_bounded_keys_1_I1)
        moreover have "has_bounded_keys_set 2 (set (xs @ ys))"
        proof (rule has_bounded_keys_set_2_I1, rule is_binomial_set_subset)
          from assms(4) Cons.prems(6) show "is_binomial_set (insert b B)"
            by (auto intro: is_binomial_setI dest: is_monomial_setD monomial_imp_binomial)
        next
          from Cons.prems(5) show "set (xs @ ys) \<subseteq> insert b B" by simp
        qed
        ultimately have "has_bounded_keys 1 z" using le_refl unfolding z by (rule has_bounded_keys_trd)
        hence "z = 0 \<or> is_monomial z" by (rule has_bounded_keys_1_D)
        with \<open>z \<noteq> 0\<close> show ?thesis by simp
      qed
    next
      fix z
      assume "z \<in> B"
      with Cons.prems(6) show "is_monomial z" by (rule is_monomial_setD)
    qed
  next
    from Cons.prems(7) show "g \<in> set (comp_red_basis_aux xs ?ys)" by simp
  qed fact+
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

lemma comp_red_basis_binomial_monomial_set_cases:
  assumes "set xs \<subseteq> insert b B" and "is_binomial b" and "is_monomial_set B"
    and "g \<in> set (comp_red_basis xs)"
  obtains "g = b" | "is_monomial g"
proof -
  let ?xs = "comp_min_basis xs"
  have "is_minimal_basis (set (?xs @ []))" and "distinct (?xs @ [])"
    by (simp_all add: comp_min_basis_is_minimal_basis comp_min_basis_distinct)
  moreover from comp_min_basis_subset assms(1) have "set (?xs @ []) \<subseteq> insert b B"
    unfolding append_Nil2 by (rule subset_trans)
  moreover note assms(2, 3)
  moreover from assms(4) have "g \<in> set (comp_red_basis_aux ?xs [])" by (simp only: comp_red_basis_def)
  ultimately show ?thesis by (rule comp_red_basis_aux_binomial_monomial_set_cases) (erule that)+
qed
  
subsection \<open>Monicity\<close>
  
lemma comp_red_monic_basis_has_bounded_keys_set:
  assumes "has_bounded_keys_set n (set xs)" and "n \<le> 2"
  shows "has_bounded_keys_set n (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis
  by (rule image_monic_has_bounded_keys, rule comp_red_basis_has_bounded_keys_set, fact+)

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
  from finite_list[OF \<open>finite B\<close>] obtain xs where set[symmetric]: "set xs = B" ..
  from assms(1) have a: "is_binomial_set (set xs)" unfolding set .
  show ?thesis unfolding set reduced_GB_comp rgb_def
    by (rule comp_red_monic_basis_is_binomial_set, simp, rule gb_is_binomial_set,
        simp add: image_image, fact a)
qed

theorem reduced_GB_binomial_monomial_set_cases:
  assumes "is_binomial b" and "is_monomial_set B" and "finite B" and "g \<in> reduced_GB (insert b B)"
  assumes "\<And>c. c \<noteq> 0 \<Longrightarrow> g = c \<cdot> b \<Longrightarrow> is_proper_binomial g \<Longrightarrow> thesis"
  assumes "is_monomial g \<Longrightarrow> thesis"
  shows thesis
proof -
  from finite_list[OF assms(3)] obtain bs where "set bs = B" ..
  hence set: "insert b B = set (b # bs)" by simp
  let ?xs = "(b, ()) # map (\<lambda>b. (b, ())) bs"
  note assms(4)
  also have "reduced_GB (insert b B) = set (rgb (b # bs))" by (simp only: set reduced_GB_comp)
  also have "\<dots> = monic ` set (comp_red_basis (map fst (gb ?xs ())))"
    by (simp add: rgb_def comp_red_monic_basis_def)
  finally obtain g' where g'_in: "g' \<in> set (comp_red_basis (map fst (gb ?xs ())))"
    and g: "g = monic g'" ..
  from assms(1) have "is_binomial (fst (b, ()))" by simp
  obtain B' where "fst ` set (gb ?xs ()) \<subseteq> insert (fst (b, ())) B'" and "is_monomial_set B'"
  proof (rule gb_binomial_monomial_set)
    from assms(1) show "is_binomial (fst (b, ()))" by simp
  next
    from assms(2) show "is_monomial_set (fst ` set (map (\<lambda>b. (b, ())) bs))"
      by (simp add: image_image \<open>set bs = B\<close>)
  qed
  from this(1) have "set (map fst (gb ?xs ())) \<subseteq> insert b B'" by simp
  thus ?thesis using assms(1) \<open>is_monomial_set B'\<close> g'_in
  proof (rule comp_red_basis_binomial_monomial_set_cases)
    assume "g' = b"
    with assms(1) have "is_monomial g' \<or> is_proper_binomial g'" by (simp only: is_binomial_alt)
    thus ?thesis
    proof
      assume "is_monomial g'"
      hence "is_monomial g" by (simp only: g is_monomial_def keys_monic)
      thus ?thesis by (rule assms(6))
    next
      assume "is_proper_binomial g'"
      hence "g' \<noteq> 0" by (rule proper_binomial_not_0)
      hence "lc g' \<noteq> 0" by (rule lc_not_0)
      hence "1 / lc g' \<noteq> 0" by simp
      moreover have "g = (1 / lc g') \<cdot> b" by (simp only: g \<open>g' = b\<close> monic_def map_scale_eq_monom_mult)
      moreover from \<open>is_proper_binomial g'\<close> have "is_proper_binomial g"
        by (simp only: g is_proper_binomial_def keys_monic)
      ultimately show ?thesis by (rule assms(5))
    qed
  next
    assume "is_monomial g'"
    hence "is_monomial g" by (simp only: g is_monomial_def keys_monic)
    thus ?thesis by (rule assms(6))
  qed
qed

section \<open>Stuff that should be moved into AFP\<close>

lemma reduced_GB_lt_addsD_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
    and "p \<in> pmdl F" and "p \<noteq> 0" and "g \<in> reduced_GB F" and "v \<in> keys g" and "lt p adds\<^sub>t v"
  shows "v = lt g" and "lt p = lt g"
proof -
  let ?G = "reduced_GB F"
  from assms(1-3) have "is_Groebner_basis ?G" and pmdl: "pmdl ?G = pmdl F" and "is_auto_reduced ?G"
    by (rule reduced_GB_is_GB_dgrad_p_set, rule reduced_GB_pmdl_dgrad_p_set,
        rule reduced_GB_is_auto_reduced_dgrad_p_set)
  note this(1)
  moreover from assms(4) have "p \<in> pmdl ?G" by (simp only: pmdl)
  ultimately obtain g' where "g' \<in> ?G" and "g' \<noteq> 0" and 2: "lt g' adds\<^sub>t lt p"
    using assms(5) by (rule GB_adds_lt)
  have "g' = g"
  proof (rule ccontr)
    assume "g' \<noteq> g"
    with \<open>g' \<in> ?G\<close> have "g' \<in> ?G - {g}" by simp
    moreover note \<open>g' \<noteq> 0\<close> assms(7)
    moreover from 2 assms(8) have "lt g' adds\<^sub>t v" by (rule adds_term_trans)
    ultimately have "is_red (?G - {g}) g" by (rule is_red_addsI)
    moreover from \<open>is_auto_reduced ?G\<close> assms(6) have "\<not> is_red (?G - {g}) g" by (rule is_auto_reducedD)
    ultimately show False by simp
  qed
  with 2 have "lt g adds\<^sub>t lt p" by simp
  hence "lt g \<preceq>\<^sub>t lt p" by (rule ord_adds_term)
  also from assms(8) have "\<dots> \<preceq>\<^sub>t v" by (rule ord_adds_term)
  finally have "lt g \<preceq>\<^sub>t v" .
  also from assms(7) have "\<dots> \<preceq>\<^sub>t lt g" by (rule lt_max_keys)
  finally show "v = lt g" by (rule sym)
  with \<open>lt p \<preceq>\<^sub>t v\<close> have "lt p \<preceq>\<^sub>t lt g" by simp
  thus "lt p = lt g" using \<open>lt g \<preceq>\<^sub>t lt p\<close> by (rule ord_term_lin.antisym)
qed

corollary reduced_GB_lt_addsD_finite:
  assumes "finite F" and "p \<in> pmdl F" and "p \<noteq> 0" and "g \<in> reduced_GB F" and "v \<in> keys g"
    and "lt p adds\<^sub>t v"
  shows "v = lt g" and "lt p = lt g"
proof -
  note dickson_grading_dgrad_dummy
  moreover from assms(1) have "finite (component_of_term ` Keys F)"
    by (rule finite_imp_finite_component_Keys)
  moreover from assms(1) have "F \<subseteq> dgrad_p_set dgrad_dummy (Max (dgrad_dummy ` pp_of_term ` Keys F))"
    by (rule dgrad_p_set_exhaust_expl)
  ultimately show "v = lt g" and "lt p = lt g"
    using assms(2-6) by (rule reduced_GB_lt_addsD_dgrad_p_set)+
qed

lemma reduced_GB_cases_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
    and "g \<in> reduced_GB F"
  assumes "\<And>f. f \<in> F \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> lt g = lt f \<Longrightarrow> thesis"
  assumes "\<not> is_red F g \<Longrightarrow> thesis"
  shows thesis
proof (cases "is_red F g")
  case True
  then obtain f v where "f \<in> F" and "f \<noteq> 0" and "v \<in> keys g" and 1: "lt f adds\<^sub>t v" by (rule is_red_addsE)
  from this(1) have "f \<in> pmdl F" by (rule pmdl.span_base)
  with assms(1-3) have "lt f = lt g"
    using \<open>f \<noteq> 0\<close> assms(4) \<open>v \<in> keys g\<close> 1 by (rule reduced_GB_lt_addsD_dgrad_p_set)
  from \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> this[symmetric] show ?thesis by (rule assms(5))
next
  case False
  thus ?thesis by (rule assms(6))
qed

corollary reduced_GB_cases_finite:
  "finite F \<Longrightarrow> g \<in> reduced_GB F \<Longrightarrow> (\<And>f. f \<in> F \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> lt g = lt f \<Longrightarrow> thesis) \<Longrightarrow>
    (\<not> is_red F g \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (rule reduced_GB_cases_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

end (* gd_term *)

end (* theory *)
