theory Binomials
imports Reduced_GB
begin

context ordered_powerprod
begin
  
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
  have lcr: "lc r = c" unfolding r_def by (rule lc_monomial, fact)
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

context od_powerprod
begin

lemma has_bounded_keys_trd:
  assumes "has_bounded_keys n p" and "has_bounded_keys_set m (set xs)" and "m \<le> 2"
  shows "has_bounded_keys n (trd xs p)"
  by (rule has_bounded_keys_red_rtrancl, rule trd_red_rtrancl, fact+)
  
section \<open>Gr\"obner Bases\<close>
  
lemma monomial_set_is_GB:
  assumes "is_monomial_set G"
  shows "is_Groebner_basis G"
  unfolding GB_alt_3
proof (intro ballI impI)
  fix f
  assume "f \<in> pideal G" and "f \<noteq> 0"
  from \<open>f \<noteq> 0\<close> have "lp f \<in> keys f" by (rule lp_in_keys)
  from assms \<open>f \<in> pideal G\<close> this have "\<exists>g\<in>G. lp g adds lp f" by (rule monomial_set_pideal)
  then obtain g where "g \<in> G" and "lp g adds lp f" ..
  show "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f"
  proof (rule, intro conjI)
    from assms \<open>g \<in> G\<close> have "is_monomial g" by (rule is_monomial_setD)
    thus "g \<noteq> 0" by (rule monomial_not_0)
  qed fact+
qed
  
section \<open>Function @{term gb}\<close>

subsection \<open>Monomials\<close>

lemma spoly_monom:
  assumes "c \<noteq> 0" and "d \<noteq> 0"
  shows "spoly (monomial c s) (monomial d t) = 0"
proof -
  define p where "p = monomial c s"
  define q where "q = monomial d t"
  define u where "u = lcs_powerprod_class.lcs (lp p) (lp q)"
 
  from \<open>c \<noteq> 0\<close> have lpp: "lp p = s" and lcp: "lc p = c" unfolding p_def by (rule lp_monomial, rule lc_monomial)
  from \<open>d \<noteq> 0\<close> have lpq: "lp q = t" and lcq: "lc q = d" unfolding q_def by (rule lp_monomial, rule lc_monomial)
      
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

lemma gbaux_monomial_set:
  assumes "\<And>p q. (p, q) \<in> (set ps) \<Longrightarrow> is_monomial p" and "\<And>p q. (p, q) \<in> (set ps) \<Longrightarrow> is_monomial q"
  shows "gbaux bs ps = bs"
  using assms
proof (induction rule: gbaux_induct)
  case (1 bs)
  show ?case ..
next
  case (2 bs ps p q)
  from this(2) show ?case
  proof this
    fix p0 q0
    assume "(p0, q0) \<in> (set ps)"
    hence "(p0, q0) \<in> (set ((p, q)#ps))" by simp
    thus "is_monomial p0" by (rule \<open>(p0, q0) \<in> set ((p, q) # ps) \<Longrightarrow> is_monomial p0\<close>)
  next
    fix p0 q0
    assume "(p0, q0) \<in> (set ps)"
    hence "(p0, q0) \<in> (set ((p, q)#ps))" by simp
    thus "is_monomial q0" by (rule \<open>(p0, q0) \<in> set ((p, q) # ps) \<Longrightarrow> is_monomial q0\<close>)
  qed
next
  case (3 bs ps p q h)
  have "(p, q) \<in> (set ((p, q)#ps))" by simp
  hence "is_monomial p" and "is_monomial q"
    by (rule \<open>(p, q) \<in> set ((p, q) # ps) \<Longrightarrow> is_monomial p\<close>,
        rule \<open>(p, q) \<in> set ((p, q) # ps) \<Longrightarrow> is_monomial q\<close>)
  from \<open>h = trdsp bs p q\<close> have "h = 0"
    unfolding trdsp_def spoly_monomial[OF \<open>is_monomial p\<close> \<open>is_monomial q\<close>]
    using rtrancl_0 trd_red_rtrancl by blast
  with \<open>h \<noteq> 0\<close> show ?case ..
qed

lemma gb_monomial_set:
  fixes G :: "('a, 'b::field) poly_mapping list"
  assumes "is_monomial_set (set G)"
  shows "gb G = G"
  unfolding gb_def
proof (rule gbaux_monomial_set)
  fix p q
  assume "(p, q) \<in> set (pairs G)"
  hence "p \<in> set G" by (rule in_pairsD1)
  with assms show "is_monomial p" by (rule is_monomial_setD)
next
  fix p q
  assume "(p, q) \<in> set (pairs G)"
  hence "q \<in> set G" by (rule in_pairsD2)
  with assms show "is_monomial q" by (rule is_monomial_setD)
qed
  
subsection \<open>Binomials\<close>

lemma spoly_binomial_monom:
  fixes tp
  assumes obd: "is_obd cp sp dp tp" and "cq \<noteq> 0"
  shows "spoly (binomial cp sp dp tp) (monomial cq sq) =
         monomial (dp / cp) (((lcs_powerprod_class.lcs sp sq) - sp) + tp)"
  unfolding spoly_def lc_binomial[OF obd] lp_binomial[OF obd] lc_monomial[OF \<open>cq \<noteq> 0\<close>] lp_monomial[OF \<open>cq \<noteq> 0\<close>]
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
  hence "is_monomial (- spoly p q)" unfolding spoly_exchange[of q p] .
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

lemma gbaux_binomial_set:
  assumes "\<And>p q. (p, q) \<in> (set ps) \<Longrightarrow> is_binomial p" and "\<And>p q. (p, q) \<in> (set ps) \<Longrightarrow> is_binomial q"
    and "is_binomial_set (set bs)"
  shows "is_binomial_set (set (gbaux bs ps))"
  using assms
proof (induction rule: gbaux_induct)
  case (1 bs)
  show ?case by fact
next
  case (2 bs ps p q)
  from this(2) show ?case
  proof this
    fix p0 q0
    assume "(p0, q0) \<in> (set ps)"
    hence "(p0, q0) \<in> (set ((p, q)#ps))" by simp
    thus "is_binomial p0" by (rule \<open>(p0, q0) \<in> set ((p, q) # ps) \<Longrightarrow> is_binomial p0\<close>)
  next
    fix p0 q0
    assume "(p0, q0) \<in> (set ps)"
    hence "(p0, q0) \<in> (set ((p, q)#ps))" by simp
    thus "is_binomial q0" by (rule \<open>(p0, q0) \<in> set ((p, q) # ps) \<Longrightarrow> is_binomial q0\<close>)
  qed fact
next
  case (3 bs ps p q h)
  from \<open>h \<noteq> 0\<close> have "keys h \<noteq> {}" by simp
  hence "card (keys h) \<noteq> 0" by simp
  have "(p, q) \<in> (set ((p, q)#ps))" by simp
  hence "is_binomial p" and "is_binomial q"
    by (rule \<open>(p, q) \<in> set ((p, q) # ps) \<Longrightarrow> is_binomial p\<close>,
        rule \<open>(p, q) \<in> set ((p, q) # ps) \<Longrightarrow> is_binomial q\<close>)
  have "(red (set bs))\<^sup>*\<^sup>* (spoly p q) h" unfolding \<open>h = trdsp bs p q\<close> trdsp_def by (rule trd_red_rtrancl)
  from \<open>is_binomial_set (set bs)\<close> this have "card (keys h) \<le> card (keys (spoly p q))"
    by (rule red_rtrancl_binomial_keys)
  also from \<open>is_binomial p\<close> \<open>is_binomial q\<close> have "... \<le> 2" by (rule spoly_binomial_keys)
  finally have "card (keys h) \<le> 2" .
  with \<open>card (keys h) \<noteq> 0\<close> have "is_binomial h" unfolding is_binomial_def by linarith
  show ?case
  proof (rule \<open>(\<And>p q. (p, q) \<in> set (up ps bs h) \<Longrightarrow> is_binomial p) \<Longrightarrow>
               (\<And>p q. (p, q) \<in> set (up ps bs h) \<Longrightarrow> is_binomial q) \<Longrightarrow>
               is_binomial_set (set (h # bs)) \<Longrightarrow>
               is_binomial_set (set (gbaux (h # bs) (up ps bs h)))\<close>)
    fix p0 q0
    assume "(p0, q0) \<in> (set (up ps bs h))"
    thus "is_binomial p0"
    proof (rule in_upE)
      assume "(p0, q0) \<in> set ps"
      hence "(p0, q0) \<in> (set ((p, q)#ps))" by simp
      thus ?thesis by (rule \<open>(p0, q0) \<in> set ((p, q) # ps) \<Longrightarrow> is_binomial p0\<close>)
    next
      assume "q0 = h \<and> p0 \<in> set bs"
      hence "p0 \<in> set bs" ..
      with \<open>is_binomial_set (set bs)\<close> show ?thesis by (rule is_binomial_setD)
    qed
  next
    fix p0 q0
    assume "(p0, q0) \<in> (set (up ps bs h))"
    thus "is_binomial q0"
    proof (rule in_upE)
      assume "(p0, q0) \<in> set ps"
      hence "(p0, q0) \<in> (set ((p, q)#ps))" by simp
      thus ?thesis by (rule \<open>(p0, q0) \<in> set ((p, q) # ps) \<Longrightarrow> is_binomial q0\<close>)
    next
      assume "q0 = h \<and> p0 \<in> set bs"
      hence "q0 = h" ..
      with \<open>is_binomial h\<close> show ?thesis by simp
    qed
  next
    show "is_binomial_set (set (h # bs))"
    proof (intro is_binomial_setI)
      fix f
      assume "f \<in> set (h # bs)"
      hence "f \<in> insert h (set bs)" by simp
      thus "is_binomial f"
      proof (rule insertE)
        assume "f = h"
        with \<open>is_binomial h\<close> show ?thesis by simp
      next
        assume "f \<in> set bs"
        with \<open>is_binomial_set (set bs)\<close> show ?thesis by (rule is_binomial_setD)
      qed
    qed
  qed
qed

lemma gb_is_binomial_set:
  fixes G :: "('a, 'b::field) poly_mapping list"
  assumes "is_binomial_set (set G)"
  shows "is_binomial_set (set (gb G))"
  unfolding gb_def
proof (rule gbaux_binomial_set)
  fix p q
  assume "(p, q) \<in> set (pairs G)"
  hence "p \<in> set G" by (rule in_pairsD1)
  with assms show "is_binomial p" by (rule is_binomial_setD)
next
  fix p q
  assume "(p, q) \<in> set (pairs G)"
  hence "q \<in> set G" by (rule in_pairsD2)
  with assms show "is_binomial q" by (rule is_binomial_setD)
qed fact
  
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
  unfolding comp_red_monic_basis_set
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
  show ?thesis unfolding set[symmetric] reduced_GB_comp gb_monomial_set[OF a]
    by (rule comp_red_monic_basis_is_monomial_set, fact a)
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
  show ?thesis unfolding set[symmetric] reduced_GB_comp
    by (rule comp_red_monic_basis_is_binomial_set, rule gb_is_binomial_set, fact a)
qed

end (* od_powerprod *)

end (* theory *)