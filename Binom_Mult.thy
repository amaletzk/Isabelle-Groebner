section \<open>Multiplication by Binomials\<close>

theory Binom_Mult
  imports Power_Products_PM Poly_Utils
begin

context ordered_powerprod
begin

abbreviation "lc \<equiv> punit.lc"
abbreviation "tc \<equiv> punit.tc"
abbreviation "lp \<equiv> punit.lt"
abbreviation "tp \<equiv> punit.tt"

lemma keys_monomial_plus_times:
  assumes "punit.is_proper_binomial (p::'a \<Rightarrow>\<^sub>0 'b::field)" and "q \<noteq> 0" and "v \<prec> u"
    and "keys (q * p) = {u + tp p, v + tp p}"
  shows "keys ((monomial (- (lc q * lc p) / tc p) u + q) * p) = {u + lp p, v + tp p}"
proof -
  from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
  from assms(1) have "p \<noteq> 0" by (rule punit.proper_binomial_not_0)
  hence "tc p \<noteq> 0" by (rule punit.tc_not_0)
  from assms(3) have "v + tp p \<prec> u + tp p" by (rule plus_monotone_strict)
  have "lp q + lp p = lp (q * p)" by (simp only: lp_times[OF assms(2) \<open>p \<noteq> 0\<close>])
  also from assms(4) have "... = u + tp p"
  proof (rule punit.keys_2_lt)
    from \<open>v + tp p \<prec> u + tp p\<close> show "v + tp p \<preceq> u + tp p" by simp
  qed
  finally have *: "u + tp p = lp q + lp p" by simp
  let ?c = "- (lc q * lc p) / tc p"
  from punit.lc_not_0[OF \<open>p \<noteq> 0\<close>] punit.lc_not_0[OF \<open>q \<noteq> 0\<close>] \<open>tc p \<noteq> 0\<close> have "?c \<noteq> 0" by simp
  show ?thesis
  proof (simp only: algebra_simps(17) times_monomial_left, rule punit.keys_2_plus,
        simp only: punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>], simp add: punit.keys_proper_binomial[OF assms(1)], fact, fact)
    from \<open>tp p \<prec> lp p\<close> show "u + tp p \<prec> u + lp p" by (rule plus_monotone_strict_left)
  qed (simp only: punit.lookup_monom_mult_plus[simplified] punit.tc_def[symmetric],
        simp add: \<open>tc p \<noteq> 0\<close> * lookup_times_lp_lp)
qed

lemma keys_plus_monomial_times:
  assumes "punit.is_proper_binomial (p::'a \<Rightarrow>\<^sub>0 'b::field)" and "q \<noteq> 0" and "v \<prec> u"
    and "keys (q * p) = {u + lp p, v + lp p}"
  shows "keys ((q + monomial (- (tc q * tc p) / lc p) v) * p) = {u + lp p, v + tp p}"
proof -
  from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
  from assms(1) have "p \<noteq> 0" by (rule punit.proper_binomial_not_0)
  hence "lc p \<noteq> 0" by (rule punit.lc_not_0)
  from assms(3) have "v + lp p \<prec> u + lp p" by (rule plus_monotone_strict)
  have "tp q + tp p = tp (q * p)" by (simp only: tp_times[OF assms(2) \<open>p \<noteq> 0\<close>])
  also from assms(4) have "... = v + lp p"
  proof (rule punit.keys_2_tt)
    from \<open>v + lp p \<prec> u + lp p\<close> show "v + lp p \<preceq> u + lp p" by simp
  qed
  finally have *: "v + lp p = tp q + tp p" by simp
  let ?c = "- (tc q * tc p) / lc p"
  from punit.tc_not_0[OF \<open>p \<noteq> 0\<close>] punit.tc_not_0[OF \<open>q \<noteq> 0\<close>] \<open>lc p \<noteq> 0\<close> have "?c \<noteq> 0" by simp
  show ?thesis
  proof (simp only: algebra_simps(17) times_monomial_left, rule punit.keys_2_plus, fact,
        simp only: punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>], simp add: punit.keys_proper_binomial[OF assms(1)])
    from \<open>tp p \<prec> lp p\<close> show "v + tp p \<prec> v + lp p" by (rule plus_monotone_strict_left)
  qed (fact, simp only: punit.lookup_monom_mult_plus[simplified] punit.lc_def[symmetric],
        simp add: \<open>lc p \<noteq> 0\<close> * lookup_times_tp_tp)
qed

end (* ordered_powerprod *)

context pm_powerprod
begin
  
subsubsection \<open>associated\<close>

definition associated :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat \<Rightarrow> bool"
  where "associated q s t k \<longleftrightarrow> (t + k \<cdot> (lp q) = s + k \<cdot> (tp q))"

lemma associatedI:
  assumes "t + k \<cdot> (lp q) = s + k \<cdot> (tp q)"
  shows "associated q s t k"
  unfolding associated_def using assms .

lemma associatedI_lookup:
  assumes "\<And>x. lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x"
  shows "associated q s t k"
  by (intro associatedI poly_mapping_eqI, simp add: lookup_add, fact)

lemma associatedD:
  assumes "associated q s t k"
  shows "t + k \<cdot> (lp q) = s + k \<cdot> (tp q)"
  using assms unfolding associated_def .

lemma associatedD_lookup:
  assumes "associated q s t k"
  shows "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x"
proof -
  from assms have "t + k \<cdot> lp q = s + k \<cdot> tp q" by (rule associatedD)
  hence "lookup (t + k \<cdot> (lp q)) x = lookup (s + k \<cdot> tp q) x" by simp
  thus ?thesis by (simp add: lookup_add)
qed

lemma associated_0: "associated q s t 0 \<longleftrightarrow> (s = t)"
  by (auto simp add: associated_def poly_mapping_eq_iff)

lemma associated_1: "associated q s t 1 \<longleftrightarrow> (s + tp q = t + lp q)"
  by (simp only: associated_def scalar_one_left, auto)

lemma associated_Suc: "associated q s t (Suc k) \<longleftrightarrow> associated q (s + tp q) (t + lp q) k"
  by (simp add: associated_def scalar_Suc ac_simps)

lemma associated_canc_left: "associated q (u + s) (u + t) k \<longleftrightarrow> associated q s t k"
proof -
  have "u + t + k \<cdot> lp q = u + (t + k \<cdot> lp q)" by (simp add: ac_simps)
  moreover have "u + s + k \<cdot> tp q = u + (s + k \<cdot> tp q)" by (simp add: ac_simps)
  ultimately show ?thesis by (simp add: associated_def scalar_distrib_right)
qed

lemma associated_canc_right: "associated q (s + u) (t + u) k \<longleftrightarrow> associated q s t k"
  by (simp only: add.commute[of _ u] associated_canc_left)

lemma associated_1_plus_tp:
  assumes "associated q s (u + tp q) 1"
  shows "s = u + lp q"
proof (rule add_right_imp_eq[of _ "tp q"])
  from assms show "s + tp q = u + lp q + tp q" by (simp only: associated_1 ac_simps)
qed

lemma associated_1_plus_lp:
  assumes "associated q (u + lp q) t 1"
  shows "t = u + tp q"
proof (rule add_right_imp_eq[of _ "lp q"])
  from assms show "t + lp q = u + tp q + lp q" by (simp only: associated_1 ac_simps)
qed

lemma associated_trans:
  assumes "associated q s t k" and "associated q u s m"
  shows "associated q u t (k + m)"
proof (rule associatedI)
  from assms(1) have "t + k \<cdot> (lp q) = s + k \<cdot> (tp q)"
    by (rule associatedD)
  moreover from assms(2) have "s + m \<cdot> (lp q) = u + m \<cdot> (tp q)"
    by (rule associatedD)
  ultimately show "t + (k + m) \<cdot> (lp q) = u + (k + m) \<cdot> (tp q)"
    by (simp only: scalar_distrib_right, metis (no_types, lifting) add.assoc add.commute)
qed

lemma associated_trans_rev:
  assumes "associated q s t (k + m)"
  obtains u where "associated q u t k" and "associated q s u m"
proof -
  let ?lp = "lookup (lp q)"
  let ?tp = "lookup (tp q)"
  have adds: "k \<cdot> (tp q) adds (t + k \<cdot> (lp q))"
  proof (rule adds_poly_mappingI, rule le_funI, simp add: lookup_add)
    fix x
    show "k * ?tp x \<le> lookup t x + k * ?lp x"
    proof (cases "?tp x \<le> ?lp x")
      case True
      hence "k * ?tp x \<le> k * ?lp x" by simp
      thus ?thesis by linarith
    next
      case False
      hence "?lp x \<le> ?tp x" by simp
      hence "m * ?lp x \<le> m * ?tp x" by simp
      hence "lookup t x + (k + m) * ?lp x \<le> lookup t x + k * ?lp x + m * ?tp x"
        by (simp add: algebra_simps)
      with associatedD_lookup[OF assms] have "lookup s x + k * ?tp x + m * ?tp x \<le> lookup t x + k * ?lp x + m * ?tp x"
        by (simp add: algebra_simps)
      hence "lookup s x + k * ?tp x \<le> lookup t x + k * ?lp x" by simp
      thus ?thesis by linarith
    qed
  qed
  let ?u = "(t + k \<cdot> (lp q)) - k \<cdot> (tp q)"
  show ?thesis
  proof
    show "associated q ?u t k"
    proof (rule associatedI)
      from adds show "t + k \<cdot> lp q = t + k \<cdot> lp q - k \<cdot> tp q + k \<cdot> tp q" by (simp add: adds_minus)
    qed
  next
    show "associated q s ?u m"
    proof (rule associatedI)
      have "?u + m \<cdot> lp q = t + (k + m) \<cdot> lp q - k \<cdot> tp q"
        by (simp add: add.assoc adds minus_plus scalar_distrib_right)
      also from associatedD[OF assms] have "... = (s + m \<cdot> tp q + k \<cdot> tp q) - k \<cdot> tp q"
        by (simp add: scalar_distrib_right ac_simps)
      finally show "?u + m \<cdot> lp q = s + m \<cdot> tp q" by simp
    qed
  qed
qed

lemma associated_inj_1:
  assumes "associated q s1 t k" and "associated q s2 t k"
  shows "s1 = s2"
proof -
  from assms(1) have "t + k \<cdot> lp q = s1 + k \<cdot> tp q" by (rule associatedD)
  moreover from assms(2) have "t + k \<cdot> lp q = s2 + k \<cdot> tp q" by (rule associatedD)
  ultimately show ?thesis by simp
qed

lemma associated_inj_2:
  assumes "associated q s t1 k" and "associated q s t2 k"
  shows "t1 = t2"
proof -
  from assms(1) have "t1 + k \<cdot> lp q = s + k \<cdot> tp q" by (rule associatedD)
  moreover from assms(2) have "t2 + k \<cdot> lp q = s + k \<cdot> tp q" by (rule associatedD)
  ultimately show ?thesis by (metis add_right_cancel)
qed

lemma associated_inj_3:
  assumes "\<not> punit.has_bounded_keys 1 q" and "associated q s t k1" and "associated q s t k2"
  shows "k1 = k2"
proof -
  let ?lp = "lookup (lp q)"
  let ?tp = "lookup (tp q)"
  from assms(1) have "lp q \<noteq> tp q" by (simp add: punit.lt_eq_tt_iff)
  hence "?lp \<noteq> ?tp" by (simp add: lookup_inject)
  then obtain x where "?lp x \<noteq> ?tp x" by auto
  from assms(2) have 1: "lookup t x + k1 * ?lp x = lookup s x + k1 * ?tp x" by (rule associatedD_lookup)
  from assms(3) have 2: "lookup t x + k2 * ?lp x = lookup s x + k2 * ?tp x" by (rule associatedD_lookup)
  show ?thesis
  proof (rule linorder_cases)
    from 1 have "lookup t x - lookup s x = k1 * (?tp x - ?lp x)" by (simp add: diff_mult_distrib2)
    moreover from 2 have "lookup t x - lookup s x = k2 * (?tp x - ?lp x)" by (simp add: diff_mult_distrib2)
    ultimately have eq: "k1 * (?tp x - ?lp x) = k2 * (?tp x - ?lp x)" by (simp only:)
    assume c2: "?lp x < ?tp x"
    hence "0 < ?tp x - ?lp x" by simp
    with eq show ?thesis by simp
  next
    from 1 have "lookup s x - lookup t x = k1 * (?lp x - ?tp x)" by (simp add: diff_mult_distrib2)
    moreover from 2 have "lookup s x - lookup t x = k2 * (?lp x - ?tp x)" by (simp add: diff_mult_distrib2)
    ultimately have eq: "k1 * (?lp x - ?tp x) = k2 * (?lp x - ?tp x)" by (simp only:)
    assume c1: "?tp x < ?lp x"
    hence "0 < ?lp x - ?tp x" by simp
    with eq show ?thesis by simp
  next
    assume c3: "?lp x = ?tp x"
    with \<open>?lp x \<noteq> ?tp x\<close> show ?thesis ..
  qed
qed

lemma associated_lp_adds_between:
  assumes "associated q s u m" and "associated q u t k" and "lp q adds s" and "lp q adds t"
  shows "lp q adds u"
proof (simp only: adds_poly_mapping le_fun_def, rule)
  let ?lp = "lookup (lp q)"
  let ?tp = "lookup (tp q)"
  fix x
  from assms(3) have "?lp x \<le> lookup s x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(4) have "?lp x \<le> lookup t x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(1) have a: "lookup u x + m * ?lp x = lookup s x + m * ?tp x" by (rule associatedD_lookup)
  from assms(2) have b: "lookup t x + k * ?lp x = lookup u x + k * ?tp x" by (rule associatedD_lookup)
  show "?lp x \<le> lookup u x"
  proof (cases "?tp x \<le> ?lp x")
    case True
    hence "k * ?tp x \<le> k * ?lp x" by simp
    with b have "lookup t x \<le> lookup u x" by linarith
    with \<open>?lp x \<le> lookup t x\<close> show ?thesis by simp
  next
    case False
    hence "m * ?lp x \<le> m * ?tp x" by simp
    with a have "lookup s x \<le> lookup u x" by linarith
    with \<open>?lp x \<le> lookup s x\<close> show ?thesis by simp
  qed
qed
  
lemma associated_lp_adds_between':
  assumes "associated p s u m" and "associated p u t k" and "lp p adds s" and "tp p adds t" and "k \<noteq> 0"
  shows "lp p adds u"
proof -
  from assms(5) have "1 + (k - 1) = k" by simp
  with assms(2) have "associated p u t (1 + (k - 1))" by simp
  then obtain v where a1: "associated p v t 1" and a2: "associated p u v (k - 1)"
    by (rule associated_trans_rev)
  from assms(4) obtain w where t_eq: "t = w + tp p" by (metis addsE add.commute)
  from a1 have v_eq: "v = w + lp p" by (simp only: t_eq, elim associated_1_plus_tp)
  hence "lp p adds v" by simp
  with assms(1) a2 assms(3) show ?thesis by (rule associated_lp_adds_between)
qed

lemma associated_lp_adds_between'':
  assumes "associated p s t m" and "associated p u t k" and "lp p adds s" and "tp p adds t" and "k \<le> m"
    and "k \<noteq> 0"
  shows "lp p adds u"
proof -
  from \<open>k \<le> m\<close> have "m = k + (m - k)" by simp
  with assms(1) have "associated p s t (k + (m - k))" by simp
  then obtain u' where "associated p u' t k" and *: "associated p s u' (m - k)"
    by (rule associated_trans_rev)
  from this(1) assms(2) have "u' = u" by (rule associated_inj_1)
  with * have "associated p s u (m - k)" by simp
  from this assms(2) assms(3) assms(4) assms(6) show ?thesis by (rule associated_lp_adds_between')
qed

lemma associated_tp_adds_between:
  assumes "associated q s u m" and "associated q u t k" and "tp q adds s" and "tp q adds t"
  shows "tp q adds u"
proof (simp only: adds_poly_mapping le_fun_def, rule)
  let ?lp = "lookup (lp q)"
  let ?tp = "lookup (tp q)"
  fix x
  from assms(3) have "?tp x \<le> lookup s x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(4) have "?tp x \<le> lookup t x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(1) have a: "lookup u x + m * ?lp x = lookup s x + m * ?tp x" by (rule associatedD_lookup)
  from assms(2) have b: "lookup t x + k * ?lp x = lookup u x + k * ?tp x" by (rule associatedD_lookup)
  show "?tp x \<le> lookup u x"
  proof (cases "?tp x \<le> ?lp x")
    case True
    hence "k * ?tp x \<le> k * ?lp x" by simp
    with b have "lookup t x \<le> lookup u x" by linarith
    with \<open>?tp x \<le> lookup t x\<close> show ?thesis by simp
  next
    case False
    hence "m * ?lp x \<le> m * ?tp x" by simp
    with a have "lookup s x \<le> lookup u x" by linarith
    with \<open>?tp x \<le> lookup s x\<close> show ?thesis by simp
  qed
qed

lemma associated_tp_adds_between':
  assumes "associated p s u m" and "associated p u t k" and "lp p adds s" and "tp p adds t" and "m \<noteq> 0"
  shows "tp p adds u"
proof -
  from assms(5) have "(m - 1) + 1 = m" by simp
  with assms(1) have "associated p s u ((m - 1) + 1)" by simp
  then obtain v where a1: "associated p s v 1" and a2: "associated p v u (m - 1)"
    by (rule associated_trans_rev)
  from assms(3) obtain w where t_eq: "s = w + lp p" by (metis addsE add.commute)
  from a1 have v_eq: "v = w + tp p" by (simp only: t_eq, elim associated_1_plus_lp)
  hence "tp p adds v" by simp
  from a2 assms(2) this assms(4) show ?thesis by (rule associated_tp_adds_between)
qed

lemma associated_0_left:
  assumes "associated 0 s t k"
  shows "s = t"
  using assms by (auto simp add: associated_def punit.lt_def punit.tt_def)

lemma associated_monomial:
  assumes "associated (monomial c u) s t k"
  shows "s = t"
proof (cases "c = 0")
  case True
  from assms have "associated (0::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) s t k" by (simp add: True monomial_0I)
  thus ?thesis by (rule associated_0_left)
next
  case False
  hence lp: "lp (monomial c u) = u" and tp: "tp (monomial c u) = u"
    by (rule punit.lt_monomial, rule punit.tt_monomial)
  from assms show ?thesis by (auto simp add: associated_def lp tp)
qed

lemma associated_has_bounded_keys_1:
  assumes "punit.has_bounded_keys 1 q" and "associated q s t k"
  shows "s = t"
proof -
  from assms(1) have "q = 0 \<or> is_monomial q" by (rule punit.has_bounded_keys_1_D)
  thus ?thesis
  proof
    assume "q = 0"
    from assms(2) show ?thesis unfolding \<open>q = 0\<close> by (rule associated_0_left)
  next
    assume "is_monomial q"
    then obtain c t where "q = monomial c t" by (rule is_monomial_monomial)
    from assms(2) show ?thesis unfolding \<open>q = monomial c t\<close> by (rule associated_monomial)
  qed
qed

lemma associated_leq:
  assumes "associated q s t k"
  shows "t \<preceq> s"
  using assms
proof (induct k arbitrary: s t)
  case base: 0
  from base have "s = t" by (simp add: associated_0)
  thus ?case by simp
next
  case ind: (Suc k)
  from ind(2) have  "associated q (s + tp q) (t + lp q) k" by (simp add: associated_Suc)
  hence "t + lp q \<preceq> s + tp q" by (rule ind(1))
  also have "... \<preceq> s + lp q"
  proof -
    from punit.lt_ge_tt[of q] have "tp q + s \<preceq> lp q + s" by (rule plus_monotone)
    thus ?thesis by (simp add: ac_simps)
  qed
  finally show ?case by (rule ord_canc)
qed

lemma associated_eq_iff:
  assumes "\<not> punit.has_bounded_keys 1 q" and "associated q s t k"
  shows "s = t \<longleftrightarrow> k = 0"
proof
  assume "s = t"
  from assms(1) have "lp q \<noteq> tp q" by (simp add: punit.lt_eq_tt_iff)
  then obtain x where "lookup (tp q) x \<noteq> lookup (lp q) x" using poly_mapping_eqI by fastforce
  from assms(2) have "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x"
    by (rule associatedD_lookup)
  hence "k * lookup (lp q) x = k * lookup (tp q) x" unfolding \<open>s = t\<close> by simp
  with \<open>lookup (tp q) x \<noteq> lookup (lp q) x\<close> show "k = 0" by simp
next
  assume "k = 0"
  from assms(2) show "s = t" by (simp add: \<open>k = 0\<close> associated_0)
qed

lemma associated_less:
  assumes "\<not> punit.has_bounded_keys 1 q" and "associated q s t k" and "k \<noteq> 0"
  shows "t \<prec> s"
proof -
  from assms(2) have "t \<preceq> s" by (rule associated_leq)
  moreover from assms(3) have "s \<noteq> t" by (simp add: associated_eq_iff[OF assms(1) assms(2)])
  ultimately show ?thesis by simp
qed

lemma associated_lp_not_in_keys:
  assumes "punit.is_proper_binomial p" and "associated p u (v + lp p) k" and "k \<noteq> 0"
  shows "u \<notin> {v + lp p, v + tp p}" (is "_ \<notin> {?s, ?t}")
proof -
  let ?lp = "lookup (lp p)"
  let ?tp = "lookup (tp p)"
  from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
  have "\<exists>x. ?tp x < ?lp x"
  proof (rule ccontr)
    assume "\<nexists>x. ?tp x < ?lp x"
    hence "lp p adds tp p" unfolding adds_poly_mapping adds_fun le_fun_def
      by (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
    hence "lp p \<preceq> tp p" by (rule ord_adds)
    with \<open>tp p \<prec> lp p\<close> show False by simp
  qed
  then obtain x where "?tp x < ?lp x" ..
  with \<open>k \<noteq> 0\<close> have ineq: "k * ?tp x < k * ?lp x" by simp
  from assms(2) have "lookup (v + lp p) x + k * ?lp x = lookup u x + k * ?tp x" by (rule associatedD_lookup)
  with ineq have "lookup ?s x < lookup u x" by linarith
  show ?thesis
  proof
    assume "u \<in> {?s, ?t}"
    hence "u = ?s \<or> u = ?t" by auto
    thus False
    proof
      assume "u = ?s"
      hence "lookup ?s x = lookup u x" by simp
      with \<open>lookup ?s x < lookup u x\<close> show ?thesis by simp
    next
      assume "u = ?t"
      hence "lookup ?t x = lookup u x" by simp
      from \<open>?tp x < ?lp x\<close> have "lookup ?t x < lookup ?s x" by (simp add: lookup_add)
      also have "... < lookup u x" using \<open>lookup ?s x < lookup u x\<close> .
      finally show ?thesis using \<open>lookup ?t x = lookup u x\<close> by simp
    qed
  qed
qed

lemma associated_tp_not_in_keys:
  assumes "punit.is_proper_binomial p" and "associated p (v + tp p) u k" and "k \<noteq> 0"
  shows "u \<notin> {v + lp p, v + tp p}" (is "_ \<notin> {?s, ?t}")
proof -
  let ?lp = "lookup (lp p)"
  let ?tp = "lookup (tp p)"
  from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
  have "\<exists>x. ?tp x < ?lp x"
  proof (rule ccontr)
    assume "\<nexists>x. ?tp x < ?lp x"
    hence "lp p adds tp p" unfolding adds_poly_mapping adds_fun le_fun_def
      by (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
    hence "lp p \<preceq> tp p" by (rule ord_adds)
    with \<open>tp p \<prec> lp p\<close> show False by simp
  qed
  then obtain x where "?tp x < ?lp x" ..
  with \<open>k \<noteq> 0\<close> have ineq: "k * ?tp x < k * ?lp x" by simp
  from assms(2) have "lookup u x + k * ?lp x = lookup (v + tp p) x + k * ?tp x" by (rule associatedD_lookup)
  with ineq have "lookup u x < lookup ?t x" by linarith
  show ?thesis
  proof
    assume "u \<in> {?s, ?t}"
    hence "u = ?s \<or> u = ?t" by auto
    thus False
    proof
      assume "u = ?t"
      hence "lookup ?t x = lookup u x" by simp
      with \<open>lookup u x < lookup ?t x\<close> show ?thesis by simp
    next
      assume "u = ?s"
      hence "lookup u x = lookup ?s x" by simp
      with \<open>lookup u x < lookup ?t x\<close> have "lookup ?s x < lookup ?t x" by simp
      also from \<open>?tp x < ?lp x\<close> have "... < lookup ?s x" by (simp add: lookup_add)
      finally have "lookup ?s x < lookup ?s x" .
      thus ?thesis by simp
    qed
  qed
qed

lemma associated_plus:
  assumes "associated p s t k" and "associated p u v m"
  shows "associated p (s + u) (t + v) (k + m)"
proof (rule associatedI, simp add: scalar_distrib_right)
  from assms(1) have "t + k \<cdot> lp p = s + k \<cdot> tp p" by (rule associatedD)
  moreover from assms(2) have "v + m \<cdot> lp p = u + m \<cdot> tp p" by (rule associatedD)
  ultimately show "t + v + (k \<cdot> lp p + m \<cdot> lp p) = s + u + (k \<cdot> tp p + m \<cdot> tp p)"
    by (metis (no_types, lifting) add.assoc add.commute)
qed

lemma associated_adds_obtains_cofactor_keys:
  assumes "punit.is_binomial p" and "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k" and "k \<noteq> 0"
    and "lp p adds s" and "tp p adds t"
  obtains q where "keys (q * p) = {s, t}"
proof (cases "is_monomial p")
  assume rl: "(\<And>q. keys (q * p) = {s, t} \<Longrightarrow> thesis)"
  assume "is_monomial p"
  hence "punit.has_bounded_keys 1 p" by (rule punit.has_bounded_keys_1_I1)
  hence "s = t" using assms(2) by (rule associated_has_bounded_keys_1)
  from assms(4) obtain u where s_eq: "s = u + lp p" by (metis addsE add.commute)
  let ?q = "monomial (1::'a) u"
  show ?thesis
  proof (rule rl)
    show "keys (?q * p) = {s, t}"
      by (simp add: times_monomial_left punit.keys_monom_mult punit.keys_monomial[OF \<open>is_monomial p\<close>]
          s_eq \<open>s = t\<close>[symmetric])
  qed
next
  assume rl: "(\<And>q. keys (q * p) = {s, t} \<Longrightarrow> thesis)"
  assume "\<not> is_monomial p"
  with assms(1) have "punit.is_proper_binomial p" by (simp add: punit.is_binomial_alt)
  have "\<not> punit.has_bounded_keys 1 p" using \<open>\<not> is_monomial p\<close> assms(1) punit.binomial_not_0 punit.has_bounded_keys_1_D
    by blast
  have "1 \<noteq> (0::'a)" by simp
  from assms(2) assms(3) assms(4) rl show ?thesis
  proof (induct k arbitrary: thesis s)
    case 0
    from this(2) show ?case by simp
  next
    case step: (Suc k)
    from assms(1) have "p \<noteq> 0" by (rule punit.binomial_not_0)
    hence "tc p \<noteq> 0" by (rule punit.tc_not_0)
    from assms(5) obtain u where t_eq: "t = u + tp p" by (metis addsE add.commute)
    show ?case
    proof (cases "k = 0")
      case True
      with step(2) have "associated p s (u + tp p) 1" unfolding t_eq One_nat_def by metis
      hence s_eq: "s = u + lp p" by (rule associated_1_plus_tp)
      let ?q = "monomial (1::'a) u"
      show ?thesis
      proof (rule step(5))
        show "keys (?q * p) = {s, t}"
          by (simp add: times_monomial_left punit.keys_monom_mult[OF \<open>1 \<noteq> 0\<close>] punit.keys_binomial[OF assms(1)] s_eq t_eq)
      qed
    next
      case False
      from step(2) have "associated p s t (k + 1)" by simp
      then obtain s' where a1: "associated p s' t k" and a2: "associated p s s' 1"
        by (rule associated_trans_rev)
      from \<open>\<not> punit.has_bounded_keys 1 p\<close> a1 False have "t \<prec> s'" by (rule associated_less)
      from a2 a1 step(4) assms(5) False have "lp p adds s'" by (rule associated_lp_adds_between')
      with a1 False obtain q' where keys_q': "keys (q' * p) = {s', t}" by (rule step(1))
      from step(4) obtain v where s_eq: "s = v + lp p" by (metis addsE add.commute)
      from a2 have s'_eq: "s' = v + tp p" unfolding s_eq by (rule associated_1_plus_lp)
      let ?c = "(- lc q' * lc p) / tc p"
      let ?q = "(monomial ?c v) + q'"
      show ?thesis
      proof (rule step(5), simp only: t_eq s_eq, rule keys_monomial_plus_times, fact, rule)
        assume "q' = 0"
        hence "q' * p = 0" by simp
        hence "keys (q' * p) = {}" by simp
        with \<open>keys (q' * p) = {s', t}\<close> show False by simp
      next
        from \<open>t \<prec> s'\<close> show "u \<prec> v" unfolding t_eq s'_eq by (rule ord_strict_canc)
      next
        from keys_q' show "keys (q' * p) = {v + tp p, u + tp p}" by (simp only: t_eq s'_eq)
      qed
    qed
  qed
qed

lemma associated_adds_obtains_cofactor_binomial_lc:
  assumes "punit.is_proper_binomial p" and "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k" and "k \<noteq> 0"
    and "lp p adds s" and "tp p adds t" and "c \<noteq> 0"
  obtains q d where "q * p = punit.binomial c s d t" and "punit.is_obd c s d t"
proof -
  from assms(1) have "punit.is_binomial p" by (rule punit.proper_binomial_imp_binomial)
  from this assms(2) assms(3) assms(4) assms(5) obtain q' where eq1: "keys (q' * p) = {s, t}"
    by (rule associated_adds_obtains_cofactor_keys)
  from assms(1) have "\<not> punit.has_bounded_keys 1 p"
    using punit.has_bounded_keys_1_D punit.proper_binomial_no_monomial punit.proper_binomial_not_0 by blast
  from this assms(2) assms(3) have "t \<prec> s" by (rule associated_less)
  hence "t \<noteq> s" by simp
  let ?p = "q' * p"
  define a where "a = lookup ?p s"
  define b where "b = lookup ?p t"
  have "a \<noteq> 0" and "b \<noteq> 0" by (simp_all add: a_def b_def eq1)
  with \<open>t \<noteq> s\<close> have "punit.is_pbd a s b t" by (simp add: punit.is_pbd_def)
  have eq: "?p = punit.binomial a s b t"
    by (rule poly_mapping_keys_eqI, simp only: eq1 punit.keys_binomial_pbd[OF \<open>punit.is_pbd a s b t\<close>], simp add: eq1, elim disjE,
          simp_all add: punit.lookup_binomial[OF \<open>punit.is_pbd a s b t\<close>], simp only: a_def, simp add: b_def \<open>t \<noteq> s\<close>)
  let ?c = "c / a"
  let ?d = "?c * b"
  let ?q = "punit.monom_mult ?c 0 q'"
  from \<open>a \<noteq> 0\<close> have "?c \<noteq> 0" using assms(6) by simp
  show ?thesis
  proof
    show "?q * p = punit.binomial c s ?d t"
      by (simp only: times_monomial_left[symmetric] ac_simps(4),
          simp add: times_monomial_left eq punit.monom_mult_binomial \<open>a \<noteq> 0\<close>)
  next
    show "punit.is_obd c s ?d t"
    proof (simp only: punit.is_obd_def, intro conjI, fact)
      from \<open>?c \<noteq> 0\<close> \<open>b \<noteq> 0\<close> show "?d \<noteq> 0" by simp
    qed fact
  qed
qed

lemma associated_adds_obtains_cofactor_binomial_tc:
  assumes "punit.is_proper_binomial p" and "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k" and "k \<noteq> 0"
    and "lp p adds s" and "tp p adds t" and "d \<noteq> 0"
  obtains q c where "q * p = punit.binomial c s d t" and "punit.is_obd c s d t"
proof -
  have "1 \<noteq> (0::'a)" by simp
  with assms(1) assms(2) assms(3) assms(4) assms(5) obtain q' d'
    where eq: "q' * p = punit.binomial 1 s d' t" and obd: "punit.is_obd 1 s d' t"
    by (rule associated_adds_obtains_cofactor_binomial_lc)
  let ?c = "d / d'"
  let ?q = "punit.monom_mult ?c 0 q'"
  from obd have "d' \<noteq> 0" by (simp add: punit.is_obd_def)
  with assms(6) have "?c \<noteq> 0" by simp
  show ?thesis
  proof
    show "?q * p = punit.binomial ?c s d t"
      by (simp only: times_monomial_left[symmetric] ac_simps(4),
          simp add: times_monomial_left eq punit.monom_mult_binomial \<open>d' \<noteq> 0\<close>)
  next
    show "punit.is_obd ?c s d t"
    proof (simp only: punit.is_obd_def, intro conjI, fact, fact)
      from obd show "t \<prec> s" by (simp add: punit.is_obd_def)
    qed
  qed
qed

subsection \<open>associated_poly\<close>
  
definition associated_poly :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_0) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "associated_poly p q \<longleftrightarrow>
    ((\<forall>s\<in>(keys q). \<forall>t\<in>(keys q). t \<prec> s \<longrightarrow> associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})) \<and>
    (\<forall>s\<in>(keys q). tp q \<prec> s \<longrightarrow> lookup q s * tc p + lc (punit.lower q s) * lc p = 0))"

lemma associated_polyD1:
  assumes "associated_poly p q" and "s \<in> keys q" and "t \<in> keys q" and "t \<prec> s"
  shows "associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})"
proof -
  from assms(1) have
    "\<forall>s\<in>(keys q). \<forall>t\<in>(keys q). t \<prec> s \<longrightarrow> associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})"
    unfolding associated_poly_def ..
  hence "\<forall>t\<in>(keys q). t \<prec> s \<longrightarrow> associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})" using assms(2) ..
  hence "t \<prec> s \<longrightarrow> associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})" using assms(3) ..
  thus ?thesis using assms(4) ..
qed
  
lemma associated_polyD1':
  assumes "associated_poly p q" and "s \<in> keys q" and "t \<in> keys q" and "t \<preceq> s"
  shows "associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})"
proof (cases "t \<prec> s")
  case True
  with assms(1) assms(2) assms(3) show ?thesis by (rule associated_polyD1)
next
  case False
  with assms(4) have "t = s" by simp
  hence "{u \<in> keys q. u \<prec> s \<and> t \<preceq> u} = {}" by auto
  have "card {u \<in> keys q. u \<prec> s \<and> t \<preceq> u} = 0" by (simp add: \<open>{u \<in> keys q. u \<prec> s \<and> t \<preceq> u} = {}\<close>) 
  thus ?thesis by (simp only: \<open>t = s\<close> associated_0)
qed

lemma associated_polyD2:
  assumes "associated_poly p q" and "s \<in> keys q" and "tp q \<prec> s"
  shows "lookup q s * tc p + lc (punit.lower q s) * lc p = 0"
proof -
  from assms(1) have "\<forall>s\<in>(keys q). tp q \<prec> s \<longrightarrow> lookup q s * tc p + lc (punit.lower q s) * lc p = 0"
    unfolding associated_poly_def ..
  hence "tp q \<prec> s \<longrightarrow> lookup q s * tc p + lc (punit.lower q s) * lc p = 0" using assms(2) ..
  thus ?thesis using assms(3) ..
qed

lemma associated_polyI:
  assumes "\<And>s t. s \<in> keys q \<Longrightarrow> t \<in> keys q \<Longrightarrow> t \<prec> s \<Longrightarrow> associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})"
    and "\<And>s. s \<in> keys q \<Longrightarrow> tp q \<prec> s \<Longrightarrow> lookup q s * tc p + lc (punit.lower q s) * lc p = 0"
  shows "associated_poly p q"
  unfolding associated_poly_def using assms by auto

lemma associated_poly_lower:
  assumes "associated_poly p q"
  shows "associated_poly p (punit.lower q v)"
proof (rule associated_polyI, simp_all add: punit.keys_lower)
  fix s t
  assume "s \<in> keys q \<and> s \<prec> v"
  hence "s \<in> keys q" and "s \<prec> v" by simp_all
  assume "t \<in> keys q \<and> t \<prec> v"
  hence "t \<in> keys q" ..
  assume "t \<prec> s"
  with assms \<open>s \<in> keys q\<close> \<open>t \<in> keys q\<close> have *: "associated p s t (card {u \<in> keys q. u \<prec> s \<and> t \<preceq> u})"
    by (rule associated_polyD1)
  from \<open>s \<prec> v\<close> have eq: "{u \<in> keys q. u \<prec> v \<and> u \<prec> s \<and> t \<preceq> u} = {u \<in> keys q. u \<prec> s \<and> t \<preceq> u}" by auto
  from * show "associated p s t (card {u \<in> keys q. u \<prec> v \<and> u \<prec> s \<and> t \<preceq> u})" by (simp add: eq)
next
  fix s
  assume "s \<in> keys q \<and> s \<prec> v"
  hence "s \<in> keys q" and "s \<prec> v" by simp_all
  from \<open>s \<in> keys q\<close> have "tp q \<preceq> s" by (rule punit.tt_min_keys)
  also have "... \<prec> v" by fact
  finally have "tp q \<prec> v" .
  assume "tp (punit.lower q v) \<prec> s"
  with \<open>tp q \<prec> v\<close> have "tp q \<prec> s" by (simp add: punit.tt_lower)
  with assms \<open>s \<in> keys q\<close> have *: "lookup q s * tc p + lc (punit.lower q s) * lc p = 0"
    by (rule associated_polyD2)
  from \<open>s \<prec> v\<close> have eq1: "lookup (punit.lower q v) s = lookup q s" by (simp add: punit.lookup_lower)
  from \<open>s \<prec> v\<close> have eq2: "lc (punit.lower (punit.lower q v) s) = lc (punit.lower q s)"
    by (simp add: punit.lower_lower ordered_powerprod_lin.min.absorb2)
  show "lookup (punit.lower q v) s * tc p + lc (punit.lower (punit.lower q v) s) * lc p = 0"
    unfolding eq1 eq2 by fact
qed

lemma associated_poly_higher:
  assumes "associated_poly p q"
  shows "associated_poly p (punit.higher q v)"
proof (rule associated_polyI, simp_all add: punit.keys_higher)
  fix s t
  assume "s \<in> keys q \<and> v \<prec> s"
  hence "s \<in> keys q" ..
  assume "t \<in> keys q \<and> v \<prec> t"
  hence "t \<in> keys q" and "v \<prec> t" by simp_all
  assume "t \<prec> s"
  with assms \<open>s \<in> keys q\<close> \<open>t \<in> keys q\<close> have *: "associated p s t (card {u \<in> keys q. u \<prec> s \<and> t \<preceq> u})"
    by (rule associated_polyD1)
  from \<open>v \<prec> t\<close> have eq: "{u \<in> keys q. v \<prec> u \<and> u \<prec> s \<and> t \<preceq> u} = {u \<in> keys q. u \<prec> s \<and> t \<preceq> u}" by auto
  from * show "associated p s t (card {u \<in> keys q. v \<prec> u \<and> u \<prec> s \<and> t \<preceq> u})" by (simp add: eq)
next
  fix s
  assume "s \<in> keys q \<and> v \<prec> s"
  hence "s \<in> keys q" and "v \<prec> s" by simp_all
  moreover from \<open>s \<in> keys q\<close> have "... \<preceq> lp q" by (rule punit.lt_max_keys)
  ultimately have "v \<prec> lp q" by simp
  hence "tp q \<preceq> tp (punit.higher q v)" by (rule punit.tt_higher)
  also assume "... \<prec> s"
  finally have "tp q \<prec> s" .
  with assms \<open>s \<in> keys q\<close> have *: "lookup q s * tc p + lc (punit.lower q s) * lc p = 0"
    by (rule associated_polyD2)
  from \<open>v \<prec> s\<close> have eq1: "lookup (punit.higher q v) s = lookup q s" by (simp add: punit.lookup_higher)
  have "punit.lower (punit.higher q v) s \<noteq> 0"
  proof (simp add: punit.lower_eq_zero_iff del: lookup_not_eq_zero_eq_in_keys, rule, rule conjI)
    have "tc (punit.higher q v) \<noteq> 0"
      by (rule punit.tc_not_0, auto simp: punit.higher_eq_zero_iff intro: \<open>s \<in> keys q\<close> \<open>v \<prec> s\<close>)
    thus "lookup (punit.higher q v) (tp (punit.higher q v)) \<noteq> 0" by (simp add: punit.tc_def)
  qed fact
  hence "keys (punit.lower (punit.higher q v) s) \<noteq> {}" by simp
  then obtain u where "u \<in> keys (punit.lower (punit.higher q v) s)" by blast
  hence "lookup (punit.lower (punit.higher q v) s) u \<noteq> 0" and "u \<prec> s" by (simp, simp add: punit.keys_lower)
  hence "lookup (punit.higher q v) u \<noteq> 0" by (simp add: punit.lookup_lower)
  have "v \<prec> lp (punit.lower q s)"
  proof (rule punit.lt_gr, rule)
    assume "lookup (punit.lower q s) u = 0"
    with \<open>u \<prec> s\<close> have "lookup q u = 0" by (simp add: punit.lookup_lower)
    hence "lookup (punit.higher q v) u = 0" by (simp add: punit.lookup_higher)
    with \<open>lookup (punit.higher q v) u \<noteq> 0\<close> show False ..
  next
    from \<open>lookup (punit.higher q v) u \<noteq> 0\<close> show "v \<prec> u" by (metis punit.lookup_higher)
  qed
  hence eq2: "lc (punit.lower (punit.higher q v) s) = lc (punit.lower q s)" by (rule punit.lc_lower_higher)
  show "lookup (punit.higher q v) s * tc p + lc (punit.lower (punit.higher q v) s) * lc p = 0"
    unfolding eq1 eq2 by fact
qed

lemma associated_poly_0: "associated_poly p 0"
  by (rule associated_polyI, simp_all)

lemma associated_poly_monomial':
  assumes "is_monomial q"
  shows "associated_poly p q"
proof -
  from assms have keys_q: "keys q = {lp q}" by (rule punit.keys_monomial)
  from assms have eq1: "tp q = lp q" by (simp add: punit.lt_eq_tt_monomial)
  have eq2: "{u. u = lp q \<and> u \<prec> lp q \<and> lp q \<preceq> u} = {}" by auto
  show ?thesis by (rule associated_polyI, simp_all add: keys_q eq1 eq2 associated_0)
qed

lemma associated_poly_monomial: "associated_poly p (monomial c t)"
proof (cases "c = 0")
  case True
  hence eq: "monomial c t = 0" by (rule monomial_0I)
  show ?thesis unfolding eq by (rule associated_poly_0)
next
  case False
  hence "is_monomial (monomial c t)" by (rule monomial_is_monomial)
  thus ?thesis by (rule associated_poly_monomial')
qed

lemma associated_poly_base:
  assumes "punit.has_bounded_keys 1 q"
  shows "associated_poly p q"
proof -
  from assms have "q = 0 \<or> is_monomial q" by (rule punit.has_bounded_keys_1_D)
  with associated_poly_0 associated_poly_monomial' show ?thesis by auto
qed

lemma associated_poly_recD1:
  assumes "\<not> punit.has_bounded_keys 1 q" and "associated_poly p q"
  shows "associated p (lp q) (lp (punit.tail q)) 1"
proof -
  let ?s = "lp q"
  let ?t = "lp (punit.tail q)"
  from assms(1) have "punit.tail q \<noteq> 0" using punit.tail_0D by auto
  hence "q \<noteq> 0" and "?t \<prec> ?s" by (auto, rule punit.lt_tail)
  note assms(2)
  moreover from \<open>q \<noteq> 0\<close> have "?s \<in> keys q" by (rule punit.lt_in_keys)
  moreover have "?t \<in> keys q"
  proof
    from \<open>punit.tail q \<noteq> 0\<close> show "?t \<in> keys (punit.tail q)" by (rule punit.lt_in_keys)
  next
    show "keys (punit.tail q) \<subseteq> keys q" unfolding punit.keys_tail by (rule Diff_subset)
  qed
  ultimately have "associated p ?s ?t (card {u\<in>(keys q). u \<prec> ?s \<and> ?t \<preceq> u})" using \<open>?t \<prec> ?s\<close>
    by (rule associated_polyD1)
  moreover have "{u\<in>(keys q). u \<prec> ?s \<and> ?t \<preceq> u} = {?t}"
  proof (rule set_eqI, simp)
    fix u
    show "(u \<in> keys q \<and> u \<prec> ?s \<and> ?t \<preceq> u) \<longleftrightarrow> (u = ?t)" (is "?L \<longleftrightarrow> ?R")
    proof
      assume ?L
      hence "u \<in> keys q" and "u \<prec> ?s" and "?t \<preceq> u" by simp_all
      from \<open>punit.tail q \<noteq> 0\<close> this(1) this(2) have "u \<preceq> ?t" by (rule punit.lt_tail_max)
      with \<open>?t \<preceq> u\<close> show ?R by simp
    next
      assume ?R
      from \<open>?t \<in> keys q\<close> \<open>?t \<prec> ?s\<close> show ?L unfolding \<open>?R\<close> by simp
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma associated_poly_recD2:
  assumes "\<not> punit.has_bounded_keys 1 q" and "associated_poly p q"
  shows "lc q * tc p + lc (punit.tail q) * lc p = 0"
proof -
  let ?s = "lp q"
  let ?t = "tp q"
  from assms(1) have "punit.tail q \<noteq> 0" using punit.tail_0D by auto
  hence "q \<noteq> 0" by auto
  hence "?s \<in> keys q" by (rule punit.lt_in_keys)
  from assms(1) have "?t \<prec> ?s" by (simp add: punit.lt_gr_tt_iff)
  with assms(2) \<open>?s \<in> keys q\<close> have "lookup q ?s * tc p + lc (punit.lower q ?s) * lc p = 0"
    by (rule associated_polyD2)
  thus ?thesis by (simp add: punit.tail_def punit.lc_def)
qed

lemma associated_poly_recD3:
  assumes "associated_poly p q"
  shows "associated_poly p (punit.tail q)"
  unfolding punit.tail_def using assms by (rule associated_poly_lower)

lemma associated_poly_recI:
  assumes "\<not> punit.has_bounded_keys 1 q" and "associated p (lp q) (lp (punit.tail q)) 1"
    and "lc q * tc p + lc (punit.tail q) * lc p = 0" and "associated_poly p (punit.tail q)"
  shows "associated_poly p q"
proof (rule associated_polyI)
  fix s t
  assume "s \<in> keys q" and "t \<in> keys q" and "t \<prec> s"
  show "associated p s t (card {u \<in> keys q. u \<prec> s \<and> t \<preceq> u})"
  proof (cases "s \<prec> lp q")
    case True
    with \<open>t \<prec> s\<close> have "t \<prec> lp q" by simp
    with True \<open>s \<in> keys q\<close> \<open>t \<in> keys q\<close> have "s \<in> keys (punit.tail q)" and "t \<in> keys (punit.tail q)"
      by (simp_all add: punit.keys_tail)
    from assms(4) this \<open>t \<prec> s\<close> have a: "associated p s t (card {u \<in> keys (punit.tail q). u \<prec> s \<and> t \<preceq> u})"
      by (rule associated_polyD1)
    {
      assume "lp q \<prec> s"
      with True have False by simp
    }
    hence eq: "{u \<in> keys (punit.tail q). u \<prec> s \<and> t \<preceq> u} = {u \<in> keys q. u \<prec> s \<and> t \<preceq> u}"
      by (auto simp add: punit.keys_tail)
    from a show ?thesis by (simp add: eq)
  next
    case False
    with punit.lt_max_keys[OF \<open>s \<in> keys q\<close>] have "s = lp q" by simp
    with \<open>t \<prec> s\<close> have "t \<prec> lp q" by simp
    with \<open>t \<in> keys q\<close> have "t \<in> keys (punit.tail q)" by (simp add: punit.keys_tail)
    hence "punit.tail q \<noteq> 0" by auto
    hence "lp (punit.tail q) \<in> keys (punit.tail q)" by (rule punit.lt_in_keys)
    from \<open>t \<in> keys (punit.tail q)\<close> have "t \<preceq> lp (punit.tail q)" by (rule punit.lt_max_keys)
    with assms(4) \<open>lp (punit.tail q) \<in> keys (punit.tail q)\<close> \<open>t \<in> keys (punit.tail q)\<close>
    have a: "associated p (lp (punit.tail q)) t (card {u \<in> keys (punit.tail q). u \<prec> lp (punit.tail q) \<and> t \<preceq> u})"
      by (rule associated_polyD1')
    have "\<And>x. x \<in> keys q \<Longrightarrow> x \<noteq> lp q \<Longrightarrow> x \<prec> lp q"
    proof -
      fix x
      assume "x \<in> keys q"
      hence "x \<preceq> lp q" by (rule punit.lt_max_keys)
      moreover assume "x \<noteq> lp q"
      ultimately show "x \<prec> lp q" by simp
    qed
    moreover have "\<And>x. x \<in> keys q \<Longrightarrow> x \<prec> lp q \<Longrightarrow> x \<noteq> lp (punit.tail q) \<Longrightarrow> x \<prec> lp (punit.tail q)"
    proof -
      fix x
      assume "x \<in> keys q" and "x \<prec> lp q"
      hence "x \<in> keys (punit.tail q)" by (simp add: punit.keys_tail)
      hence "x \<preceq> lp (punit.tail q)" by (rule punit.lt_max_keys)
      moreover assume "x \<noteq> lp (punit.tail q)"
      ultimately show "x \<prec> lp (punit.tail q)" by simp
    qed
    moreover have "lp (punit.tail q) \<in> {u \<in> keys q. u \<prec> s \<and> t \<preceq> u}" (is "_ \<in> ?A")
      by (simp add: \<open>s = lp q\<close>, intro conjI, rule, fact, auto simp add: punit.keys_tail, rule punit.lt_tail, fact, fact)
    ultimately have "... = insert (lp (punit.tail q)) {u \<in> keys (punit.tail q). u \<prec> lp (punit.tail q) \<and> t \<preceq> u}"
      (is "_ = insert _ ?B")
      by (auto simp add: punit.keys_tail \<open>s = lp q\<close>)
    moreover have "?B - {lp (punit.tail q)} = ?B" by simp
    moreover have "finite ?B" using finite_keys[of "punit.tail q"] by simp
    ultimately have eq: "card ?A = card ?B + 1" by (simp add: card_insert)
    from a show ?thesis unfolding eq
    proof (rule associated_trans)
      show "associated p s (lp (punit.tail q)) 1" unfolding \<open>s = lp q\<close> by (fact assms(2))
    qed
  qed
next
  fix s
  assume "s \<in> keys q" and "tp q \<prec> s"
  show "lookup q s * tc p + lc (punit.lower q s) * lc p = 0"
  proof (cases "s \<prec> lp q")
    case True
    from \<open>s \<in> keys q\<close> \<open>tp q \<prec> s\<close> have "tp q \<prec> lp q" by (rule punit.lt_gr_keys)
    note assms(4)
    moreover from \<open>s \<in> keys q\<close> True have "s \<in> keys (punit.tail q)" by (simp add: punit.keys_tail)
    moreover from \<open>tp q \<prec> s\<close> have "tp (punit.tail q) \<prec> s"
      by (simp add: punit.tail_def punit.tt_lower[OF \<open>tp q \<prec> lp q\<close>])
    ultimately have "lookup (punit.tail q) s * tc p + lc (punit.lower (punit.tail q) s) * lc p = 0"
      by (rule associated_polyD2)
    moreover from True have "ordered_powerprod_lin.min (lp q) s = s"
      unfolding ordered_powerprod_lin.min_def by auto
    ultimately show ?thesis using True by (simp add: punit.tail_def punit.lower_lower punit.lookup_lower)
  next
    case False
    with punit.lt_max_keys[OF \<open>s \<in> keys q\<close>] have "s = lp q" by simp
    from assms(3) show ?thesis by (simp add: \<open>s = lp q\<close> punit.lc_def punit.tail_def)
  qed
qed

lemma associated_poly_rec_iff:
  assumes "\<not> punit.has_bounded_keys 1 q"
  shows "associated_poly p q \<longleftrightarrow>
          (associated p (lp q) (lp (punit.tail q)) 1 \<and> lc q * tc p + lc (punit.tail q) * lc p = 0 \<and>
            associated_poly p (punit.tail q))"
  using assms associated_poly_recI associated_poly_recD1 associated_poly_recD2 associated_poly_recD3
  by auto

lemma associated_poly_associated_lp_tp:
  assumes "q \<noteq> 0" and "associated_poly p q"
  shows "associated p (lp q) (tp q) (card (keys q) - 1)"
proof -
  from assms(1) have 1: "lp q \<in> keys q" and 2: "tp q \<in> keys q"
    by (rule punit.lt_in_keys, rule punit.tt_in_keys)
  have 3: "tp q \<preceq> lp q" by (rule punit.lt_ge_tt)
  have eq: "card (keys q) - 1 = card {u\<in>(keys q). u \<prec> lp q \<and> tp q \<preceq> u}" (is "?l = card ?r")
  proof -
    have "?r = keys q - {lp q}"
    proof (rule set_eqI, simp)
      fix x
      show "(x \<in> keys q \<and> x \<prec> lp q \<and> tp q \<preceq> x) = (x \<in> keys q \<and> x \<noteq> lp q)" (is "?L = ?R")
      proof
        assume ?L
        hence "x \<in> keys q" and "x \<prec> lp q" by simp_all
        hence "x \<noteq> lp q" by simp
        with \<open>x \<in> keys q\<close> show ?R ..
      next
        assume ?R
        hence "x \<in> keys q" and "x \<noteq> lp q" by simp_all
        from \<open>x \<in> keys q\<close> have "lookup q x \<noteq> 0" by simp
        hence "x \<preceq> lp q" and "tp q \<preceq> x" by (rule punit.lt_max, rule punit.tt_min)
        from \<open>x \<preceq> lp q\<close> \<open>x \<noteq> lp q\<close> have "x \<prec> lp q" by simp
        from \<open>x \<in> keys q\<close> this \<open>tp q \<preceq> x\<close> show ?L by simp
      qed
    qed
    thus ?thesis using 1 finite_keys[of q] by simp
  qed
  from assms(2) 1 2 3 show ?thesis unfolding eq by (rule associated_polyD1')
qed

lemma associated_associated_poly:
  assumes "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k"
  obtains q where "q \<noteq> 0" and "lp q = s" and "tp q = t" and "associated_poly p q"
proof (cases "punit.has_bounded_keys 1 p")
  assume rl: "(\<And>q. q \<noteq> 0 \<Longrightarrow> lp q = s \<Longrightarrow> tp q = t \<Longrightarrow> associated_poly p q \<Longrightarrow> thesis)"
  assume "punit.has_bounded_keys 1 p"
  hence "s = t" using assms by (rule associated_has_bounded_keys_1)
  let ?q = "monomial (1::'a) t"
  show ?thesis
  proof (rule rl)
    show "?q \<noteq> 0"
    proof
      assume "?q = 0"
      hence "1 = (0::'a)" by (rule monomial_0D)
      thus False by simp
    qed
  next
    from \<open>s = t\<close> show "lp ?q = s" by (simp add: punit.lt_monomial)
  next
    show "tp ?q = t" by (rule punit.tt_monomial, simp)
  qed (rule associated_poly_monomial)
next
  assume rl: "(\<And>q. q \<noteq> 0 \<Longrightarrow> lp q = s \<Longrightarrow> tp q = t \<Longrightarrow> associated_poly p q \<Longrightarrow> thesis)"
  assume p_keys: "\<not> punit.has_bounded_keys 1 p"
  hence "p \<noteq> 0" using punit.has_bounded_keys_1_I2 by auto
  from assms rl show ?thesis
  proof (induct k arbitrary: thesis s)
    case base: 0
    from base(1) have "s = t" by (simp only: associated_0)
    let ?q = "monomial (1::'a) t"
    show ?case
    proof (rule base(2))
      show "?q \<noteq> 0"
      proof
        assume "?q = 0"
        hence "1 = (0::'a)" by (rule monomial_0D)
        thus False by simp
      qed
    next
      from \<open>s = t\<close> show "lp ?q = s" by (simp add: punit.lt_monomial)
    next
      show "tp ?q = t" by (rule punit.tt_monomial, simp)
    qed (rule associated_poly_monomial)
  next
    case step: (Suc k)
    from step(2) have "associated p s t (k + 1)" by simp
    then obtain s' where a1: "associated p s' t k" and a2: "associated p s s' 1"
      by (rule associated_trans_rev)
    from a1 obtain q' where "q' \<noteq> 0" and "lp q' = s'" and "tp q' = t" and "associated_poly p q'"
      by (rule step(1))
    from \<open>p \<noteq> 0\<close> have "tc p \<noteq> 0" by (rule punit.tc_not_0)
    let ?c = "(- lc q' * lc p) / tc p"
    let ?q = "(monomial ?c s) + q'"
    from punit.lc_not_0[OF \<open>p \<noteq> 0\<close>] punit.lc_not_0[OF \<open>q' \<noteq> 0\<close>] \<open>tc p \<noteq> 0\<close> have "?c \<noteq> 0" by simp
    from p_keys a2 have "lp q' \<prec> s" by (simp only: \<open>lp q' = s'\<close>, rule associated_less, simp)
    from \<open>?c \<noteq> 0\<close> \<open>lp q' \<prec> s\<close> have "?q \<noteq> 0" and lp_q: "lp ?q = s" and lc_q: "lc ?q = ?c"
      and tail_q: "punit.tail ?q = q'"
      by (rule punit.monomial_plus_not_0, rule punit.lt_monomial_plus[simplified],
          rule punit.lc_monomial_plus[simplified], rule punit.tail_monomial_plus)
    show ?case
    proof (rule step(3))
      from \<open>q' \<noteq> 0\<close> \<open>lp q' \<prec> s\<close> show "tp ?q = t" by (simp only: \<open>tp q' = t\<close>[symmetric], rule punit.tt_monomial_plus)
    next
      show "associated_poly p ?q"
      proof (rule associated_poly_recI,
            simp_all only: lp_q lc_q tail_q \<open>lp q' = s'\<close> punit.tail_eq_0_iff_has_bounded_keys_1[symmetric])
        from \<open>tc p \<noteq> 0\<close> show "?c * tc p + lc q' * lc p = 0" by (simp add: field_simps)
      qed fact+
    qed fact+
  qed
qed

(* Removed one redundant assumption. *)
lemma associated_poly_times_binomial_associated:
  assumes "q \<noteq> 0" and "associated_poly p q"
  shows "associated p (lp q + lp p) (tp q + tp p) (card (keys q))"
proof -
  from keys_eq_empty_iff[of q] assms(1) have "keys q \<noteq> {}" by auto
  with finite_keys[of q] have "card (keys q) \<noteq> 0" by simp
  hence eq: "associated p (lp q + lp p) (tp q + tp p) (card (keys q)) \<longleftrightarrow>
              associated p (lp q + lp p) (tp q + tp p) ((card (keys q) - 1) + 1)" by force
  show ?thesis unfolding eq
  proof (rule associated_plus, rule associated_poly_associated_lp_tp, fact assms(1), fact assms(2))
    show "associated p (lp p) (tp p) 1" unfolding associated_1 by (simp add: add.commute)
  qed
qed

lemma associated_poly_times_binomial_keys:
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)" and "q \<noteq> 0"
    and "associated_poly p q"
  shows "keys (q * p) = {lp q + lp p, tp q + tp p}"
  using assms(2) assms(3)
proof (induct q rule: punit.poly_mapping_tail_induct)
  case 0
  thus ?case by simp
next
  case step: (tail q)
  let ?m = "punit.monom_mult (lc q) (lp q) p"
  let ?q = "punit.tail q"
  let ?A = "{lp q + lp p, tp q + tp p}"
  from assms(1) have "punit.is_binomial p" and "p \<noteq> 0"
    by (rule punit.proper_binomial_imp_binomial, rule punit.proper_binomial_not_0)
  moreover from \<open>q \<noteq> 0\<close> have "lc q \<noteq> 0" by (rule punit.lc_not_0)
  ultimately have keys_m: "keys ?m = {lp q + lp p, lp q + tp p}"
    by (simp add: punit.keys_binomial punit.keys_monom_mult)
  show ?case
  proof (cases "punit.has_bounded_keys 1 q")
    case True
    hence "q = 0 \<or> is_monomial q" by (rule punit.has_bounded_keys_1_D)
    with \<open>q \<noteq> 0\<close> have "is_monomial q" by simp
    hence "punit.tail q = 0" using is_monomial_monomial punit.tail_monomial by metis
    from \<open>is_monomial q\<close> have "tp q = lp q" by (simp add: punit.lt_eq_tt_monomial)
    from keys_m show ?thesis
      by (simp add: times_tail_rec_left[of q p] \<open>punit.tail q = 0\<close> \<open>tp q = lp q\<close> plus_fun_def)
  next
    case False
    hence "?q \<noteq> 0" using punit.tail_0D by blast
    from step(4) have assoc_tail: "associated_poly p ?q" by (rule associated_poly_recD3)
    from associated_poly_recD1[OF False step(4)] have eq1: "lp q + tp p = lp ?q + lp p"
      by (simp only: associated_1)
    from \<open>?q \<noteq> 0\<close> assoc_tail have eq2: "keys (?q * p) = {lp ?q + lp p, tp ?q + tp p}" by (rule step(2))
    from associated_poly_recD2[OF False step(4)]
      have eq3: "lookup ?m (lp q + tp p) + lookup (?q * p) (lp ?q + lp p) = 0"
        by (simp add: punit.lookup_monom_mult lookup_times_lp_lp punit.tc_def)
    from False have "tp q \<prec> lp q" by (simp add: punit.lt_gr_tt_iff)
    hence tp_tail: "tp (punit.tail q) = tp q" by (simp only: punit.tail_def, rule punit.tt_lower)
    show ?thesis unfolding times_tail_rec_left[of q p]
    proof
      have "keys (?m + ?q * p) \<subseteq> keys ?m \<union> keys (?q * p)" by (rule keys_add_subset)
      also have "... = {lp q + lp p, lp ?q + lp p, tp ?q + tp p}" by (auto simp only: keys_m eq2 eq1)
      finally have "keys (?m + ?q * p) \<subseteq> {lp q + lp p, lp ?q + lp p, tp ?q + tp p}" .
      moreover from eq3 have "lp ?q + lp p \<notin> keys (?m + ?q * p)" by (simp add: lookup_add eq1)
      ultimately show "keys (?m + ?q * p) \<subseteq> ?A" by (auto simp only: tp_tail)
    next
      show "?A \<subseteq> keys (?m + ?q * p)"
      proof (rule, simp, elim disjE, simp_all)
        show "lp q + lp p \<in> keys (?m + ?q * p)"
        proof (rule in_keys_plusI1,
              simp add: in_keys_iff punit.lookup_monom_mult \<open>lc q \<noteq> 0\<close> del: lookup_not_eq_zero_eq_in_keys)
          from \<open>p \<noteq> 0\<close> have "lc p \<noteq> 0" by (rule punit.lc_not_0)
          thus "lookup p (lp p) \<noteq> 0" by (simp add: punit.lc_def)
        next
          show "lp q + lp p \<notin> keys (?q * p)"
          proof
            assume "lp q + lp p \<in> keys (?q * p)"
            hence "lp q + lp p \<preceq> lp ?q + lp p" by (rule in_keys_times_le)
            hence "lp q \<preceq> lp ?q" by (rule ord_canc)
            also from \<open>?q \<noteq> 0\<close> have "lp ?q \<prec> lp q" by (rule punit.lt_tail)
            finally show False ..
          qed
        qed
      next
        show "tp q + tp p \<in> keys (?m + ?q * p)"
        proof (rule in_keys_plusI2, simp only: in_keys_iff tp_tail[symmetric] lookup_times_tp_tp)
          from \<open>?q \<noteq> 0\<close> have "tc ?q \<noteq> 0" by (rule punit.tc_not_0)
          moreover from \<open>p \<noteq> 0\<close> have "tc p \<noteq> 0" by (rule punit.tc_not_0)
          ultimately show "tc ?q * tc p \<noteq> 0" by simp
        next
          show "tp q + tp p \<notin> keys ?m"
          proof
            assume "tp q + tp p \<in> keys ?m"
            thm punit.in_keys_monom_mult_ge
            hence "lp q + tp p \<preceq> tp q + tp p" by (rule punit_in_keys_monom_mult_ge)
            hence "lp q \<preceq> tp q" by (rule ord_canc)
            with \<open>tp q \<prec> lp q\<close> show False by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma times_binomial_keys_associated_poly:
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
    and "keys (q * p) = {lp q + lp p, tp q + tp p}"
  shows "associated_poly p q"
  using assms(2)
proof (induct q rule: punit.poly_mapping_tail_induct)
  case 0
  hence "{lp 0 + lp p, tp 0 + tp p} = {}" by simp
  thus ?case by simp
next
  case step: (tail q)
  from step(1) have "lc q \<noteq> 0" and "tc q \<noteq> 0" by (rule punit.lc_not_0, rule punit.tc_not_0)
  show ?case
  proof (cases "punit.has_bounded_keys 1 q")
    case True
    with step(1) have "is_monomial q" using punit.has_bounded_keys_1_D by blast
    then obtain c t where "q = monomial c t" by (rule is_monomial_monomial)
    show ?thesis by (simp only: \<open>q = monomial c t\<close>, rule associated_poly_monomial)
  next
    case False
    with step(1) have "punit.tail q \<noteq> 0" using punit.tail_0D by blast
    hence tp_tail_q: "tp (punit.tail q) = tp q" by (rule punit.tt_tail)
    from False have "tp q \<prec> lp q" by (simp add: punit.lt_gr_tt_iff)
    hence "tp q + tp p \<prec> lp q + tp p" by (simp only: plus_monotone_strict)
    from assms(1) have "p \<noteq> 0" and keys_p: "keys p = {lp p, tp p}" and "tp p \<prec> lp p"
      by (rule punit.proper_binomial_not_0, rule punit.keys_proper_binomial, rule punit.lt_gr_tt_binomial)
    from \<open>p \<noteq> 0\<close> have "tc p \<noteq> 0" by (rule punit.tc_not_0)
    from \<open>punit.tail q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have "tp (punit.tail q * p) = tp (punit.tail q) + tp p" by (rule tp_times)
    also have "... = tp q + tp p" by (simp only: tp_tail_q)
    finally have tp_tail_times: "tp (punit.tail q * p) = tp q + tp p" .
    from assms(1) have tail_p: "punit.tail p = monomial (tc p) (tp p)"
      by (metis Poly_Utils.punit.binomial_def \<open>p \<noteq> 0\<close> \<open>tc p \<noteq> 0\<close> \<open>tp p \<prec> lp p\<close> punit.binomial_eq_itself
          punit.lc_not_0 punit.lt_monomial punit.tail_monomial_plus)
    let ?m = "punit.monom_mult (lc q) (lp q) p"
    let ?r = "punit.tail q * p"
    from \<open>lc q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have lp_m: "lp ?m = lp q + lp p" and tp_m: "tp ?m = lp q + tp p"
      by (rule lp_monom_mult, rule tp_monom_mult)
    have "punit.tail ?m = punit.monom_mult (lc q) (lp q) (punit.tail p)" by (rule punit.tail_monom_mult)
    also have "... = punit.monom_mult (lc q) (lp q) (monomial (tc p) (tp p))" by (simp only: tail_p)
    also have "... = monomial (lc q * tc p) (lp q + tp p)" by (rule punit_monom_mult_monomial)
    finally have tail_m: "punit.tail ?m = monomial (lc q * tc p) (lp q + tp p)" .
    from \<open>punit.tail q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have lp_r: "lp ?r = lp (punit.tail q) + lp p" and tp_r: "tp ?r = tp q + tp p"
      by (rule lp_times, simp add: tp_times tp_tail_q)
    from punit.tc_tail[OF \<open>punit.tail q \<noteq> 0\<close>] have tc_r: "tc ?r = tc q * tc p" by (simp add: tc_times)
    from step(3) have "keys (?m + ?r) = {lp ?m, tp ?r}"
      by (simp only: times_tail_rec_left[of q] tp_tail_times lp_monom_mult[OF \<open>lc q \<noteq> 0\<close> \<open>p \<noteq> 0\<close>])
    hence "punit.tail ?m + punit.higher ?r (tp ?r) = 0"
    proof (rule punit.keys_plus_eq_lt_tt_D, simp_all only: lp_r lp_m tp_r tp_m)
      from \<open>punit.tail q \<noteq> 0\<close> have "lp (punit.tail q) \<prec> lp q" by (rule punit.lt_tail)
      thus "lp (punit.tail q) + lp p \<prec> lp q + lp p" by (simp add: plus_monotone_strict)
    next
      show "tp q + tp p \<prec> lp q + tp p" by fact
    qed
    hence eq1: "monomial (lc q * tc p) (lp q + tp p) + punit.higher ?r (tp ?r) = 0" by (simp only: tail_m)
    define c where "c = lookup (punit.higher ?r (tp ?r)) (lp q + tp p)"
    have higher_r: "punit.higher ?r (tp ?r) = monomial c (lp q + tp p)"
    proof (rule poly_mapping_eqI, simp add: lookup_single Poly_Mapping.when_def, intro conjI impI, simp only: c_def)
      fix t
      assume a: "lp q + tp p \<noteq> t"
      from eq1 have "0 = lookup (monomial (lc q * tc p) (lp q + tp p) + (punit.higher ?r (tp ?r))) t"
        by (simp only: lookup_zero)
      also from a have "... = lookup (punit.higher ?r (tp ?r)) t" by (simp add: lookup_add lookup_single)
      finally show "lookup (punit.higher ?r (tp ?r)) t = 0" by simp
    qed
    from eq1 have "0 = lookup (monomial (lc q * tc p) (lp q + tp p) + (punit.higher ?r (tp ?r))) (lp q + tp p)"
      by (simp only: lookup_zero)
    also have "... = lc q * tc p + c" by (simp add: lookup_add lookup_single c_def)
    finally have c: "lc q * tc p + c = 0" by simp
    from \<open>punit.tail q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have "?r \<noteq> 0" by (rule times_not_zero)
    from punit.trailing_monomial_higher[OF this] higher_r
    have r_eq: "?r = punit.binomial c (lp q + tp p) (tc q * tc p) (tp q + tp p)"
      by (simp add: tp_r tc_r punit.binomial_def)
    have obd: "punit.is_obd c (lp q + tp p) (tc q * tc p) (tp q + tp p)"
    proof (simp only: punit.is_obd_def, intro conjI, rule)
      assume "c = 0"
      with c have "lc q * tc p = 0" by simp
      with \<open>lc q \<noteq> 0\<close> \<open>tc p \<noteq> 0\<close> show False by simp
    next
      from \<open>tc q \<noteq> 0\<close> \<open>tc p \<noteq> 0\<close> show "tc q * tc p \<noteq> 0" by simp
    qed fact
    from lp_r obd have lp_tp: "lp q + tp p = lp (punit.tail q) + lp p" by (simp only: r_eq punit.lt_binomial)
    show ?thesis
    proof (rule associated_poly_recI, fact False, simp only: associated_1 lp_tp)
      from lc_times[of "punit.tail q" p] obd c show "lc q * tc p + lc (punit.tail q) * lc p = 0"
        by (simp only: r_eq punit.lc_binomial)
    next
      show "associated_poly p (punit.tail q)"
      proof (rule step(2))
        from obd have "punit.is_pbd c (lp q + tp p) (tc q * tc p) (tp q + tp p)" by (rule punit.obd_imp_pbd)
        from punit.keys_binomial_pbd[OF this] show "keys ?r = {lp (punit.tail q) + lp p, tp (punit.tail q) + tp p}"
          by (simp only: r_eq tp_tail_q lp_tp)
      qed
    qed
  qed
qed

subsection \<open>Multiplication by Binomials\<close>

lemma lookup_times_binomial_1:
  assumes "punit.is_proper_binomial p" and "u + tp p = v + lp p"
  shows "lookup (q * p) (v + lp p) = lookup q v * lc p + lookup q u * tc p"
proof -
  from assms(1) obtain c d s t where obd: "punit.is_obd c s d t" and p_eq: "p = punit.binomial c s d t"
    by (rule punit.is_proper_binomial_binomial_od)
  from obd have lp_p: "lp p = s" and lc_p: "lc p = c" and tp_p: "tp p = t" and tc_p: "tc p = d"
    unfolding p_eq  by (rule punit.lt_binomial, rule punit.lc_binomial, rule punit.tt_binomial, rule punit.tc_binomial)
  have eq1: "q * p = q * monomial c s + q * monomial d t"
    by (simp add: p_eq punit.binomial_def algebra_simps)
  have eq2: "lookup (q * monomial d t) (v + lp p) = lookup q u * d"
    by (simp add: assms(2)[symmetric] tp_p lookup_times_monomial_right)
  show ?thesis unfolding eq1 lookup_add eq2 by (simp add: lp_p lc_p tp_p tc_p lookup_times_monomial_right)
qed

lemma lookup_times_binomial_2:
  assumes "punit.is_proper_binomial p" and "\<not>(\<exists>u\<in>(keys q). u + tp p = v + lp p)"
  shows "lookup (q * p) (v + lp p) = lookup q v * lc p"
proof (cases "\<exists>u. u + tp p = v + lp p")
  case True
  then obtain u where u: "u + tp p = v + lp p" ..
  with assms(1) have eq: "lookup (q * p) (v + lp p) = lookup q v * lc p + lookup q u * tc p"
    by (rule lookup_times_binomial_1)
  have "u \<notin> keys q"
  proof
    assume "u \<in> keys q"
    with u have "\<exists>u\<in>(keys q). u + tp p = v + lp p" ..
    with assms(2) show False ..
  qed
  hence "lookup q u = 0" by simp
  thus ?thesis unfolding eq by simp
next
  case False
  from assms(1) obtain c d s t where obd: "punit.is_obd c s d t" and p_eq: "p = punit.binomial c s d t"
    by (rule punit.is_proper_binomial_binomial_od)
  from obd have lp_p: "lp p = s" and lc_p: "lc p = c" and tp_p: "tp p = t" and tc_p: "tc p = d"
    unfolding p_eq  by (rule punit.lt_binomial, rule punit.lc_binomial, rule punit.tt_binomial, rule punit.tc_binomial)
  have eq1: "q * p = q * monomial c s + q * monomial d t"
    by (simp add: p_eq punit.binomial_def algebra_simps)
  have "\<not> tp p adds v + lp p"
  proof
    assume "tp p adds v + lp p"
    then obtain u where u: "v + lp p = tp p + u" unfolding adds_def ..
    from False have "\<forall>u. u + tp p \<noteq> v + lp p" by simp
    hence "u + tp p \<noteq> v + lp p" ..
    with u show False by (simp add: ac_simps)
  qed
  hence eq2: "lookup (q * monomial d t) (v + lp p) = 0" by (simp add: lp_p tp_p lookup_times_monomial_right)
  show ?thesis unfolding eq1 lookup_add eq2 by (simp add: lp_p lc_p tp_p tc_p lookup_times_monomial_right)
qed

lemma lookup_times_binomial_3:
  assumes "punit.is_proper_binomial p" and "\<not>(\<exists>v\<in>(keys q). v + lp p = u + tp p)"
  shows "lookup (q * p) (u + tp p) = lookup q u * tc p"
proof (cases "\<exists>v. v + lp p = u + tp p")
  case True
  then obtain v where v: "v + lp p = u + tp p" ..
  hence u: "u + tp p = v + lp p" by simp
  with assms(1) have eq: "lookup (q * p) (v + lp p) = lookup q v * lc p + lookup q u * tc p"
    by (rule lookup_times_binomial_1)
  have "v \<notin> keys q"
  proof
    assume "v \<in> keys q"
    with v have "\<exists>v\<in>(keys q). v + lp p = u + tp p" ..
    with assms(2) show False ..
  qed
  hence "lookup q v = 0" by simp
  thus ?thesis unfolding u eq by simp
next
  case False
  from assms(1) obtain c d s t where obd: "punit.is_obd c s d t" and p_eq: "p = punit.binomial c s d t"
    by (rule punit.is_proper_binomial_binomial_od)
  from obd have lp_p: "lp p = s" and lc_p: "lc p = c" and tp_p: "tp p = t" and tc_p: "tc p = d"
    unfolding p_eq  by (rule punit.lt_binomial, rule punit.lc_binomial, rule punit.tt_binomial, rule punit.tc_binomial)
  have eq1: "q * p = q * monomial c s + q * monomial d t"
    by (simp add: p_eq punit.binomial_def algebra_simps)
  have "\<not> lp p adds u + tp p"
  proof
    assume "lp p adds u + tp p"
    then obtain v where v: "u + tp p = lp p + v" unfolding adds_def ..
    from False have "\<forall>v. v + lp p \<noteq> u + tp p" by simp
    hence "v + lp p \<noteq> u + tp p" ..
    with v show False by (simp add: ac_simps)
  qed
  hence eq2: "lookup (q * monomial c s) (u + tp p) = 0" by (simp add: lp_p tp_p lookup_times_monomial_right)
  show ?thesis unfolding eq1 lookup_add eq2 by (simp add: lp_p lc_p tp_p tc_p lookup_times_monomial_right)
qed

lemma times_binomial_lp_not_in_keys:
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + lp p \<notin> keys (q * p)"
  obtains v' where "v' \<in> keys q" and "v \<prec> v'" and "v' + tp p = v + lp p" and "lookup q v' * tc p = -(lookup q v * lc p)"
proof (cases "\<exists>v'\<in>(keys q). v' + tp p = v + lp p")
  case True
  then obtain v' where "v' \<in> keys q" and v': "v' + tp p = v + lp p" ..
  from \<open>v' \<in> keys q\<close> _ v' show ?thesis
  proof
    from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
    hence "v + tp p \<prec> v + lp p" by (rule plus_monotone_strict_left)
    also have "... = v' + tp p" by (simp only: v')
    finally show "v \<prec> v'" by (rule ord_strict_canc)
  next
    from assms(1) v' have "lookup (q * p) (v + lp p) = lookup q v * lc p + lookup q v' * tc p"
      by (rule lookup_times_binomial_1)
    moreover from assms(3) have "lookup (q * p) (v + lp p) = 0" by simp
    ultimately show "lookup q v' * tc p = - (lookup q v * lc p)" by (simp add: add_eq_0_iff) 
  qed
next
  case False
  with assms(1) have "lookup (q * p) (v + lp p) = lookup q v * lc p" by (rule lookup_times_binomial_2)
  moreover from assms(3) have "lookup (q * p) (v + lp p) = 0" by simp
  ultimately have "lookup q v * lc p = 0" by simp
  hence "lookup q v = 0 \<or> lc p = 0" by simp
  thus ?thesis
  proof
    assume "lookup q v = 0"
    hence "v \<notin> keys q" by simp
    from this assms(2) show ?thesis ..
  next
    assume "lc p = 0"
    from assms(1) have "p \<noteq> 0" by (rule punit.proper_binomial_not_0)
    hence "lc p \<noteq> 0" by (rule punit.lc_not_0)
    from this \<open>lc p = 0\<close> show ?thesis ..
  qed
qed

lemma times_binomial_tp_not_in_keys:
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + tp p \<notin> keys (q * p)"
  obtains v' where "v' \<in> keys q" and "v' \<prec> v" and "v' + lp p = v + tp p" and "lookup q v' * lc p = -(lookup q v * tc p)"
proof (cases "\<exists>v'\<in>(keys q). v' + lp p = v + tp p")
  case True
  then obtain v' where "v' \<in> keys q" and v': "v' + lp p = v + tp p" ..
  from \<open>v' \<in> keys q\<close> _ v' show ?thesis
  proof
    from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
    hence "v' + tp p \<prec> v' + lp p" by (rule plus_monotone_strict_left)
    also have "... = v + tp p" by (simp only: v')
    finally show "v' \<prec> v" by (rule ord_strict_canc)
  next
    from assms(1) v'[symmetric] have "lookup (q * p) (v' + lp p) = lookup q v' * lc p + lookup q v * tc p"
      by (rule lookup_times_binomial_1)
    moreover from assms(3) have "lookup (q * p) (v' + lp p) = 0" by (simp add: v'[symmetric])
    ultimately show "lookup q v' * lc p = - (lookup q v * tc p)" by (simp add: add_eq_0_iff) 
  qed
next
  case False
  with assms(1) have "lookup (q * p) (v + tp p) = lookup q v * tc p" by (rule lookup_times_binomial_3)
  moreover from assms(3) have "lookup (q * p) (v + tp p) = 0" by simp
  ultimately have "lookup q v * tc p = 0" by simp
  hence "lookup q v = 0 \<or> tc p = 0" by simp
  thus ?thesis
  proof
    assume "lookup q v = 0"
    hence "v \<notin> keys q" by simp
    from this assms(2) show ?thesis ..
  next
    assume "tc p = 0"
    from assms(1) have "p \<noteq> 0" by (rule punit.proper_binomial_not_0)
    hence "tc p \<noteq> 0" by (rule punit.tc_not_0)
    from this \<open>tc p = 0\<close> show ?thesis ..
  qed
qed

lemma binomial_mult_shape_lp':
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + lp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "punit.subpoly q' q" and "lp q' = v" and "associated_poly p q'" and "tp q' + tp p \<in> keys (q * p)"
  using assms(2) assms(3)
proof (induct q arbitrary: thesis v rule: poly_mapping_except_induct')
  case step: (1 q)
  from \<open>punit.is_proper_binomial p\<close> have "p \<noteq> 0" by (rule punit.proper_binomial_not_0)
  let ?c = "lookup q v"
  from \<open>v \<in> keys q\<close> have "?c \<noteq> 0" by simp
  have q_rec: "q = monomial ?c v + except q {v}" (is "q = ?m + ?q") by (rule plus_except)
  hence "q * p = (?m + ?q) * p" by simp
  also have "... = ?m * p + ?q * p" by (rule algebra_simps(17))
  also have "... = punit.monom_mult ?c v p + ?q * p" by (simp only: times_monomial_left)
  finally have qp_eq: "q * p = punit.monom_mult ?c v p + ?q * p" (is "_ = ?p + ?q * p") .
  have keys_m: "keys ?m = {v}" unfolding keys_of_monomial[OF \<open>?c \<noteq> 0\<close>] ..
  from \<open>?c \<noteq> 0\<close> have "?m \<noteq> 0" and lp_m: "lp ?m = v" and tp_m: "tp ?m = v"
    by (meson monomial_0D, rule punit.lt_monomial, rule punit.tt_monomial)
  let ?t = "v + tp p"
  let ?s = "v + lp p"
  from \<open>punit.is_proper_binomial p\<close> have keys_p: "keys p = {lp p, tp p}" by (rule punit.keys_proper_binomial)
  hence "keys ?p = {?s, ?t}" unfolding punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>, of v p] by simp
  hence "?t \<in> keys ?p" by simp
  show ?case
  proof (cases "?t \<in> keys (q * p)")
    case True
    show ?thesis by (rule step(2), fact \<open>?m \<noteq> 0\<close>, rule punit.monomial_subpoly, simp only: lp_m,
                      rule associated_poly_monomial, simp only: tp_m True)
  next
    case False
    with \<open>punit.is_proper_binomial p\<close> \<open>v \<in> keys q\<close> obtain v' where "v' \<in> keys q" and "v' \<prec> v"
      and *: "v' + lp p = ?t" and **: "lookup q v' * lc p = -(?c * tc p)"
      by (rule times_binomial_tp_not_in_keys)
    from in_keys_plusI1[OF \<open>?t \<in> keys ?p\<close>, of "except q {v} * p"] False
      have "?t \<in> keys (?q * p)" unfolding qp_eq by blast
    from \<open>v' \<prec> v\<close> have "v' \<noteq> v" by simp
    with \<open>v' \<in> keys q\<close> have "v' \<in> keys ?q" by (simp add: keys_except)
    
    text \<open>Obtaining some @{term q'} from the induction hypothesis:\<close>
    from step(3) _ \<open>v' \<in> keys ?q\<close> \<open>?t \<in> keys (?q * p)\<close> obtain q'
      where "q' \<noteq> 0" and "punit.subpoly q' ?q" and "lp q' = v'" and assoc: "associated_poly p q'"
      and "tp q' + tp p \<in> keys (?q * p)"
      unfolding \<open>v' + lp p = ?t\<close>[symmetric] by (rule step(1))
    from \<open>q' \<noteq> 0\<close> have "v' \<in> keys q'" unfolding \<open>lp q' = v'\<close>[symmetric] by (rule punit.lt_in_keys)
    have "punit.subpoly q' q" by (rule punit.subpoly_trans, fact, rule punit.except_subpoly)
    from * \<open>lp q' = v'\<close> have ***: "lp q' + lp p = v + tp p" by simp
    
    let ?q' = "?m + q'"
    
    text \<open>Properties of @{term ?q'}:\<close>
    have "v \<notin> keys ?q" by (simp add: keys_except)
    hence "v \<notin> keys q'" using punit.subpoly_keys[OF \<open>punit.subpoly q' ?q\<close>] by auto
    hence "keys ?m \<inter> keys q' = {}" and "lookup q' v = 0" by (simp add: keys_m, simp)
    from this(1) have keys_q': "keys ?q' = {v} \<union> keys q'" unfolding keys_m[symmetric] by (rule keys_plus_eqI)
    have tp_q': "tp ?q' = tp q'"
    proof (simp only: add.commute, rule punit.tt_plus_eqI, fact, simp only: tp_m)
      have "tp q' \<preceq> lp q'" by (rule punit.lt_ge_tt)
      also from \<open>v' \<prec> v\<close> have "... \<prec> v" by (simp only: \<open>lp q' = v'\<close>)
      finally show "tp q' \<prec> v" .
    qed
    have "lp (q' + ?m) = lp ?m" by (rule punit.lt_plus_eqI, simp only: lp_m \<open>lp q' = v'\<close> \<open>v' \<prec> v\<close>)
    hence lp_q': "lp ?q' = v" by (simp only: add.commute lp_m)
    have lc_q': "lc ?q' = ?c" by (simp add: punit.lc_def lp_q' lookup_add lookup_single, fact)
    have tail_q': "punit.tail ?q' = q'"
      by (rule poly_mapping_eqI, simp add: punit.lookup_tail_2 lp_q' lookup_add lookup_single \<open>lookup q' v = 0\<close>)
    have "?q' \<noteq> 0"
    proof
      assume "?q' = 0"
      hence "keys ?q' = {}" by simp
      with keys_q' show False by simp
    qed

    show ?thesis
    proof (rule step(2), fact \<open>?q' \<noteq> 0\<close>, rule punit.plus_subpolyI, rule punit.monomial_subpoly, fact, fact, fact)
      show "associated_poly p ?q'"
      proof (rule associated_poly_recI, simp_all only: tail_q' lp_q' lc_q',
              simp only: punit.has_bounded_keys_def keys_q')
        from \<open>v' \<in> keys q'\<close> have "keys q' \<noteq> {}" by auto
        with finite_keys[of q'] have "card (keys q') > 0" by (simp add: card_gt_0_iff)
        with \<open>v \<notin> keys q'\<close> have "card ({v} \<union> keys q') > 1" by simp
        thus "\<not> card ({v} \<union> keys q') \<le> 1" by simp
      next
        from *** show "associated p v (lp q') 1" by (simp only: associated_1)
      next
        from punit.subpolyE[OF \<open>punit.subpoly q' q\<close> \<open>v' \<in> keys q'\<close>] have "lc q' = lookup q v'"
          by (simp add: punit.lc_def \<open>lp q' = v'\<close>)
        with ** show "lookup q v * tc p + lc q' * lc p = 0" by simp
      qed fact
    next
      have eq: "q * p = ?q * p + punit.monom_mult ?c v p" unfolding qp_eq by simp
      from \<open>q' \<noteq> 0\<close> assoc have "associated p (lp q' + lp p) (tp q' + tp p) (card (keys q'))"
        by (rule associated_poly_times_binomial_associated)
      hence "associated p ?t (tp q' + tp p) (card (keys q'))" by (simp only: ***)
      with assms(1) have "tp ?q' + tp p \<notin> keys ?p" unfolding \<open>keys ?p = {?s, ?t}\<close> tp_q'
      proof (rule associated_tp_not_in_keys)
        from \<open>v' \<in> keys q'\<close> finite_keys[of q'] show "card (keys q') \<noteq> 0" by auto
      qed
      with \<open>tp q' + tp p \<in> keys (?q * p)\<close> show "tp ?q' + tp p \<in> keys (q * p)" unfolding tp_q' eq by (rule in_keys_plusI1)
    qed
  qed
qed
  
lemma binomial_mult_shape_lp:
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + lp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "punit.subpoly q' q" and "lp q' = v" and "keys (q' * p) = {v + lp p, tp q' + tp p}"
    and "tp q' + tp p \<in> keys (q * p)"
proof -
  from assms obtain q' where 1: "q' \<noteq> 0" and 2: "punit.subpoly q' q" and 3: "lp q' = v" and 4: "associated_poly p q'"
    and 5: "tp q' + tp p \<in> keys (q * p)" by (rule binomial_mult_shape_lp')
  from 1 2 3 _ 5 show ?thesis
  proof
    from assms(1) 1 4 show "keys (q' * p) = {v + lp p, tp q' + tp p}" unfolding 3[symmetric]
      by (rule associated_poly_times_binomial_keys)
  qed
qed

text \<open>If the following lemma shall be proved in the same style as the one above, the analogue of
  @{thm associated_poly_recI} for @{term higher} instead of @{term tail} is needed.\<close>
lemma binomial_mult_shape_tp:
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + tp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "punit.subpoly q' q" and "tp q' = v" and "keys (q' * p) = {lp q' + lp p, v + tp p}"
    and "lp q' + lp p \<in> keys (q * p)"
  using assms(2) assms(3)
proof (induct "card (keys q)" arbitrary: thesis q v)
  case base: 0
  from base(1) finite_keys[of q] have "keys q = {}" by simp
  with base(3) show ?case by simp
next
  case ind: (Suc n)
  from \<open>punit.is_proper_binomial p\<close> have "p \<noteq> 0" by (rule punit.proper_binomial_not_0)
  let ?c = "lookup q v"
  from \<open>v \<in> keys q\<close> have "?c \<noteq> 0" by simp
  have q_rec: "q = monomial ?c v + except q {v}" (is "q = ?m + ?q") by (rule plus_except)
  hence "q * p = (?m + ?q) * p" by simp
  also have "... = ?m * p + ?q * p" by (rule algebra_simps(17))
  also have "... = punit.monom_mult ?c v p + ?q * p" by (simp only: times_monomial_left)
  finally have qp_eq: "q * p = punit.monom_mult ?c v p + ?q * p" (is "q * p = ?p + ?q * p") .
  from \<open>?c \<noteq> 0\<close> have lp_m: "lp ?m = v" and tp_m: "tp ?m = v" and keys_m: "keys ?m = {v}" and "?m \<noteq> 0"
    by (rule punit.lt_monomial, rule punit.tt_monomial, rule keys_of_monomial, meson monomial_0D)
  let ?t = "v + tp p"
  let ?s = "v + lp p"
  from \<open>punit.is_proper_binomial p\<close> have keys_p: "keys p = {lp p, tp p}"
    by (simp add: punit.proper_binomial_imp_binomial punit.keys_binomial)
  hence "keys ?p = {?s, ?t}" unfolding punit.keys_monom_mult[OF \<open>lookup q v \<noteq> 0\<close>, of v p] by simp
  hence "?s \<in> keys ?p" by simp
  show ?case
  proof (cases "?s \<in> keys (q * p)")
    case True
    show ?thesis
    proof (rule ind(3), fact \<open>?m \<noteq> 0\<close>, rule punit.monomial_subpoly, fact, unfold keys_m lp_m)
      show "keys (?m * p) = {v + lp p, ?t}"
        unfolding times_monomial_left punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>] keys_p by simp
    next
      from True show "v + lp p \<in> keys (q * p)" .
    qed
  next
    case False
    with \<open>punit.is_proper_binomial p\<close> \<open>v \<in> keys q\<close> obtain v' where "v' \<in> keys q" and "v \<prec> v'"
      and *: "v' + tp p = ?s" and **: "lookup q v' * tc p = -(?c * lc p)"
      by (rule times_binomial_lp_not_in_keys)
    from in_keys_plusI1[OF \<open>?s \<in> keys ?p\<close>, of "except q {v} * p"] False
    have "?s \<in> keys (?q * p)" unfolding qp_eq by blast
    from \<open>v \<prec> v'\<close> have "v' \<noteq> v" by simp
    with \<open>v' \<in> keys q\<close> have "v' \<in> keys ?q" by (simp add: keys_except)
    from \<open>v \<in> keys q\<close> ind(2) have "n = card (keys ?q)" unfolding keys_except using finite_keys[of q]
      by simp
    from this _ \<open>v' \<in> keys ?q\<close> \<open>?s \<in> keys (?q * p)\<close> obtain q'
      where "q' \<noteq> 0" and "punit.subpoly q' ?q" and "tp q' = v'"
      and ***: "keys (q' * p) = {lp q' + lp p, ?s}" and "lp q' + lp p \<in> keys (?q * p)"
      unfolding \<open>v' + tp p = ?s\<close>[symmetric] by (rule ind(1))
    from \<open>q' \<noteq> 0\<close> have "v' \<in> keys q'" unfolding \<open>tp q' = v'\<close>[symmetric] by (rule punit.tt_in_keys)
    let ?q' = "q' + ?m"
    have "v \<notin> keys ?q" unfolding keys_except by simp
    hence "v \<notin> keys q'" using punit.subpoly_keys[OF \<open>punit.subpoly q' ?q\<close>] by auto
    hence "keys q' \<inter> keys ?m = {}" unfolding keys_m by simp
    hence keys_q': "keys ?q' = keys q' \<union> {v}" unfolding keys_m[symmetric] by (rule keys_plus_eqI)
    from \<open>v \<notin> keys q'\<close> finite_keys[of q'] have card_keys_q': "card (keys ?q') = Suc (card (keys q'))"
      unfolding keys_q' by simp
    have "punit.subpoly q' q" by (rule punit.subpoly_trans, fact, rule punit.except_subpoly)
    note \<open>v \<prec> v'\<close>
    also have "v' = tp q'" by (simp only: \<open>tp q' = v'\<close>)
    also have "... \<preceq> lp q'" by (rule punit.lt_ge_tt)
    finally have "v \<prec> lp q'" .
    have "?q' \<noteq> 0"
    proof
      assume "?q' = 0"
      hence "keys ?q' = {}" by simp
      with keys_q' show False by simp
    qed
    have lp_q': "lp ?q' = lp q'"
    by (simp only: add.commute[of q'], rule punit.lt_plus_eqI, simp only: lp_m, fact)
    show ?thesis
    proof (rule ind(3), fact \<open>?q' \<noteq> 0\<close>, rule punit.plus_subpolyI, fact, rule punit.monomial_subpoly, fact)
      from \<open>?m \<noteq> 0\<close> have "tp ?q' = tp ?m"
      proof (simp only: add.commute[of q'], rule punit.tt_plus_eqI, simp only: tp_m \<open>tp q' = v'\<close>)
        show "v \<prec> v'" by fact
      qed
      thus "tp ?q' = v" by (simp add: tp_m)
    next
      have eq1: "?q' * p = q' * p + punit.monom_mult ?c v p"
        by (simp add: algebra_simps(17) times_monomial_left)
      have eq2: "lookup (punit.monom_mult ?c v p) ?s = ?c * lc p" by (simp add: punit.lc_def punit.lookup_monom_mult)
      from \<open>punit.subpoly q' q\<close> \<open>v' \<in> keys q'\<close> have "lookup q' v' = lookup q v'" by (rule punit.subpolyE)
      have "lookup (q' * p) (v' + tp p) = (lookup q' v') * tc p"
      proof (rule lookup_times_binomial_3, fact assms(1), rule)
        assume "\<exists>w\<in>(keys q'). w + lp p = v' + tp p"
        then obtain w where "w \<in> keys q'" and "w + lp p = v' + tp p" ..
        hence "w = v" unfolding * by simp
        from \<open>v \<notin> keys q'\<close> \<open>w \<in> keys q'\<close> show False unfolding \<open>w = v\<close> ..
      qed
      also have "... = (lookup q v') * tc p" unfolding punit.subpolyE[OF \<open>punit.subpoly q' q\<close> \<open>v' \<in> keys q'\<close>] ..
      also from ** have "... = -(?c * lc p)" .
      finally have "0 = lookup (q' * p) (v' + tp p) + ?c * lc p" by simp
      also have "... = lookup (?q' * p) ?s" unfolding eq1 eq2 lookup_add \<open>v' + tp p = ?s\<close> ..
      finally have "lookup (?q' * p) ?s = 0" by simp
      hence "?s \<notin> keys (?q' * p)" by simp
      show "keys (?q' * p) = {lp ?q' + lp p, ?t}" unfolding lp_q'
      proof
        have "keys (?q' * p) \<subseteq> keys (q' * p) \<union> keys (punit.monom_mult ?c v p)" unfolding eq1
          by (rule keys_add_subset)
        also have "... = {lp q' + lp p, ?s} \<union> {?s, ?t}" by (simp add: punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>] *** keys_p)
        finally have "keys (?q' * p) \<subseteq> {lp q' + lp p, ?s, ?t}" by auto
        with \<open>?s \<notin> keys (?q' * p)\<close> show "keys (?q' * p) \<subseteq> {lp q' + lp p, ?t}" by auto
      next
        from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
        hence "?t \<prec> ?s" by (rule plus_monotone_strict_left)
        also from \<open>v \<prec> lp q'\<close> have "... \<preceq> lp q' + lp p" by (simp add: plus_monotone)
        finally have uneq: "lp q' + lp p \<noteq> ?t" by simp
        have "lp q' + lp p \<in> keys (?q' * p)" unfolding eq1
        proof (rule in_keys_plusI1, simp add: ***, simp add: \<open>keys ?p = {?s, ?t}\<close>, rule conjI, rule)
          assume "lp q' = v"
          from \<open>q' \<noteq> 0\<close> have "lp q' \<in> keys q'" by (rule punit.lt_in_keys)
          with \<open>v \<notin> keys q'\<close> show False unfolding \<open>lp q' = v\<close> ..
        qed (fact uneq)
        moreover have "?t \<in> keys (?q' * p)" unfolding eq1
        proof (rule in_keys_plusI2, simp add: \<open>keys ?p = {?s, ?t}\<close>, simp add: ***, rule conjI, fact uneq[symmetric])
          from \<open>tp p \<prec> lp p\<close> show "tp p \<noteq> lp p" by simp
        qed
        ultimately show "{lp q' + lp p, ?t} \<subseteq> keys (?q' * p)" by simp
      qed
    next
      have eq: "q * p = ?q * p + punit.monom_mult ?c v p" unfolding qp_eq by simp
      have "lp q' + lp p \<notin> keys ?p" unfolding \<open>keys ?p = {?s, ?t}\<close>
      proof
        assume "lp q' + lp p \<in> {?s, ?t}"
        hence "lp q' + lp p = ?s \<or> lp q' + lp p = ?t" by auto
        thus False
        proof
          assume "lp q' + lp p = ?s"
          hence "lp q' = v" by (simp only: add_right_cancel)
          with \<open>v \<prec> lp q'\<close> show False by simp
        next
          assume "lp q' + lp p = ?t"
          from \<open>v \<prec> lp q'\<close> have "?t \<prec> lp q' + tp p" by (rule plus_monotone_strict)
          also have "... \<preceq> lp q' + lp p" by (rule plus_monotone_left, rule punit.lt_ge_tt)
          finally show False by (simp add: \<open>lp q' + lp p = ?t\<close>)
        qed
      qed
      with \<open>lp q' + lp p \<in> keys (?q * p)\<close> show "lp ?q' + lp p \<in> keys (q * p)" unfolding eq lp_q'
        by (rule in_keys_plusI1)
    qed
  qed
qed

lemma binomial_mult_shape_tp':
  assumes "punit.is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + tp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "punit.subpoly q' q" and "tp q' = v" and "associated_poly p q'" and "lp q' + lp p \<in> keys (q * p)"
proof -
  from assms obtain q' where 1: "q' \<noteq> 0" and 2: "punit.subpoly q' q" and 3: "tp q' = v"
    and 4: "keys (q' * p) = {lp q' + lp p, v + tp p}" and 5: "lp q' + lp p \<in> keys (q * p)"
    by (rule binomial_mult_shape_tp)
  from 1 2 3 _ 5 show ?thesis
  proof
    from assms(1) 4 show "associated_poly p q'" unfolding 3[symmetric]
      by (rule times_binomial_keys_associated_poly)
  qed
qed

end (* fun_powerprod *)

end (* theory *)
