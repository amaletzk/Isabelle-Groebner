section \<open>Multiplication by Binomials\<close>

theory Binom_Mult
  imports Polynomials.MPoly_PM Poly_Utils
begin

context ordered_powerprod
begin

lemma keys_monomial_plus_times:
  assumes "is_proper_binomial (p::'a \<Rightarrow>\<^sub>0 'b::field)" and "q \<noteq> 0" and "v \<prec> u"
    and "keys (q * p) = {u + tpp p, v + tpp p}"
  shows "keys ((monomial (- (lcf q * lcf p) / tcf p) u + q) * p) = {u + lpp p, v + tpp p}"
proof -
  from assms(1) have "tpp p \<prec> lpp p" by (rule punit.lt_gr_tt_binomial)
  from assms(1) have "p \<noteq> 0" by (rule proper_binomial_not_0)
  hence "tcf p \<noteq> 0" by (rule punit.tc_not_0)
  from assms(3) have "v + tpp p \<prec> u + tpp p" by (rule plus_monotone_strict)
  have "lpp q + lpp p = lpp (q * p)" by (simp only: lp_times[OF assms(2) \<open>p \<noteq> 0\<close>])
  also from assms(4) have "\<dots> = u + tpp p"
  proof (rule punit.keys_2_lt)
    from \<open>v + tpp p \<prec> u + tpp p\<close> show "v + tpp p \<preceq> u + tpp p" by simp
  qed
  finally have *: "u + tpp p = lpp q + lpp p" by simp
  let ?c = "- (lcf q * lcf p) / tcf p"
  from punit.lc_not_0[OF \<open>p \<noteq> 0\<close>] punit.lc_not_0[OF \<open>q \<noteq> 0\<close>] \<open>tcf p \<noteq> 0\<close> have "?c \<noteq> 0" by simp
  show ?thesis
  proof (simp only: algebra_simps(17) times_monomial_left, rule punit.keys_2_plus,
        simp only: punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>], simp add: punit.keys_proper_binomial[OF assms(1)], fact, fact)
    from \<open>tpp p \<prec> lpp p\<close> show "u + tpp p \<prec> u + lpp p" by (rule plus_monotone_strict_left)
  qed (simp only: punit.lookup_monom_mult_plus[simplified] punit.tc_def[symmetric],
        simp add: \<open>tcf p \<noteq> 0\<close> * lookup_times_lp_lp)
qed

lemma keys_plus_monomial_times:
  assumes "is_proper_binomial (p::'a \<Rightarrow>\<^sub>0 'b::field)" and "q \<noteq> 0" and "v \<prec> u"
    and "keys (q * p) = {u + lpp p, v + lpp p}"
  shows "keys ((q + monomial (- (tcf q * tcf p) / lcf p) v) * p) = {u + lpp p, v + tpp p}"
proof -
  from assms(1) have "tpp p \<prec> lpp p" by (rule punit.lt_gr_tt_binomial)
  from assms(1) have "p \<noteq> 0" by (rule proper_binomial_not_0)
  hence "lcf p \<noteq> 0" by (rule punit.lc_not_0)
  from assms(3) have "v + lpp p \<prec> u + lpp p" by (rule plus_monotone_strict)
  have "tpp q + tpp p = tpp (q * p)" by (simp only: tp_times[OF assms(2) \<open>p \<noteq> 0\<close>])
  also from assms(4) have "\<dots> = v + lpp p"
  proof (rule punit.keys_2_tt)
    from \<open>v + lpp p \<prec> u + lpp p\<close> show "v + lpp p \<preceq> u + lpp p" by simp
  qed
  finally have *: "v + lpp p = tpp q + tpp p" by simp
  let ?c = "- (tcf q * tcf p) / lcf p"
  from punit.tc_not_0[OF \<open>p \<noteq> 0\<close>] punit.tc_not_0[OF \<open>q \<noteq> 0\<close>] \<open>lcf p \<noteq> 0\<close> have "?c \<noteq> 0" by simp
  show ?thesis
  proof (simp only: algebra_simps(17) times_monomial_left, rule punit.keys_2_plus, fact,
        simp only: punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>], simp add: punit.keys_proper_binomial[OF assms(1)])
    from \<open>tpp p \<prec> lpp p\<close> show "v + tpp p \<prec> v + lpp p" by (rule plus_monotone_strict_left)
  qed (fact, simp only: punit.lookup_monom_mult_plus[simplified] punit.lc_def[symmetric],
        simp add: \<open>lcf p \<noteq> 0\<close> * lookup_times_tp_tp)
qed

end (* ordered_powerprod *)

context pm_powerprod
begin
  
subsubsection \<open>associated\<close>

definition associated :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat \<Rightarrow> bool"
  where "associated q s t k \<longleftrightarrow> (t + k \<cdot> (lpp q) = s + k \<cdot> (tpp q))"

lemma associatedI:
  assumes "t + k \<cdot> (lpp q) = s + k \<cdot> (tpp q)"
  shows "associated q s t k"
  unfolding associated_def using assms .

lemma associatedI_lookup:
  assumes "\<And>x. lookup t x + k * lookup (lpp q) x = lookup s x + k * lookup (tpp q) x"
  shows "associated q s t k"
  by (intro associatedI poly_mapping_eqI, simp add: lookup_add, fact)

lemma associatedD:
  assumes "associated q s t k"
  shows "t + k \<cdot> (lpp q) = s + k \<cdot> (tpp q)"
  using assms unfolding associated_def .

lemma associatedD_lookup:
  assumes "associated q s t k"
  shows "lookup t x + k * lookup (lpp q) x = lookup s x + k * lookup (tpp q) x"
proof -
  from assms have "t + k \<cdot> lpp q = s + k \<cdot> tpp q" by (rule associatedD)
  hence "lookup (t + k \<cdot> (lpp q)) x = lookup (s + k \<cdot> tpp q) x" by simp
  thus ?thesis by (simp add: lookup_add)
qed

lemma associated_0: "associated q s t 0 \<longleftrightarrow> (s = t)"
  by (auto simp: associated_def)

lemma associated_1: "associated q s t 1 \<longleftrightarrow> (s + tpp q = t + lpp q)"
  by (simp only: associated_def map_scale_one_left, auto)

lemma associated_Suc: "associated q s t (Suc k) \<longleftrightarrow> associated q (s + tpp q) (t + lpp q) k"
  by (simp add: associated_def map_scale_Suc ac_simps)

lemma associated_canc_left: "associated q (u + s) (u + t) k \<longleftrightarrow> associated q s t k"
proof -
  have "u + t + k \<cdot> lpp q = u + (t + k \<cdot> lpp q)" by (simp add: ac_simps)
  moreover have "u + s + k \<cdot> tpp q = u + (s + k \<cdot> tpp q)" by (simp add: ac_simps)
  ultimately show ?thesis by (simp add: associated_def map_scale_distrib_right)
qed

lemma associated_canc_right: "associated q (s + u) (t + u) k \<longleftrightarrow> associated q s t k"
  by (simp only: add.commute[of _ u] associated_canc_left)

lemma associated_1_plus_tpp:
  assumes "associated q s (u + tpp q) 1"
  shows "s = u + lpp q"
proof (rule add_right_imp_eq[of _ "tpp q"])
  from assms show "s + tpp q = u + lpp q + tpp q" by (simp only: associated_1 ac_simps)
qed

lemma associated_1_plus_lpp:
  assumes "associated q (u + lpp q) t 1"
  shows "t = u + tpp q"
proof (rule add_right_imp_eq[of _ "lpp q"])
  from assms show "t + lpp q = u + tpp q + lpp q" by (simp only: associated_1 ac_simps)
qed

lemma associated_trans:
  assumes "associated q s t k" and "associated q u s m"
  shows "associated q u t (k + m)"
proof (rule associatedI)
  from assms(1) have "t + k \<cdot> (lpp q) = s + k \<cdot> (tpp q)"
    by (rule associatedD)
  moreover from assms(2) have "s + m \<cdot> (lpp q) = u + m \<cdot> (tpp q)"
    by (rule associatedD)
  ultimately show "t + (k + m) \<cdot> (lpp q) = u + (k + m) \<cdot> (tpp q)"
    by (simp only: map_scale_distrib_right, metis (no_types, lifting) add.assoc add.commute)
qed

lemma associated_trans_rev:
  assumes "associated q s t (k + m)"
  obtains u where "associated q u t k" and "associated q s u m"
proof -
  let ?lpp = "lookup (lpp q)"
  let ?tpp = "lookup (tpp q)"
  have adds: "k \<cdot> (tpp q) adds (t + k \<cdot> (lpp q))"
  proof (rule adds_poly_mappingI, rule le_funI, simp add: lookup_add)
    fix x
    show "k * ?tpp x \<le> lookup t x + k * ?lpp x"
    proof (cases "?tpp x \<le> ?lpp x")
      case True
      hence "k * ?tpp x \<le> k * ?lpp x" by simp
      thus ?thesis by linarith
    next
      case False
      hence "?lpp x \<le> ?tpp x" by simp
      hence "m * ?lpp x \<le> m * ?tpp x" by simp
      hence "lookup t x + (k + m) * ?lpp x \<le> lookup t x + k * ?lpp x + m * ?tpp x"
        by (simp add: algebra_simps)
      with associatedD_lookup[OF assms] have "lookup s x + k * ?tpp x + m * ?tpp x \<le> lookup t x + k * ?lpp x + m * ?tpp x"
        by (simp add: algebra_simps)
      hence "lookup s x + k * ?tpp x \<le> lookup t x + k * ?lpp x" by simp
      thus ?thesis by linarith
    qed
  qed
  let ?u = "(t + k \<cdot> (lpp q)) - k \<cdot> (tpp q)"
  show ?thesis
  proof
    show "associated q ?u t k"
    proof (rule associatedI)
      from adds show "t + k \<cdot> lpp q = t + k \<cdot> lpp q - k \<cdot> tpp q + k \<cdot> tpp q" by (simp add: adds_minus)
    qed
  next
    show "associated q s ?u m"
    proof (rule associatedI)
      have "?u + m \<cdot> lpp q = t + (k + m) \<cdot> lpp q - k \<cdot> tpp q"
        by (simp add: add.assoc adds minus_plus map_scale_distrib_right)
      also from associatedD[OF assms] have "\<dots> = (s + m \<cdot> tpp q + k \<cdot> tpp q) - k \<cdot> tpp q"
        by (simp add: map_scale_distrib_right ac_simps)
      finally show "?u + m \<cdot> lpp q = s + m \<cdot> tpp q" by simp
    qed
  qed
qed

lemma associated_inj_1:
  assumes "associated q s1 t k" and "associated q s2 t k"
  shows "s1 = s2"
proof -
  from assms(1) have "t + k \<cdot> lpp q = s1 + k \<cdot> tpp q" by (rule associatedD)
  moreover from assms(2) have "t + k \<cdot> lpp q = s2 + k \<cdot> tpp q" by (rule associatedD)
  ultimately show ?thesis by simp
qed

lemma associated_inj_2:
  assumes "associated q s t1 k" and "associated q s t2 k"
  shows "t1 = t2"
proof -
  from assms(1) have "t1 + k \<cdot> lpp q = s + k \<cdot> tpp q" by (rule associatedD)
  moreover from assms(2) have "t2 + k \<cdot> lpp q = s + k \<cdot> tpp q" by (rule associatedD)
  ultimately show ?thesis by (metis add_right_cancel)
qed

lemma associated_inj_3:
  assumes "\<not> has_bounded_keys 1 q" and "associated q s t k1" and "associated q s t k2"
  shows "k1 = k2"
proof -
  let ?lpp = "lookup (lpp q)"
  let ?tpp = "lookup (tpp q)"
  from assms(1) have "lpp q \<noteq> tpp q" by (simp add: punit.lt_eq_tt_iff)
  hence "?lpp \<noteq> ?tpp" by simp
  then obtain x where "?lpp x \<noteq> ?tpp x" by fastforce
  from assms(2) have 1: "lookup t x + k1 * ?lpp x = lookup s x + k1 * ?tpp x" by (rule associatedD_lookup)
  from assms(3) have 2: "lookup t x + k2 * ?lpp x = lookup s x + k2 * ?tpp x" by (rule associatedD_lookup)
  show ?thesis
  proof (rule linorder_cases)
    from 1 have "lookup t x - lookup s x = k1 * (?tpp x - ?lpp x)" by (simp add: diff_mult_distrib2)
    moreover from 2 have "lookup t x - lookup s x = k2 * (?tpp x - ?lpp x)" by (simp add: diff_mult_distrib2)
    ultimately have eq: "k1 * (?tpp x - ?lpp x) = k2 * (?tpp x - ?lpp x)" by (simp only:)
    assume c2: "?lpp x < ?tpp x"
    hence "0 < ?tpp x - ?lpp x" by simp
    with eq show ?thesis by simp
  next
    from 1 have "lookup s x - lookup t x = k1 * (?lpp x - ?tpp x)" by (simp add: diff_mult_distrib2)
    moreover from 2 have "lookup s x - lookup t x = k2 * (?lpp x - ?tpp x)" by (simp add: diff_mult_distrib2)
    ultimately have eq: "k1 * (?lpp x - ?tpp x) = k2 * (?lpp x - ?tpp x)" by (simp only:)
    assume c1: "?tpp x < ?lpp x"
    hence "0 < ?lpp x - ?tpp x" by simp
    with eq show ?thesis by simp
  next
    assume c3: "?lpp x = ?tpp x"
    with \<open>?lpp x \<noteq> ?tpp x\<close> show ?thesis ..
  qed
qed

lemma associated_lpp_adds_between:
  assumes "associated q s u m" and "associated q u t k" and "lpp q adds s" and "lpp q adds t"
  shows "lpp q adds u"
proof (simp only: adds_poly_mapping le_fun_def, rule)
  let ?lpp = "lookup (lpp q)"
  let ?tpp = "lookup (tpp q)"
  fix x
  from assms(3) have "?lpp x \<le> lookup s x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(4) have "?lpp x \<le> lookup t x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(1) have a: "lookup u x + m * ?lpp x = lookup s x + m * ?tpp x" by (rule associatedD_lookup)
  from assms(2) have b: "lookup t x + k * ?lpp x = lookup u x + k * ?tpp x" by (rule associatedD_lookup)
  show "?lpp x \<le> lookup u x"
  proof (cases "?tpp x \<le> ?lpp x")
    case True
    hence "k * ?tpp x \<le> k * ?lpp x" by simp
    with b have "lookup t x \<le> lookup u x" by linarith
    with \<open>?lpp x \<le> lookup t x\<close> show ?thesis by simp
  next
    case False
    hence "m * ?lpp x \<le> m * ?tpp x" by simp
    with a have "lookup s x \<le> lookup u x" by linarith
    with \<open>?lpp x \<le> lookup s x\<close> show ?thesis by simp
  qed
qed
  
lemma associated_lpp_adds_between':
  assumes "associated p s u m" and "associated p u t k" and "lpp p adds s" and "tpp p adds t" and "k \<noteq> 0"
  shows "lpp p adds u"
proof -
  from assms(5) have "1 + (k - 1) = k" by simp
  with assms(2) have "associated p u t (1 + (k - 1))" by simp
  then obtain v where a1: "associated p v t 1" and a2: "associated p u v (k - 1)"
    by (rule associated_trans_rev)
  from assms(4) obtain w where t_eq: "t = w + tpp p" by (metis addsE add.commute)
  from a1 have v_eq: "v = w + lpp p" by (simp only: t_eq, elim associated_1_plus_tpp)
  hence "lpp p adds v" by simp
  with assms(1) a2 assms(3) show ?thesis by (rule associated_lpp_adds_between)
qed

lemma associated_lpp_adds_between'':
  assumes "associated p s t m" and "associated p u t k" and "lpp p adds s" and "tpp p adds t" and "k \<le> m"
    and "k \<noteq> 0"
  shows "lpp p adds u"
proof -
  from \<open>k \<le> m\<close> have "m = k + (m - k)" by simp
  with assms(1) have "associated p s t (k + (m - k))" by simp
  then obtain u' where "associated p u' t k" and *: "associated p s u' (m - k)"
    by (rule associated_trans_rev)
  from this(1) assms(2) have "u' = u" by (rule associated_inj_1)
  with * have "associated p s u (m - k)" by simp
  from this assms(2) assms(3) assms(4) assms(6) show ?thesis by (rule associated_lpp_adds_between')
qed

lemma associated_tpp_adds_between:
  assumes "associated q s u m" and "associated q u t k" and "tpp q adds s" and "tpp q adds t"
  shows "tpp q adds u"
proof (simp only: adds_poly_mapping le_fun_def, rule)
  let ?lpp = "lookup (lpp q)"
  let ?tpp = "lookup (tpp q)"
  fix x
  from assms(3) have "?tpp x \<le> lookup s x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(4) have "?tpp x \<le> lookup t x" by (simp add: adds_poly_mapping le_fun_def)
  from assms(1) have a: "lookup u x + m * ?lpp x = lookup s x + m * ?tpp x" by (rule associatedD_lookup)
  from assms(2) have b: "lookup t x + k * ?lpp x = lookup u x + k * ?tpp x" by (rule associatedD_lookup)
  show "?tpp x \<le> lookup u x"
  proof (cases "?tpp x \<le> ?lpp x")
    case True
    hence "k * ?tpp x \<le> k * ?lpp x" by simp
    with b have "lookup t x \<le> lookup u x" by linarith
    with \<open>?tpp x \<le> lookup t x\<close> show ?thesis by simp
  next
    case False
    hence "m * ?lpp x \<le> m * ?tpp x" by simp
    with a have "lookup s x \<le> lookup u x" by linarith
    with \<open>?tpp x \<le> lookup s x\<close> show ?thesis by simp
  qed
qed

lemma associated_tpp_adds_between':
  assumes "associated p s u m" and "associated p u t k" and "lpp p adds s" and "tpp p adds t" and "m \<noteq> 0"
  shows "tpp p adds u"
proof -
  from assms(5) have "(m - 1) + 1 = m" by simp
  with assms(1) have "associated p s u ((m - 1) + 1)" by simp
  then obtain v where a1: "associated p s v 1" and a2: "associated p v u (m - 1)"
    by (rule associated_trans_rev)
  from assms(3) obtain w where t_eq: "s = w + lpp p" by (metis addsE add.commute)
  from a1 have v_eq: "v = w + tpp p" by (simp only: t_eq, elim associated_1_plus_lpp)
  hence "tpp p adds v" by simp
  from a2 assms(2) this assms(4) show ?thesis by (rule associated_tpp_adds_between)
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
  hence lpp: "lpp (monomial c u) = u" and tpp: "tpp (monomial c u) = u"
    by (rule punit.lt_monomial, rule punit.tt_monomial)
  from assms show ?thesis by (auto simp add: associated_def lpp tpp)
qed

lemma associated_has_bounded_keys_1:
  assumes "has_bounded_keys 1 q" and "associated q s t k"
  shows "s = t"
proof -
  from assms(1) have "q = 0 \<or> is_monomial q" by (rule has_bounded_keys_1_D)
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
  from ind(2) have  "associated q (s + tpp q) (t + lpp q) k" by (simp add: associated_Suc)
  hence "t + lpp q \<preceq> s + tpp q" by (rule ind(1))
  also have "\<dots> \<preceq> s + lpp q"
  proof -
    from punit.lt_ge_tt[of q] have "tpp q + s \<preceq> lpp q + s" by (rule plus_monotone)
    thus ?thesis by (simp add: ac_simps)
  qed
  finally show ?case by (rule ord_canc)
qed

lemma associated_eq_iff:
  assumes "\<not> has_bounded_keys 1 q" and "associated q s t k"
  shows "s = t \<longleftrightarrow> k = 0"
proof
  assume "s = t"
  from assms(1) have "lpp q \<noteq> tpp q" by (simp add: punit.lt_eq_tt_iff)
  then obtain x where "lookup (tpp q) x \<noteq> lookup (lpp q) x" using poly_mapping_eqI by fastforce
  from assms(2) have "lookup t x + k * lookup (lpp q) x = lookup s x + k * lookup (tpp q) x"
    by (rule associatedD_lookup)
  hence "k * lookup (lpp q) x = k * lookup (tpp q) x" unfolding \<open>s = t\<close> by simp
  with \<open>lookup (tpp q) x \<noteq> lookup (lpp q) x\<close> show "k = 0" by simp
next
  assume "k = 0"
  from assms(2) show "s = t" by (simp add: \<open>k = 0\<close> associated_0)
qed

lemma associated_less:
  assumes "\<not> has_bounded_keys 1 q" and "associated q s t k" and "k \<noteq> 0"
  shows "t \<prec> s"
proof -
  from assms(2) have "t \<preceq> s" by (rule associated_leq)
  moreover from assms(3) have "s \<noteq> t" by (simp add: associated_eq_iff[OF assms(1) assms(2)])
  ultimately show ?thesis by simp
qed

lemma associated_lpp_not_in_keys:
  assumes "is_proper_binomial p" and "associated p u (v + lpp p) k" and "k \<noteq> 0"
  shows "u \<notin> {v + lpp p, v + tpp p}" (is "_ \<notin> {?s, ?t}")
proof -
  let ?lpp = "lookup (lpp p)"
  let ?tpp = "lookup (tpp p)"
  from assms(1) have "tpp p \<prec> lpp p" by (rule punit.lt_gr_tt_binomial)
  have "\<exists>x. ?tpp x < ?lpp x"
  proof (rule ccontr)
    assume "\<nexists>x. ?tpp x < ?lpp x"
    hence "lpp p adds tpp p" unfolding adds_poly_mapping adds_fun le_fun_def
      by (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
    hence "lpp p \<preceq> tpp p" by (rule ord_adds)
    with \<open>tpp p \<prec> lpp p\<close> show False by simp
  qed
  then obtain x where "?tpp x < ?lpp x" ..
  with \<open>k \<noteq> 0\<close> have ineq: "k * ?tpp x < k * ?lpp x" by simp
  from assms(2) have "lookup (v + lpp p) x + k * ?lpp x = lookup u x + k * ?tpp x" by (rule associatedD_lookup)
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
      from \<open>?tpp x < ?lpp x\<close> have "lookup ?t x < lookup ?s x" by (simp add: lookup_add)
      also have "\<dots> < lookup u x" using \<open>lookup ?s x < lookup u x\<close> .
      finally show ?thesis using \<open>lookup ?t x = lookup u x\<close> by simp
    qed
  qed
qed

lemma associated_tpp_not_in_keys:
  assumes "is_proper_binomial p" and "associated p (v + tpp p) u k" and "k \<noteq> 0"
  shows "u \<notin> {v + lpp p, v + tpp p}" (is "_ \<notin> {?s, ?t}")
proof -
  let ?lpp = "lookup (lpp p)"
  let ?tpp = "lookup (tpp p)"
  from assms(1) have "tpp p \<prec> lpp p" by (rule punit.lt_gr_tt_binomial)
  have "\<exists>x. ?tpp x < ?lpp x"
  proof (rule ccontr)
    assume "\<nexists>x. ?tpp x < ?lpp x"
    hence "lpp p adds tpp p" unfolding adds_poly_mapping adds_fun le_fun_def
      by (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
    hence "lpp p \<preceq> tpp p" by (rule ord_adds)
    with \<open>tpp p \<prec> lpp p\<close> show False by simp
  qed
  then obtain x where "?tpp x < ?lpp x" ..
  with \<open>k \<noteq> 0\<close> have ineq: "k * ?tpp x < k * ?lpp x" by simp
  from assms(2) have "lookup u x + k * ?lpp x = lookup (v + tpp p) x + k * ?tpp x" by (rule associatedD_lookup)
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
      also from \<open>?tpp x < ?lpp x\<close> have "\<dots> < lookup ?s x" by (simp add: lookup_add)
      finally have "lookup ?s x < lookup ?s x" .
      thus ?thesis by simp
    qed
  qed
qed

lemma associated_plus:
  assumes "associated p s t k" and "associated p u v m"
  shows "associated p (s + u) (t + v) (k + m)"
proof (rule associatedI, simp add: map_scale_distrib_right)
  from assms(1) have "t + k \<cdot> lpp p = s + k \<cdot> tpp p" by (rule associatedD)
  moreover from assms(2) have "v + m \<cdot> lpp p = u + m \<cdot> tpp p" by (rule associatedD)
  ultimately show "t + v + (k \<cdot> lpp p + m \<cdot> lpp p) = s + u + (k \<cdot> tpp p + m \<cdot> tpp p)"
    by (metis (no_types, lifting) add.assoc add.commute)
qed

lemma associated_adds_obtains_cofactor_keys:
  assumes "is_binomial p" and "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k" and "k \<noteq> 0"
    and "lpp p adds s" and "tpp p adds t"
  obtains q where "keys (q * p) = {s, t}"
proof (cases "is_monomial p")
  assume rl: "(\<And>q. keys (q * p) = {s, t} \<Longrightarrow> thesis)"
  assume "is_monomial p"
  hence "has_bounded_keys 1 p" by (rule has_bounded_keys_1_I1)
  hence "s = t" using assms(2) by (rule associated_has_bounded_keys_1)
  from assms(4) obtain u where s_eq: "s = u + lpp p" by (metis addsE add.commute)
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
  with assms(1) have "is_proper_binomial p" by (simp add: is_binomial_alt)
  have "\<not> has_bounded_keys 1 p" using \<open>\<not> is_monomial p\<close> assms(1) binomial_not_0 has_bounded_keys_1_D
    by blast
  have "1 \<noteq> (0::'a)" by simp
  from assms(2) assms(3) assms(4) rl show ?thesis
  proof (induct k arbitrary: thesis s)
    case 0
    from this(2) show ?case by simp
  next
    case step: (Suc k)
    from assms(1) have "p \<noteq> 0" by (rule binomial_not_0)
    hence "tcf p \<noteq> 0" by (rule punit.tc_not_0)
    from assms(5) obtain u where t_eq: "t = u + tpp p" by (metis addsE add.commute)
    show ?case
    proof (cases "k = 0")
      case True
      with step(2) have "associated p s (u + tpp p) 1" unfolding t_eq One_nat_def by metis
      hence s_eq: "s = u + lpp p" by (rule associated_1_plus_tpp)
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
      from \<open>\<not> has_bounded_keys 1 p\<close> a1 False have "t \<prec> s'" by (rule associated_less)
      from a2 a1 step(4) assms(5) False have "lpp p adds s'" by (rule associated_lpp_adds_between')
      with a1 False obtain q' where keys_q': "keys (q' * p) = {s', t}" by (rule step(1))
      from step(4) obtain v where s_eq: "s = v + lpp p" by (metis addsE add.commute)
      from a2 have s'_eq: "s' = v + tpp p" unfolding s_eq by (rule associated_1_plus_lpp)
      let ?c = "(- lcf q' * lcf p) / tcf p"
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
        from keys_q' show "keys (q' * p) = {v + tpp p, u + tpp p}" by (simp only: t_eq s'_eq)
      qed
    qed
  qed
qed

lemma associated_adds_obtains_cofactor_binomial_lcf:
  assumes "is_proper_binomial p" and "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k" and "k \<noteq> 0"
    and "lpp p adds s" and "tpp p adds t" and "c \<noteq> 0"
  obtains q d where "q * p = binomial c s d t" and "punit.is_obd c s d t"
proof -
  from assms(1) have "is_binomial p" by (rule proper_binomial_imp_binomial)
  from this assms(2) assms(3) assms(4) assms(5) obtain q' where eq1: "keys (q' * p) = {s, t}"
    by (rule associated_adds_obtains_cofactor_keys)
  from assms(1) have "\<not> has_bounded_keys 1 p"
    using has_bounded_keys_1_D proper_binomial_no_monomial proper_binomial_not_0 by blast
  from this assms(2) assms(3) have "t \<prec> s" by (rule associated_less)
  hence "t \<noteq> s" by simp
  let ?p = "q' * p"
  define a where "a = lookup ?p s"
  define b where "b = lookup ?p t"
  have "a \<noteq> 0" and "b \<noteq> 0" by (simp_all add: a_def b_def eq1 flip: in_keys_iff)
  with \<open>t \<noteq> s\<close> have "is_pbd a s b t" by (simp add: is_pbd_def)
  have eq: "?p = binomial a s b t"
    by (rule poly_mapping_keys_eqI, simp only: eq1 keys_binomial_pbd[OF \<open>is_pbd a s b t\<close>], simp add: eq1, elim disjE,
          simp_all add: lookup_binomial[OF \<open>is_pbd a s b t\<close>], simp only: a_def, simp add: b_def \<open>t \<noteq> s\<close>)
  let ?c = "c / a"
  let ?d = "?c * b"
  let ?q = "punit.monom_mult ?c 0 q'"
  from \<open>a \<noteq> 0\<close> have "?c \<noteq> 0" using assms(6) by simp
  show ?thesis
  proof
    show "?q * p = binomial c s ?d t"
      by (simp only: times_monomial_left[symmetric] ac_simps(4),
          simp add: times_monomial_left eq punit.monom_mult_binomial \<open>a \<noteq> 0\<close>)
  next
    show "punit.is_obd c s ?d t"
    proof (simp only: punit.is_obd_def, intro conjI, fact)
      from \<open>?c \<noteq> 0\<close> \<open>b \<noteq> 0\<close> show "?d \<noteq> 0" by simp
    qed fact
  qed
qed

lemma associated_adds_obtains_cofactor_binomial_tcf:
  assumes "is_proper_binomial p" and "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k" and "k \<noteq> 0"
    and "lpp p adds s" and "tpp p adds t" and "d \<noteq> 0"
  obtains q c where "q * p = binomial c s d t" and "punit.is_obd c s d t"
proof -
  have "1 \<noteq> (0::'a)" by simp
  with assms(1) assms(2) assms(3) assms(4) assms(5) obtain q' d'
    where eq: "q' * p = binomial 1 s d' t" and obd: "punit.is_obd 1 s d' t"
    by (rule associated_adds_obtains_cofactor_binomial_lcf)
  let ?c = "d / d'"
  let ?q = "punit.monom_mult ?c 0 q'"
  from obd have "d' \<noteq> 0" by (simp add: punit.is_obd_def)
  with assms(6) have "?c \<noteq> 0" by simp
  show ?thesis
  proof
    show "?q * p = binomial ?c s d t"
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
    (\<forall>s\<in>(keys q). tpp q \<prec> s \<longrightarrow> lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0))"

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
  assumes "associated_poly p q" and "s \<in> keys q" and "tpp q \<prec> s"
  shows "lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0"
proof -
  from assms(1) have "\<forall>s\<in>(keys q). tpp q \<prec> s \<longrightarrow> lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0"
    unfolding associated_poly_def ..
  hence "tpp q \<prec> s \<longrightarrow> lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0" using assms(2) ..
  thus ?thesis using assms(3) ..
qed

lemma associated_polyI:
  assumes "\<And>s t. s \<in> keys q \<Longrightarrow> t \<in> keys q \<Longrightarrow> t \<prec> s \<Longrightarrow> associated p s t (card {u\<in>(keys q). u \<prec> s \<and> t \<preceq> u})"
    and "\<And>s. s \<in> keys q \<Longrightarrow> tpp q \<prec> s \<Longrightarrow> lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0"
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
  from \<open>s \<in> keys q\<close> have "tpp q \<preceq> s" by (rule punit.tt_min_keys)
  also have "\<dots> \<prec> v" by fact
  finally have "tpp q \<prec> v" .
  assume "tpp (punit.lower q v) \<prec> s"
  with \<open>tpp q \<prec> v\<close> have "tpp q \<prec> s" by (simp add: punit.tt_lower)
  with assms \<open>s \<in> keys q\<close> have *: "lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0"
    by (rule associated_polyD2)
  from \<open>s \<prec> v\<close> have eq1: "lookup (punit.lower q v) s = lookup q s" by (simp add: punit.lookup_lower)
  from \<open>s \<prec> v\<close> have eq2: "lcf (punit.lower (punit.lower q v) s) = lcf (punit.lower q s)"
    by (simp add: punit.lower_lower ordered_powerprod_lin.min.absorb2)
  show "lookup (punit.lower q v) s * tcf p + lcf (punit.lower (punit.lower q v) s) * lcf p = 0"
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
  moreover from \<open>s \<in> keys q\<close> have "\<dots> \<preceq> lpp q" by (rule punit.lt_max_keys)
  ultimately have "v \<prec> lpp q" by simp
  hence "tpp q \<preceq> tpp (punit.higher q v)" by (rule punit.tt_higher)
  also assume "\<dots> \<prec> s"
  finally have "tpp q \<prec> s" .
  with assms \<open>s \<in> keys q\<close> have *: "lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0"
    by (rule associated_polyD2)
  from \<open>v \<prec> s\<close> have eq1: "lookup (punit.higher q v) s = lookup q s" by (simp add: punit.lookup_higher)
  have "punit.lower (punit.higher q v) s \<noteq> 0"
  proof (simp add: punit.lower_eq_zero_iff, rule, rule conjI)
    have "tcf (punit.higher q v) \<noteq> 0"
      by (rule punit.tc_not_0, auto simp: punit.higher_eq_zero_iff intro: \<open>s \<in> keys q\<close> \<open>v \<prec> s\<close>)
    thus "lookup (punit.higher q v) (tpp (punit.higher q v)) \<noteq> 0" by (simp add: punit.tc_def)
  qed fact
  hence "keys (punit.lower (punit.higher q v) s) \<noteq> {}" by simp
  then obtain u where "u \<in> keys (punit.lower (punit.higher q v) s)" by blast
  hence "lookup (punit.lower (punit.higher q v) s) u \<noteq> 0" and "u \<prec> s"
    by (simp add: in_keys_iff, simp add: punit.keys_lower)
  hence "lookup (punit.higher q v) u \<noteq> 0" by (simp add: punit.lookup_lower)
  have "v \<prec> lpp (punit.lower q s)"
  proof (rule punit.lt_gr, rule)
    assume "lookup (punit.lower q s) u = 0"
    with \<open>u \<prec> s\<close> have "lookup q u = 0" by (simp add: punit.lookup_lower)
    hence "lookup (punit.higher q v) u = 0" by (simp add: punit.lookup_higher)
    with \<open>lookup (punit.higher q v) u \<noteq> 0\<close> show False ..
  next
    from \<open>lookup (punit.higher q v) u \<noteq> 0\<close> show "v \<prec> u" by (metis punit.lookup_higher)
  qed
  hence eq2: "lcf (punit.lower (punit.higher q v) s) = lcf (punit.lower q s)" by (rule punit.lc_lower_higher)
  show "lookup (punit.higher q v) s * tcf p + lcf (punit.lower (punit.higher q v) s) * lcf p = 0"
    unfolding eq1 eq2 by fact
qed

lemma associated_poly_0: "associated_poly p 0"
  by (rule associated_polyI, simp_all)

lemma associated_poly_monomial':
  assumes "is_monomial q"
  shows "associated_poly p q"
proof -
  from assms have keys_q: "keys q = {lpp q}" by (rule punit.keys_monomial)
  from assms have eq1: "tpp q = lpp q" by (simp add: punit.lt_eq_tt_monomial)
  have eq2: "{u. u = lpp q \<and> u \<prec> lpp q \<and> lpp q \<preceq> u} = {}" by auto
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
  assumes "has_bounded_keys 1 q"
  shows "associated_poly p q"
proof -
  from assms have "q = 0 \<or> is_monomial q" by (rule has_bounded_keys_1_D)
  with associated_poly_0 associated_poly_monomial' show ?thesis by auto
qed

lemma associated_poly_recD1:
  assumes "\<not> has_bounded_keys 1 q" and "associated_poly p q"
  shows "associated p (lpp q) (lpp (punit.tail q)) 1"
proof -
  let ?s = "lpp q"
  let ?t = "lpp (punit.tail q)"
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
  assumes "\<not> has_bounded_keys 1 q" and "associated_poly p q"
  shows "lcf q * tcf p + lcf (punit.tail q) * lcf p = 0"
proof -
  let ?s = "lpp q"
  let ?t = "tpp q"
  from assms(1) have "punit.tail q \<noteq> 0" using punit.tail_0D by auto
  hence "q \<noteq> 0" by auto
  hence "?s \<in> keys q" by (rule punit.lt_in_keys)
  from assms(1) have "?t \<prec> ?s" by (simp add: punit.lt_gr_tt_iff)
  with assms(2) \<open>?s \<in> keys q\<close> have "lookup q ?s * tcf p + lcf (punit.lower q ?s) * lcf p = 0"
    by (rule associated_polyD2)
  thus ?thesis by (simp add: punit.tail_def punit.lc_def)
qed

lemma associated_poly_recD3:
  assumes "associated_poly p q"
  shows "associated_poly p (punit.tail q)"
  unfolding punit.tail_def using assms by (rule associated_poly_lower)

lemma associated_poly_recI:
  assumes "\<not> has_bounded_keys 1 q" and "associated p (lpp q) (lpp (punit.tail q)) 1"
    and "lcf q * tcf p + lcf (punit.tail q) * lcf p = 0" and "associated_poly p (punit.tail q)"
  shows "associated_poly p q"
proof (rule associated_polyI)
  fix s t
  assume "s \<in> keys q" and "t \<in> keys q" and "t \<prec> s"
  show "associated p s t (card {u \<in> keys q. u \<prec> s \<and> t \<preceq> u})"
  proof (cases "s \<prec> lpp q")
    case True
    with \<open>t \<prec> s\<close> have "t \<prec> lpp q" by simp
    with True \<open>s \<in> keys q\<close> \<open>t \<in> keys q\<close> have "s \<in> keys (punit.tail q)" and "t \<in> keys (punit.tail q)"
      by (simp_all add: punit.keys_tail)
    from assms(4) this \<open>t \<prec> s\<close> have a: "associated p s t (card {u \<in> keys (punit.tail q). u \<prec> s \<and> t \<preceq> u})"
      by (rule associated_polyD1)
    {
      assume "lpp q \<prec> s"
      with True have False by simp
    }
    hence eq: "{u \<in> keys (punit.tail q). u \<prec> s \<and> t \<preceq> u} = {u \<in> keys q. u \<prec> s \<and> t \<preceq> u}"
      by (auto simp add: punit.keys_tail)
    from a show ?thesis by (simp add: eq)
  next
    case False
    with punit.lt_max_keys[OF \<open>s \<in> keys q\<close>] have "s = lpp q" by simp
    with \<open>t \<prec> s\<close> have "t \<prec> lpp q" by simp
    with \<open>t \<in> keys q\<close> have "t \<in> keys (punit.tail q)" by (simp add: punit.keys_tail)
    hence "punit.tail q \<noteq> 0" by auto
    hence "lpp (punit.tail q) \<in> keys (punit.tail q)" by (rule punit.lt_in_keys)
    from \<open>t \<in> keys (punit.tail q)\<close> have "t \<preceq> lpp (punit.tail q)" by (rule punit.lt_max_keys)
    with assms(4) \<open>lpp (punit.tail q) \<in> keys (punit.tail q)\<close> \<open>t \<in> keys (punit.tail q)\<close>
    have a: "associated p (lpp (punit.tail q)) t (card {u \<in> keys (punit.tail q). u \<prec> lpp (punit.tail q) \<and> t \<preceq> u})"
      by (rule associated_polyD1')
    have "\<And>x. x \<in> keys q \<Longrightarrow> x \<noteq> lpp q \<Longrightarrow> x \<prec> lpp q"
    proof -
      fix x
      assume "x \<in> keys q"
      hence "x \<preceq> lpp q" by (rule punit.lt_max_keys)
      moreover assume "x \<noteq> lpp q"
      ultimately show "x \<prec> lpp q" by simp
    qed
    moreover have "\<And>x. x \<in> keys q \<Longrightarrow> x \<prec> lpp q \<Longrightarrow> x \<noteq> lpp (punit.tail q) \<Longrightarrow> x \<prec> lpp (punit.tail q)"
    proof -
      fix x
      assume "x \<in> keys q" and "x \<prec> lpp q"
      hence "x \<in> keys (punit.tail q)" by (simp add: punit.keys_tail)
      hence "x \<preceq> lpp (punit.tail q)" by (rule punit.lt_max_keys)
      moreover assume "x \<noteq> lpp (punit.tail q)"
      ultimately show "x \<prec> lpp (punit.tail q)" by simp
    qed
    moreover have "lpp (punit.tail q) \<in> {u \<in> keys q. u \<prec> s \<and> t \<preceq> u}" (is "_ \<in> ?A")
      by (simp add: \<open>s = lpp q\<close>, intro conjI, rule, fact, auto simp add: punit.keys_tail, rule punit.lt_tail, fact, fact)
    ultimately have "\<dots> = insert (lpp (punit.tail q)) {u \<in> keys (punit.tail q). u \<prec> lpp (punit.tail q) \<and> t \<preceq> u}"
      (is "_ = insert _ ?B")
      by (auto simp add: punit.keys_tail \<open>s = lpp q\<close>)
    moreover have "?B - {lpp (punit.tail q)} = ?B" by simp
    moreover have "finite ?B" using finite_keys[of "punit.tail q"] by simp
    ultimately have eq: "card ?A = card ?B + 1" by (simp add: card_insert)
    from a show ?thesis unfolding eq
    proof (rule associated_trans)
      show "associated p s (lpp (punit.tail q)) 1" unfolding \<open>s = lpp q\<close> by (fact assms(2))
    qed
  qed
next
  fix s
  assume "s \<in> keys q" and "tpp q \<prec> s"
  show "lookup q s * tcf p + lcf (punit.lower q s) * lcf p = 0"
  proof (cases "s \<prec> lpp q")
    case True
    from \<open>s \<in> keys q\<close> \<open>tpp q \<prec> s\<close> have "tpp q \<prec> lpp q" by (rule punit.lt_gr_keys)
    note assms(4)
    moreover from \<open>s \<in> keys q\<close> True have "s \<in> keys (punit.tail q)" by (simp add: punit.keys_tail)
    moreover from \<open>tpp q \<prec> s\<close> have "tpp (punit.tail q) \<prec> s"
      by (simp add: punit.tail_def punit.tt_lower[OF \<open>tpp q \<prec> lpp q\<close>])
    ultimately have "lookup (punit.tail q) s * tcf p + lcf (punit.lower (punit.tail q) s) * lcf p = 0"
      by (rule associated_polyD2)
    moreover from True have "ordered_powerprod_lin.min (lpp q) s = s"
      unfolding ordered_powerprod_lin.min_def by auto
    ultimately show ?thesis using True by (simp add: punit.tail_def punit.lower_lower punit.lookup_lower)
  next
    case False
    with punit.lt_max_keys[OF \<open>s \<in> keys q\<close>] have "s = lpp q" by simp
    from assms(3) show ?thesis by (simp add: \<open>s = lpp q\<close> punit.lc_def punit.tail_def)
  qed
qed

lemma associated_poly_rec_iff:
  assumes "\<not> has_bounded_keys 1 q"
  shows "associated_poly p q \<longleftrightarrow>
          (associated p (lpp q) (lpp (punit.tail q)) 1 \<and> lcf q * tcf p + lcf (punit.tail q) * lcf p = 0 \<and>
            associated_poly p (punit.tail q))"
  using assms associated_poly_recI associated_poly_recD1 associated_poly_recD2 associated_poly_recD3
  by auto

lemma associated_poly_associated_lpp_tpp:
  assumes "q \<noteq> 0" and "associated_poly p q"
  shows "associated p (lpp q) (tpp q) (card (keys q) - 1)"
proof -
  from assms(1) have 1: "lpp q \<in> keys q" and 2: "tpp q \<in> keys q"
    by (rule punit.lt_in_keys, rule punit.tt_in_keys)
  have 3: "tpp q \<preceq> lpp q" by (rule punit.lt_ge_tt)
  have eq: "card (keys q) - 1 = card {u\<in>(keys q). u \<prec> lpp q \<and> tpp q \<preceq> u}" (is "?l = card ?r")
  proof -
    have "?r = keys q - {lpp q}"
    proof (rule set_eqI, simp)
      fix x
      show "(x \<in> keys q \<and> x \<prec> lpp q \<and> tpp q \<preceq> x) = (x \<in> keys q \<and> x \<noteq> lpp q)" (is "?L = ?R")
      proof
        assume ?L
        hence "x \<in> keys q" and "x \<prec> lpp q" by simp_all
        hence "x \<noteq> lpp q" by simp
        with \<open>x \<in> keys q\<close> show ?R ..
      next
        assume ?R
        hence "x \<in> keys q" and "x \<noteq> lpp q" by simp_all
        from \<open>x \<in> keys q\<close> have "lookup q x \<noteq> 0" by (simp add: in_keys_iff)
        hence "x \<preceq> lpp q" and "tpp q \<preceq> x" by (rule punit.lt_max, rule punit.tt_min)
        from \<open>x \<preceq> lpp q\<close> \<open>x \<noteq> lpp q\<close> have "x \<prec> lpp q" by simp
        from \<open>x \<in> keys q\<close> this \<open>tpp q \<preceq> x\<close> show ?L by simp
      qed
    qed
    thus ?thesis using 1 finite_keys[of q] by simp
  qed
  from assms(2) 1 2 3 show ?thesis unfolding eq by (rule associated_polyD1')
qed

lemma associated_associated_poly:
  assumes "associated (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) s t k"
  obtains q where "q \<noteq> 0" and "lpp q = s" and "tpp q = t" and "associated_poly p q"
proof (cases "has_bounded_keys 1 p")
  assume rl: "(\<And>q. q \<noteq> 0 \<Longrightarrow> lpp q = s \<Longrightarrow> tpp q = t \<Longrightarrow> associated_poly p q \<Longrightarrow> thesis)"
  assume "has_bounded_keys 1 p"
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
    from \<open>s = t\<close> show "lpp ?q = s" by (simp add: punit.lt_monomial)
  next
    show "tpp ?q = t" by (rule punit.tt_monomial, simp)
  qed (rule associated_poly_monomial)
next
  assume rl: "(\<And>q. q \<noteq> 0 \<Longrightarrow> lpp q = s \<Longrightarrow> tpp q = t \<Longrightarrow> associated_poly p q \<Longrightarrow> thesis)"
  assume p_keys: "\<not> has_bounded_keys 1 p"
  hence "p \<noteq> 0" using has_bounded_keys_1_I2 by auto
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
      from \<open>s = t\<close> show "lpp ?q = s" by (simp add: punit.lt_monomial)
    next
      show "tpp ?q = t" by (rule punit.tt_monomial, simp)
    qed (rule associated_poly_monomial)
  next
    case step: (Suc k)
    from step(2) have "associated p s t (k + 1)" by simp
    then obtain s' where a1: "associated p s' t k" and a2: "associated p s s' 1"
      by (rule associated_trans_rev)
    from a1 obtain q' where "q' \<noteq> 0" and "lpp q' = s'" and "tpp q' = t" and "associated_poly p q'"
      by (rule step(1))
    from \<open>p \<noteq> 0\<close> have "tcf p \<noteq> 0" by (rule punit.tc_not_0)
    let ?c = "(- lcf q' * lcf p) / tcf p"
    let ?q = "(monomial ?c s) + q'"
    from punit.lc_not_0[OF \<open>p \<noteq> 0\<close>] punit.lc_not_0[OF \<open>q' \<noteq> 0\<close>] \<open>tcf p \<noteq> 0\<close> have "?c \<noteq> 0" by simp
    from p_keys a2 have "lpp q' \<prec> s" by (simp only: \<open>lpp q' = s'\<close>, rule associated_less, simp)
    from \<open>?c \<noteq> 0\<close> \<open>lpp q' \<prec> s\<close> have "?q \<noteq> 0" and lpp_q: "lpp ?q = s" and lcf_q: "lcf ?q = ?c"
      and tail_q: "punit.tail ?q = q'"
      by (rule punit.monomial_plus_not_0, rule punit.lt_monomial_plus[simplified],
          rule punit.lc_monomial_plus[simplified], rule punit.tail_monomial_plus)
    show ?case
    proof (rule step(3))
      from \<open>q' \<noteq> 0\<close> \<open>lpp q' \<prec> s\<close> show "tpp ?q = t" by (simp only: \<open>tpp q' = t\<close>[symmetric], rule punit.tt_monomial_plus)
    next
      show "associated_poly p ?q"
      proof (rule associated_poly_recI,
            simp_all only: lpp_q lcf_q tail_q \<open>lpp q' = s'\<close> punit.tail_eq_0_iff_has_bounded_keys_1[symmetric])
        from \<open>tcf p \<noteq> 0\<close> show "?c * tcf p + lcf q' * lcf p = 0" by simp
      qed fact+
    qed fact+
  qed
qed

lemma associated_poly_times_binomial_associated:
  assumes "q \<noteq> 0" and "associated_poly p q"
  shows "associated p (lpp q + lpp p) (tpp q + tpp p) (card (keys q))"
proof -
  from assms(1) have "keys q \<noteq> {}" by auto
  with finite_keys[of q] have "card (keys q) \<noteq> 0" by simp
  hence eq: "associated p (lpp q + lpp p) (tpp q + tpp p) (card (keys q)) \<longleftrightarrow>
              associated p (lpp q + lpp p) (tpp q + tpp p) ((card (keys q) - 1) + 1)" by force
  show ?thesis unfolding eq
  proof (rule associated_plus, rule associated_poly_associated_lpp_tpp, fact assms(1), fact assms(2))
    show "associated p (lpp p) (tpp p) 1" unfolding associated_1 by (simp add: add.commute)
  qed
qed

lemma associated_poly_times_binomial_keys:
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)" and "q \<noteq> 0"
    and "associated_poly p q"
  shows "keys (q * p) = {lpp q + lpp p, tpp q + tpp p}"
  using assms(2) assms(3)
proof (induct q rule: punit.poly_mapping_tail_induct)
  case 0
  thus ?case by simp
next
  case step: (tail q)
  let ?m = "punit.monom_mult (lcf q) (lpp q) p"
  let ?q = "punit.tail q"
  let ?A = "{lpp q + lpp p, tpp q + tpp p}"
  from assms(1) have "is_binomial p" and "p \<noteq> 0"
    by (rule proper_binomial_imp_binomial, rule proper_binomial_not_0)
  moreover from \<open>q \<noteq> 0\<close> have "lcf q \<noteq> 0" by (rule punit.lc_not_0)
  ultimately have keys_m: "keys ?m = {lpp q + lpp p, lpp q + tpp p}"
    by (simp add: punit.keys_binomial punit.keys_monom_mult)
  show ?case
  proof (cases "has_bounded_keys 1 q")
    case True
    hence "q = 0 \<or> is_monomial q" by (rule has_bounded_keys_1_D)
    with \<open>q \<noteq> 0\<close> have "is_monomial q" by simp
    hence "punit.tail q = 0" using is_monomial_monomial punit.tail_monomial by metis
    from \<open>is_monomial q\<close> have "tpp q = lpp q" by (simp add: punit.lt_eq_tt_monomial)
    from keys_m show ?thesis
      by (simp add: times_tail_rec_left[of q p] \<open>punit.tail q = 0\<close> \<open>tpp q = lpp q\<close> plus_fun_def)
  next
    case False
    hence "?q \<noteq> 0" using punit.tail_0D by blast
    from step(4) have assoc_tail: "associated_poly p ?q" by (rule associated_poly_recD3)
    from associated_poly_recD1[OF False step(4)] have eq1: "lpp q + tpp p = lpp ?q + lpp p"
      by (simp only: associated_1)
    from \<open>?q \<noteq> 0\<close> assoc_tail have eq2: "keys (?q * p) = {lpp ?q + lpp p, tpp ?q + tpp p}" by (rule step(2))
    from associated_poly_recD2[OF False step(4)]
      have eq3: "lookup ?m (lpp q + tpp p) + lookup (?q * p) (lpp ?q + lpp p) = 0"
        by (simp add: punit.lookup_monom_mult lookup_times_lp_lp punit.tc_def)
    from False have "tpp q \<prec> lpp q" by (simp add: punit.lt_gr_tt_iff)
    hence tpp_tail: "tpp (punit.tail q) = tpp q" by (simp only: punit.tail_def, rule punit.tt_lower)
    show ?thesis unfolding times_tail_rec_left[of q p]
    proof
      have "keys (?m + ?q * p) \<subseteq> keys ?m \<union> keys (?q * p)" by (rule Poly_Mapping.keys_add)
      also have "\<dots> = {lpp q + lpp p, lpp ?q + lpp p, tpp ?q + tpp p}" by (auto simp only: keys_m eq2 eq1)
      finally have "keys (?m + ?q * p) \<subseteq> {lpp q + lpp p, lpp ?q + lpp p, tpp ?q + tpp p}" .
      moreover from eq3 have "lpp ?q + lpp p \<notin> keys (?m + ?q * p)" by (simp add: lookup_add eq1 in_keys_iff)
      ultimately show "keys (?m + ?q * p) \<subseteq> ?A" by (auto simp only: tpp_tail)
    next
      show "?A \<subseteq> keys (?m + ?q * p)"
      proof (rule, simp, elim disjE, simp_all)
        show "lpp q + lpp p \<in> keys (?m + ?q * p)"
        proof (rule in_keys_plusI1, simp add: in_keys_iff punit.lookup_monom_mult \<open>lcf q \<noteq> 0\<close>)
          from \<open>p \<noteq> 0\<close> have "lcf p \<noteq> 0" by (rule punit.lc_not_0)
          thus "lookup p (lpp p) \<noteq> 0" by (simp add: punit.lc_def)
        next
          show "lpp q + lpp p \<notin> keys (?q * p)"
          proof
            assume "lpp q + lpp p \<in> keys (?q * p)"
            hence "lpp q + lpp p \<preceq> lpp ?q + lpp p" by (rule in_keys_times_le)
            hence "lpp q \<preceq> lpp ?q" by (rule ord_canc)
            also from \<open>?q \<noteq> 0\<close> have "lpp ?q \<prec> lpp q" by (rule punit.lt_tail)
            finally show False ..
          qed
        qed
      next
        show "tpp q + tpp p \<in> keys (?m + ?q * p)"
        proof (rule in_keys_plusI2, simp only: in_keys_iff tpp_tail[symmetric] lookup_times_tp_tp)
          from \<open>?q \<noteq> 0\<close> have "tcf ?q \<noteq> 0" by (rule punit.tc_not_0)
          moreover from \<open>p \<noteq> 0\<close> have "tcf p \<noteq> 0" by (rule punit.tc_not_0)
          ultimately show "tcf ?q * tcf p \<noteq> 0" by simp
        next
          show "tpp q + tpp p \<notin> keys ?m"
          proof
            assume "tpp q + tpp p \<in> keys ?m"
            thm punit.in_keys_monom_mult_ge
            hence "lpp q + tpp p \<preceq> tpp q + tpp p" by (rule punit_in_keys_monom_mult_ge)
            hence "lpp q \<preceq> tpp q" by (rule ord_canc)
            with \<open>tpp q \<prec> lpp q\<close> show False by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma times_binomial_keys_associated_poly:
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors)"
    and "keys (q * p) = {lpp q + lpp p, tpp q + tpp p}"
  shows "associated_poly p q"
  using assms(2)
proof (induct q rule: punit.poly_mapping_tail_induct)
  case 0
  hence "{lpp 0 + lpp p, tpp 0 + tpp p} = {}" by simp
  thus ?case by simp
next
  case step: (tail q)
  from step(1) have "lcf q \<noteq> 0" and "tcf q \<noteq> 0" by (rule punit.lc_not_0, rule punit.tc_not_0)
  show ?case
  proof (cases "has_bounded_keys 1 q")
    case True
    with step(1) have "is_monomial q" using has_bounded_keys_1_D by blast
    then obtain c t where "q = monomial c t" by (rule is_monomial_monomial)
    show ?thesis by (simp only: \<open>q = monomial c t\<close>, rule associated_poly_monomial)
  next
    case False
    with step(1) have "punit.tail q \<noteq> 0" using punit.tail_0D by blast
    hence tpp_tail_q: "tpp (punit.tail q) = tpp q" by (rule punit.tt_tail)
    from False have "tpp q \<prec> lpp q" by (simp add: punit.lt_gr_tt_iff)
    hence "tpp q + tpp p \<prec> lpp q + tpp p" by (simp only: plus_monotone_strict)
    from assms(1) have "p \<noteq> 0" and keys_p: "keys p = {lpp p, tpp p}" and "tpp p \<prec> lpp p"
      by (rule proper_binomial_not_0, rule punit.keys_proper_binomial, rule punit.lt_gr_tt_binomial)
    from \<open>p \<noteq> 0\<close> have "tcf p \<noteq> 0" by (rule punit.tc_not_0)
    from \<open>punit.tail q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have "tpp (punit.tail q * p) = tpp (punit.tail q) + tpp p"
      by (rule tp_times)
    also have "\<dots> = tpp q + tpp p" by (simp only: tpp_tail_q)
    finally have tpp_tail_times: "tpp (punit.tail q * p) = tpp q + tpp p" .
    from assms(1) have tail_p: "punit.tail p = monomial (tcf p) (tpp p)"
      by (metis Poly_Utils.binomial_def \<open>p \<noteq> 0\<close> \<open>tcf p \<noteq> 0\<close> \<open>tpp p \<prec> lpp p\<close> punit.binomial_eq_itself
          punit.lc_not_0 punit.lt_monomial punit.tail_monomial_plus)
    let ?m = "punit.monom_mult (lcf q) (lpp q) p"
    let ?r = "punit.tail q * p"
    from \<open>lcf q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have lpp_m: "lpp ?m = lpp q + lpp p" and tpp_m: "tpp ?m = lpp q + tpp p"
      by (rule lp_monom_mult, rule tp_monom_mult)
    have "punit.tail ?m = punit.monom_mult (lcf q) (lpp q) (punit.tail p)" by (rule punit.tail_monom_mult)
    also have "\<dots> = punit.monom_mult (lcf q) (lpp q) (monomial (tcf p) (tpp p))" by (simp only: tail_p)
    also have "\<dots> = monomial (lcf q * tcf p) (lpp q + tpp p)" by (rule punit_monom_mult_monomial)
    finally have tail_m: "punit.tail ?m = monomial (lcf q * tcf p) (lpp q + tpp p)" .
    from \<open>punit.tail q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have lpp_r: "lpp ?r = lpp (punit.tail q) + lpp p" and tpp_r: "tpp ?r = tpp q + tpp p"
      by (rule lp_times, simp add: tp_times tpp_tail_q)
    from punit.tc_tail[OF \<open>punit.tail q \<noteq> 0\<close>] have tcf_r: "tcf ?r = tcf q * tcf p" by (simp add: tc_times)
    from step(3) have "keys (?m + ?r) = {lpp ?m, tpp ?r}"
      by (simp only: times_tail_rec_left[of q] tpp_tail_times lp_monom_mult[OF \<open>lcf q \<noteq> 0\<close> \<open>p \<noteq> 0\<close>])
    hence "punit.tail ?m + punit.higher ?r (tpp ?r) = 0"
    proof (rule punit.keys_plus_eq_lt_tt_D, simp_all only: lpp_r lpp_m tpp_r tpp_m)
      from \<open>punit.tail q \<noteq> 0\<close> have "lpp (punit.tail q) \<prec> lpp q" by (rule punit.lt_tail)
      thus "lpp (punit.tail q) + lpp p \<prec> lpp q + lpp p" by (simp add: plus_monotone_strict)
    next
      show "tpp q + tpp p \<prec> lpp q + tpp p" by fact
    qed
    hence eq1: "monomial (lcf q * tcf p) (lpp q + tpp p) + punit.higher ?r (tpp ?r) = 0" by (simp only: tail_m)
    define c where "c = lookup (punit.higher ?r (tpp ?r)) (lpp q + tpp p)"
    have higher_r: "punit.higher ?r (tpp ?r) = monomial c (lpp q + tpp p)"
    proof (rule poly_mapping_eqI, simp add: lookup_single Poly_Mapping.when_def, intro conjI impI, simp only: c_def)
      fix t
      assume a: "lpp q + tpp p \<noteq> t"
      from eq1 have "0 = lookup (monomial (lcf q * tcf p) (lpp q + tpp p) + (punit.higher ?r (tpp ?r))) t"
        by (simp only: lookup_zero)
      also from a have "\<dots> = lookup (punit.higher ?r (tpp ?r)) t" by (simp add: lookup_add lookup_single)
      finally show "lookup (punit.higher ?r (tpp ?r)) t = 0" by simp
    qed
    from eq1 have "0 = lookup (monomial (lcf q * tcf p) (lpp q + tpp p) + (punit.higher ?r (tpp ?r))) (lpp q + tpp p)"
      by (simp only: lookup_zero)
    also have "\<dots> = lcf q * tcf p + c" by (simp add: lookup_add lookup_single c_def)
    finally have c: "lcf q * tcf p + c = 0" by simp
    from \<open>punit.tail q \<noteq> 0\<close> \<open>p \<noteq> 0\<close> have "?r \<noteq> 0" by (rule times_not_zero)
    from punit.trailing_monomial_higher[OF this] higher_r
    have r_eq: "?r = binomial c (lpp q + tpp p) (tcf q * tcf p) (tpp q + tpp p)"
      by (simp add: tpp_r tcf_r binomial_def)
    have obd: "punit.is_obd c (lpp q + tpp p) (tcf q * tcf p) (tpp q + tpp p)"
    proof (simp only: punit.is_obd_def, intro conjI, rule)
      assume "c = 0"
      with c have "lcf q * tcf p = 0" by simp
      with \<open>lcf q \<noteq> 0\<close> \<open>tcf p \<noteq> 0\<close> show False by simp
    next
      from \<open>tcf q \<noteq> 0\<close> \<open>tcf p \<noteq> 0\<close> show "tcf q * tcf p \<noteq> 0" by simp
    qed fact
    from lpp_r obd have lpp_tpp: "lpp q + tpp p = lpp (punit.tail q) + lpp p" by (simp only: r_eq punit.lt_binomial)
    show ?thesis
    proof (rule associated_poly_recI, fact False, simp only: associated_1 lpp_tpp)
      from lc_times[of "punit.tail q" p] obd c show "lcf q * tcf p + lcf (punit.tail q) * lcf p = 0"
        by (simp only: r_eq punit.lc_binomial)
    next
      show "associated_poly p (punit.tail q)"
      proof (rule step(2))
        from obd have "is_pbd c (lpp q + tpp p) (tcf q * tcf p) (tpp q + tpp p)" by (rule punit.obd_imp_pbd)
        from keys_binomial_pbd[OF this] show "keys ?r = {lpp (punit.tail q) + lpp p, tpp (punit.tail q) + tpp p}"
          by (simp only: r_eq tpp_tail_q lpp_tpp)
      qed
    qed
  qed
qed

subsection \<open>Multiplication by Binomials\<close>

lemma lookup_times_binomial_1:
  assumes "is_proper_binomial p" and "u + tpp p = v + lpp p"
  shows "lookup (q * p) (v + lpp p) = lookup q v * lcf p + lookup q u * tcf p"
proof -
  from assms(1) obtain c d s t where obd: "punit.is_obd c s d t" and p_eq: "p = binomial c s d t"
    by (rule punit.is_proper_binomial_binomial_od)
  from obd have lpp_p: "lpp p = s" and lcf_p: "lcf p = c" and tpp_p: "tpp p = t" and tcf_p: "tcf p = d"
    unfolding p_eq 
    by (rule punit.lt_binomial, rule punit.lc_binomial, rule punit.tt_binomial, rule punit.tc_binomial)
  have eq1: "q * p = q * monomial c s + q * monomial d t"
    by (simp add: p_eq binomial_def algebra_simps)
  have eq2: "lookup (q * monomial d t) (v + lpp p) = lookup q u * d"
    by (simp add: assms(2)[symmetric] tpp_p lookup_times_monomial_right)
  show ?thesis unfolding eq1 lookup_add eq2 by (simp add: lpp_p lcf_p tpp_p tcf_p lookup_times_monomial_right)
qed

lemma lookup_times_binomial_2:
  assumes "is_proper_binomial p" and "\<not>(\<exists>u\<in>keys q. u + tpp p = v + lpp p)"
  shows "lookup (q * p) (v + lpp p) = lookup q v * lcf p"
proof (cases "\<exists>u. u + tpp p = v + lpp p")
  case True
  then obtain u where u: "u + tpp p = v + lpp p" ..
  with assms(1) have eq: "lookup (q * p) (v + lpp p) = lookup q v * lcf p + lookup q u * tcf p"
    by (rule lookup_times_binomial_1)
  have "u \<notin> keys q"
  proof
    assume "u \<in> keys q"
    with u have "\<exists>u\<in>(keys q). u + tpp p = v + lpp p" ..
    with assms(2) show False ..
  qed
  hence "lookup q u = 0" by (simp add: in_keys_iff)
  thus ?thesis unfolding eq by simp
next
  case False
  from assms(1) obtain c d s t where obd: "punit.is_obd c s d t" and p_eq: "p = binomial c s d t"
    by (rule punit.is_proper_binomial_binomial_od)
  from obd have lpp_p: "lpp p = s" and lcf_p: "lcf p = c" and tpp_p: "tpp p = t" and tcf_p: "tcf p = d"
    unfolding p_eq
    by (rule punit.lt_binomial, rule punit.lc_binomial, rule punit.tt_binomial, rule punit.tc_binomial)
  have eq1: "q * p = q * monomial c s + q * monomial d t"
    by (simp add: p_eq binomial_def algebra_simps)
  have "\<not> tpp p adds v + lpp p"
  proof
    assume "tpp p adds v + lpp p"
    then obtain u where u: "v + lpp p = tpp p + u" unfolding adds_def ..
    from False have "\<forall>u. u + tpp p \<noteq> v + lpp p" by simp
    hence "u + tpp p \<noteq> v + lpp p" ..
    with u show False by (simp add: ac_simps)
  qed
  hence eq2: "lookup (q * monomial d t) (v + lpp p) = 0" by (simp add: lpp_p tpp_p lookup_times_monomial_right)
  show ?thesis unfolding eq1 lookup_add eq2 by (simp add: lpp_p lcf_p tpp_p tcf_p lookup_times_monomial_right)
qed

lemma lookup_times_binomial_3:
  assumes "is_proper_binomial p" and "\<not>(\<exists>v\<in>(keys q). v + lpp p = u + tpp p)"
  shows "lookup (q * p) (u + tpp p) = lookup q u * tcf p"
proof (cases "\<exists>v. v + lpp p = u + tpp p")
  case True
  then obtain v where v: "v + lpp p = u + tpp p" ..
  hence u: "u + tpp p = v + lpp p" by simp
  with assms(1) have eq: "lookup (q * p) (v + lpp p) = lookup q v * lcf p + lookup q u * tcf p"
    by (rule lookup_times_binomial_1)
  have "v \<notin> keys q"
  proof
    assume "v \<in> keys q"
    with v have "\<exists>v\<in>(keys q). v + lpp p = u + tpp p" ..
    with assms(2) show False ..
  qed
  hence "lookup q v = 0" by (simp add: in_keys_iff)
  thus ?thesis unfolding u eq by simp
next
  case False
  from assms(1) obtain c d s t where obd: "punit.is_obd c s d t" and p_eq: "p = binomial c s d t"
    by (rule punit.is_proper_binomial_binomial_od)
  from obd have lpp_p: "lpp p = s" and lcf_p: "lcf p = c" and tpp_p: "tpp p = t" and tcf_p: "tcf p = d"
    unfolding p_eq
    by (rule punit.lt_binomial, rule punit.lc_binomial, rule punit.tt_binomial, rule punit.tc_binomial)
  have eq1: "q * p = q * monomial c s + q * monomial d t"
    by (simp add: p_eq binomial_def algebra_simps)
  have "\<not> lpp p adds u + tpp p"
  proof
    assume "lpp p adds u + tpp p"
    then obtain v where v: "u + tpp p = lpp p + v" unfolding adds_def ..
    from False have "\<forall>v. v + lpp p \<noteq> u + tpp p" by simp
    hence "v + lpp p \<noteq> u + tpp p" ..
    with v show False by (simp add: ac_simps)
  qed
  hence eq2: "lookup (q * monomial c s) (u + tpp p) = 0" by (simp add: lpp_p tpp_p lookup_times_monomial_right)
  show ?thesis unfolding eq1 lookup_add eq2 by (simp add: lpp_p lcf_p tpp_p tcf_p lookup_times_monomial_right)
qed

lemma times_binomial_lpp_not_in_keys:
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + lpp p \<notin> keys (q * p)"
  obtains v' where "v' \<in> keys q" and "v \<prec> v'" and "v' + tpp p = v + lpp p" and "lookup q v' * tcf p = -(lookup q v * lcf p)"
proof (cases "\<exists>v'\<in>(keys q). v' + tpp p = v + lpp p")
  case True
  then obtain v' where "v' \<in> keys q" and v': "v' + tpp p = v + lpp p" ..
  from \<open>v' \<in> keys q\<close> _ v' show ?thesis
  proof
    from assms(1) have "tpp p \<prec> lpp p" by (rule punit.lt_gr_tt_binomial)
    hence "v + tpp p \<prec> v + lpp p" by (rule plus_monotone_strict_left)
    also have "\<dots> = v' + tpp p" by (simp only: v')
    finally show "v \<prec> v'" by (rule ord_strict_canc)
  next
    from assms(1) v' have "lookup (q * p) (v + lpp p) = lookup q v * lcf p + lookup q v' * tcf p"
      by (rule lookup_times_binomial_1)
    moreover from assms(3) have "lookup (q * p) (v + lpp p) = 0" by (simp add: in_keys_iff)
    ultimately show "lookup q v' * tcf p = - (lookup q v * lcf p)" by (simp add: add_eq_0_iff) 
  qed
next
  case False
  with assms(1) have "lookup (q * p) (v + lpp p) = lookup q v * lcf p" by (rule lookup_times_binomial_2)
  moreover from assms(3) have "lookup (q * p) (v + lpp p) = 0" by (simp add: in_keys_iff)
  ultimately have "lookup q v * lcf p = 0" by simp
  hence "lookup q v = 0 \<or> lcf p = 0" by simp
  thus ?thesis
  proof
    assume "lookup q v = 0"
    hence "v \<notin> keys q" by (simp add: in_keys_iff)
    from this assms(2) show ?thesis ..
  next
    assume "lcf p = 0"
    from assms(1) have "p \<noteq> 0" by (rule proper_binomial_not_0)
    hence "lcf p \<noteq> 0" by (rule punit.lc_not_0)
    from this \<open>lcf p = 0\<close> show ?thesis ..
  qed
qed

lemma times_binomial_tpp_not_in_keys:
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + tpp p \<notin> keys (q * p)"
  obtains v' where "v' \<in> keys q" and "v' \<prec> v" and "v' + lpp p = v + tpp p" and "lookup q v' * lcf p = -(lookup q v * tcf p)"
proof (cases "\<exists>v'\<in>(keys q). v' + lpp p = v + tpp p")
  case True
  then obtain v' where "v' \<in> keys q" and v': "v' + lpp p = v + tpp p" ..
  from \<open>v' \<in> keys q\<close> _ v' show ?thesis
  proof
    from assms(1) have "tpp p \<prec> lpp p" by (rule punit.lt_gr_tt_binomial)
    hence "v' + tpp p \<prec> v' + lpp p" by (rule plus_monotone_strict_left)
    also have "\<dots> = v + tpp p" by (simp only: v')
    finally show "v' \<prec> v" by (rule ord_strict_canc)
  next
    from assms(1) v'[symmetric] have "lookup (q * p) (v' + lpp p) = lookup q v' * lcf p + lookup q v * tcf p"
      by (rule lookup_times_binomial_1)
    moreover from assms(3) have "lookup (q * p) (v' + lpp p) = 0" by (simp add: v'[symmetric] in_keys_iff)
    ultimately show "lookup q v' * lcf p = - (lookup q v * tcf p)" by (simp add: add_eq_0_iff) 
  qed
next
  case False
  with assms(1) have "lookup (q * p) (v + tpp p) = lookup q v * tcf p" by (rule lookup_times_binomial_3)
  moreover from assms(3) have "lookup (q * p) (v + tpp p) = 0" by (simp add: in_keys_iff)
  ultimately have "lookup q v * tcf p = 0" by simp
  hence "lookup q v = 0 \<or> tcf p = 0" by simp
  thus ?thesis
  proof
    assume "lookup q v = 0"
    hence "v \<notin> keys q" by (simp add: in_keys_iff)
    from this assms(2) show ?thesis ..
  next
    assume "tcf p = 0"
    from assms(1) have "p \<noteq> 0" by (rule proper_binomial_not_0)
    hence "tcf p \<noteq> 0" by (rule punit.tc_not_0)
    from this \<open>tcf p = 0\<close> show ?thesis ..
  qed
qed

lemma binomial_mult_shape_lpp':
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + lpp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "subpoly q' q" and "lpp q' = v" and "associated_poly p q'" and "tpp q' + tpp p \<in> keys (q * p)"
  using assms(2) assms(3)
proof (induct q arbitrary: thesis v rule: poly_mapping_except_induct')
  case step: (1 q)
  from \<open>is_proper_binomial p\<close> have "p \<noteq> 0" by (rule proper_binomial_not_0)
  let ?c = "lookup q v"
  from \<open>v \<in> keys q\<close> have "?c \<noteq> 0" by (simp add: in_keys_iff)
  have q_rec: "q = monomial ?c v + except q {v}" (is "q = ?m + ?q") by (rule plus_except)
  hence "q * p = (?m + ?q) * p" by simp
  also have "\<dots> = ?m * p + ?q * p" by (rule algebra_simps(17))
  also have "\<dots> = punit.monom_mult ?c v p + ?q * p" by (simp only: times_monomial_left)
  finally have qp_eq: "q * p = punit.monom_mult ?c v p + ?q * p" (is "_ = ?p + ?q * p") .
  have keys_m: "keys ?m = {v}" unfolding keys_of_monomial[OF \<open>?c \<noteq> 0\<close>] ..
  from \<open>?c \<noteq> 0\<close> have "?m \<noteq> 0" and lpp_m: "lpp ?m = v" and tpp_m: "tpp ?m = v"
    by (meson monomial_0D, rule punit.lt_monomial, rule punit.tt_monomial)
  let ?t = "v + tpp p"
  let ?s = "v + lpp p"
  from \<open>is_proper_binomial p\<close> have keys_p: "keys p = {lpp p, tpp p}" by (rule punit.keys_proper_binomial)
  hence "keys ?p = {?s, ?t}" unfolding punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>, of v p] by simp
  hence "?t \<in> keys ?p" by simp
  show ?case
  proof (cases "?t \<in> keys (q * p)")
    case True
    show ?thesis by (rule step(2), fact \<open>?m \<noteq> 0\<close>, rule monomial_subpoly, simp only: lpp_m,
                      rule associated_poly_monomial, simp only: tpp_m True)
  next
    case False
    with \<open>is_proper_binomial p\<close> \<open>v \<in> keys q\<close> obtain v' where "v' \<in> keys q" and "v' \<prec> v"
      and *: "v' + lpp p = ?t" and **: "lookup q v' * lcf p = -(?c * tcf p)"
      by (rule times_binomial_tpp_not_in_keys)
    from in_keys_plusI1[OF \<open>?t \<in> keys ?p\<close>, of "except q {v} * p"] False
      have "?t \<in> keys (?q * p)" unfolding qp_eq by blast
    from \<open>v' \<prec> v\<close> have "v' \<noteq> v" by simp
    with \<open>v' \<in> keys q\<close> have "v' \<in> keys ?q" by (simp add: keys_except)
    
    text \<open>Obtaining some @{term q'} from the induction hypothesis:\<close>
    from step(3) _ \<open>v' \<in> keys ?q\<close> \<open>?t \<in> keys (?q * p)\<close> obtain q'
      where "q' \<noteq> 0" and "subpoly q' ?q" and "lpp q' = v'" and assoc: "associated_poly p q'"
      and "tpp q' + tpp p \<in> keys (?q * p)"
      unfolding \<open>v' + lpp p = ?t\<close>[symmetric] by (rule step(1))
    from \<open>q' \<noteq> 0\<close> have "v' \<in> keys q'" unfolding \<open>lpp q' = v'\<close>[symmetric] by (rule punit.lt_in_keys)
    have "subpoly q' q" by (rule subpoly_trans, fact, rule except_subpoly)
    from * \<open>lpp q' = v'\<close> have ***: "lpp q' + lpp p = v + tpp p" by simp
    
    let ?q' = "?m + q'"
    
    text \<open>Properties of @{term ?q'}:\<close>
    have "v \<notin> keys ?q" by (simp add: keys_except)
    hence "v \<notin> keys q'" using subpoly_keys[OF \<open>subpoly q' ?q\<close>] by auto
    hence "keys ?m \<inter> keys q' = {}" and "lookup q' v = 0" by (simp add: keys_m, simp add: in_keys_iff)
    from this(1) have keys_q': "keys ?q' = {v} \<union> keys q'" unfolding keys_m[symmetric] by (rule keys_plus_eqI)
    have tpp_q': "tpp ?q' = tpp q'"
    proof (simp only: add.commute, rule punit.tt_plus_eqI, fact, simp only: tpp_m)
      have "tpp q' \<preceq> lpp q'" by (rule punit.lt_ge_tt)
      also from \<open>v' \<prec> v\<close> have "\<dots> \<prec> v" by (simp only: \<open>lpp q' = v'\<close>)
      finally show "tpp q' \<prec> v" .
    qed
    have "lpp (q' + ?m) = lpp ?m" by (rule punit.lt_plus_eqI, simp only: lpp_m \<open>lpp q' = v'\<close> \<open>v' \<prec> v\<close>)
    hence lpp_q': "lpp ?q' = v" by (simp only: add.commute lpp_m)
    have lcf_q': "lcf ?q' = ?c" by (simp add: punit.lc_def lpp_q' lookup_add lookup_single, fact)
    have tail_q': "punit.tail ?q' = q'"
      by (rule poly_mapping_eqI, simp add: punit.lookup_tail_2 lpp_q' lookup_add lookup_single \<open>lookup q' v = 0\<close>)
    have "?q' \<noteq> 0"
    proof
      assume "?q' = 0"
      hence "keys ?q' = {}" by simp
      with keys_q' show False by simp
    qed

    show ?thesis
    proof (rule step(2), fact \<open>?q' \<noteq> 0\<close>, rule plus_subpolyI, rule monomial_subpoly, fact, fact, fact)
      show "associated_poly p ?q'"
      proof (rule associated_poly_recI, simp_all only: tail_q' lpp_q' lcf_q',
              simp only: has_bounded_keys_def keys_q')
        from \<open>v' \<in> keys q'\<close> have "keys q' \<noteq> {}" by auto
        with finite_keys[of q'] have "card (keys q') > 0" by (simp add: card_gt_0_iff)
        with \<open>v \<notin> keys q'\<close> have "card ({v} \<union> keys q') > 1" by simp
        thus "\<not> card ({v} \<union> keys q') \<le> 1" by simp
      next
        from *** show "associated p v (lpp q') 1" by (simp only: associated_1)
      next
        from subpolyE[OF \<open>subpoly q' q\<close> \<open>v' \<in> keys q'\<close>] have "lcf q' = lookup q v'"
          by (simp add: punit.lc_def \<open>lpp q' = v'\<close>)
        with ** show "lookup q v * tcf p + lcf q' * lcf p = 0" by simp
      qed fact
    next
      have eq: "q * p = ?q * p + punit.monom_mult ?c v p" unfolding qp_eq by simp
      from \<open>q' \<noteq> 0\<close> assoc have "associated p (lpp q' + lpp p) (tpp q' + tpp p) (card (keys q'))"
        by (rule associated_poly_times_binomial_associated)
      hence "associated p ?t (tpp q' + tpp p) (card (keys q'))" by (simp only: ***)
      with assms(1) have "tpp ?q' + tpp p \<notin> keys ?p" unfolding \<open>keys ?p = {?s, ?t}\<close> tpp_q'
      proof (rule associated_tpp_not_in_keys)
        from \<open>v' \<in> keys q'\<close> finite_keys[of q'] show "card (keys q') \<noteq> 0" by auto
      qed
      with \<open>tpp q' + tpp p \<in> keys (?q * p)\<close> show "tpp ?q' + tpp p \<in> keys (q * p)"
        unfolding tpp_q' eq by (rule in_keys_plusI1)
    qed
  qed
qed
  
lemma binomial_mult_shape_lpp:
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + lpp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "subpoly q' q" and "lpp q' = v" and "keys (q' * p) = {v + lpp p, tpp q' + tpp p}"
    and "tpp q' + tpp p \<in> keys (q * p)"
proof -
  from assms obtain q' where 1: "q' \<noteq> 0" and 2: "subpoly q' q" and 3: "lpp q' = v" and 4: "associated_poly p q'"
    and 5: "tpp q' + tpp p \<in> keys (q * p)" by (rule binomial_mult_shape_lpp')
  from 1 2 3 _ 5 show ?thesis
  proof
    from assms(1) 1 4 show "keys (q' * p) = {v + lpp p, tpp q' + tpp p}" unfolding 3[symmetric]
      by (rule associated_poly_times_binomial_keys)
  qed
qed

text \<open>If the following lemma shall be proved in the same style as the one above, the analogue of
  @{thm associated_poly_recI} for @{term higher} instead of @{term tail} is needed.\<close>
lemma binomial_mult_shape_tpp:
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + tpp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "subpoly q' q" and "tpp q' = v" and "keys (q' * p) = {lpp q' + lpp p, v + tpp p}"
    and "lpp q' + lpp p \<in> keys (q * p)"
  using assms(2) assms(3)
proof (induct "card (keys q)" arbitrary: thesis q v)
  case base: 0
  from base(1) finite_keys[of q] have "keys q = {}" by simp
  with base(3) show ?case by simp
next
  case ind: (Suc n)
  from \<open>is_proper_binomial p\<close> have "p \<noteq> 0" by (rule proper_binomial_not_0)
  let ?c = "lookup q v"
  from \<open>v \<in> keys q\<close> have "?c \<noteq> 0" by (simp add: in_keys_iff)
  have q_rec: "q = monomial ?c v + except q {v}" (is "q = ?m + ?q") by (rule plus_except)
  hence "q * p = (?m + ?q) * p" by simp
  also have "\<dots> = ?m * p + ?q * p" by (rule algebra_simps(17))
  also have "\<dots> = punit.monom_mult ?c v p + ?q * p" by (simp only: times_monomial_left)
  finally have qp_eq: "q * p = punit.monom_mult ?c v p + ?q * p" (is "q * p = ?p + ?q * p") .
  from \<open>?c \<noteq> 0\<close> have lpp_m: "lpp ?m = v" and tpp_m: "tpp ?m = v" and keys_m: "keys ?m = {v}" and "?m \<noteq> 0"
    by (rule punit.lt_monomial, rule punit.tt_monomial, rule keys_of_monomial, meson monomial_0D)
  let ?t = "v + tpp p"
  let ?s = "v + lpp p"
  from \<open>is_proper_binomial p\<close> have keys_p: "keys p = {lpp p, tpp p}"
    by (simp add: proper_binomial_imp_binomial punit.keys_binomial)
  hence "keys ?p = {?s, ?t}" unfolding punit.keys_monom_mult[OF \<open>lookup q v \<noteq> 0\<close>, of v p] by simp
  hence "?s \<in> keys ?p" by simp
  show ?case
  proof (cases "?s \<in> keys (q * p)")
    case True
    show ?thesis
    proof (rule ind(3), fact \<open>?m \<noteq> 0\<close>, rule monomial_subpoly, fact, unfold keys_m lpp_m)
      show "keys (?m * p) = {v + lpp p, ?t}"
        unfolding times_monomial_left punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>] keys_p by simp
    next
      from True show "v + lpp p \<in> keys (q * p)" .
    qed
  next
    case False
    with \<open>is_proper_binomial p\<close> \<open>v \<in> keys q\<close> obtain v' where "v' \<in> keys q" and "v \<prec> v'"
      and *: "v' + tpp p = ?s" and **: "lookup q v' * tcf p = -(?c * lcf p)"
      by (rule times_binomial_lpp_not_in_keys)
    from in_keys_plusI1[OF \<open>?s \<in> keys ?p\<close>, of "except q {v} * p"] False
    have "?s \<in> keys (?q * p)" unfolding qp_eq by blast
    from \<open>v \<prec> v'\<close> have "v' \<noteq> v" by simp
    with \<open>v' \<in> keys q\<close> have "v' \<in> keys ?q" by (simp add: keys_except)
    from \<open>v \<in> keys q\<close> ind(2) have "n = card (keys ?q)" unfolding keys_except using finite_keys[of q]
      by simp
    from this _ \<open>v' \<in> keys ?q\<close> \<open>?s \<in> keys (?q * p)\<close> obtain q'
      where "q' \<noteq> 0" and "subpoly q' ?q" and "tpp q' = v'"
      and ***: "keys (q' * p) = {lpp q' + lpp p, ?s}" and "lpp q' + lpp p \<in> keys (?q * p)"
      unfolding \<open>v' + tpp p = ?s\<close>[symmetric] by (rule ind(1))
    from \<open>q' \<noteq> 0\<close> have "v' \<in> keys q'" unfolding \<open>tpp q' = v'\<close>[symmetric] by (rule punit.tt_in_keys)
    let ?q' = "q' + ?m"
    have "v \<notin> keys ?q" unfolding keys_except by simp
    hence "v \<notin> keys q'" using subpoly_keys[OF \<open>subpoly q' ?q\<close>] by auto
    hence "keys q' \<inter> keys ?m = {}" unfolding keys_m by simp
    hence keys_q': "keys ?q' = keys q' \<union> {v}" unfolding keys_m[symmetric] by (rule keys_plus_eqI)
    from \<open>v \<notin> keys q'\<close> finite_keys[of q'] have card_keys_q': "card (keys ?q') = Suc (card (keys q'))"
      unfolding keys_q' by simp
    have "subpoly q' q" by (rule subpoly_trans, fact, rule except_subpoly)
    note \<open>v \<prec> v'\<close>
    also have "v' = tpp q'" by (simp only: \<open>tpp q' = v'\<close>)
    also have "\<dots> \<preceq> lpp q'" by (rule punit.lt_ge_tt)
    finally have "v \<prec> lpp q'" .
    have "?q' \<noteq> 0"
    proof
      assume "?q' = 0"
      hence "keys ?q' = {}" by simp
      with keys_q' show False by simp
    qed
    have lpp_q': "lpp ?q' = lpp q'"
    by (simp only: add.commute[of q'], rule punit.lt_plus_eqI, simp only: lpp_m, fact)
    show ?thesis
    proof (rule ind(3), fact \<open>?q' \<noteq> 0\<close>, rule plus_subpolyI, fact, rule monomial_subpoly, fact)
      from \<open>?m \<noteq> 0\<close> have "tpp ?q' = tpp ?m"
      proof (simp only: add.commute[of q'], rule punit.tt_plus_eqI, simp only: tpp_m \<open>tpp q' = v'\<close>)
        show "v \<prec> v'" by fact
      qed
      thus "tpp ?q' = v" by (simp add: tpp_m)
    next
      have eq1: "?q' * p = q' * p + punit.monom_mult ?c v p"
        by (simp add: algebra_simps(17) times_monomial_left)
      have eq2: "lookup (punit.monom_mult ?c v p) ?s = ?c * lcf p"
        by (simp add: punit.lc_def punit.lookup_monom_mult)
      from \<open>subpoly q' q\<close> \<open>v' \<in> keys q'\<close> have "lookup q' v' = lookup q v'" by (rule subpolyE)
      have "lookup (q' * p) (v' + tpp p) = (lookup q' v') * tcf p"
      proof (rule lookup_times_binomial_3, fact assms(1), rule)
        assume "\<exists>w\<in>(keys q'). w + lpp p = v' + tpp p"
        then obtain w where "w \<in> keys q'" and "w + lpp p = v' + tpp p" ..
        hence "w = v" unfolding * by simp
        from \<open>v \<notin> keys q'\<close> \<open>w \<in> keys q'\<close> show False unfolding \<open>w = v\<close> ..
      qed
      also have "\<dots> = (lookup q v') * tcf p" unfolding subpolyE[OF \<open>subpoly q' q\<close> \<open>v' \<in> keys q'\<close>] ..
      also from ** have "\<dots> = -(?c * lcf p)" .
      finally have "0 = lookup (q' * p) (v' + tpp p) + ?c * lcf p" by simp
      also have "\<dots> = lookup (?q' * p) ?s" unfolding eq1 eq2 lookup_add \<open>v' + tpp p = ?s\<close> ..
      finally have "lookup (?q' * p) ?s = 0" by simp
      hence "?s \<notin> keys (?q' * p)" by (simp add: in_keys_iff)
      show "keys (?q' * p) = {lpp ?q' + lpp p, ?t}" unfolding lpp_q'
      proof
        have "keys (?q' * p) \<subseteq> keys (q' * p) \<union> keys (punit.monom_mult ?c v p)" unfolding eq1
          by (rule Poly_Mapping.keys_add)
        also have "\<dots> = {lpp q' + lpp p, ?s} \<union> {?s, ?t}"
          by (simp add: punit.keys_monom_mult[OF \<open>?c \<noteq> 0\<close>] *** keys_p)
        finally have "keys (?q' * p) \<subseteq> {lpp q' + lpp p, ?s, ?t}" by auto
        with \<open>?s \<notin> keys (?q' * p)\<close> show "keys (?q' * p) \<subseteq> {lpp q' + lpp p, ?t}" by auto
      next
        from assms(1) have "tpp p \<prec> lpp p" by (rule punit.lt_gr_tt_binomial)
        hence "?t \<prec> ?s" by (rule plus_monotone_strict_left)
        also from \<open>v \<prec> lpp q'\<close> have "\<dots> \<preceq> lpp q' + lpp p" by (simp add: plus_monotone)
        finally have uneq: "lpp q' + lpp p \<noteq> ?t" by simp
        have "lpp q' + lpp p \<in> keys (?q' * p)" unfolding eq1
        proof (rule in_keys_plusI1, simp add: ***, simp add: \<open>keys ?p = {?s, ?t}\<close>, rule conjI, rule)
          assume "lpp q' = v"
          from \<open>q' \<noteq> 0\<close> have "lpp q' \<in> keys q'" by (rule punit.lt_in_keys)
          with \<open>v \<notin> keys q'\<close> show False unfolding \<open>lpp q' = v\<close> ..
        qed (fact uneq)
        moreover have "?t \<in> keys (?q' * p)" unfolding eq1
        proof (rule in_keys_plusI2, simp add: \<open>keys ?p = {?s, ?t}\<close>,
                simp add: ***, rule conjI, fact uneq[symmetric])
          from \<open>tpp p \<prec> lpp p\<close> show "tpp p \<noteq> lpp p" by simp
        qed
        ultimately show "{lpp q' + lpp p, ?t} \<subseteq> keys (?q' * p)" by simp
      qed
    next
      have eq: "q * p = ?q * p + punit.monom_mult ?c v p" unfolding qp_eq by simp
      have "lpp q' + lpp p \<notin> keys ?p" unfolding \<open>keys ?p = {?s, ?t}\<close>
      proof
        assume "lpp q' + lpp p \<in> {?s, ?t}"
        hence "lpp q' + lpp p = ?s \<or> lpp q' + lpp p = ?t" by auto
        thus False
        proof
          assume "lpp q' + lpp p = ?s"
          hence "lpp q' = v" by (simp only: add_right_cancel)
          with \<open>v \<prec> lpp q'\<close> show False by simp
        next
          assume "lpp q' + lpp p = ?t"
          from \<open>v \<prec> lpp q'\<close> have "?t \<prec> lpp q' + tpp p" by (rule plus_monotone_strict)
          also have "\<dots> \<preceq> lpp q' + lpp p" by (rule plus_monotone_left, rule punit.lt_ge_tt)
          finally show False by (simp add: \<open>lpp q' + lpp p = ?t\<close>)
        qed
      qed
      with \<open>lpp q' + lpp p \<in> keys (?q * p)\<close> show "lpp ?q' + lpp p \<in> keys (q * p)" unfolding eq lpp_q'
        by (rule in_keys_plusI1)
    qed
  qed
qed

lemma binomial_mult_shape_tpp':
  assumes "is_proper_binomial (p::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::idom)" and "v \<in> keys q" and "v + tpp p \<in> keys (q * p)"
  obtains q' where "q' \<noteq> 0" and "subpoly q' q" and "tpp q' = v" and "associated_poly p q'" and "lpp q' + lpp p \<in> keys (q * p)"
proof -
  from assms obtain q' where 1: "q' \<noteq> 0" and 2: "subpoly q' q" and 3: "tpp q' = v"
    and 4: "keys (q' * p) = {lpp q' + lpp p, v + tpp p}" and 5: "lpp q' + lpp p \<in> keys (q * p)"
    by (rule binomial_mult_shape_tpp)
  from 1 2 3 _ 5 show ?thesis
  proof
    from assms(1) 4 show "associated_poly p q'" unfolding 3[symmetric]
      by (rule times_binomial_keys_associated_poly)
  qed
qed

end (* fun_powerprod *)

end (* theory *)
