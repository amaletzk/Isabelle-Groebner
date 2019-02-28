section \<open>Two Polynomials\<close>

theory Two_Polynomials
  imports Binomials Binom_Mult Power_Products_PM
begin

(* FIXME: Theory "Binom_Mult" is only needed because of constant "associated". Restructuring that
  theory could thereby save the import. *)

subsection \<open>Preliminaries\<close>

lemma idealI_2: "q1 * f1 + q2 * f2 \<in> ideal {f1, f2::'a::comm_powerprod \<Rightarrow>\<^sub>0 'b::comm_ring_1}"
  by (rule ideal.span_add, rule ideal.span_scale, rule ideal.span_base,
      simp, rule ideal.span_scale, rule ideal.span_base, simp)

lemma idealE_2:
  assumes "f \<in> ideal {f1, f2}"
  obtains q1 q2 where "f = q1 * f1 + q2 * f2"
  using assms
proof (induct f arbitrary: thesis rule: ideal.span_induct')
  case base
  show ?case
  proof (rule base)
    show "0 = 0 * f1 + 0 * f2" by simp
  qed
next
  case (step f' c g)
  obtain q1 q2 where f'_eq: "f' = q1 * f1 + q2 * f2" by (rule step(2))
  from step(3) have "g = f1 \<or> g = f2" by simp
  thus ?case
  proof
    assume "g = f1"
    show ?case
    proof (rule step(5))
      show "f' + c * g = (q1 + c) * f1 + q2 * f2" by (simp add: f'_eq \<open>g = f1\<close> algebra_simps)
    qed
  next
    assume "g = f2"
    show ?case
    proof (rule step(5))
      show "f' + c * g = q1 * f1 + (q2 + c) * f2" by (simp add: f'_eq \<open>g = f2\<close> algebra_simps)
    qed
  qed
qed

lemma ideal_iff_2:
  "f \<in> ideal {f1, f2} \<longleftrightarrow> (\<exists>q1 q2. f = q1 * f1 + q2 * (f2::'a::comm_powerprod \<Rightarrow>\<^sub>0 'b::comm_ring_1))"
proof
  assume "f \<in> ideal {f1, f2}"
  then obtain q1 q2 where "f = q1 * f1 + q2 * f2" by (rule idealE_2)
  show "\<exists>q1 q2. f = q1 * f1 + q2 * f2" by (intro exI, fact)
next
  assume "\<exists>q1 q2. f = q1 * f1 + q2 * f2"
  then obtain q1 q2 where f_eq: "f = q1 * f1 + q2 * f2" by auto
  show "f \<in> ideal {f1, f2}" unfolding f_eq by (rule idealI_2)
qed

lemma map_scale_binomial:
  "a \<cdot> binomial c s d t = binomial (a * c) s (a * (d::_::semiring_0)) (t::_::comm_powerprod)"
  by (simp add: punit.map_scale_eq_monom_mult punit.monom_mult_binomial)

lemma map_scale_two_left: "(2::_::semiring_1) \<cdot> v = v + v"
proof -
  have "2 \<cdot> v = (1 + 1) \<cdot> v" by simp
  also have "\<dots> = v + v" by (simp only: map_scale_distrib_right map_scale_one_left)
  finally show ?thesis .
qed

definition is_nat_pm_pair :: "(('x \<Rightarrow>\<^sub>0 'b) * ('x \<Rightarrow>\<^sub>0 'b::floor_ceiling)) \<Rightarrow> bool" where
  "is_nat_pm_pair pp = (is_nat_pm (fst pp) \<and> is_nat_pm (snd pp))"

definition is_int_pm_pair :: "(('x \<Rightarrow>\<^sub>0 'b) * ('x \<Rightarrow>\<^sub>0 'b::floor_ceiling)) \<Rightarrow> bool" where
  "is_int_pm_pair pp = (is_int_pm (fst pp) \<and> is_int_pm (snd pp))"
  
lemma is_nat_pm_pairI: "is_nat_pm (fst pp) \<Longrightarrow> is_nat_pm (snd pp) \<Longrightarrow> is_nat_pm_pair pp"
  unfolding is_nat_pm_pair_def ..
    
lemma is_nat_pm_pairD:
  assumes "is_nat_pm_pair pp"
  shows "is_nat_pm (fst pp)" and "is_nat_pm (snd pp)"
  using assms by (simp_all add: is_nat_pm_pair_def)

lemma is_nat_pm_pair_swap [iff]: "is_nat_pm_pair (prod.swap pp) \<longleftrightarrow> is_nat_pm_pair pp"
  by (auto simp: is_nat_pm_pair_def)

lemma is_int_pm_pairI: "is_int_pm (fst pp) \<Longrightarrow> is_int_pm (snd pp) \<Longrightarrow> is_int_pm_pair pp"
  unfolding is_int_pm_pair_def ..
    
lemma is_int_pm_pairD:
  assumes "is_int_pm_pair pp"
  shows "is_int_pm (fst pp)" and "is_int_pm (snd pp)"
  using assms by (simp_all add: is_int_pm_pair_def)
    
lemma nat_pm_pair_is_int_pm_pair: "is_nat_pm_pair pp \<Longrightarrow> is_int_pm_pair pp"
  by (auto intro: is_int_pm_pairI dest: is_nat_pm_pairD nat_pm_is_int_pm)

abbreviation "rat \<equiv> rat_of_nat"

type_synonym 'x point = "('x \<Rightarrow>\<^sub>0 rat)"

context pm_powerprod
begin

lemma binomial_lp_in_ideal_iff:
  assumes "f \<in> ideal F" and "is_binomial f"
  shows "monomial 1 (lp f) \<in> ideal F \<longleftrightarrow> monomial (1::_::field) (tp f) \<in> ideal F"
proof (cases "is_monomial f")
  case True
  hence "lp f = tp f" by (rule punit.lt_eq_tt_monomial)
  thus ?thesis by simp
next
  case False
  with assms(2) have "is_proper_binomial f" by (simp add: is_binomial_alt)
  hence "tp f \<prec> lp f" by (rule punit.lt_gr_tt_binomial)
  hence "lp f \<noteq> tp f" by simp
  from assms(2) have "keys f = {lp f, tp f}" by (rule punit.keys_binomial)
  moreover have "monomial 1 u \<in> ideal F" if "monomial 1 v \<in> ideal F" and "keys f = {u, v}" for u v
  proof -
    from \<open>keys f = {lp f, tp f}\<close> that(2) \<open>lp f \<noteq> tp f\<close> have "u \<noteq> v" by auto
    hence "monomial (lookup f u) u + monomial (lookup f v) v = f"
      by (auto intro!: poly_mapping_eqI simp: lookup_add lookup_single when_def \<open>keys f = {u, v}\<close>)
    moreover define c where "c = lookup f u"
    moreover define d where "d = lookup f v"
    ultimately have f: "f = monomial c u + punit.monom_mult d 0 (monomial 1 v)"
      by (simp add: punit.monom_mult_monomial)
    from that(1) have "punit.monom_mult d 0 (monomial 1 v) \<in> ideal F"
      by (rule punit.pmdl_closed_monom_mult[simplified])
    with assms(1) have "f - punit.monom_mult d 0 (monomial 1 v) \<in> ideal F" by (rule ideal.span_diff)
    hence "monomial c u \<in> ideal F" by (simp add: f)
    hence "punit.monom_mult (1 / c) 0 (monomial c u) \<in> ideal F"
      by (rule punit.pmdl_closed_monom_mult[simplified])
    moreover have "c \<noteq> 0" by (simp add: c_def \<open>keys f = {u, v}\<close>)
    ultimately show ?thesis by (simp add: punit.monom_mult_monomial)
  qed
  ultimately show ?thesis by blast
qed

lemma lem_3_3_12:
  assumes "f \<in> ideal F" and "f' \<in> ideal F" and "is_proper_binomial f" and "monomial 1 (tp f) \<notin> ideal F"
    and "keys f = keys f'"
  obtains c where "c \<noteq> (0::_::field)" and "f = punit.monom_mult c 0 f'"
proof -
  define c where "c = lc f / lc f'"
  from assms(3, 5) have f'_pbinomial: "is_proper_binomial f'" by (simp only: is_proper_binomial_def)
  hence "f' \<noteq> 0" by (rule proper_binomial_not_0)
  hence "lc f' \<noteq> 0" by (rule punit.lc_not_0)
  hence eq1: "c * lc f' = lc f" by (simp add: c_def)
  from f'_pbinomial have "binomial (lc f') (lp f') (tc f') (tp f') = f'" by (rule punit.binomial_eq_itself)
  moreover from assms(5) have "lp f' = lp f"
    by (metis lookup_zero not_in_keys_iff_lookup_eq_zero punit.lt_def punit.lt_in_keys)
  moreover from assms(5) have "tp f' = tp f"
    by (metis lookup_zero not_in_keys_iff_lookup_eq_zero punit.tt_def punit.tt_in_keys)
  ultimately have f': "binomial (lc f') (lp f) (tc f') (tp f) = f'" by simp
  also note assms(2)
  finally have "monomial c 0 * binomial (lc f') (lp f) (tc f') (tp f) \<in> ideal F"
    by (rule ideal.span_scale)
  with \<open>lc f' \<noteq> 0\<close> have 1: "binomial (lc f) (lp f) (c * tc f') (tp f) \<in> ideal F"
    by (simp add: times_monomial_left punit.monom_mult_binomial c_def)
  from assms(3) have "binomial (lc f) (lp f) (tc f) (tp f) = f" by (rule punit.binomial_eq_itself)
  also note assms(1)
  finally have "binomial (lc f) (lp f) (tc f) (tp f) - binomial (lc f) (lp f) (c * tc f') (tp f) \<in> ideal F"
    using 1 by (rule ideal.span_diff)
  hence 2: "monomial (tc f - c * tc f') (tp f) \<in> ideal F" by (simp add: binomial_def single_diff)
  have eq2: "c * tc f' = tc f"
  proof (rule ccontr)
    assume "c * tc f' \<noteq> tc f"
    hence "tc f - c * tc f' \<noteq> 0" by simp
    moreover from 2 have "monomial (1 / (tc f - c * tc f')) 0 * monomial (tc f - c * tc f') (tp f) \<in> ideal F"
      by (rule ideal.span_scale)
    ultimately have "monomial 1 (tp f) \<in> ideal F" by (simp add: times_monomial_monomial)
    with assms(4) show False ..
  qed
  show ?thesis
  proof
    from assms(3) have "f \<noteq> 0" by (rule proper_binomial_not_0)
    hence "lc f \<noteq> 0" by (rule punit.lc_not_0)
    with \<open>lc f' \<noteq> 0\<close> show "c \<noteq> 0" by (simp add: c_def)
  next
    have "punit.monom_mult c 0 f' = punit.monom_mult c 0 (binomial (lc f') (lp f) (tc f') (tp f))"
      by (simp only: f')
    also have "\<dots> = binomial (lc f) (lp f) (tc f) (tp f)"
      by (simp add: punit.monom_mult_binomial eq1 eq2)
    also have "\<dots> = f" by fact
    finally show "f = punit.monom_mult c 0 f'" by (rule sym)
  qed
qed

lemma map_scale_mono:
  assumes "m \<le> n"
  shows "m \<cdot> t \<preceq> n \<cdot> t"
proof -
  have "m \<cdot> t \<preceq> m \<cdot> t + (n - m) \<cdot> t" using zero_min plus_monotone_left by fastforce
  also have "\<dots> = (m + (n - m)) \<cdot> t" by (simp only: map_scale_distrib_right)
  also from assms have "\<dots> = n \<cdot> t" by simp
  finally show ?thesis .
qed

lemma map_scale_mono_left:
  assumes "s \<preceq> t"
  shows "m \<cdot> s \<preceq> m \<cdot> t"
proof (induct m)
  case 0
  show ?case by simp
next
  case (Suc m)
  have "Suc m \<cdot> s = (m + 1) \<cdot> s" by simp
  also have "\<dots> = m \<cdot> s + s" by (simp only: map_scale_distrib_right map_scale_one_left)
  also from Suc have "\<dots> \<preceq> m \<cdot> t + s" by (rule plus_monotone)
  also from assms have "\<dots> \<preceq> m \<cdot> t + t" by (rule plus_monotone_left)
  also have "\<dots> = (m + 1) \<cdot> t" by (simp only: map_scale_distrib_right map_scale_one_left)
  also have "\<dots> = Suc m \<cdot> t" by simp
  finally show ?case .
qed

lemma map_scale_mono_strict:
  assumes "m < n" and "t \<noteq> 0"
  shows "m \<cdot> t \<prec> n \<cdot> t"
proof -
  from assms(1) have "m \<le> n" by simp
  hence "m \<cdot> t \<preceq> n \<cdot> t" by (rule map_scale_mono)
  moreover have "m \<cdot> t \<noteq> n \<cdot> t"
  proof
    from assms(2) obtain x where "0 < lookup t x" using aux by auto
    assume "m \<cdot> t = n \<cdot> t"
    hence "lookup (m \<cdot> t) x = lookup (n \<cdot> t) x" by simp
    with \<open>0 < lookup t x\<close> assms(1) show False by simp
  qed
  ultimately show ?thesis by simp
qed

lemma map_scale_mono_strict_left:
  assumes "s \<prec> t" and "0 < m"
  shows "m \<cdot> s \<prec> m \<cdot> t"
proof -
  from assms(1) have "s \<preceq> t" by simp
  hence "m \<cdot> s \<preceq> m \<cdot> t" by (rule map_scale_mono_left)
  moreover have "m \<cdot> s \<noteq> m \<cdot> t"
  proof
    from assms(1) have "s \<noteq> t" by simp
    then obtain x where "lookup s x \<noteq> lookup t x" by (meson poly_mapping_eqI)
    with assms(2) have "lookup (m \<cdot> s) x \<noteq> lookup (m \<cdot> t) x" by simp
    moreover assume "m \<cdot> s = m \<cdot> t"
    ultimately show False by simp
  qed
  ultimately show ?thesis by simp
qed

definition poly_point :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('x point \<times> 'x point)" where
  "poly_point p = (of_nat_pm (lp p), of_nat_pm (tp p))"

definition vect :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('x point)"
  where "vect p = fst (poly_point p) - snd (poly_point p)"

definition pos_comps :: "'x point \<Rightarrow> 'x point" ("(_\<^sub>+)" [1000] 999)
  where "pos_comps p = lcs p 0"

definition neg_comps :: "'x point \<Rightarrow> 'x point" ("(_\<^sub>-)" [1000] 999)
  where "neg_comps p = lcs (- p) 0"

lemma fst_poly_point: "fst (poly_point p) = of_nat_pm (lp p)"
  by (simp add: poly_point_def)
    
lemma snd_poly_point: "snd (poly_point p) = of_nat_pm (tp p)"
  by (simp add: poly_point_def)

lemma poly_point_is_nat_pm_pair: "is_nat_pm_pair (poly_point p)"
  unfolding poly_point_def by (rule is_nat_pm_pairI, simp_all, (rule of_nat_pm_is_nat_pm)+)

lemma poly_point_is_int_pm_pair: "is_int_pm_pair (poly_point p)"
  using poly_point_is_nat_pm_pair by (rule nat_pm_pair_is_int_pm_pair)

lemma swap_poly_point_not_eq:
  assumes "is_proper_binomial p"
  shows "prod.swap (poly_point p) \<noteq> poly_point q"
proof
  assume "prod.swap (poly_point p) = poly_point q"
  hence 1: "lp p = tp q" and 2: "tp p = lp q" by (simp_all add: poly_point_def)
  from assms(1) have "tp p \<prec> lp p" by (rule punit.lt_gr_tt_binomial)
  hence "lp q \<prec> tp q" by (simp only: 1 2)
  with punit.lt_ge_tt[of q] show False by simp
qed

corollary swap_poly_point_not_eq':
  assumes "is_proper_binomial q"
  shows "prod.swap (poly_point p) \<noteq> poly_point q"
proof
  assume *: "prod.swap (poly_point p) = poly_point q"
  from assms have "prod.swap (poly_point q) \<noteq> poly_point p" by (rule swap_poly_point_not_eq)
  moreover from *[symmetric] have "prod.swap (poly_point q) = poly_point p" by simp
  ultimately show False ..
qed

lemma fst_eq_snd_poly_point_iff: "fst (poly_point p) = snd (poly_point p) \<longleftrightarrow> card (keys p) \<le> 1"
proof -
  have "fst (poly_point p) = snd (poly_point p) \<longleftrightarrow> lp p = tp p"
    by (simp add: poly_point_def)
  also have "\<dots> \<longleftrightarrow> card (keys p) \<le> 1" by (simp only: punit.lt_eq_tt_iff has_bounded_keys_def)
  finally show ?thesis .
qed

lemma vect_alt: "vect p = of_nat_pm (lp p) - of_nat_pm (tp p)"
  by (simp only: vect_def fst_poly_point snd_poly_point)

lemma vect_is_int_pm: "is_int_pm (vect p)"
  by (simp add: vect_def is_int_pm_pairD[OF poly_point_is_int_pm_pair] is_int_pm_pairD minus_is_int_pm)

lemma associated_alt_rat:
  "associated q s t k \<longleftrightarrow> of_nat_pm s = ((of_nat_pm t)::'x point) + rat k \<cdot> vect q" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R unfolding vect_alt
  proof (rule poly_mapping_eqI, simp add: lookup_of_nat_pm lookup_add lookup_minus)
    fix x
    from \<open>?L\<close> have "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x"
      by (rule associatedD_lookup)
    hence "rat (lookup t x + k * lookup (lp q) x) = rat (lookup s x + k * lookup (tp q) x)" by simp
    thus "rat (lookup s x) = rat (lookup t x) + rat k * (rat (lookup (lp q) x) - rat (lookup (tp q) x))"
      by (simp add: right_diff_distrib)
  qed
next
  assume ?R
  show ?L
  proof (rule associatedI_lookup)
    fix x
    from \<open>?R\<close> have "lookup (of_nat_pm t + rat k \<cdot> vect q) x = lookup (of_nat_pm s) x" by simp
    hence "rat (lookup t x) + rat k * (rat (lookup (lp q) x) - rat (lookup (tp q) x)) = rat (lookup s x)"
      by (simp add: vect_alt lookup_of_nat_pm lookup_add lookup_minus)
    hence "rat (lookup t x + k * lookup (lp q) x) = rat (lookup s x + k * lookup (tp q) x)"
      by (simp add: right_diff_distrib)
    thus "lookup t x + k * lookup (lp q) x = lookup s x + k * lookup (tp q) x" using of_nat_eq_iff by blast 
  qed
qed

lemma pos_minus_neg_comps [simp]: "p\<^sub>+ - p\<^sub>- = p"
  by (rule poly_mapping_eqI) (simp add: pos_comps_def neg_comps_def lookup_minus lookup_lcs_fun lcs_fun_def)

lemma pos_comps_is_int_pm: "is_int_pm p \<Longrightarrow> is_int_pm (p\<^sub>+)"
  unfolding pos_comps_def by (intro lcs_is_int_pm zero_is_int_pm)

lemma pos_comps_ge_zero: "0 \<unlhd> p\<^sub>+"
  unfolding pos_comps_def by (rule lcs_ge_pm)

lemma pos_comps_ge_self: "p \<unlhd> p\<^sub>+"
  unfolding pos_comps_def by (rule lcs_ge_pm)

lemma pos_comps_is_nat_pm: "is_int_pm p \<Longrightarrow> is_nat_pm (p\<^sub>+)"
  by (auto intro: int_pm_is_nat_pmI pos_comps_is_int_pm pos_comps_ge_zero zero_is_nat_pm)

lemma pos_comps_zero [simp]: "0\<^sub>+ = 0"
  by (simp add: pos_comps_def lcs_ge_pm(1) lcs_le_pm le_pm_antisym)

lemma pos_comps_zero_iff [iff]: "p\<^sub>+ = 0 \<longleftrightarrow> p \<unlhd> 0"
  by (metis lcs_comm lcs_ge_pm(1) lcs_le_pm le_pm_antisym le_pm_refl pos_comps_def)

lemma pos_comps_uminus [simp]: "(- p)\<^sub>+ = p\<^sub>-"
  by (simp only: pos_comps_def neg_comps_def)

lemma pos_comps_plus_le: "(p + q)\<^sub>+ \<unlhd> p\<^sub>+ + q\<^sub>+"
  by (rule le_pmI) (simp add: pos_comps_def lookup_add lookup_lcs_fun lcs_fun_def)

lemma pos_comps_minus_le: "(p - q)\<^sub>+ \<unlhd> p\<^sub>+ + q\<^sub>-"
proof -
  have "(p + (- q))\<^sub>+ \<unlhd> p\<^sub>+ + (- q)\<^sub>+" by (rule pos_comps_plus_le)
  thus ?thesis by simp
qed

lemma pos_comps_map_scale: "(c \<cdot> p)\<^sub>+ = (if 0 \<le> c then c \<cdot> p\<^sub>+ else - c \<cdot> p\<^sub>-)"
  by (rule poly_mapping_eqI)
    (simp add: pos_comps_def neg_comps_def lookup_lcs_fun lcs_fun_def max_mult_distrib_left)

lemma neg_comps_is_int_pm: "is_int_pm p \<Longrightarrow> is_int_pm (p\<^sub>-)"
  unfolding neg_comps_def by (intro lcs_is_int_pm uminus_is_int_pm zero_is_int_pm)

lemma neg_comps_ge_zero: "0 \<unlhd> p\<^sub>-"
  unfolding neg_comps_def by (rule lcs_ge_pm)

lemma neg_comps_ge_self: "- p \<unlhd> p\<^sub>-"
  unfolding neg_comps_def by (rule lcs_ge_pm)

lemma neg_comps_is_nat_pm: "is_int_pm p \<Longrightarrow> is_nat_pm (p\<^sub>-)"
  by (auto intro: int_pm_is_nat_pmI neg_comps_is_int_pm neg_comps_ge_zero zero_is_nat_pm)

lemma neg_comps_zero [simp]: "0\<^sub>- = 0"
  by (simp add: neg_comps_def lcs_ge_pm(1) lcs_le_pm le_pm_antisym)

lemma neg_comps_zero_iff [iff]: "p\<^sub>- = 0 \<longleftrightarrow> 0 \<unlhd> p"
  by (metis add.right_inverse diff_zero le_pm_increasing le_pm_refl pos_comps_ge_zero
      pos_comps_uminus pos_comps_zero_iff pos_minus_neg_comps)

lemma neg_comps_uminus [simp]: "(- p)\<^sub>- = p\<^sub>+"
  by (simp add: pos_comps_def neg_comps_def)

lemma neg_comps_plus_le: "(p + q)\<^sub>- \<unlhd> p\<^sub>- + q\<^sub>-"
  by (rule le_pmI) (simp add: neg_comps_def lookup_add lookup_minus lookup_lcs_fun lcs_fun_def)

lemma neg_comps_minus_le: "(p - q)\<^sub>- \<unlhd> p\<^sub>- + q\<^sub>+"
proof -
  have "(p + (- q))\<^sub>- \<unlhd> p\<^sub>- + (- q)\<^sub>-" by (rule neg_comps_plus_le)
  thus ?thesis by simp
qed

lemma neg_comps_map_scale: "(c \<cdot> p)\<^sub>- = (if 0 \<le> c then c \<cdot> p\<^sub>- else - c \<cdot> p\<^sub>+)"
  by (rule poly_mapping_eqI)
    (simp add: pos_comps_def neg_comps_def lookup_lcs_fun lcs_fun_def max_mult_distrib_left)

end (* pm_powerprod *)

subsection \<open>Overlap\<close>

locale two_polys =
  pm_powerprod ord ord_strict
  for ord::"('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50) +
  fixes f1 f2 :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field"
begin

definition overlap :: "'x point"
  where "overlap = lcs (gcs (fst (poly_point f1)) (snd (poly_point f1)))
                       (gcs (fst (poly_point f2)) (snd (poly_point f2)))"

lemma overlap_alt:
  "overlap = lcs (gcs (of_nat_pm (lp f1)) (of_nat_pm (tp f1)))
                 (gcs (of_nat_pm (lp f2)) (of_nat_pm (tp f2)))"
  by (simp only: overlap_def fst_poly_point snd_poly_point)

lemma overlap_alt': "overlap = of_nat_pm (lcs (gcs (lp f1) (tp f1)) (gcs (lp f2) (tp f2)))"
  by (simp add: overlap_alt gcs_of_nat_pm lcs_of_nat_pm)

lemma overlap_is_nat_pm: "is_nat_pm overlap"
  by (simp add: overlap_def is_nat_pm_pairD[OF poly_point_is_nat_pm_pair] gcs_is_nat_pm lcs_is_nat_pm)

lemma gcs_le_overlap:
  shows "gcs (of_nat_pm (lp f1)) (of_nat_pm (tp f1)) \<unlhd> overlap"
    and "gcs (of_nat_pm (lp f2)) (of_nat_pm (tp f2)) \<unlhd> overlap"
  by (simp_all add: overlap_alt le_pm_def lookup_lcs_fun leq_lcs_fun_1 leq_lcs_fun_2)

lemma gcs_le_overlap':
  shows "of_nat_pm (gcs (lp f1) (tp f1)) \<unlhd> overlap" and "of_nat_pm (gcs (lp f2) (tp f2)) \<unlhd> overlap"
  using gcs_le_overlap by (simp_all add: gcs_of_nat_pm)

lemma overlap_is_int_pm: "is_int_pm overlap"
  using overlap_is_nat_pm by (rule nat_pm_is_int_pm)

lemma overlap_leI:
  "gcs (lp f1) (tp f1) adds t \<Longrightarrow> gcs (lp f2) (tp f2) adds t \<Longrightarrow> overlap \<unlhd> of_nat_pm t"
  unfolding overlap_alt' le_of_nat_pm adds_pm[symmetric] by (rule lcs_adds)

lemma overlap_leD:
  assumes "overlap \<unlhd> of_nat_pm t"
  shows "gcs (lp f1) (tp f1) adds t" and "gcs (lp f2) (tp f2) adds t"
  using assms by (auto simp: overlap_alt' le_of_nat_pm adds_pm[symmetric]
                       intro: adds_trans[OF adds_lcs] adds_trans[OF adds_lcs_2])

lemma lem_3_1_13:
  assumes "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p"
  shows "overlap \<unlhd> p"
  unfolding overlap_alt lookup_lcs_fun le_pm_def
proof (rule lcs_leq_fun)
  let ?t = "of_nat_pm (lp f1)"
  let ?s = "of_nat_pm (tp f1)"
  have "lookup (gcs ?t ?s) \<le> lookup ?s" unfolding lookup_gcs_fun by (fact gcs_leq_fun_2)
  also from assms(1) have "... \<le> lookup p" by (simp only: le_pm_def)
  finally show "lookup (gcs ?t ?s) \<le> lookup p" .
next
  let ?t = "of_nat_pm (lp f2)"
  let ?s = "of_nat_pm (tp f2)"
  have "lookup (gcs ?t ?s) \<le> lookup ?s" unfolding lookup_gcs_fun by (fact gcs_leq_fun_2)
  also from assms(2) have "... \<le> lookup p" by (simp only: le_pm_def)
  finally show "lookup (gcs ?t ?s) \<le> lookup p" .
qed

lemma line_above_overlapD:
  assumes "overlap \<unlhd> p" and "overlap \<unlhd> p + l \<cdot> vect f" and "f \<in> {f1, f2}" and "1 \<le> l"
  shows "of_nat_pm (tp f) \<unlhd> p" and "tp f \<unlhd> to_nat_pm p" and "of_nat_pm (lp f) \<unlhd> p + l \<cdot> vect f"
    and "lp f \<unlhd> to_nat_pm (p + l \<cdot> vect f)"
proof -
  define q where "q = p + l \<cdot> vect f"
  let ?l = "of_nat_pm (lp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?t = "of_nat_pm (tp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?p = "to_nat_pm p"
  let ?q = "to_nat_pm q"

  from assms(1, 3) have 1: "gcs ?l ?t \<unlhd> p" by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)
  from assms(1) have "overlap \<unlhd> p + 0 \<cdot> vect f" by simp
  hence "overlap \<unlhd> p + 1 \<cdot> vect f" using assms(2) _ assms(4) by (rule map_scale_le_interval) simp
  hence "overlap \<unlhd> p + vect f" by simp
  with assms(3) have 2: "gcs ?l ?t \<unlhd> p + vect f"
    by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)

  show "?t \<unlhd> p"
  proof (rule le_pmI)
    fix x
    show "lookup ?t x \<le> lookup p x"
    proof (rule ccontr)
      assume "\<not> lookup ?t x \<le> lookup p x"
      hence 3: "lookup p x < lookup ?t x" by simp
      hence "lookup (p + vect f) x < lookup (?t + vect f) x" by (simp only: lookup_add)
      also have "\<dots> = lookup ?l x" by (simp add: vect_alt)
      finally have 4: "lookup (p + vect f) x < lookup ?l x" .
      have *: "min (lookup ?l x) (lookup ?t x) = lookup (gcs ?l ?t) x"
        by (simp only: lookup_gcs_fun gcs_fun)
      also from 1 have "\<dots> \<le> lookup p x" by (rule le_pmD)
      finally have **: "lookup ?l x < lookup ?t x" using 3 by simp
      note *
      also from 2 have "lookup (gcs ?l ?t) x \<le> lookup (p + vect f) x" by (rule le_pmD)
      finally have "lookup ?t x < lookup ?l x" using 4 by simp
      with ** show False by simp
    qed
  qed

  hence "to_nat_pm ?t \<unlhd> ?p" by (rule to_nat_pm_mono)
  thus "tp f \<unlhd> ?p" by simp

  from assms(2, 3) have 1: "gcs ?l ?t \<unlhd> q" by (auto simp: q_def overlap_alt intro: le_pm_trans lcs_ge_pm)
  from assms(1) have "overlap \<unlhd> p + 0 \<cdot> vect f" by simp
  hence "overlap \<unlhd> p + (l - 1) \<cdot> vect f" using assms(2)
    by (rule map_scale_le_interval) (simp_all add: assms(4))
  hence "overlap \<unlhd> q -  vect f" by (simp add: q_def algebra_simps)
  with assms(3) have 2: "gcs ?l ?t \<unlhd> q - vect f"
    by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)

  show "?l \<unlhd> q"
  proof (rule le_pmI)
    fix x
    show "lookup ?l x \<le> lookup q x"
    proof (rule ccontr)
      assume "\<not> lookup ?l x \<le> lookup q x"
      hence 3: "lookup q x < lookup ?l x" by simp
      hence "lookup (q - vect f) x < lookup (?l - vect f) x" by (simp only: lookup_minus)
      also have "\<dots> = lookup ?t x" by (simp add: vect_alt)
      finally have 4: "lookup (q - vect f) x < lookup ?t x" .
      have *: "min (lookup ?l x) (lookup ?t x) = lookup (gcs ?l ?t) x"
        by (simp only: lookup_gcs_fun gcs_fun)
      also from 1 have "\<dots> \<le> lookup q x" by (rule le_pmD)
      finally have **: "lookup ?t x < lookup ?l x" using 3 by simp
      note *
      also from 2 have "lookup (gcs ?l ?t) x \<le> lookup (q - vect f) x" by (rule le_pmD)
      finally have "lookup ?l x < lookup ?t x" using 4 by simp
      with ** show False by simp
    qed
  qed

  hence "to_nat_pm ?l \<unlhd> ?q" by (rule to_nat_pm_mono)
  thus "lp f \<unlhd> ?q" by simp
qed

lemma line_above_tp_overlapD:
  assumes "of_nat_pm (tp f) \<unlhd> p" and "overlap \<unlhd> p + l \<cdot> vect f" and "f \<in> {f1, f2}" and "1 \<le> l"
  shows "of_nat_pm (lp f) \<unlhd> p + l \<cdot> vect f" and "lp f \<unlhd> to_nat_pm (p + l \<cdot> vect f)"
proof -
  define q where "q = p + l \<cdot> vect f"
  let ?l = "of_nat_pm (lp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?t = "of_nat_pm (tp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?q = "to_nat_pm q"

  from assms(2, 3) have 1: "gcs ?l ?t \<unlhd> q" by (auto simp: q_def overlap_alt intro: le_pm_trans lcs_ge_pm)

  show "?l \<unlhd> q"
  proof (rule le_pmI)
    fix x
    show "lookup ?l x \<le> lookup q x"
    proof (rule ccontr)
      assume "\<not> lookup ?l x \<le> lookup q x"
      hence 3: "lookup q x < lookup ?l x" by simp
      hence "lookup (q - vect f) x < lookup (?l - vect f) x" by (simp only: lookup_minus)
      also have "\<dots> = lookup ?t x" by (simp add: vect_alt)
      also from assms(1) have "\<dots> \<le> lookup p x" by (rule le_pmD)
      finally have "lookup (q - vect f) x < lookup p x" .
      hence "(l - 1) * lookup (vect f) x < 0" by (simp add: q_def lookup_add lookup_minus algebra_simps)
      with assms(4) have "lookup (vect f) x < 0" by (simp add: mult_less_0_iff)

      have "min (lookup ?l x) (lookup ?t x) = lookup (gcs ?l ?t) x"
        by (simp only: lookup_gcs_fun gcs_fun)
      also from 1 have "\<dots> \<le> lookup q x" by (rule le_pmD)
      finally have "lookup ?t x < lookup ?l x" using 3 by simp
      hence "0 < lookup (vect f) x" by (simp add: vect_alt lookup_minus)
      also have "\<dots> < 0" by fact
      finally show False ..
    qed
  qed

  hence "to_nat_pm ?l \<unlhd> ?q" by (rule to_nat_pm_mono)
  thus "lp f \<unlhd> ?q" by simp
qed

lemma line_above_lp_overlapD:
  assumes "overlap \<unlhd> p" and "of_nat_pm (lp f) \<unlhd> p + l \<cdot> vect f" and "f \<in> {f1, f2}" and "1 \<le> l"
  shows "of_nat_pm (tp f) \<unlhd> p" and "tp f \<unlhd> to_nat_pm p"
proof -
  let ?l = "of_nat_pm (lp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?t = "of_nat_pm (tp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?p = "to_nat_pm p"

  from assms(1, 3) have 1: "gcs ?l ?t \<unlhd> p" by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)

  show "?t \<unlhd> p"
  proof (rule le_pmI)
    fix x
    show "lookup ?t x \<le> lookup p x"
    proof (rule ccontr)
      assume "\<not> lookup ?t x \<le> lookup p x"
      hence 3: "lookup p x < lookup ?t x" by simp
      hence "lookup (p + vect f) x < lookup (?t + vect f) x" by (simp only: lookup_add)
      also have "\<dots> = lookup ?l x" by (simp add: vect_alt)
      also from assms(2) have "\<dots> \<le> lookup (p + l \<cdot> vect f) x" by (rule le_pmD)
      finally have "lookup (p + vect f) x < lookup (p + l \<cdot> vect f) x" .
      hence "0 < (l - 1) * lookup (vect f) x" by (simp add: lookup_add algebra_simps)
      with assms(4) have "0 < lookup (vect f) x" by (simp add: zero_less_mult_iff)

      have "min (lookup ?l x) (lookup ?t x) = lookup (gcs ?l ?t) x"
        by (simp only: lookup_gcs_fun gcs_fun)
      also from 1 have "\<dots> \<le> lookup p x" by (rule le_pmD)
      finally have "lookup ?l x < lookup ?t x" using 3 by simp
      hence "lookup (vect f) x < 0" by (simp add: vect_alt lookup_minus)
      also have "\<dots> < lookup (vect f) x" by fact
      finally show False ..
    qed
  qed

  hence "to_nat_pm ?t \<unlhd> ?p" by (rule to_nat_pm_mono)
  thus "tp f \<unlhd> ?p" by simp
qed

definition step_p' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'x point \<Rightarrow> nat" where
  "step_p' f p = Max ({nat \<lceil>(lookup overlap x - lookup p x) / lookup (vect f) x\<rceil> |
                      x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<union> {0})"

text \<open>Note that the original definition of @{term step_p'} requires @{term \<open>lookup (vect f) x \<noteq> 0\<close>} instead
      of @{term \<open>0 < lookup (vect f) x\<close>}. One can easily prove, however, that both formulations are equivalent.\<close>

definition step_p :: "'x point \<Rightarrow> nat" where
  "step_p p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) then
      step_p' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p
    else 0)"

definition overlapshift_p' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'x point \<Rightarrow> 'x point" where
  "overlapshift_p' f p = p + rat (step_p' f p) \<cdot> vect f"

definition overlapshift_p :: "'x point \<Rightarrow> 'x point" where
  "overlapshift_p p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) then
      overlapshift_p' (SOME f. f \<in> {f1,f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p
    else p)"

definition step' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "step' f t = step_p' f (of_nat_pm t)"

definition step :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "step t = step_p (of_nat_pm t)"

definition overlapshift' :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat)" where
  "overlapshift' f p = to_nat_pm (overlapshift_p' f (of_nat_pm p))"

definition overlapshift :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat)" where
  "overlapshift = to_nat_pm o overlapshift_p o of_nat_pm"

lemma finite_step_p'_carrier: "finite {x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x}"
proof (rule finite_subset)
  show "{x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<subseteq> keys (vect f)"
  proof (rule, simp, elim conjE)
    fix x
    assume "0 < lookup (vect f) x"
    hence "lookup (vect f) x \<noteq> 0" by simp
    thus "x \<in> keys (vect f)" by simp
  qed
qed (fact finite_keys)

lemma step_p'_alt:
  "step_p' f p = nat \<lceil>Max ({(lookup overlap x - lookup p x) / lookup (vect f) x |
                          x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<union> {0::rat})\<rceil>"
proof -
  let ?ol = "lookup overlap"
  let ?vc = "lookup (vect f)"
  have "\<lceil>Max ({(?ol x - lookup p x) / ?vc x | x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::rat})\<rceil> =
        Max (ceiling ` ({(?ol x - lookup p x) / ?vc x | x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::rat}))"
    by (rule mono_Max_commute, rule, fact ceiling_mono, simp_all add: finite_step_p'_carrier)
  also have "\<dots> = Max ({\<lceil>(?ol x - lookup p x) / ?vc x\<rceil> | x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::int})"
    by (simp add: image_image_Collect)
  also have "nat \<dots> = Max (nat ` ({\<lceil>(?ol x - lookup p x) / ?vc x\<rceil> |
                      x::'x. 0 < ?vc x \<and> lookup p x < ?ol x} \<union> {0::int}))"
    by (rule mono_Max_commute, rule, simp_all add: finite_step_p'_carrier)
  also have "\<dots> = step_p' f p" by (simp add: step_p'_def image_image_Collect)
  finally show ?thesis by (rule sym)
qed

lemma int_step_p':
  "int (step_p' f p) = \<lceil>Max ({(lookup overlap x - lookup p x) / lookup (vect f) x |
                          x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x} \<union> {0})\<rceil>"
  (is "?l = \<lceil>?r\<rceil>")
proof -
  define c where "c = ?r"
  have "0 \<le> c" by (simp only: c_def, rule Max_ge, simp_all add: finite_step_p'_carrier)
  hence "0 \<le> \<lceil>c\<rceil>" by simp
  hence "int (nat \<lceil>c\<rceil>) = \<lceil>c\<rceil>" by simp
  thus ?thesis by (simp only: step_p'_alt c_def)
qed

lemma step_p'_above_overlap:
  assumes "overlap \<unlhd> p"
  shows "step_p' f p = 0"
proof -
  let ?A = "{nat \<lceil>(lookup overlap x - lookup p x) / lookup (vect f) x\<rceil> |
                      x::'x. 0 < lookup (vect f) x \<and> lookup p x < lookup overlap x}"
  have eq: "?A = {}"
  proof (simp, intro allI impI)
    fix x
    assume "0 < lookup (vect f) x"
    from assms have "lookup overlap x \<le> lookup p x"
      by (simp add: le_pm_def le_fun_def of_nat_pm.rep_eq of_nat_fun_def)
    thus "\<not> lookup p x < lookup overlap x" by simp
  qed
  show ?thesis unfolding step_p'_def eq by simp
qed

lemma step_p_welldefined:
  assumes "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p"
  shows "step_p p = 0"
  unfolding step_p_def
proof (split if_split, intro conjI impI)
  from assms have "overlap \<unlhd> p" by (rule lem_3_1_13)
  thus "step_p' (SOME f. f\<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p = 0"
    by (rule step_p'_above_overlap)
qed rule

lemma some_step_p_eqI:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
    and "\<exists>g\<in>{f1,f2}. \<not> of_nat_pm (tp g) \<unlhd> p"
  shows "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) = f"
proof (rule some_equality)
  from assms show "f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p" by simp
next
  fix f'
  assume "f' \<in> {f1, f2} \<and> is_proper_binomial f' \<and> of_nat_pm (tp f') \<unlhd> p"
  hence "f' \<in> {f1, f2}" and "of_nat_pm (tp f') \<unlhd> p" by simp_all
  show "f' = f"
  proof (rule ccontr)
    assume "f' \<noteq> f"
    have "\<forall>g\<in>{f1, f2}. of_nat_pm (tp g) \<unlhd> p"
    proof
      fix g
      assume "g \<in> {f1, f2}"
      with \<open>f \<in> {f1, f2}\<close> \<open>f' \<in> {f1, f2}\<close> \<open>f' \<noteq> f\<close> have "g = f \<or> g = f'" by auto
      with \<open>of_nat_pm (tp f) \<unlhd> p\<close> \<open>of_nat_pm (tp f') \<unlhd> p\<close> show "of_nat_pm (tp g) \<unlhd> p" by auto
    qed
    with assms(4) show False by simp
  qed
qed

lemma step_p_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
  shows "step_p p = step_p' f p"
proof (cases "\<forall>g\<in>{f1, f2}. of_nat_pm (tp g) \<unlhd> p")
  case True
  hence "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p" by simp_all
  hence "step_p p = 0" and "overlap \<unlhd> p" by (rule step_p_welldefined, rule lem_3_1_13)
  from this(2) have "step_p' f p = 0" by (rule step_p'_above_overlap)
  with \<open>step_p p = 0\<close> show ?thesis by simp
next
  case False
  hence "\<exists>g\<in>{f1,f2}. \<not> of_nat_pm (tp g) \<unlhd> p" by simp
  with assms have eq: "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) = f"
    by (rule some_step_p_eqI)
  show ?thesis unfolding step_p_def eq
  proof (split if_split, intro conjI impI, rule)
    assume "\<not> (\<exists>g\<in>{f1, f2}.is_proper_binomial g \<and> of_nat_pm (tp g) \<unlhd> p)"
    hence "\<forall>g\<in>{f1,f2}. (\<not> is_proper_binomial g) \<or> \<not> of_nat_pm (tp g) \<unlhd> p" by simp
    from this \<open>f \<in> {f1, f2}\<close> have "(\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" ..
    with assms(2) assms(3) show "0 = step_p' f p" by simp
  qed
qed

lemma step_p_alt2: "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) \<Longrightarrow> step_p p = 0"
  by (auto simp: step_p_def)

lemma overlapshift_p'_is_int_pm: "is_int_pm p \<Longrightarrow> is_int_pm (overlapshift_p' f p)"
  unfolding overlapshift_p'_def by (intro plus_is_int_pm map_scale_is_int_pm Ints_of_nat vect_is_int_pm)

lemma overlapshift_p'_above_overlap: "overlap \<unlhd> p \<Longrightarrow> overlapshift_p' f p = p"
  by (simp add: overlapshift_p'_def step_p'_above_overlap)

lemma overlapshift_p_welldefined:
  assumes "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p"
  shows "overlapshift_p p = p"
  unfolding overlapshift_p_def
proof (split if_split, intro conjI impI)
  from assms have "overlap \<unlhd> p" by (rule lem_3_1_13)
  thus "overlapshift_p' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) p = p"
    by (rule overlapshift_p'_above_overlap)
qed rule

lemma overlapshift_p_alt0:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "of_nat_pm (tp f) \<unlhd> p"
  shows "overlapshift_p p = p + rat (step_p p) \<cdot> vect f"
proof (cases "\<forall>g\<in>{f1, f2}. of_nat_pm (tp g) \<unlhd> p")
  case True
  hence "of_nat_pm (tp f1) \<unlhd> p" and "of_nat_pm (tp f2) \<unlhd> p" by simp_all
  hence "overlapshift_p p = p" and "step_p p = 0" by (rule overlapshift_p_welldefined, rule step_p_welldefined)
  thus ?thesis by simp
next
  case False
  hence "\<exists>g\<in>{f1,f2}. \<not> of_nat_pm (tp g) \<unlhd> p" by simp
  with assms have eq: "(SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) = f"
    by (rule some_step_p_eqI)
  show ?thesis unfolding overlapshift_p_def eq
  proof (split if_split, intro conjI impI)
    from assms have "step_p p = step_p' f p" by (rule step_p_alt1)
    thus "overlapshift_p' f p = p + rat (step_p p) \<cdot> vect f" by (simp add: overlapshift_p'_def)
  next
    assume "\<not> (\<exists>f\<in>{f1, f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p)"
    hence "\<forall>f\<in>{f1,f2}. (\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" by simp
    from this \<open>f \<in> {f1, f2}\<close> have "(\<not> is_proper_binomial f) \<or> \<not> of_nat_pm (tp f) \<unlhd> p" ..
    with assms(2) assms(3) show "p = p + rat (step_p p) \<cdot> vect f" by simp
  qed
qed

lemma overlapshift_p_alt1:
  "f \<in> {f1, f2} \<Longrightarrow> is_proper_binomial f \<Longrightarrow> of_nat_pm (tp f) \<unlhd> p \<Longrightarrow> overlapshift_p p = overlapshift_p' f p"
  by (simp only: overlapshift_p'_def overlapshift_p_alt0 step_p_alt1)

lemma overlapshift_p_alt2:
  "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> of_nat_pm (tp f) \<unlhd> p) \<Longrightarrow> overlapshift_p p = p"
  by (auto simp: overlapshift_p_def)
  
lemma overlapshift_p_is_int_pm:
  assumes "is_int_pm p"
  shows "is_int_pm (overlapshift_p p)"
  unfolding overlapshift_p_def
  by (split if_split, intro conjI impI, rule overlapshift_p'_is_int_pm, (rule assms)+)

lemma step_p'_min:
  assumes "overlap \<unlhd> p + rat k \<cdot> vect f"
  shows "step_p' f p \<le> k"
proof (simp add: step_p'_alt finite_step_p'_carrier ceiling_le_iff nat_le_iff, intro allI impI, elim exE)
  fix a x
  assume "a = (lookup overlap x - lookup p x) / lookup (vect f) x \<and>
              0 < lookup (vect f) x \<and> lookup p x < lookup overlap x"
  hence a_eq: "a = (lookup overlap x - lookup p x) / lookup (vect f) x"
    and "0 < lookup (vect f) x" and "lookup p x < lookup overlap x" by simp_all
  show "a \<le> rat k"
  proof (simp only: a_eq pos_divide_le_eq[OF \<open>0 < lookup (vect f) x\<close>])
    from assms have "lookup overlap x \<le> lookup p x + rat k * lookup (vect f) x"
      by (simp add: le_pm_def of_nat_pm.rep_eq plus_poly_mapping.rep_eq lookup_of_int_pm le_fun_def of_nat_fun_def)
    thus "lookup overlap x - lookup p x \<le> rat k * lookup (vect f) x" by simp
  qed
qed

lemma overlapshift_p'_is_above_overlap:
  assumes "overlap \<unlhd> p + rat k \<cdot> vect f"
  shows "overlap \<unlhd> overlapshift_p' f p"
proof -
  let ?ol = "lookup overlap"
  let ?os = "lookup (overlapshift_p' f p)"
  let ?vc = "lookup (vect f)"
  let ?p = "lookup p"
  show ?thesis
  proof (simp only: le_pm_def le_fun_def lookup_of_nat_pm of_nat_fun_def o_def, rule)
    fix x
    show "?ol x \<le> ?os x"
    proof (cases "0 < ?vc x \<and> ?p x < ?ol x")
      case True
      hence "0 < ?vc x" and "?p x < ?ol x" by simp_all
      have "(?ol x - ?p x) / ?vc x \<le> Max ({(?ol x - ?p x) / ?vc x | x. 0 < ?vc x \<and> ?p x < ?ol x} \<union> {0})"
        by (rule Max_ge, simp add: finite_step_p'_carrier, rule, rule, rule, rule conjI, rule refl, rule True)
      hence "\<lceil>(?ol x - ?p x) / ?vc x\<rceil> \<le> int (step_p' f p)" unfolding int_step_p' by (rule ceiling_mono)
      hence "(?ol x - ?p x) / ?vc x \<le> rat_of_int (int (step_p' f p))" by linarith
      hence "?ol x - ?p x \<le> rat_of_int (int (step_p' f p)) * ?vc x"
        by (simp only: pos_divide_le_eq[OF \<open>0 < ?vc x\<close>])
      thus ?thesis by (simp add: overlapshift_p'_def lookup_add lookup_of_int_pm)
    next
      case False
      hence disj: "?vc x \<le> 0 \<or> ?ol x \<le> ?p x" by auto
      show ?thesis
      proof (cases "?vc x \<le> 0")
        case True
        from assms have "step_p' f p \<le> k" by (rule step_p'_min)
        hence "rat (step_p' f p) \<le> rat k" by simp
        from this True have "rat k * ?vc x \<le> rat (step_p' f p) * ?vc x"
          by (rule mult_right_mono_neg)
        hence "?p x + rat k * ?vc x \<le> ?p x + rat (step_p' f p) * ?vc x" by linarith
        hence "lookup (p + rat k \<cdot> vect f) x \<le> lookup (p + rat (step_p' f p) \<cdot> vect f) x"
          by (simp add: lookup_add lookup_of_int_pm)
        moreover from assms have "?ol x \<le> lookup (p + rat k \<cdot> vect f) x"
          by (simp only: le_pm_def le_fun_def lookup_of_nat_pm)
        ultimately show ?thesis by (simp add: overlapshift_p'_def)
      next
        case False
        with disj have "0 < ?vc x" and *: "?ol x \<le> ?p x" by simp_all
        from this(1) have "0 \<le> rat (step_p' f p) * ?vc x" by simp
        hence "?p x \<le> ?p x + rat (step_p' f p) * ?vc x" by linarith
        hence "?p x \<le> lookup (p + rat (step_p' f p) \<cdot> vect f) x"
          by (simp add: lookup_add lookup_of_int_pm)
        with * show ?thesis by (simp add: overlapshift_p'_def)
      qed
    qed
  qed
qed

lemma step'_alt:
  "step' f p = Max ({nat \<lceil>(lookup overlap x - of_nat (lookup p x)) / lookup (vect f) x\<rceil> |
                      x::'x. 0 < lookup (vect f) x \<and> of_nat (lookup p x) < lookup overlap x} \<union> {0})"
  by (simp only: step'_def step_p'_def lookup_of_nat_pm)

lemma step_alt:
  "step p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p) then
      step' (SOME f. f \<in> {f1, f2} \<and> is_proper_binomial f \<and> tp f \<unlhd> p) p
    else 0)"
  by (simp only: le_pm_def step_def step_p_def step'_def[symmetric] leq_of_nat_fun of_nat_pm.rep_eq)

lemma step_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<unlhd> p"
  shows "step p = step' f p"
  unfolding step_def step'_def
  by (rule step_p_alt1, fact, fact, simp only: le_of_nat_pm, fact)

lemma step_alt2:
  assumes "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p)"
  shows "step p = 0"
  unfolding step_def
  by (rule step_p_alt2, simp only: le_of_nat_pm, fact)

lemma overlapshift'_alt:
  "lookup (overlapshift' f p) = to_nat \<circ> (lookup (of_nat_pm p + rat (step' f p) \<cdot> vect f))"
  by (simp add: overlapshift'_def overlapshift_p'_def to_nat_pm.rep_eq plus_poly_mapping.rep_eq
      lookup_of_nat_pm to_nat_fun_def flip: step'_def)

lemma overlapshift_alt:
  "overlapshift p =
    (if (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p) then
      overlapshift' (SOME f. f \<in> {f1,f2} \<and> is_proper_binomial f \<and> tp f \<unlhd> p) p
    else p)"
  by (simp only: overlapshift_def o_def overlapshift_p_def le_of_nat_pm if_distrib[of to_nat_pm]
      overlapshift'_def[symmetric] to_nat_pm_comp_of_nat_pm)

lemma overlapshift_alt1:
  assumes "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<unlhd> p"
  shows "overlapshift p = overlapshift' f p"
proof -
  have "overlapshift_p (of_nat_pm p) = overlapshift_p' f (of_nat_pm p)"
    by (rule overlapshift_p_alt1, fact, fact, simp only: le_of_nat_pm, fact)
  thus ?thesis by (simp add: overlapshift_def overlapshift'_def)
qed

lemma overlapshift_alt2:
  assumes "\<not> (\<exists>f\<in>{f1,f2}. is_proper_binomial f \<and> tp f \<unlhd> p)"
  shows "overlapshift p = p"
proof -
  have "overlapshift_p (of_nat_pm p) = of_nat_pm p"
    by (rule overlapshift_p_alt2, simp_all only: le_of_nat_pm, fact+)
  thus ?thesis by (simp add: overlapshift_def to_nat_fun_comp_of_nat_fun)
qed

lemma overlapshift_step_idI:
  assumes "step p = 0"
  shows "overlapshift p = p"
proof (cases "\<exists>f\<in>{f1, f2}. is_proper_binomial f \<and> tp f \<unlhd> p")
  case True
  then obtain f where "f \<in> {f1, f2}" and "is_proper_binomial f" and "tp f \<unlhd> p" by auto
  hence eq: "step p = step' f p" and "overlapshift p = overlapshift' f p"
    by (rule step_alt1, rule overlapshift_alt1)
  note this(2)
  also have "lookup \<dots> = to_nat \<circ> lookup (of_nat_pm p + rat (step' f p) \<cdot> vect f)"
    by (fact overlapshift'_alt)
  also have "\<dots> = to_nat \<circ> lookup ((of_nat_pm p)::_ \<Rightarrow>\<^sub>0 rat)" by (simp add: eq[symmetric] assms)
  finally show ?thesis by (simp add: poly_mapping_eq_iff to_nat_comp_of_nat_fun of_nat_pm.rep_eq)
next
  case False
  thus ?thesis by (rule overlapshift_alt2)
qed

lemma step'_min:
  assumes "associated f p q k" and "overlap \<unlhd> of_nat_pm p"
  shows "step' f q \<le> k"
  unfolding step'_def
proof (rule step_p'_min)
  from assms(1) have eq: "(of_nat_pm p = ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f)"
    by (simp only: associated_alt_rat)
  from assms(2) show "overlap \<unlhd> ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f" by (simp only: eq)
qed

lemma overlapshift'_is_above_overlap:
  assumes "associated f p q k" and "overlap \<unlhd> of_nat_pm p"
  shows "overlap \<unlhd> of_nat_pm (overlapshift' f q)"
proof -
  have "overlap \<unlhd> overlapshift_p' f (of_nat_pm q)"
  proof (rule overlapshift_p'_is_above_overlap)
    from assms(1) have eq: "(of_nat_pm p = ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f)"
      by (simp only: associated_alt_rat)
    from assms(2) show "overlap \<unlhd> ((of_nat_pm q)::'x \<Rightarrow>\<^sub>0 rat) + rat k \<cdot> vect f" by (simp only: eq)
  qed
  also have "\<dots> \<unlhd> of_nat_pm (overlapshift' f q)"
  proof (rule leD_to_int_pm)
    show "to_int_pm (overlapshift_p' f (of_nat_pm q)) \<unlhd> to_int_pm (of_nat_pm (overlapshift' f q))"
      by (simp add: overlapshift'_def le_pm_def le_fun_def lookup_to_int_pm lookup_of_nat_pm
          lookup_to_nat_pm to_nat_def)
  next
    show "is_int_pm (overlapshift_p' f (of_nat_pm q))"
      by (intro overlapshift_p'_is_int_pm nat_pm_is_int_pm of_nat_pm_is_nat_pm)
  next
    from of_nat_pm_is_nat_pm show "is_int_pm (of_nat_pm (overlapshift' f q))" by (rule nat_pm_is_int_pm)
  qed
  finally show ?thesis .
qed

context
  fixes f p q k
  assumes f_in: "f \<in> {f1, f2}"
    and f_pbinomial: "is_proper_binomial f"
    and tp_adds: "tp f adds q"
    and assoc: "associated f p q k"
    and overlap_le: "overlap \<unlhd> of_nat_pm p"
begin

lemma step_min: "step q \<le> k"
proof -
  from tp_adds have "tp f \<unlhd> q" by (simp only: adds_pm)
  from assoc overlap_le have "step' f q \<le> k" by (rule step'_min)
  thus ?thesis by (simp only: step_alt1[OF f_in f_pbinomial \<open>tp f \<unlhd> q\<close>])
qed

lemma overlapshift_is_above_overlap: "overlap \<unlhd> of_nat_pm (overlapshift q)"
proof -
  from tp_adds have "tp f \<unlhd> q" by (simp only: adds_pm)
  from assoc overlap_le have "overlap \<unlhd> of_nat_pm (overlapshift' f q)"
    by (rule overlapshift'_is_above_overlap)
  thus ?thesis by (simp only: overlapshift_alt1[OF f_in f_pbinomial \<open>tp f \<unlhd> q\<close>])
qed

lemma overlapshift_p_is_nat_pm: "is_nat_pm (overlapshift_p (of_nat_pm q))"
proof (rule int_pm_is_nat_pm, rule overlapshift_p_is_int_pm, rule nat_pm_is_int_pm,
        rule of_nat_pm_is_nat_pm)
  fix x
  note overlap_le
  also have "of_nat_pm p = of_nat_pm q + rat k \<cdot> vect f" using assoc
    by (simp add: associated_alt_rat)
  finally have "overlap \<unlhd> overlapshift_p' f (of_nat_pm q)"
    by (rule overlapshift_p'_is_above_overlap)
  hence "lookup overlap x \<le> lookup (overlapshift_p' f (of_nat_pm q)) x" by (rule le_pmD)
  have eq: "overlapshift_p (of_nat_pm q) = overlapshift_p' f (of_nat_pm q)"
    by (rule overlapshift_p_alt1, fact f_in, fact f_pbinomial,
        simp only: le_of_nat_pm adds_pm[symmetric], fact tp_adds)
  from overlap_is_nat_pm have "lookup overlap x \<in> \<nat>" by (rule is_nat_pmD)
  hence "(0::rat) \<le> lookup overlap x" by (rule Nats_ge_0)
  also have "\<dots> \<le> lookup (overlapshift_p' f (of_nat_pm q)) x" by fact
  finally show "0 \<le> lookup (overlapshift_p (of_nat_pm q)) x" by (simp only: eq)
qed

lemma of_nat_pm_overlapshift: "of_nat_pm (overlapshift q) = overlapshift_p (of_nat_pm q)"
  using overlapshift_p_is_nat_pm by (simp only: overlapshift_def o_def of_nat_pm_comp_to_nat_pm)

lemma of_nat_pm_overlapshift': "of_nat_pm (overlapshift q) = of_nat_pm q + rat (step q) \<cdot> vect f"
  unfolding of_nat_pm_overlapshift step_def
  by (rule overlapshift_p_alt0, fact f_in, fact f_pbinomial,
      simp only: le_of_nat_pm adds_pm[symmetric], fact tp_adds)

lemma associated_overlapshift: "associated f (overlapshift q) q (step q)"
  by (simp only: associated_alt_rat of_nat_pm_overlapshift')

end

end (* two_polys *)

locale two_binoms =
  two_polys ord ord_strict f1 f2
  for ord :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x::{countable,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
  and f1 f2 :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field" +
  assumes f1_pbinomial: "is_proper_binomial f1"
  and f2_pbinomial: "is_proper_binomial f2"

end (* theory *)
