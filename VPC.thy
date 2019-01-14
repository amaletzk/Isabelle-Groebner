section \<open>Valid Polygonial Chains\<close>

theory VPC
  imports Two_Polynomials
begin

subsection \<open>Shifts\<close>

definition nat_plus_point_pair :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> ('x point \<times> 'x point) \<Rightarrow> ('x point \<times> 'x point)" (infixl "+\<^sub>N" 70)
  where "nat_plus_point_pair t pp = (of_nat_pm t + fst pp, of_nat_pm t + snd pp)"

lemma nat_plus_point_pair_zero [simp]: "0 +\<^sub>N pp = pp"
  by (simp add: nat_plus_point_pair_def)

lemma swap_nat_plus_point_pair: "prod.swap (t +\<^sub>N pp) = t +\<^sub>N prod.swap pp"
  by (simp add: nat_plus_point_pair_def)

lemma nat_plus_point_pair_is_nat_pm_pair: "is_nat_pm_pair pp \<Longrightarrow> is_nat_pm_pair (t +\<^sub>N pp)"
  by (simp add: nat_plus_point_pair_def is_nat_pm_pair_def plus_is_nat_pm of_nat_pm_is_nat_pm)

lemma nat_plus_point_pair_is_int_pm_pair: "is_int_pm_pair pp \<Longrightarrow> is_int_pm_pair (t +\<^sub>N pp)"
  by (simp add: nat_plus_point_pair_def is_int_pm_pair_def plus_is_int_pm of_nat_pm_is_nat_pm nat_pm_is_int_pm)

lemma nat_plus_point_pair_fst_eq_snd_iff [iff]: "fst (t +\<^sub>N pp) = snd (t +\<^sub>N pp) \<longleftrightarrow> fst pp = snd pp"
  by (auto simp: nat_plus_point_pair_def)

context pm_powerprod
begin

text \<open>It is better to define sets of shifts for arbitrary sets of polynomials, not just for the two
  implicitly fixed \<open>f1\<close> and \<open>f2\<close>.\<close>

definition shifts :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set \<Rightarrow> ('x point \<times> 'x point) set"
  where "shifts F = prod.swap ` poly_point ` F \<union> poly_point ` F"

definition shifts_of :: "('x point \<times> 'x point) set \<Rightarrow> ('x point \<times> 'x point) set"
  where "shifts_of F = case_prod (+\<^sub>N) ` (UNIV \<times> F)"

definition pos_Nshifts :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set \<Rightarrow> ('x point \<times> 'x point) set"
  where "pos_Nshifts F = case_prod (+\<^sub>N) ` (UNIV \<times> prod.swap ` poly_point ` F)"

definition neg_Nshifts :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set \<Rightarrow> ('x point \<times> 'x point) set"
  where "neg_Nshifts F = case_prod (+\<^sub>N) ` (UNIV \<times> poly_point ` F)"

definition Nshifts :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set \<Rightarrow> ('x point \<times> 'x point) set"
  where "Nshifts F = pos_Nshifts F \<union> neg_Nshifts F"

lemma shiftsE_poly:
  assumes "z \<in> shifts F"
  obtains f where "f \<in> F" and "z \<in> shifts {f}"
  using assms by (auto simp: shifts_def)

lemma shifts_ofE_poly:
  assumes "z \<in> shifts_of F"
  obtains f where "f \<in> F" and "z \<in> shifts_of {f}"
  using assms by (auto simp: shifts_of_def)

lemma shifts_of_singleton: "shifts_of {f} = range (\<lambda>t. t +\<^sub>N f)"
  by (auto simp: shifts_of_def intro!: image_eqI)

corollary shifts_of_singletonD: "z \<in> shifts_of {f} \<Longrightarrow> snd z = fst z + snd f - fst f"
  by (auto simp: shifts_of_singleton nat_plus_point_pair_def)

lemma shifts_of_mono: "F \<subseteq> G \<Longrightarrow> shifts_of F \<subseteq> shifts_of G"
  by (fastforce simp: shifts_of_def)

lemma pos_NshiftsI: "f \<in> F \<Longrightarrow> z = t +\<^sub>N prod.swap (poly_point f) \<Longrightarrow> z \<in> pos_Nshifts F"
  by (auto simp: pos_Nshifts_def)

lemma pos_NshiftsE:
  assumes "z \<in> pos_Nshifts F"
  obtains f t where "f \<in> F" and "z = t +\<^sub>N prod.swap (poly_point f)"
  using assms by (auto simp: pos_Nshifts_def)

lemma pos_Nshifts_singleton: "pos_Nshifts {f} = range (\<lambda>t. t +\<^sub>N prod.swap (poly_point f))"
  by (auto elim: pos_NshiftsE intro: pos_NshiftsI)

lemma pos_Nshifts_conv_vect: "z \<in> pos_Nshifts {f} \<Longrightarrow> snd z = fst z + vect f"
  by (auto simp: pos_Nshifts_singleton nat_plus_point_pair_def vect_def)

lemma neg_NshiftsI: "f \<in> F \<Longrightarrow> z = t +\<^sub>N poly_point f \<Longrightarrow> z \<in> neg_Nshifts F"
  by (auto simp: neg_Nshifts_def)

lemma neg_NshiftsE:
  assumes "z \<in> neg_Nshifts F"
  obtains f t where "f \<in> F" and "z = t +\<^sub>N poly_point f"
  using assms by (auto simp: neg_Nshifts_def)

lemma neg_Nshifts_singleton: "neg_Nshifts {f} = range (\<lambda>t. t +\<^sub>N poly_point f)"
  by (auto elim: neg_NshiftsE intro: neg_NshiftsI)

lemma neg_Nshifts_conv_vect: "z \<in> neg_Nshifts {f} \<Longrightarrow> snd z = fst z - vect f"
  by (auto simp: neg_Nshifts_singleton nat_plus_point_pair_def vect_def)

lemma NshiftsI1: "z \<in> pos_Nshifts F \<Longrightarrow> z \<in> Nshifts F"
  by (simp add: Nshifts_def)

lemma NshiftsI2: "z \<in> neg_Nshifts F \<Longrightarrow> z \<in> Nshifts F"
  by (simp add: Nshifts_def)

lemma NshiftsI:
  assumes "f \<in> F"
  shows "t +\<^sub>N poly_point f \<in> Nshifts F" and "t +\<^sub>N prod.swap (poly_point f) \<in> Nshifts F"
  using assms by (auto simp: Nshifts_def intro: pos_NshiftsI neg_NshiftsI)

lemma NshiftsI_poly: "z \<in> Nshifts {f} \<Longrightarrow> f \<in> F \<Longrightarrow> z \<in> Nshifts F"
  by (metis Un_iff neg_NshiftsE pos_NshiftsE NshiftsI Nshifts_def singletonD)

lemma NshiftsE:
  assumes "z \<in> Nshifts F"
  obtains f t where "f \<in> F" and "z = t +\<^sub>N poly_point f \<or> z = t +\<^sub>N prod.swap (poly_point f)"
  using assms unfolding Nshifts_def
proof
  assume "z \<in> neg_Nshifts F"
  then obtain f t where "f \<in> F" and "z = t +\<^sub>N poly_point f" by (rule neg_NshiftsE)
  from this(2) have "z = t +\<^sub>N poly_point f \<or> z = t +\<^sub>N prod.swap (poly_point f)" by simp
  with \<open>f \<in> F\<close> show ?thesis ..
next
  assume "z \<in> pos_Nshifts F"
  then obtain f t where "f \<in> F" and "z = t +\<^sub>N prod.swap (poly_point f)" by (rule pos_NshiftsE)
  from this(2) have "z = t +\<^sub>N poly_point f \<or> z = t +\<^sub>N prod.swap (poly_point f)" by simp
  with \<open>f \<in> F\<close> show ?thesis ..
qed

lemma NshiftsE_singleton:
  assumes "z \<in> Nshifts {f}"
  obtains t where "z = t +\<^sub>N poly_point f \<or> z = t +\<^sub>N prod.swap (poly_point f)"
  using assms by (auto simp: Nshifts_def pos_Nshifts_singleton neg_Nshifts_singleton)

lemma NshiftsE_shift:
  assumes "z \<in> Nshifts F"
  obtains "z \<in> pos_Nshifts F" | "z \<in> neg_Nshifts F"
  using assms by (auto simp: Nshifts_def)

lemma NshiftsE_poly:
  assumes "z \<in> Nshifts F"
  obtains f where "f \<in> F" and "z \<in> Nshifts {f}"
  using assms
proof (rule NshiftsE_shift)
  assume "z \<in> neg_Nshifts F"
  then obtain f t where "f \<in> F" and "z = t +\<^sub>N poly_point f" by (rule neg_NshiftsE)
  from _ this(2) have "z \<in> neg_Nshifts {f}" by (rule neg_NshiftsI) simp
  hence "z \<in> Nshifts {f}" by (rule NshiftsI2)
  with \<open>f \<in> F\<close> show ?thesis ..
next
  assume "z \<in> pos_Nshifts F"
  then obtain f t where "f \<in> F" and "z = t +\<^sub>N prod.swap (poly_point f)" by (rule pos_NshiftsE)
  from _ this(2) have "z \<in> pos_Nshifts {f}" by (rule pos_NshiftsI) simp
  hence "z \<in> Nshifts {f}" by (rule NshiftsI1)
  with \<open>f \<in> F\<close> show ?thesis ..
qed

lemma Nshifts_alt: "Nshifts F = shifts_of (shifts F)"
  by (simp only: Nshifts_def pos_Nshifts_def neg_Nshifts_def shifts_of_def shifts_def Sigma_Un_distrib2 image_Un)

lemma image_swap_shifts [simp]: "prod.swap ` shifts F = shifts F"
  by (simp add: shifts_def image_Un image_image Un_commute)

lemma image_swap_pos_Nshifts [simp]: "prod.swap ` pos_Nshifts F = neg_Nshifts F"
proof -
  have "prod.swap ` pos_Nshifts F =
            case_prod (+\<^sub>N) ` (\<lambda>(x, y). (x, prod.swap y)) ` (UNIV \<times> prod.swap ` poly_point ` F)"
    by (simp add: pos_Nshifts_def image_image prod.case_distrib swap_nat_plus_point_pair)
  also have "(\<lambda>(x, y). (x, prod.swap y)) ` (UNIV \<times> prod.swap ` poly_point ` F) = UNIV \<times> poly_point ` F"
    by (auto intro!: image_eqI)
  finally show ?thesis by (simp only: neg_Nshifts_def)
qed

lemma image_swap_neg_Nshifts [simp]: "prod.swap ` neg_Nshifts F = pos_Nshifts F"
proof -
  have "prod.swap ` neg_Nshifts F =
            case_prod (+\<^sub>N) ` (\<lambda>(x, y). (x, prod.swap y)) ` (UNIV \<times> poly_point ` F)"
    by (simp add: neg_Nshifts_def image_image prod.case_distrib swap_nat_plus_point_pair)
  also have "(\<lambda>(x, y). (x, prod.swap y)) ` (UNIV \<times> poly_point ` F) = UNIV \<times> prod.swap ` poly_point ` F"
    by (auto intro!: image_eqI)
  finally show ?thesis by (simp only: pos_Nshifts_def)
qed

lemma image_swap_Nshifts [simp]: "prod.swap ` Nshifts F = Nshifts F"
  by (simp add: Nshifts_def image_Un Un_commute)

lemma shifts_is_nat_pm_pair: "z \<in> shifts F \<Longrightarrow> is_nat_pm_pair z"
  by (auto simp: shifts_def nat_plus_point_pair_is_nat_pm_pair poly_point_is_nat_pm_pair)

lemma pos_Nshifts_is_nat_pm_pair: "z \<in> pos_Nshifts F \<Longrightarrow> is_nat_pm_pair z"
  by (elim pos_NshiftsE) (simp add: nat_plus_point_pair_is_nat_pm_pair poly_point_is_nat_pm_pair)

lemma neg_Nshifts_is_nat_pm_pair: "z \<in> neg_Nshifts F \<Longrightarrow> is_nat_pm_pair z"
  by (elim neg_NshiftsE) (simp add: nat_plus_point_pair_is_nat_pm_pair poly_point_is_nat_pm_pair)

lemma Nshifts_is_nat_pm_pair: "z \<in> Nshifts F \<Longrightarrow> is_nat_pm_pair z"
  by (auto simp: Nshifts_def intro: pos_Nshifts_is_nat_pm_pair neg_Nshifts_is_nat_pm_pair)

lemma pos_neg_Nshifts_not_disjointD:
  assumes "pos_Nshifts {f} \<inter> neg_Nshifts {f} \<noteq> {}"
  shows "lp f = tp f " and "pos_Nshifts {f} = neg_Nshifts {f}"
proof -
  from assms obtain z where "z \<in> pos_Nshifts {f}" and "z \<in> neg_Nshifts {f}" by blast
  from this(2) obtain s where "z = s +\<^sub>N poly_point f" unfolding neg_Nshifts_singleton ..
  moreover from \<open>z \<in> pos_Nshifts {f}\<close> obtain t where "z = t +\<^sub>N prod.swap (poly_point f)"
    unfolding pos_Nshifts_singleton ..
  ultimately have "s +\<^sub>N poly_point f = t +\<^sub>N prod.swap (poly_point f)" by simp
  hence "s + lp f = t + tp f" and "s + tp f = t + lp f"
    by (simp_all add: nat_plus_point_pair_def poly_point_def flip: of_nat_pm_plus)
  hence "(s + lp f) + (t + lp f) = (s + tp f) + (t + tp f)" by (simp only: add.commute)
  thus "lp f = tp f"
    by (simp add: ac_simps)
        (metis (no_types, hide_lams) ord_canc ordered_powerprod_lin.antisym plus_monotone_left punit.lt_ge_tt)
  hence "prod.swap (poly_point f) = poly_point f" by (simp add: poly_point_def)
  thus "pos_Nshifts {f} = neg_Nshifts {f}" by (simp only: pos_Nshifts_singleton neg_Nshifts_singleton)
qed

corollary pos_neg_Nshifts_disjointI:
  assumes "is_proper_binomial f"
  shows "pos_Nshifts {f} \<inter> neg_Nshifts {f} = {}"
proof (rule ccontr)
  assume "pos_Nshifts {f} \<inter> neg_Nshifts {f} \<noteq> {}"
  hence "lp f = tp f" by (rule pos_neg_Nshifts_not_disjointD)
  also from assms have "\<dots> \<prec> lp f" by (rule punit.lt_gr_tt_binomial)
  finally show False ..
qed

lemma Nshifts_fst_not_eq_snd_proper_binomials:
  assumes "\<And>f. f \<in> F \<Longrightarrow> is_proper_binomial f" and "z \<in> Nshifts F"
  shows "fst z \<noteq> snd z"
  using assms(2)
proof (rule NshiftsE_poly)
  fix f
  assume "f \<in> F"
  hence "is_proper_binomial f" by (rule assms(1))
  hence "fst (poly_point f) \<noteq> snd (poly_point f)"
    by (simp add: fst_eq_snd_poly_point_iff is_proper_binomial_def)
  moreover assume "z \<in> Nshifts {f}"
  ultimately show ?thesis by (auto simp: Nshifts_def pos_Nshifts_singleton neg_Nshifts_singleton)
qed

end (* pm_powerprod *)

subsection \<open>VPC Basics\<close>

context two_polys
begin

definition set_of_vpc :: "('x point \<times> 'x point) list \<Rightarrow> 'x point set"
  where "set_of_vpc zs = fst ` set zs \<union> snd ` set zs"

definition is_vpc :: "('x point \<times> 'x point) list \<Rightarrow> bool"
  where "is_vpc zs \<longleftrightarrow> zs \<noteq> [] \<and> (\<forall>i<length zs - 1. snd (zs ! i) = fst (zs ! Suc i)) \<and>
                      set zs \<subseteq> Nshifts {f1, f2}"

lemma finite_set_of_vpc: "finite (set_of_vpc zs)"
  by (simp add: set_of_vpc_def)

lemma set_of_vpcE:
  assumes "p \<in> set_of_vpc zs"
  obtains z where "z \<in> set zs" and "p = fst z \<or> p = snd z"
  using assms by (auto simp: set_of_vpc_def)

lemma set_of_vpc_Nil [simp]: "set_of_vpc [] = {}"
  by (simp add: set_of_vpc_def)

lemma set_of_vpc_empty_iff: "set_of_vpc zs = {} \<longleftrightarrow> zs = []"
  by (simp add: set_of_vpc_def)

lemma set_of_vpc_Cons: "set_of_vpc (z # zs) = insert (fst z) (insert (snd z) (set_of_vpc zs))"
  by (simp add: set_of_vpc_def insert_commute)

lemma is_vpcI:
  "zs \<noteq> [] \<Longrightarrow> (\<And>i. Suc i < length zs \<Longrightarrow> snd (zs ! i) = fst (zs ! Suc i)) \<Longrightarrow>
    set zs \<subseteq> Nshifts {f1, f2} \<Longrightarrow> is_vpc zs"
  by (simp add: is_vpc_def)

lemma is_vpcD:
  assumes "is_vpc zs"
  shows "zs \<noteq> []" and "Suc i < length zs \<Longrightarrow> snd (zs ! i) = fst (zs ! Suc i)"
    and "set zs \<subseteq> Nshifts {f1, f2}"
  using assms by (simp_all add: is_vpc_def)

lemma set_of_vpcE_vpc:
  assumes "is_vpc zs" and "p \<in> set_of_vpc zs"
  assumes "p = fst (hd zs) \<Longrightarrow> thesis"
  assumes "p = snd (last zs) \<Longrightarrow> thesis"
  assumes "\<And>i. i < length zs \<Longrightarrow> Suc i < length zs \<Longrightarrow> p = snd (zs ! i) \<Longrightarrow> p = fst (zs ! Suc i) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "zs \<noteq> []" by (rule is_vpcD)
  from assms(2) obtain z where "z \<in> set zs" and disj: "p = fst z \<or> p = snd z" by (rule set_of_vpcE)
  from this(1) obtain i where "i < length zs" and z: "z = zs ! i" by (metis in_set_conv_nth)
  from disj show ?thesis
  proof
    assume p: "p = fst z"
    show ?thesis
    proof (cases i)
      case 0
      show ?thesis by (rule assms(3)) (simp add: p z 0 hd_conv_nth \<open>zs \<noteq> []\<close>)
    next
      case (Suc j)
      with \<open>i < length zs\<close> have "j < length zs" and *: "Suc j < length zs" by simp_all
      thus ?thesis
      proof (rule assms(5))
        show "p = fst (zs ! Suc j)" by (simp only: p z Suc)
        also from assms(1) * have "\<dots> = snd (zs ! j)" by (rule is_vpcD(2)[symmetric])
        finally show "p = snd (zs ! j)" .
      qed
    qed
  next
    assume p: "p = snd z"
    show ?thesis
    proof (cases "Suc i = length zs")
      case True
      hence i: "i = length zs - 1" by simp
      show ?thesis by (rule assms(4)) (simp add: p z i last_conv_nth \<open>zs \<noteq> []\<close>)
    next
      case False
      with \<open>i < length zs\<close> have *: "Suc i < length zs" by simp
      with \<open>i < length zs\<close> show ?thesis
      proof (rule assms(5))
        show "p = snd (zs ! i)" by (simp only: p z)
        also from assms(1) * have "\<dots> = fst (zs ! Suc i)" by (rule is_vpcD)
        finally show "p = fst (zs ! Suc i)" .
      qed
    qed
  qed
qed

lemma vpc_is_nat_pm_pair:
  assumes "is_vpc zs" and "z \<in> set zs"
  shows "is_nat_pm_pair z"
proof -
  from assms(1) have "set zs \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  with assms(2) have "z \<in> Nshifts {f1, f2}" ..
  thus ?thesis by (rule Nshifts_is_nat_pm_pair)
qed

lemma vpc_is_nat_pm:
  assumes "is_vpc zs" and "p \<in> set_of_vpc zs"
  shows "is_nat_pm p"
  using assms(2) unfolding set_of_vpc_def
proof
  assume "p \<in> fst ` set zs"
  then obtain z where "z \<in> set zs" and p: "p = fst z" ..
  from assms(1) this(1) have "is_nat_pm_pair z" by (rule vpc_is_nat_pm_pair)
  thus ?thesis unfolding p by (rule is_nat_pm_pairD)
next
  assume "p \<in> snd ` set zs"
  then obtain z where "z \<in> set zs" and p: "p = snd z" ..
  from assms(1) this(1) have "is_nat_pm_pair z" by (rule vpc_is_nat_pm_pair)
  thus ?thesis unfolding p by (rule is_nat_pm_pairD)
qed

lemma set_of_vpc_alt_1:
  assumes "is_vpc zs"
  shows "set_of_vpc zs = insert (fst (hd zs)) (snd ` set zs)" (is "_ = ?A")
proof
  have "fst ` set zs \<subseteq> ?A"
  proof
    fix p
    assume "p \<in> fst ` set zs"
    then obtain z where "z \<in> set zs" and p: "p = fst z" ..
    from this(1) obtain i where "i < length zs" and z: "z = zs ! i" by (metis in_set_conv_nth)
    show "p \<in> ?A"
    proof (cases i)
      case 0
      moreover from assms have "zs \<noteq> []" by (rule is_vpcD)
      ultimately show ?thesis by (simp add: p z hd_conv_nth)
    next
      case i: (Suc j)
      from assms \<open>i < length zs\<close> have "p = snd (zs ! j)"
        unfolding p z i by (rule is_vpcD(2)[symmetric])
      moreover from \<open>i < length zs\<close> have "j < length zs" by (simp add: i)
      ultimately show ?thesis by auto
    qed
  qed
  thus "set_of_vpc zs \<subseteq> ?A" unfolding set_of_vpc_def by blast
next
  from assms have "zs \<noteq> []" by (rule is_vpcD)
  hence "hd zs \<in> set zs" by (rule hd_in_set)
  thus "?A \<subseteq> set_of_vpc zs" unfolding set_of_vpc_def by blast
qed

lemma set_of_vpc_alt_2:
  assumes "is_vpc zs"
  shows "set_of_vpc zs = insert (snd (last zs)) (fst ` set zs)" (is "_ = ?A")
proof
  have "snd ` set zs \<subseteq> ?A"
  proof
    fix p
    assume "p \<in> snd ` set zs"
    then obtain z where "z \<in> set zs" and p: "p = snd z" ..
    from this(1) obtain i where "i < length zs" and z: "z = zs ! i" by (metis in_set_conv_nth)
    show "p \<in> ?A"
    proof (cases "length zs = Suc i")
      case True
      moreover from assms have "zs \<noteq> []" by (rule is_vpcD)
      ultimately show ?thesis by (simp add: p z last_conv_nth)
    next
      case False
      with \<open>i < length zs\<close> have "Suc i < length zs" by simp
      with assms have "snd (zs ! i) = fst (zs ! Suc i)" by (rule is_vpcD)
      thus ?thesis using \<open>Suc i < length zs\<close> by (auto simp: p z)
    qed
  qed
  thus "set_of_vpc zs \<subseteq> ?A" unfolding set_of_vpc_def by blast
next
  from assms have "zs \<noteq> []" by (rule is_vpcD)
  hence "last zs \<in> set zs" by (rule last_in_set)
  thus "?A \<subseteq> set_of_vpc zs" unfolding set_of_vpc_def by blast
qed

lemma is_vpc_takeI: "is_vpc zs \<Longrightarrow> 0 < n \<Longrightarrow> is_vpc (take n zs)"
  using set_take_subset[of n zs] by (auto intro!: is_vpcI dest: is_vpcD)

lemma is_vpc_dropI:
  assumes "is_vpc zs" and "n < length zs"
  shows "is_vpc (drop n zs)"
proof (rule is_vpcI)
  from assms(2) show "drop n zs \<noteq> []" by simp
next
  fix i
  assume "Suc i < length (drop n zs)"
  with assms(2) have *: "Suc (n + i) < length zs" by simp
  from assms(2) have "snd (drop n zs ! i) = snd (zs ! (n + i))" by simp
  also from assms(1) * have "\<dots> = fst (zs ! Suc (n + i))" by (rule is_vpcD)
  also from assms(2) have "\<dots> = fst (drop n zs ! Suc i)" by simp
  finally show "snd (drop n zs ! i) = fst (drop n zs ! Suc i)" .
next
  from assms(1) have "set zs \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  with set_drop_subset show "set (drop n zs) \<subseteq> Nshifts {f1, f2}" by (rule subset_trans)
qed

lemma is_vpc_singleton [simp]: "is_vpc [z] \<longleftrightarrow> z \<in> Nshifts {f1, f2}"
  by (simp add: is_vpc_def)

lemma is_vpc_appendI:
  assumes "is_vpc zs1" and "is_vpc zs2" and "snd (last zs1) = fst (hd zs2)"
  shows "is_vpc (zs1 @ zs2)"
proof (rule is_vpcI)
  from assms(2) have "zs2 \<noteq> []" by (rule is_vpcD)
  from assms(1) have "zs1 \<noteq> []" by (rule is_vpcD)
  thus "zs1 @ zs2 \<noteq> []" by simp

  fix i
  assume 1: "Suc i < length (zs1 @ zs2)"
  show "snd ((zs1 @ zs2) ! i) = fst ((zs1 @ zs2) ! Suc i)"
  proof (rule linorder_cases)
    assume 2: "Suc i < length zs1"
    with assms(1) have "snd (zs1 ! i) = fst (zs1 ! Suc i)" by (rule is_vpcD)
    with 2 show ?thesis by (simp add: nth_append)
  next
    assume 2: "Suc i = length zs1"
    hence 3: "i = length zs1 - 1" and "i < length zs1" by simp_all
    have "snd ((zs1 @ zs2) ! i) = snd (zs1 ! i)" by (simp add: nth_append \<open>i < length zs1\<close>)
    also from \<open>zs1 \<noteq> []\<close> have "\<dots> = snd (last zs1)" by (simp add: last_conv_nth 3)
    also have "\<dots> = fst (hd zs2)" by fact
    also from \<open>zs2 \<noteq> []\<close> have "\<dots> = fst (zs2 ! 0)" by (simp add: hd_conv_nth)
    also have "\<dots> = fst ((zs1 @ zs2) ! (Suc i))" by (simp add: nth_append 2)
    finally show ?thesis .
  next
    assume 2: "length zs1 < Suc i"
    with 1 have "Suc (i - length zs1) < length zs2" by simp
    with assms(2) have "snd (zs2 ! (i - length zs1)) = fst (zs2 ! Suc (i - length zs1))" by (rule is_vpcD)
    with 2 show ?thesis by (simp add: nth_append Suc_diff_le)
  qed
next
  from assms(1) have "set zs1 \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  moreover from assms(2) have "set zs2 \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  ultimately show "set (zs1 @ zs2) \<subseteq> Nshifts {f1, f2}" by simp
qed

lemma is_vpc_ConsI:
  assumes "is_vpc zs" and "z \<in> Nshifts {f1, f2}" and "snd z = fst (hd zs)"
  shows "is_vpc (z # zs)"
proof -
  have "is_vpc ([z] @ zs)" by (rule is_vpc_appendI) (simp_all add: assms)
  thus ?thesis by simp
qed

lemma is_vpc_ConsD:
  assumes "is_vpc (z # zs)"
  shows "z \<in> Nshifts {f1, f2}" and "zs \<noteq> [] \<Longrightarrow> is_vpc zs" and "zs \<noteq> [] \<Longrightarrow> snd z = fst (hd zs)"
proof -
  have "z \<in> set (z # zs)" by simp
  also from assms have "\<dots> \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  finally show "z \<in> Nshifts {f1, f2}" .
next
  assume "zs \<noteq> []"
  hence "Suc 0 < length (z # zs)" by simp
  with assms have "is_vpc (drop (Suc 0) (z # zs))" and "snd ((z # zs) ! 0) = fst ((z # zs) ! Suc 0)"
    by (rule is_vpc_dropI, rule is_vpcD)
  thus "is_vpc zs" and "snd z = fst (hd zs)" using \<open>zs \<noteq> []\<close> by (simp_all add: hd_conv_nth)
qed

lemma is_vpc_revI:
  assumes "is_vpc zs"
  shows "is_vpc (map prod.swap (rev zs))" (is "is_vpc ?zs")
proof (rule is_vpcI)
  from assms have "zs \<noteq> []" by (rule is_vpcD)
  thus "?zs \<noteq> []" by simp
next
  fix i
  assume "Suc i < length ?zs"
  hence *: "Suc i < length zs" by simp
  moreover define j where "j = length zs - Suc (Suc i)"
  ultimately have Sj: "Suc j = length zs - Suc i" and **: "Suc j < length zs" by simp_all
  from * have "fst (?zs ! Suc i) = snd (zs ! j)" by (simp add: rev_nth j_def)
  also from assms ** have "\<dots> = fst (zs ! Suc j)" by (rule is_vpcD)
  also from * have "\<dots> = snd (?zs ! i)" by (simp add: rev_nth Sj)
  finally show "snd (?zs ! i) = fst (?zs ! Suc i)" by (rule sym)
next
  have "set ?zs = prod.swap ` set zs" by simp
  also from assms have "set zs \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  finally have "set ?zs \<subseteq> prod.swap ` Nshifts {f1, f2}" by blast
  thus "set ?zs \<subseteq> Nshifts {f1, f2}" by simp
qed

lemma replace_vpc:
  assumes "is_vpc zs" and "i \<le> j" and "j < length zs"
    and "zs2 \<noteq> [] \<Longrightarrow> is_vpc zs2" and "zs2 \<noteq> [] \<Longrightarrow> fst (hd zs2) = fst (zs ! i)"
    and "zs2 \<noteq> [] \<Longrightarrow> snd (last zs2) = snd (zs ! j)"
    and "zs2 = [] \<Longrightarrow> i = 0 \<Longrightarrow> Suc j = length zs \<Longrightarrow> False" and "zs2 = [] \<Longrightarrow> fst (zs ! i) = snd (zs ! j)"
  obtains zs' where "is_vpc zs'" and "fst (hd zs') = fst (hd zs)" and "snd (last zs') = snd (last zs)"
    and "set zs' = set (take i zs) \<union> set (drop (Suc j) zs) \<union> set zs2"
    and "length zs + length zs2 = length zs' + (Suc j - i)" and "zs' = take i zs @ zs2 @ drop (Suc j) zs"
proof
  let ?zs = "take i zs @ zs2 @ drop (Suc j) zs"
  from assms(1) have "zs \<noteq> []" by (rule is_vpcD)
  from assms(2, 3) have "i < length zs" by (rule le_less_trans)

  have "is_vpc ?zs \<and> fst (hd ?zs) = fst (hd zs) \<and> snd (last ?zs) = snd (last zs)"
  proof (cases i)
    case i: 0
    let ?ys = "zs2 @ drop (Suc j) zs"
    have "is_vpc ?ys \<and> fst (hd ?ys) = fst (hd zs) \<and> snd (last ?ys) = snd (last zs)"
    proof (cases "Suc j = length zs")
      case True
      with assms(7) \<open>i = 0\<close> have "zs2 \<noteq> []" by blast
      hence "is_vpc zs2" and "fst (hd zs2) = fst (zs ! i)" and "snd (last zs2) = snd (zs ! j)"
        by (rule assms(4-6))+
      moreover from True have "j = length zs - 1" by simp
      ultimately show ?thesis using \<open>zs \<noteq> []\<close> by (simp add: i hd_conv_nth last_conv_nth)
    next
      case False
      with assms(3) have *: "Suc j < length zs" by simp
      hence "snd (last ?ys) = snd (last zs)" by simp
      moreover have "is_vpc ?ys \<and> fst (hd ?ys) = fst (hd zs)"
      proof (cases "zs2 = []")
        case True
        let ?xs = "drop (Suc j) zs"
        from \<open>zs \<noteq> []\<close> have "fst (hd zs) = fst (zs ! i)" by (simp add: hd_conv_nth \<open>i = 0\<close>)
        also from True have "\<dots> = snd (zs ! j)" by (rule assms(8))
        also from assms(1) * have "\<dots> = fst (zs ! Suc j)" by (rule is_vpcD)
        also from * have "zs ! Suc j = hd ?xs" by (rule hd_drop_conv_nth[symmetric])
        finally have "fst (hd zs) = fst (hd (drop (Suc j) zs))" .
        moreover from assms(1) * have "is_vpc ?xs" by (rule is_vpc_dropI)
        ultimately show ?thesis by (simp add: True)
      next
        case False
        hence "snd (last zs2) = snd (zs ! j)" by (rule assms(6))
        also from assms(1) * have "\<dots> = fst (zs ! Suc j)" by (rule is_vpcD)
        also from * have "zs ! Suc j = hd (drop (Suc j) zs)" by (rule hd_drop_conv_nth[symmetric])
        finally have "is_vpc ?ys" using assms(1) * False by (intro is_vpc_appendI is_vpc_dropI assms(4))
        moreover from \<open>zs \<noteq> []\<close> False have "fst (hd ?ys) = fst (hd zs)"
          by (simp add: assms(5) \<open>i = 0\<close>) (simp add: hd_conv_nth)
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
    thus ?thesis by (simp add: i)
  next
    case i: (Suc k)
    hence "0 < i" and "k < length zs" using \<open>i < length zs\<close> by simp_all
    hence "fst (hd ?zs) = fst (hd zs)" by (simp add: hd_append \<open>zs \<noteq> []\<close>)
    moreover have "is_vpc ?zs \<and> snd (last ?zs) = snd (last zs)"
    proof (cases "Suc j = length zs")
      case True
      hence j: "j = length zs - 1" by simp
      let ?ys = "take i zs @ zs2"
      have "is_vpc ?ys \<and> snd (last ?ys) = snd (last zs)"
      proof (cases "zs2 = []")
        case True
        from assms(1) \<open>i < length zs\<close> have "snd (zs ! k) = fst (zs ! i)" unfolding i by (rule is_vpcD)
        also from True have "\<dots> = snd (zs ! j)" by (rule assms(8))
        finally have "snd (last (take i zs)) = snd (last zs)" using \<open>k < length zs\<close>
          by (simp add: i last_take_conv_nth) (simp add: j last_conv_nth \<open>zs \<noteq> []\<close>)
        moreover from assms(1) \<open>0 < i\<close> have "is_vpc (take i zs)" by (rule is_vpc_takeI)
        ultimately show ?thesis by (simp add: True)
      next
        case False
        from \<open>k < length zs\<close> have "snd (last (take i zs)) = snd (zs ! k)"
          by (simp add: i last_take_conv_nth)
        also from assms(1) \<open>i < length zs\<close> have "\<dots> = fst (zs ! i)" unfolding i by (rule is_vpcD)
        also from False have "\<dots> = fst (hd zs2)" by (rule assms(5)[symmetric])
        finally have "is_vpc ?ys"
          using assms(1) \<open>0 < i\<close> False by (intro is_vpc_appendI is_vpc_takeI assms(4))
        moreover from False have "snd (last ?ys) = snd (last zs)"
          by (simp add: assms(6) j) (simp add: last_conv_nth \<open>zs \<noteq> []\<close>)
        ultimately show ?thesis by simp
      qed
      thus ?thesis by (simp add: True)
    next
      case False
      with assms(3) have *: "Suc j < length zs" by simp
      hence "snd (last ?zs) = snd (last zs)" by simp
      moreover have "is_vpc ?zs"
      proof (cases "zs2 = []")
        case True
        let ?ys = "take i zs @ drop (Suc j) zs"
        from \<open>k < length zs\<close> have "snd (last (take i zs)) = snd (zs ! k)"
          by (simp only: i last_take_conv_nth)
        also from assms(1) \<open>i < length zs\<close> have "\<dots> = fst (zs ! i)" unfolding i by (rule is_vpcD)
        also from True have "\<dots> = snd (zs ! j)" by (rule assms(8))
        also from assms(1) * have "\<dots> = fst (zs ! Suc j)" by (rule is_vpcD)
        also from * have "\<dots> = fst (hd (drop (Suc j) zs))" by (simp only: hd_drop_conv_nth)
        finally have "is_vpc ?ys"
          using assms(1) \<open>0 < i\<close> * by (intro is_vpc_appendI is_vpc_takeI is_vpc_dropI)
        thus ?thesis by (simp add: True)
      next
        case False
        with assms(1) \<open>0 < i\<close> * show ?thesis
        proof (intro is_vpc_appendI is_vpc_takeI assms(4) is_vpc_dropI)
          from False have "snd (last zs2) = snd (zs ! j)" by (rule assms(6))
          also from assms(1) * have "\<dots> = fst (zs ! Suc j)" by (rule is_vpcD)
          finally show "snd (last zs2) = fst (hd (drop (Suc j) zs))"
            using False * by (simp add: hd_drop_conv_nth)
        next
          from assms(1) \<open>i < length zs\<close> have "snd (zs ! k) = fst (zs ! i)" unfolding i by (rule is_vpcD)
          also from False have "\<dots> = fst (hd zs2)" by (rule assms(5)[symmetric])
          finally show "snd (last (take i zs)) = fst (hd (zs2 @ drop (Suc j) zs))"
            using False \<open>k < length zs\<close> by (simp add: hd_append i last_take_conv_nth)
        qed
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
  thus "is_vpc ?zs" and "fst (hd ?zs) = fst (hd zs)" and "snd (last ?zs) = snd (last zs)" by simp_all

  show "set ?zs = set (take i zs) \<union> set (drop (Suc j) zs) \<union> set zs2" by (simp add: ac_simps)

  from assms(2, 3) show "length zs + length zs2 = length ?zs + (Suc j - i)" by simp
qed (rule refl)

lemma vpc_induct [consumes 1, case_names single Cons]:
  assumes "is_vpc zs" and "\<And>z. z \<in> Nshifts {f1, f2} \<Longrightarrow> P [z]"
    and "\<And>z zs. is_vpc zs \<Longrightarrow> z \<in> Nshifts {f1, f2} \<Longrightarrow> snd z = fst (hd zs) \<Longrightarrow> P zs \<Longrightarrow> P (z # zs)"
  shows "P zs"
  using assms(1)
proof (induct zs)
  case Nil
  thus ?case by (simp add: is_vpc_def)
next
  case (Cons z zs)
  from Cons(2) have 1: "z \<in> Nshifts {f1, f2}" by (rule is_vpc_ConsD)
  show ?case
  proof (cases "zs = []")
    case True
    moreover from 1 have "P [z]" by (rule assms(2))
    ultimately show ?thesis by simp
  next
    case False
    with Cons(2) have 2: "is_vpc zs" and 3: "snd z = fst (hd zs)" by (rule is_vpc_ConsD)+
    from this(1) have "P zs" by (rule Cons(1))
    with 2 1 3 show ?thesis by (rule assms(3))
  qed
qed

lemma vpc_trans_fst:
  assumes "transp rel" and "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> rel (fst z) (snd z)"
    and "i < j" and "j < length zs"
  shows "rel (fst (zs ! i)) (fst (zs ! j))"
proof -
  from assms(4) have "0 < j - i" by simp
  then obtain k where "j - i = Suc k" using Suc_pred' by blast
  hence j: "j = i + Suc k" by simp
  from assms(5) show ?thesis unfolding j
  proof (induct k)
    case 0
    hence "Suc i < length zs" by simp
    hence "zs ! i \<in> set zs" by simp
    hence "rel (fst (zs ! i)) (snd (zs ! i))" by (rule assms(3))
    also from assms(2) \<open>Suc i < length zs\<close> have "\<dots> = fst (zs ! Suc i)" by (rule is_vpcD)
    finally show ?case by simp
  next
    case (Suc k)
    from Suc.prems have *: "Suc (Suc (i + k)) < length zs" by simp
    hence "Suc (i + k) < length zs" by simp
    hence "i + Suc k < length zs" by simp
    hence "rel (fst (zs ! i)) (fst (zs ! (i + Suc k)))" by (rule Suc.hyps)
    also have "\<dots> = fst (zs ! (Suc (i + k)))" by simp
    also from nth_mem have "rel \<dots> (snd (zs ! (Suc (i + k))))" by (rule assms(3)) fact
    also(assms(1)[THEN transpD]) from assms(2) * have "\<dots> = fst (zs ! (Suc (Suc (i + k))))"
      by (rule is_vpcD)
    finally show ?case by simp
  qed
qed

corollary vpc_trans_snd:
  assumes "transp rel" and "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> rel (fst z) (snd z)"
    and "i < j" and "j < length zs"
  shows "rel (snd (zs ! i)) (snd (zs ! j))"
proof -
  from assms(5) have "zs ! j \<in> set zs" by simp
  hence *: "rel (fst (zs ! j)) (snd (zs ! j))" by (rule assms(3))
  from assms(4) have "Suc i \<le> j" by simp
  hence "Suc i < length zs" using assms(5) by (rule le_less_trans)
  with assms(2) have eq: "snd (zs ! i) = fst (zs ! Suc i)" by (rule is_vpcD)
  show ?thesis
  proof (cases "Suc i = j")
    case True
    with * show ?thesis by (simp only: eq)
  next
    case False
    with \<open>Suc i \<le> j\<close> have "Suc i < j" by simp
    with assms(1-3) have "rel (fst (zs ! Suc i)) (fst (zs ! j))" using assms(5) by (rule vpc_trans_fst)
    with assms(1) show ?thesis using * unfolding eq by (rule transpD)
  qed
qed

corollary vpc_trans_fst_snd:
  assumes "transp rel" and "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> rel (fst z) (snd z)"
    and "i \<le> j" and "j < length zs"
  shows "rel (fst (zs ! i)) (snd (zs ! j))"
proof -
  from assms(4, 5) have "i < length zs" by (rule le_less_trans)
  hence "zs ! i \<in> set zs" by simp
  hence *: "rel (fst (zs ! i)) (snd (zs ! i))" by (rule assms(3))
  show ?thesis
  proof (cases "i = j")
    case True
    with * show ?thesis by simp
  next
    case False
    with assms(4) have "i < j" by simp
    with assms(1-3) have "rel (snd (zs ! i)) (snd (zs ! j))" using assms(5) by (rule vpc_trans_snd)
    with assms(1) * show ?thesis by (rule transpD)
  qed
qed

corollary vpc_trans_hd:
  assumes "transp rel" and "reflp rel" and "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> rel (fst z) (snd z)"
    and "p \<in> set_of_vpc zs"
  shows "rel (fst (hd zs)) p"
proof -
  from assms(5) obtain z where "z \<in> set zs" and disj: "p = fst z \<or> p = snd z" by (rule set_of_vpcE)
  from this(1) obtain j where "j < length zs" and z: "z = zs ! j" by (metis in_set_conv_nth)
  from assms(3) have "zs \<noteq> []" by (rule is_vpcD)
  hence hd: "hd zs = zs ! 0" by (rule hd_conv_nth)
  from disj show ?thesis unfolding hd
  proof
    assume p: "p = fst z"
    show "rel (fst (zs ! 0)) p" unfolding p z
    proof (cases "j = 0")
      case True
      from assms(2) show "rel (fst (zs ! 0)) (fst (zs ! j))" unfolding True by (rule reflpD)
    next
      case False
      hence "0 < j" by simp
      with assms(1, 3, 4) show "rel (fst (zs ! 0)) (fst (zs ! j))"
        using \<open>j < length zs\<close> by (rule vpc_trans_fst)
    qed
  next
    assume p: "p = snd z"
    from assms(1, 3, 4) le0 \<open>j < length zs\<close> show "rel (fst (zs ! 0)) p"
      unfolding p z by (rule vpc_trans_fst_snd)
  qed
qed

corollary vpc_trans_last:
  assumes "transp rel" and "reflp rel" and "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> rel (fst z) (snd z)"
    and "p \<in> set_of_vpc zs"
  shows "rel p (snd (last zs))"
proof -
  from assms(5) obtain z where "z \<in> set zs" and disj: "p = fst z \<or> p = snd z" by (rule set_of_vpcE)
  from this(1) obtain i where "i < length zs" and z: "z = zs ! i" by (metis in_set_conv_nth)
  from assms(3) have "zs \<noteq> []" by (rule is_vpcD)
  hence *: "length zs - 1 < length zs" and last: "last zs = zs ! (length zs - 1)"
    by (simp_all add: last_conv_nth)
  from disj show ?thesis unfolding last
  proof
    assume p: "p = snd z"
    show "rel p (snd (zs ! (length zs - 1)))" unfolding p z
    proof (cases "i = length zs - 1")
      case True
      from assms(2) show "rel (snd (zs ! i)) (snd (zs ! (length zs - 1)))"
        unfolding True by (rule reflpD)
    next
      case False
      with \<open>i < length zs\<close> have "i < length zs - 1" by simp
      with assms(1, 3, 4) show "rel (snd (zs ! i)) (snd (zs ! (length zs - 1)))"
        using * by (rule vpc_trans_snd)
    qed
  next
    assume p: "p = fst z"
    from \<open>i < length zs\<close> have "i \<le> length zs - 1" by simp
    with assms(1, 3, 4) show "rel p (snd (zs ! (length zs - 1)))" using *
      unfolding p z by (rule vpc_trans_fst_snd)
  qed
qed

corollary vpc_trans_hd_last:
  assumes "transp rel" and "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> rel (fst z) (snd z)"
  shows "rel (fst (hd zs)) (snd (last zs))"
proof -
  from assms(2) have "zs \<noteq> []" by (rule is_vpcD)
  hence "length zs - 1 < length zs" by simp
  with assms le0 have "rel (fst (zs ! 0)) (snd (zs ! (length zs - 1)))" by (rule vpc_trans_fst_snd)
  with \<open>zs \<noteq> []\<close> show ?thesis by (simp add: hd_conv_nth last_conv_nth)
qed

subsection \<open>Correspondence Between VPCs and Ideal Elements\<close>

context
  assumes f1_pbinomial: "is_proper_binomial f1"
  assumes f2_pbinomial: "is_proper_binomial f2"
begin

lemma Nshifts_fst_not_eq_snd:
  assumes "z \<in> Nshifts {f1, f2}"
  shows "fst z \<noteq> snd z"
proof -
  from f1_pbinomial f2_pbinomial have "is_proper_binomial f" if "f \<in> {f1, f2}" for f
    using that by blast
  thus ?thesis using assms by (rule Nshifts_fst_not_eq_snd_proper_binomials)
qed

lemma vpc_fst_not_eq_snd:
  assumes "is_vpc zs" and "z \<in> set zs"
  shows "fst z \<noteq> snd z" and "to_nat_pm (fst z) \<noteq> to_nat_pm (snd z)"
proof -
  from assms(1) have "set zs \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  with assms(2) have "z \<in> Nshifts {f1, f2}" ..
  thus "fst z \<noteq> snd z" by (rule Nshifts_fst_not_eq_snd)

  from assms have "is_nat_pm_pair z" by (rule vpc_is_nat_pm_pair)
  hence "is_nat_pm (fst z)" and "is_nat_pm (snd z)" by (rule is_nat_pm_pairD)+
  hence "of_nat_pm (to_nat_pm (fst z)) = fst z" and "of_nat_pm (to_nat_pm (snd z)) = snd z"
    by (simp_all add: of_nat_pm_comp_to_nat_pm)
  with \<open>fst z \<noteq> snd z\<close> have "of_nat_pm (to_nat_pm (fst z)) \<noteq> (of_nat_pm (to_nat_pm (snd z))::_ \<Rightarrow>\<^sub>0 rat)"
    by simp
  thus "to_nat_pm (fst z) \<noteq> to_nat_pm (snd z)" by simp
qed

text \<open>If VPCs were defined w.r.t. arbitrary sets of polynomials, the following lemma could most
  probably be proved for arbitrary sets of proper binomials.\<close>

lemma idealE_vpc:
  assumes "f \<in> ideal {f1, f2}" and "is_proper_binomial f" and "monomial 1 (lp f) \<notin> ideal {f1, f2}"
  obtains zs where "is_vpc zs" and "fst (hd zs) = of_nat_pm (lp f)" and "snd (last zs) = of_nat_pm (tp f)"
proof -
  let ?l = "of_nat_pm (lp f)"
  define F where "F = {f1, f2}"
  have "finite F" by (simp add: F_def)
  moreover from assms(1) have "f \<in> ideal F" by (simp only: F_def)
  ultimately obtain q where f: "f = (\<Sum>f0\<in>F. q f0 * f0)" by (rule ideal.span_finiteE)
  from assms(2) have keys_f: "keys f = {lp f, tp f}" by (rule punit.keys_proper_binomial)
  define Y where "Y = (\<lambda>f0. {t \<in> keys (q f0). \<exists>zs. is_vpc zs \<and> fst (hd zs) = ?l \<and>
                            (t +\<^sub>N poly_point f0 \<in> set zs \<or> t +\<^sub>N prod.swap (poly_point f0) \<in> set zs)})"
  define q' where "q' = (\<lambda>f0. except (q f0) (- Y f0))"
  define q'' where "q'' = (\<lambda>f0. except (q f0) (Y f0))"
  have "Y f0 \<subseteq> keys (q f0)" for f0 by (simp add: Y_def)
  hence keys_q': "keys (q' f0) = Y f0" for f0 by (simp add: q'_def keys_except Int_absorb1)
  let ?f = "(\<Sum>f0\<in>F. q' f0 * f0)"
  have vpcE: thesis0
    if "t \<in> keys ?f" and "\<And>zs. is_vpc zs \<Longrightarrow> fst (hd zs) = ?l \<Longrightarrow> snd (last zs) = of_nat_pm t \<Longrightarrow> thesis0"
    for thesis0 t
  proof -
    have "keys ?f \<subseteq> (\<Union>f0\<in>F. keys (q' f0 * f0))" by (rule keys_sum_subset)
    with that(1) have "t \<in> (\<Union>f0\<in>F. keys (q' f0 * f0))" ..
    thus ?thesis
    proof
      fix f0
      assume "f0 \<in> F"
      hence "f0 = f1 \<or> f0 = f2" by (simp add: F_def)
      with f1_pbinomial f2_pbinomial have "is_proper_binomial f0" by blast
      hence keys_f0: "keys f0 = {lp f0, tp f0}" by (rule punit.keys_proper_binomial)
      assume "t \<in> keys (q' f0 * f0)"
      then obtain s u where "s \<in> keys (q' f0)" and "u \<in> keys f0" and t: "t = s + u"
        by (rule in_keys_timesE)
      from this(2) have u_cases: "u = lp f0 \<or> u = tp f0" by (simp add: keys_f0)
      from \<open>s \<in> keys (q' f0)\<close> obtain zs where "is_vpc zs" and eq1: "fst (hd zs) = ?l"
        and "s +\<^sub>N poly_point f0 \<in> set zs \<or> s +\<^sub>N prod.swap (poly_point f0) \<in> set zs"
        unfolding keys_q' Y_def by blast
      from this(3) show ?thesis
      proof
        assume "s +\<^sub>N poly_point f0 \<in> set zs"
        then obtain i where "i < length zs" and eq2: "zs ! i = s +\<^sub>N poly_point f0"
          by (meson in_set_conv_nth)
        let ?zs = "take (Suc i) zs"
        from \<open>is_vpc zs\<close> have "is_vpc ?zs" by (rule is_vpc_takeI) simp
        have eq3: "fst (hd ?zs) = ?l" by (simp add: eq1)
        from \<open>i < length zs\<close> have eq4: "last ?zs = s +\<^sub>N poly_point f0" and "?zs \<noteq> []"
          by (auto simp: last_take_conv_nth eq2)
        from u_cases show ?thesis
        proof
          assume u: "u = lp f0"
          let ?ys = "?zs @ [s +\<^sub>N prod.swap (poly_point f0)]"
          from \<open>is_vpc ?zs\<close> have "is_vpc ?ys"
          proof (rule is_vpc_appendI)
            from \<open>f0 \<in> F\<close> show "is_vpc [s +\<^sub>N prod.swap (poly_point f0)]"
              by (auto simp: F_def intro: NshiftsI)
          qed (simp add: eq4 nat_plus_point_pair_def)
          moreover from \<open>?zs \<noteq> []\<close> have "fst (hd ?ys) = ?l" by (simp add: eq1)
          moreover from \<open>i < length zs\<close> have "snd (last ?ys) = of_nat_pm t"
            by (simp add: nat_plus_point_pair_def t u fst_poly_point of_nat_pm_plus)
          ultimately show ?thesis by (rule that(2))
        next
          assume "u = tp f0"
          hence "snd (last ?zs) = of_nat_pm t"
            by (simp add: eq4 nat_plus_point_pair_def snd_poly_point t of_nat_pm_plus)
          with \<open>is_vpc ?zs\<close> eq3 show ?thesis by (rule that(2))
        qed
      next
        assume "s +\<^sub>N prod.swap (poly_point f0) \<in> set zs"
        then obtain i where "i < length zs" and eq2: "zs ! i = s +\<^sub>N prod.swap (poly_point f0)"
          by (meson in_set_conv_nth)
        let ?zs = "take (Suc i) zs"
        from \<open>is_vpc zs\<close> have "is_vpc ?zs" by (rule is_vpc_takeI) simp
        have eq3: "fst (hd ?zs) = ?l" by (simp add: eq1)
        from \<open>i < length zs\<close> have eq4: "last ?zs = s +\<^sub>N prod.swap (poly_point f0)" and "?zs \<noteq> []"
          by (auto simp: last_take_conv_nth eq2)
        from u_cases show ?thesis
        proof
          assume u: "u = tp f0"
          let ?ys = "?zs @ [s +\<^sub>N poly_point f0]"
          from \<open>is_vpc ?zs\<close> have "is_vpc ?ys"
          proof (rule is_vpc_appendI)
            from \<open>f0 \<in> F\<close> show "is_vpc [s +\<^sub>N poly_point f0]" by (auto simp: F_def intro: NshiftsI)
          qed (simp add: eq4 nat_plus_point_pair_def)
          moreover from \<open>?zs \<noteq> []\<close> have "fst (hd ?ys) = ?l" by (simp add: eq1)
          moreover from \<open>i < length zs\<close> have "snd (last ?ys) = of_nat_pm t"
            by (simp add: nat_plus_point_pair_def t u snd_poly_point of_nat_pm_plus)
          ultimately show ?thesis by (rule that(2))
        next
          assume "u = lp f0"
          hence "snd (last ?zs) = of_nat_pm t"
            by (simp add: eq4 nat_plus_point_pair_def fst_poly_point t of_nat_pm_plus)
          with \<open>is_vpc ?zs\<close> eq3 show ?thesis by (rule that(2))
        qed
      qed
    qed
  qed
  have "f = (\<Sum>f0\<in>F. (q'' f0 + q' f0) * f0)" by (simp only: q''_def q'_def f flip: except_decomp)
  also have "\<dots> = (\<Sum>f0\<in>F. q'' f0 * f0) + ?f" (is "_ = ?g + _") by (simp add: algebra_simps sum.distrib)
  finally have f': "f = ?g + ?f" .
  have 1: "t \<notin> keys ?g" if "is_vpc zs" and "fst (hd zs) = ?l" and "snd (last zs) = of_nat_pm t" for t zs
  proof
    from that(1) have "zs \<noteq> []" by (rule is_vpcD)
    assume "t \<in> keys ?g"
    also have "\<dots> \<subseteq> (\<Union>f0\<in>F. keys (q'' f0 * f0))" by (rule keys_sum_subset)
    finally have "t \<in> (\<Union>f0\<in>F. keys (q'' f0 * f0))" .
    thus False
    proof
      fix f0
      assume "f0 \<in> F"
      hence "f0 = f1 \<or> f0 = f2" by (simp add: F_def)
      with f1_pbinomial f2_pbinomial have "is_proper_binomial f0" by blast
      hence keys_f0: "keys f0 = {lp f0, tp f0}" by (rule punit.keys_proper_binomial)
      assume "t \<in> keys (q'' f0 * f0)"
      then obtain s u where "s \<in> keys (q'' f0)" and "u \<in> keys f0" and t: "t = s + u"
        by (rule in_keys_timesE)
      have "keys (q'' f0) \<subseteq> keys (q f0)" by (simp add: q''_def keys_except)
      with \<open>s \<in> keys (q'' f0)\<close> have "s \<in> keys (q f0)" ..
      from \<open>u \<in> keys f0\<close> have u_cases: "u = lp f0 \<or> u = tp f0" by (simp add: keys_f0)
      thus ?thesis
      proof
        assume u: "u = lp f0"
        let ?zs = "zs @ [s +\<^sub>N poly_point f0]"
        from \<open>is_vpc zs\<close> have "is_vpc ?zs"
        proof (rule is_vpc_appendI)
          from \<open>f0 \<in> F\<close> show "is_vpc [s +\<^sub>N poly_point f0]" by (auto simp: F_def intro: NshiftsI)
        qed (simp add: that(3) nat_plus_point_pair_def fst_poly_point t u of_nat_pm_plus)
        moreover from \<open>zs \<noteq> []\<close> have "fst (hd ?zs) = ?l" by (simp add: that(2))
        ultimately have "s \<in> Y f0" using \<open>s \<in> keys (q f0)\<close> by (auto simp: Y_def)
        hence "s \<notin> keys (q'' f0)" by (simp add: q''_def keys_except)
        thus ?thesis using \<open>s \<in> keys (q'' f0)\<close> ..
      next
        assume u: "u = tp f0"
        let ?zs = "zs @ [s +\<^sub>N prod.swap (poly_point f0)]"
        from \<open>is_vpc zs\<close> have "is_vpc ?zs"
        proof (rule is_vpc_appendI)
          from \<open>f0 \<in> F\<close> show "is_vpc [s +\<^sub>N prod.swap (poly_point f0)]"
            by (auto simp: F_def intro: NshiftsI)
        qed (simp add: that(3) nat_plus_point_pair_def snd_poly_point t u of_nat_pm_plus)
        moreover from \<open>zs \<noteq> []\<close> have "fst (hd ?zs) = ?l" by (simp add: that(2))
        ultimately have "s \<in> Y f0" using \<open>s \<in> keys (q f0)\<close> by (auto simp: Y_def)
        hence "s \<notin> keys (q'' f0)" by (simp add: q''_def keys_except)
        thus ?thesis using \<open>s \<in> keys (q'' f0)\<close> ..
      qed
    qed
  qed
  have disjnt: "keys ?g \<inter> keys ?f = {}"
  proof (intro subset_antisym subsetI)
    fix t
    assume "t \<in> keys ?g \<inter> keys ?f"
    hence "t \<in> keys ?g" and "t \<in> keys ?f" by simp_all
    from this(2) obtain zs where "is_vpc zs" and "fst (hd zs) = ?l"
      and "snd (last zs) = of_nat_pm t" by (rule vpcE)
    hence "t \<notin> keys ?g" by (rule 1)
    thus "t \<in> {}" using \<open>t \<in> keys ?g\<close> ..
  qed simp
  hence "keys ?g \<union> keys ?f = keys (?g + ?f)" by (rule keys_add)
  also have "\<dots> = {lp f, tp f}" by (simp only: keys_f flip: f')
  finally have *: "keys ?g \<union> keys ?f = {lp f, tp f}" .
  moreover have "lp f \<notin> keys ?g"
  proof -
    have "lp f \<in> keys f" by (simp add: keys_f)
    also have "\<dots> \<subseteq> (\<Union>f0\<in>F. keys (q f0 * f0))" unfolding f by (rule keys_sum_subset)
    finally obtain f0 where "f0 \<in> F" and "lp f \<in> keys (q f0 * f0)" ..
    from this(2) obtain s u where "s \<in> keys (q f0)" and "u \<in> keys f0" and lp: "lp f = s + u"
      by (rule in_keys_timesE)
    from \<open>f0 \<in> F\<close> have f0_cases: "f0 = f1 \<or> f0 = f2" by (simp add: F_def)
    with f1_pbinomial f2_pbinomial have "is_proper_binomial f0" by blast
    hence "keys f0 = {lp f0, tp f0}" by (rule punit.keys_proper_binomial)
    with \<open>u \<in> keys f0\<close> have "u = lp f0 \<or> u = tp f0" by simp
    thus ?thesis
    proof
      assume u: "u = lp f0"
      let ?zs = "[s +\<^sub>N poly_point f0, s +\<^sub>N prod.swap (poly_point f0)]"
      have "is_vpc ?zs"
      proof (rule is_vpc_ConsI)
        from \<open>f0 \<in> F\<close> show "is_vpc [s +\<^sub>N prod.swap (poly_point f0)]"
          by (auto simp: F_def intro: NshiftsI)
      next
        from \<open>f0 \<in> F\<close> show "s +\<^sub>N poly_point f0 \<in> Nshifts {f1, f2}" unfolding F_def by (intro NshiftsI)
      qed (simp add: nat_plus_point_pair_def)
      moreover have "fst (hd ?zs) = of_nat_pm (lp f)" and "snd (last ?zs) = of_nat_pm (lp f)"
        by (simp_all add: nat_plus_point_pair_def poly_point_def lp u of_nat_pm_plus)
      ultimately show ?thesis by (rule 1)
    next
      assume u: "u = tp f0"
      let ?zs = "[s +\<^sub>N prod.swap (poly_point f0), s +\<^sub>N poly_point f0]"
      have "is_vpc ?zs"
      proof (rule is_vpc_ConsI)
        from \<open>f0 \<in> F\<close> show "is_vpc [s +\<^sub>N poly_point f0]" by (auto simp: F_def intro: NshiftsI)
      next
        from \<open>f0 \<in> F\<close> show "s +\<^sub>N prod.swap (poly_point f0) \<in> Nshifts {f1, f2}"
          unfolding F_def by (intro NshiftsI)
      qed (simp add: nat_plus_point_pair_def)
      moreover have "fst (hd ?zs) = of_nat_pm (lp f)" and "snd (last ?zs) = of_nat_pm (lp f)"
        by (simp_all add: nat_plus_point_pair_def poly_point_def lp u of_nat_pm_plus)
      ultimately show ?thesis by (rule 1)
    qed
  qed
  ultimately have "lp f \<in> keys ?f" by blast
  have "tp f \<in> keys ?f"
  proof (rule ccontr)
    assume "tp f \<notin> keys ?f"
    with \<open>lp f \<in> keys ?f\<close> * have keys_f': "keys ?f = {lp f}" by blast
    moreover define c where "c = lookup ?f (lp f)"
    ultimately have "monomial c (lp f) = ?f"
      by (auto intro!: poly_mapping_eqI simp: lookup_single when_def)
    also have "\<dots> \<in> ideal F" by (rule ideal.sum_in_spanI)
    finally have "monomial (1 / c) 0 * monomial c (lp f) \<in> ideal F" by (rule ideal.span_scale)
    moreover have "c \<noteq> 0" by (simp add: c_def keys_f')
    ultimately have "monomial 1 (lp f) \<in> ideal {f1, f2}" by (simp add: times_monomial_monomial F_def)
    with assms(3) show False ..
  qed
  then obtain zs where "is_vpc zs" and "fst (hd zs) = ?l" and "snd (last zs) = of_nat_pm (tp f)"
    by (rule vpcE)
  thus ?thesis ..
qed

text \<open>Lemma \<open>idealE_vpc\<close> corresponds to Theorem 3.3.14 in @{cite "MWW2015"}. There, however, it is
  proved quite differently, relying on the fairly complicated Lemma 3.3.11. The proof of this lemma
  contains a substantial gap which, intuitively, seems correct and could thus be closed, but I have
  no idea how to do it rigorously. That is the reason for the different approach here.\<close>

definition deg_vpc :: "('x point \<times> 'x point) list \<Rightarrow> rat"
  where "deg_vpc zs = (if zs = [] then 0 else Max (deg_pm ` set_of_vpc zs))"

text \<open>Although @{const deg_vpc} will mostly be applied to arguments \<open>zs\<close> satisfying @{prop "is_vpc zs"}
  and which are therefore not empty, it still makes sense to treat the case @{prop "zs = []"}
  separately in the definition of @{const deg_vpc}.\<close>

lemma deg_vpc_max:
  assumes "p \<in> set_of_vpc zs"
  shows "deg_pm p \<le> deg_vpc zs"
proof -
  from finite_set_of_vpc have "finite (deg_pm ` set_of_vpc zs)" by (rule finite_imageI)
  moreover from assms have "deg_pm p \<in> deg_pm ` set_of_vpc zs" by (rule imageI)
  ultimately have "deg_pm p \<le> Max (deg_pm ` set_of_vpc zs)" by (rule Max_ge)
  with assms show ?thesis by (auto simp: deg_vpc_def)
qed

lemma deg_vpc_leI:
  assumes "is_vpc zs" and "\<And>p. p \<in> set_of_vpc zs \<Longrightarrow> deg_pm p \<le> d"
  shows "deg_vpc zs \<le> d"
proof-
  from assms(1) have "zs \<noteq> []" by (rule is_vpcD)
  from finite_set_of_vpc have "finite (deg_pm ` set_of_vpc zs)" by (rule finite_imageI)
  moreover from \<open>zs \<noteq> []\<close> have "deg_pm ` set_of_vpc zs \<noteq> {}" by (simp add: set_of_vpc_empty_iff)
  ultimately have "Max (deg_pm ` set_of_vpc zs) \<le> d"
  proof (rule Max.boundedI)
    fix a
    assume "a \<in> deg_pm ` set_of_vpc zs"
    then obtain p where "p \<in> set_of_vpc zs" and a: "a = deg_pm p" ..
    from this(1) show "a \<le> d" unfolding a by (rule assms)
  qed
  with \<open>zs \<noteq> []\<close> show ?thesis by (simp add: deg_vpc_def)
qed

lemma deg_vpc_Cons: "zs \<noteq> [] \<Longrightarrow> deg_vpc (z # zs) = max (deg_vpc [z]) (deg_vpc zs)"
  by (simp add: deg_vpc_def set_of_vpc_Cons finite_set_of_vpc max.assoc set_of_vpc_empty_iff)

corollary deg_vpc_Cons_ge: "deg_vpc [z] \<le> deg_vpc (z # zs)"
  by (cases "zs = []") (simp_all add: deg_vpc_Cons)

lemma vpcE_ideal_singleton:
  assumes "z \<in> Nshifts {f1, f2}"
  obtains q1 q2 where "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {fst z, snd z}"
    and "rat (poly_deg (q1 * f1)) \<le> deg_vpc [z]" and "rat (poly_deg (q2 * f2)) \<le> deg_vpc [z]"
  using assms
proof (rule NshiftsE)
  fix f t
  assume "f \<in> {f1, f2}" and "z = t +\<^sub>N poly_point f \<or> z = t +\<^sub>N prod.swap (poly_point f)"
  from this(2) have eq1: "{fst z, snd z} = of_nat_pm ` {t + lp f, t + tp f}"
    by (auto simp: poly_point_def nat_plus_point_pair_def of_nat_pm_plus)
  hence eq1': "set_of_vpc [z] = of_nat_pm ` {t + lp f, t + tp f}" by (simp add: set_of_vpc_Cons)
  from \<open>f \<in> {f1, f2}\<close> have "f = f1 \<or> f = f2" by blast
  thus ?thesis
  proof
    assume f: "f = f1"
    show ?thesis
    proof
      have "keys (monomial 1 t * f1 + 0 * f2) = keys (monomial 1 t * f1)" by simp
      also from f1_pbinomial have eq2: "keys (monomial 1 t * f1) = {t + lp f1, t + tp f1}"
        by (simp add: times_monomial_left punit.keys_monom_mult punit.keys_proper_binomial)
      finally show "of_nat_pm ` keys (monomial 1 t * f1 + 0 * f2) = {fst z, snd z}"
        by (simp only: f eq1)

      have "poly_deg (monomial 1 t * f1) \<le> max (deg_pm (t + lp f1)) (deg_pm (t + tp f1))"
        by (rule poly_deg_leI) (auto simp: eq2)
      also have "rat \<dots> = max (deg_pm (of_nat_pm (t + lp f1))) (deg_pm (of_nat_pm (t + tp f1)))"
        by (simp add: deg_of_nat_pm)
      also have "\<dots> \<le> deg_vpc [z]" by (intro max.boundedI deg_vpc_max) (simp_all add: f eq1')
      finally show "rat (poly_deg (monomial 1 t * f1)) \<le> deg_vpc [z]" by simp

      have "rat (poly_deg (0 * f2)) \<le> rat (poly_deg (monomial 1 t * f1))" by simp
      also have "\<dots> \<le> deg_vpc [z]" by fact
      finally show "rat (poly_deg (0 * f2)) \<le> deg_vpc [z]" .
    qed
  next
    assume f: "f = f2"
    show ?thesis
    proof
      have "keys (0 * f1 + monomial 1 t * f2) = keys (monomial 1 t * f2)" by simp
      also from f2_pbinomial have eq2: "keys (monomial 1 t * f2) = {t + lp f2, t + tp f2}"
        by (simp add: times_monomial_left punit.keys_monom_mult punit.keys_proper_binomial)
      finally show "of_nat_pm ` keys (0 * f1 + monomial 1 t * f2) = {fst z, snd z}"
        by (simp only: f eq1)

      have "poly_deg (monomial 1 t * f2) \<le> max (deg_pm (t + lp f2)) (deg_pm (t + tp f2))"
        by (rule poly_deg_leI) (auto simp: eq2)
      also have "rat \<dots> = max (deg_pm (of_nat_pm (t + lp f2))) (deg_pm (of_nat_pm (t + tp f2)))"
        by (simp add: deg_of_nat_pm)
      also have "\<dots> \<le> deg_vpc [z]" by (intro max.boundedI deg_vpc_max) (simp_all add: f eq1')
      finally show "rat (poly_deg (monomial 1 t * f2)) \<le> deg_vpc [z]" by simp

      have "rat (poly_deg (0 * f1)) \<le> rat (poly_deg (monomial 1 t * f2))" by simp
      also have "\<dots> \<le> deg_vpc [z]" by fact
      finally show "rat (poly_deg (0 * f1)) \<le> deg_vpc [z]" .
    qed
  qed
qed

lemma vpcE_ideal:
  assumes "is_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)"
  obtains q1 q2 where "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {fst (hd zs), snd (last zs)}"
    and "rat (poly_deg (q1 * f1)) \<le> deg_vpc zs" and "rat (poly_deg (q2 * f2)) \<le> deg_vpc zs"
  using assms
proof (induct zs arbitrary: thesis rule: vpc_induct)
  case (single z)
  from single(1) obtain q1 q2 where "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {fst z, snd z}"
    and 1: "rat (poly_deg (q1 * f1)) \<le> deg_vpc [z]" and 2: "rat (poly_deg (q2 * f2)) \<le> deg_vpc [z]"
    by (rule vpcE_ideal_singleton)
  from this(1) have "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {fst (hd [z]), snd (last [z])}"
    by simp
  thus ?case using 1 2 by (rule single)
next
  case (Cons z zs)
  from Cons.hyps(1) have "zs \<noteq> []" by (rule is_vpcD)
  with Cons.prems(2) have "fst z \<noteq> snd (last zs)" by simp
  from Cons.hyps(2) have "is_nat_pm_pair z" by (rule Nshifts_is_nat_pm_pair)
  hence "is_nat_pm (fst z)" by (rule is_nat_pm_pairD)
  hence eq_z: "of_nat_pm (to_nat_pm (fst z)) = fst z" by (simp add: of_nat_pm_comp_to_nat_pm)
  from Cons.hyps(1) last_in_set have "is_nat_pm_pair (last zs)"
    by (rule vpc_is_nat_pm_pair) fact
  hence "is_nat_pm (snd (last zs))" by (rule is_nat_pm_pairD)
  hence eq0: "of_nat_pm (to_nat_pm (snd (last zs))) = snd (last zs)"
    by (simp add: of_nat_pm_comp_to_nat_pm)
  hence "of_nat_pm (to_nat_pm (fst z)) \<noteq> (of_nat_pm (to_nat_pm (snd (last zs)))::_ \<Rightarrow>\<^sub>0 rat)"
    using \<open>fst z \<noteq> snd (last zs)\<close> by (simp add: eq_z)
  hence neq1: "to_nat_pm (fst z) \<noteq> to_nat_pm (snd (last zs))" by simp
  from Cons.hyps(2) have "is_vpc [z]" by simp
  hence neq2: "to_nat_pm (fst z) \<noteq> to_nat_pm (snd z)" by (rule vpc_fst_not_eq_snd) simp
  from Cons.hyps(2) obtain q1 q2 where eq1: "of_nat_pm ` keys (q1 * f1 + q2 * f2) = {fst z, snd z}"
    and 10: "rat (poly_deg (q1 * f1)) \<le> deg_vpc [z]" and 20: "rat (poly_deg (q2 * f2)) \<le> deg_vpc [z]"
    by (rule vpcE_ideal_singleton)
  let ?f = "q1 * f1 + q2 * f2"
  from 10 deg_vpc_Cons_ge have 1: "rat (poly_deg (q1 * f1)) \<le> deg_vpc (z # zs)" by (rule order.trans)
  from 20 deg_vpc_Cons_ge have 2: "rat (poly_deg (q2 * f2)) \<le> deg_vpc (z # zs)" by (rule order.trans)
  show ?case
  proof (cases "fst (hd zs) = snd (last zs)")
    case True
    with \<open>zs \<noteq> []\<close> have eq2: "snd (last (z # zs)) = snd z" by (simp add: Cons.hyps(3))
    have "of_nat_pm ` keys ?f = {fst (hd (z # zs)), snd (last (z # zs))}"
      by (simp only: eq1 eq2 list.sel(1))
    thus ?thesis using 1 2 by (rule Cons.prems)
  next
    case False
    then obtain q1' q2' where eq2: "of_nat_pm ` keys (q1' * f1 + q2' * f2) = {fst (hd zs), snd (last zs)}"
      and 30: "rat (poly_deg (q1' * f1)) \<le> deg_vpc zs" and 40: "rat (poly_deg (q2' * f2)) \<le> deg_vpc zs"
      using Cons.hyps(4) by blast
    from \<open>zs \<noteq> []\<close> 30 have 3: "rat (poly_deg (q1' * f1)) \<le> deg_vpc (z # zs)" by (simp add: deg_vpc_Cons)
    from \<open>zs \<noteq> []\<close> 40 have 4: "rat (poly_deg (q2' * f2)) \<le> deg_vpc (z # zs)" by (simp add: deg_vpc_Cons)
    let ?g = "q1' * f1 + q2' * f2"
    have eq3: "of_nat_pm ` keys (q1' * f1 + q2' * f2) = {snd z, snd (last zs)}"
      by (simp only: eq2 Cons.hyps(3))
    define c where "c = lookup ?f (to_nat_pm (snd z))"
    define d where "d = lookup ?g (to_nat_pm (snd z))"
    have "keys ?f = to_nat_pm ` (of_nat_pm::_ \<Rightarrow> ('x \<Rightarrow>\<^sub>0 rat)) ` keys ?f" by (simp add: image_image)
    also have "\<dots> = {to_nat_pm (fst z), to_nat_pm (snd z)}" by (simp add: eq1)
    finally have keys_f: "keys ?f = {to_nat_pm (fst z), to_nat_pm (snd z)}" .
    hence "c \<noteq> 0" by (simp add: c_def)
    have "keys ?g = to_nat_pm ` (of_nat_pm::_ \<Rightarrow> ('x \<Rightarrow>\<^sub>0 rat)) ` keys ?g" by (simp add: image_image)
    also have "\<dots> = {to_nat_pm (snd z), to_nat_pm (snd (last zs))}" by (simp add: eq3)
    finally have keys_g: "keys ?g = {to_nat_pm (snd z), to_nat_pm (snd (last zs))}" .
    hence "d \<noteq> 0" by (simp add: d_def)
    with \<open>c \<noteq> 0\<close> have "- (c / d) \<noteq> 0" by simp
    hence keys_g': "keys ((- (c / d)) \<cdot> ?g) = {to_nat_pm (snd z), to_nat_pm (snd (last zs))}"
      by (simp add: keys_map_scale keys_g)
    define q1'' where "q1'' = - (c / d) \<cdot> q1'"
    define q2'' where "q2'' = - (c / d) \<cdot> q2'"
    show ?thesis
    proof (rule Cons.prems)
      have "keys ((q1 + q1'') * f1 + (q2 + q2'') * f2) = keys (?f + (- (c / d)) \<cdot> ?g)"
        by (simp add: q1''_def q2''_def map_scale_eq_times algebra_simps)
      also have "\<dots> = {to_nat_pm (fst z), to_nat_pm (snd (last zs))}" (is "?A = ?B")
      proof (intro subset_antisym insert_subsetI empty_subsetI, rule subsetI)
        fix t
        assume "t \<in> ?A"
        also have "\<dots> \<subseteq> keys ?f \<union> keys ((- (c / d)) \<cdot> ?g)" by (rule keys_add_subset)
        finally have "t \<in> insert (to_nat_pm (snd z)) ?B" by (auto simp: keys_f keys_g')
        moreover have "t \<noteq> to_nat_pm (snd z)"
        proof
          assume "t = to_nat_pm (snd z)"
          with \<open>d \<noteq> 0\<close> have "t \<notin> ?A" by (simp add: lookup_add c_def d_def)
          thus False using \<open>t \<in> ?A\<close> ..
        qed
        ultimately show "t \<in> ?B" by simp
      next
        have "to_nat_pm (fst z) \<in> keys ?f" by (simp add: keys_f)
        moreover from neq1 neq2 have "to_nat_pm (fst z) \<notin> keys ((- (c / d)) \<cdot> ?g)"
          by (simp add: keys_g')
        ultimately show "to_nat_pm (fst z) \<in> ?A" by (rule in_keys_plusI1)
      next
        have neq3: "to_nat_pm (snd (last zs)) \<noteq> to_nat_pm (snd z)"
        proof -
          from Cons.hyps(1) hd_in_set have "is_nat_pm_pair (hd zs)"
            by (rule vpc_is_nat_pm_pair) fact
          hence "is_nat_pm (fst (hd zs))" by (rule is_nat_pm_pairD)
          hence "of_nat_pm (to_nat_pm (fst (hd zs))) = fst (hd zs)" by (simp add: of_nat_pm_comp_to_nat_pm)
          hence "of_nat_pm (to_nat_pm (snd z)) \<noteq> (of_nat_pm (to_nat_pm (snd (last zs)))::_ \<Rightarrow>\<^sub>0 rat)"
            using False by (simp add: Cons.hyps(3) eq0)
          thus ?thesis by simp
        qed
        have "to_nat_pm (snd (last zs)) \<in> keys ((- (c / d)) \<cdot> ?g)" by (simp add: keys_g')
        moreover from neq1[symmetric] neq3 False have "to_nat_pm (snd (last zs)) \<notin> keys ?f"
          by (simp add: keys_f)
        ultimately show "to_nat_pm (snd (last zs)) \<in> ?A" by (rule in_keys_plusI2)
      qed
      finally show "of_nat_pm ` keys ((q1 + q1'') * f1 + (q2 + q2'') * f2) =
                      {fst (hd (z # zs)), snd (last (z # zs))}"
        using \<open>zs \<noteq> []\<close> by (simp add: eq_z eq0)
    next
      have "poly_deg ((q1 + q1'') * f1) = poly_deg (q1 * f1 + q1'' * f1)" by (simp only: algebra_simps)
      also have "\<dots> \<le> max (poly_deg (q1 * f1)) (poly_deg (q1'' * f1))" by (rule poly_deg_plus_le)
      also have "poly_deg (q1'' * f1) = poly_deg ((- (c / d)) \<cdot> (q1' * f1))"
        by (simp only: q1''_def map_scale_eq_times ac_simps)
      also from \<open>- (c / d) \<noteq> 0\<close> have "\<dots> = poly_deg (q1' * f1)" by (simp add: poly_deg_map_scale)
      finally have "rat (poly_deg ((q1 + q1'') * f1)) \<le>
                      max (rat (poly_deg (q1 * f1))) (rat (poly_deg (q1' * f1)))"
        by simp
      also from 1 3 have "\<dots> \<le> deg_vpc (z # zs)" by (rule max.boundedI)
      finally show "rat (poly_deg ((q1 + q1'') * f1)) \<le> deg_vpc (z # zs)" .
    next
      have "poly_deg ((q2 + q2'') * f2) = poly_deg (q2 * f2 + q2'' * f2)" by (simp only: algebra_simps)
      also have "\<dots> \<le> max (poly_deg (q2 * f2)) (poly_deg (q2'' * f2))" by (rule poly_deg_plus_le)
      also have "poly_deg (q2'' * f2) = poly_deg ((- (c / d)) \<cdot> (q2' * f2))"
        by (simp only: q2''_def map_scale_eq_times ac_simps)
      also from \<open>- (c / d) \<noteq> 0\<close> have "\<dots> = poly_deg (q2' * f2)" by (simp add: poly_deg_map_scale)
      finally have "rat (poly_deg ((q2 + q2'') * f2)) \<le>
                      max (rat (poly_deg (q2 * f2))) (rat (poly_deg (q2' * f2)))"
        by simp
      also from 2 4 have "\<dots> \<le> deg_vpc (z # zs)" by (rule max.boundedI)
      finally show "rat (poly_deg ((q2 + q2'') * f2)) \<le> deg_vpc (z # zs)" .
    qed
  qed
qed

subsection \<open>Structure of VPCs\<close>

lemma thm_3_3_18:
  assumes "is_vpc zs" and "Suc i < length zs" and "zs ! i \<in> Nshifts {f}" and "zs ! Suc i \<in> Nshifts {f'}"
    and "{f, f'} = {f1, f2}"
  shows "overlap \<unlhd> snd (zs ! i)"
proof -
  from assms(3) obtain s where "zs ! i = s +\<^sub>N poly_point f \<or> zs ! i = s +\<^sub>N prod.swap (poly_point f)"
    by (rule NshiftsE_singleton)
  hence *: "gcs (of_nat_pm (lp f)) (of_nat_pm (tp f)) \<unlhd> snd (zs ! i)"
    by (auto simp: poly_point_def nat_plus_point_pair_def of_nat_pm_plus
            intro!: le_pm_increasing gcs_le_pm zero_le_of_nat_pm)
  from assms(4) obtain t where "zs ! Suc i = t +\<^sub>N poly_point f' \<or> zs ! Suc i = t +\<^sub>N prod.swap (poly_point f')"
    by (rule NshiftsE_singleton)
  hence "gcs (of_nat_pm (lp f')) (of_nat_pm (tp f')) \<unlhd> fst (zs ! Suc i)"
    by (auto simp: poly_point_def nat_plus_point_pair_def of_nat_pm_plus
            intro!: le_pm_increasing gcs_le_pm zero_le_of_nat_pm)
  also from assms(1, 2) have "\<dots> = snd (zs ! i)" by (rule is_vpcD(2)[symmetric])
  finally have "gcs (of_nat_pm (lp f')) (of_nat_pm (tp f')) \<unlhd> snd (zs ! i)" .
  moreover from assms(5) have "(f = f1 \<and> f' = f2) \<or> (f = f2 \<and> f' = f1)" by fastforce
  ultimately show ?thesis using * by (auto simp: overlap_alt intro: lcs_le_pm)
qed

definition min_length_vpc :: "('x point \<times> 'x point) list \<Rightarrow> bool"
  where "min_length_vpc zs \<longleftrightarrow> is_vpc zs \<and>
                   (\<forall>zs'. is_vpc zs' \<longrightarrow> fst (hd zs') = fst (hd zs) \<longrightarrow> snd (last zs') = snd (last zs) \<longrightarrow>
                          length zs \<le> length zs')"

definition min_vpc :: "('x point \<times> 'x point) list \<Rightarrow> bool"
  where "min_vpc zs \<longleftrightarrow> is_vpc zs \<and>
                   (\<forall>zs'. is_vpc zs' \<longrightarrow> fst (hd zs') = fst (hd zs) \<longrightarrow> snd (last zs') = snd (last zs) \<longrightarrow>
                          length zs < length zs' \<or> (length zs = length zs' \<and> deg_vpc zs \<le> deg_vpc zs'))"

lemma min_length_vpcI:
  "is_vpc zs \<Longrightarrow> (\<And>zs'. is_vpc zs' \<Longrightarrow> fst (hd zs') = fst (hd zs) \<Longrightarrow> snd (last zs') = snd (last zs) \<Longrightarrow>
          length zs \<le> length zs') \<Longrightarrow> min_length_vpc zs"
  by (simp add: min_length_vpc_def)

lemma min_length_vpcD:
  assumes "min_length_vpc zs"
  shows "is_vpc zs"
    and "is_vpc zs' \<Longrightarrow> fst (hd zs') = fst (hd zs) \<Longrightarrow> snd (last zs') = snd (last zs) \<Longrightarrow> length zs \<le> length zs'"
  using assms by (simp_all add: min_length_vpc_def)

lemma min_vpcI:
  "is_vpc zs \<Longrightarrow> (\<And>zs'. is_vpc zs' \<Longrightarrow> fst (hd zs') = fst (hd zs) \<Longrightarrow> snd (last zs') = snd (last zs) \<Longrightarrow>
          (length zs < length zs' \<or> (length zs = length zs' \<and> deg_vpc zs \<le> deg_vpc zs'))) \<Longrightarrow> min_vpc zs"
  by (simp add: min_vpc_def)

lemma min_vpcD:
  assumes "min_vpc zs"
  shows "is_vpc zs" and "min_length_vpc zs"
  using assms by (auto simp: min_length_vpc_def min_vpc_def)

lemma min_vpc_cases:
  assumes "min_vpc zs" and "is_vpc zs'" and "fst (hd zs') = fst (hd zs)" and "snd (last zs') = snd (last zs)"
  assumes "length zs < length zs' \<Longrightarrow> thesis"
  assumes "length zs = length zs' \<Longrightarrow> deg_vpc zs \<le> deg_vpc zs' \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: min_vpc_def)

lemma min_length_vpc_distinct:
  assumes "min_length_vpc zs"
  shows "distinct (map fst zs)" and "distinct (map snd zs)" and "distinct zs"
proof -
  from assms have "is_vpc zs" by (rule min_length_vpcD)

  show "distinct (map fst zs)"
  proof (intro distinctI notI)
    fix i j :: nat
    assume "i < j"
    moreover define k where "k = j - 1"
    ultimately have j: "j = Suc k" and "i \<le> k" by simp_all
    assume "i < length (map fst zs)" and "j < length (map fst zs)"
    hence "i < length zs" and "j < length zs" by simp_all
    moreover assume "map fst zs ! i = map fst zs ! j"
    ultimately have "fst (zs ! i) = fst (zs ! j)" by simp
    also from \<open>is_vpc zs\<close> \<open>j < length zs\<close> have "snd (zs ! k) = fst (zs ! j)"
      unfolding j by (rule is_vpcD)
    finally have "fst (zs ! i) = snd (zs ! k)" by (rule sym)
    from \<open>j < length zs\<close> have "k < length zs" by (simp add: k_def)
    with \<open>is_vpc zs\<close> \<open>i \<le> k\<close> obtain zs' where "is_vpc zs'"
      and "fst (hd zs') = fst (hd zs)" and "snd (last zs') = snd (last zs)"
      and eq: "length zs + length ([]::('x point \<times> 'x point) list) = length zs' + (Suc k - i)"
    proof (rule replace_vpc)
      assume "[] \<noteq> []"
      thus "is_vpc []" and "fst (hd []) = fst (zs ! i)" and "snd (last []) = snd (zs ! k)"
        by simp_all
    next
      assume "Suc k = length zs"
      with \<open>j < length zs\<close> show False by (simp add: j)
    next
      show "fst (zs ! i) = snd (zs ! k)" by fact
    qed
    from assms this(1, 2, 3) have "length zs \<le> length zs'" by (rule min_length_vpcD)
    moreover from eq have "length zs = length zs' + (j - i)" by (simp add: j)
    ultimately show False using \<open>i < j\<close> by simp
  qed

  show "distinct (map snd zs)"
  proof (intro distinctI notI)
    fix i j :: nat
    assume "i < j"
    hence "Suc i \<le> j" by simp
    assume "i < length (map snd zs)" and "j < length (map snd zs)"
    hence "i < length zs" and "j < length zs" by simp_all
    from \<open>Suc i \<le> j\<close> this(2) have "Suc i < length zs" by (rule le_less_trans)
    assume "map snd zs ! i = map snd zs ! j"
    hence "snd (zs ! i) = snd (zs ! j)" using \<open>i < length zs\<close> \<open>j < length zs\<close> by simp
    also from \<open>is_vpc zs\<close> \<open>Suc i < length zs\<close> have "snd (zs ! i) = fst (zs ! Suc i)"
      by (rule is_vpcD)
    finally have "fst (zs ! Suc i) = snd (zs ! j)" .
    from \<open>is_vpc zs\<close> \<open>Suc i \<le> j\<close> \<open>j < length zs\<close> obtain zs' where "is_vpc zs'"
      and "fst (hd zs') = fst (hd zs)" and "snd (last zs') = snd (last zs)"
      and eq: "length zs + length ([]::('x point \<times> 'x point) list) = length zs' + (Suc j - Suc i)"
    proof (rule replace_vpc)
      assume "[] \<noteq> []"
      thus "is_vpc []" and "fst (hd []) = fst (zs ! Suc i)" and "snd (last []) = snd (zs ! j)"
        by simp_all
    next
      assume "Suc i = 0"
      thus False by simp
    next
      show "fst (zs ! Suc i) = snd (zs ! j)" by fact
    qed
    from assms this(1, 2, 3) have "length zs \<le> length zs'" by (rule min_length_vpcD)
    moreover from eq have "length zs = length zs' + (j - i)" by simp
    ultimately show False using \<open>i < j\<close> by simp
  qed

  thus "distinct zs" by (simp only: distinct_map)
qed

corollary lem_3_3_19:
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "Suc i < length zs"
    and "zs ! i \<in> Nshifts {f}" and "zs ! Suc i \<in> Nshifts {f}"
  assumes "zs ! i \<in> pos_Nshifts {f} \<Longrightarrow> zs ! Suc i \<in> pos_Nshifts {f} \<Longrightarrow> thesis"
  assumes "zs ! i \<in> neg_Nshifts {f} \<Longrightarrow> zs ! Suc i \<in> neg_Nshifts {f} \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  have rl: ?thesis if "fst (zs ! i) = snd (zs ! Suc i)"
  proof (cases i)
    case i: 0
    show ?thesis
    proof (cases "length zs = Suc (Suc i)")
      case True
      from \<open>is_vpc zs\<close> have "zs \<noteq> []" by (rule is_vpcD)
      with that have "fst (hd zs) = snd (last zs)" by (simp add: hd_conv_nth last_conv_nth i True)
      with assms(2) show ?thesis ..
    next
      case False
      with assms(3) have 0: "Suc (Suc i) < length zs" by simp
      with \<open>is_vpc zs\<close> have "snd (zs ! Suc i) = fst (zs ! Suc (Suc i))" by (rule is_vpcD)
      hence eq5: "fst (zs ! i) = fst (zs ! Suc (Suc i))" by (simp only: that)
      from assms(1) have "distinct (map fst zs)" by (rule min_length_vpc_distinct)
      moreover from assms(3) have 1: "i < length (map fst zs)" by simp
      moreover from 0 have 2: "Suc (Suc i) < length (map fst zs)" by simp
      ultimately have "(map fst zs) ! i = (map fst zs) ! Suc (Suc i) \<longleftrightarrow> i = Suc (Suc i)"
        by (rule nth_eq_iff_index_eq)
      with 1 2 show ?thesis by (simp add: eq5)
    qed
  next
    case i: (Suc j)
    with assms(3) have "Suc j < length zs" by simp
    with \<open>is_vpc zs\<close> have "snd (zs ! j) = fst (zs ! Suc j)" by (rule is_vpcD)
    also have "\<dots> = snd (zs ! Suc (Suc j))" by (simp only: that flip: i)
    finally have eq5: "snd (zs ! j) = snd (zs ! Suc (Suc j))" .
    from assms(1) have "distinct (map snd zs)" by (rule min_length_vpc_distinct)
    moreover from \<open>Suc j < length zs\<close> have 1: "j < length (map snd zs)" by simp
    moreover from assms(3) have 2: "Suc (Suc j) < length (map snd zs)" by (simp add: i)
    ultimately have "(map snd zs) ! j = (map snd zs) ! Suc (Suc j) \<longleftrightarrow> j = Suc (Suc j)"
      by (rule nth_eq_iff_index_eq)
    with 1 2 show ?thesis by (simp add: eq5)
  qed
  from assms(4, 5) show ?thesis
  proof (elim NshiftsE_shift)
    assume "zs ! i \<in> pos_Nshifts {f}" and "zs ! Suc i \<in> pos_Nshifts {f}"
    thus ?thesis by (rule assms(6))
  next
    from \<open>is_vpc zs\<close> have eq1: "snd (zs ! i) = fst (zs ! Suc i)" using assms(3) by (rule is_vpcD)
    assume "zs ! i \<in> neg_Nshifts {f}"
    then obtain s where eq2: "zs ! i = s +\<^sub>N poly_point f" unfolding neg_Nshifts_singleton ..
    assume "zs ! Suc i \<in> pos_Nshifts {f}"
    then obtain t where eq3: "zs ! Suc i = t +\<^sub>N prod.swap (poly_point f)" unfolding pos_Nshifts_singleton ..
    from eq1 have "fst (zs ! i) = snd (zs ! Suc i)" by (simp add: eq2 eq3 nat_plus_point_pair_def)
    thus ?thesis by (rule rl)
  next
    from \<open>is_vpc zs\<close> have eq1: "snd (zs ! i) = fst (zs ! Suc i)" using assms(3) by (rule is_vpcD)
    assume "zs ! i \<in> pos_Nshifts {f}"
    then obtain s where eq2: "zs ! i = s +\<^sub>N prod.swap (poly_point f)" unfolding pos_Nshifts_singleton ..
    assume "zs ! Suc i \<in> neg_Nshifts {f}"
    then obtain t where eq3: "zs ! Suc i = t +\<^sub>N poly_point f" unfolding neg_Nshifts_singleton ..
    from eq1 have "fst (zs ! i) = snd (zs ! Suc i)" by (simp add: eq2 eq3 nat_plus_point_pair_def)
    thus ?thesis by (rule rl)
  next
    assume "zs ! i \<in> neg_Nshifts {f}" and "zs ! Suc i \<in> neg_Nshifts {f}"
    thus ?thesis by (rule assms(7))
  qed
qed

corollary lem_3_3_19':
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "i \<le> j" and "j < length zs"
    and "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> Nshifts {f}"
  assumes "(\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> pos_Nshifts {f}) \<Longrightarrow> thesis"
  assumes "(\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> neg_Nshifts {f}) \<Longrightarrow> thesis"
  shows thesis
proof -
  from le_refl assms(3) have "zs ! i \<in> Nshifts {f}" by (rule assms(5))
  thus ?thesis
  proof (rule NshiftsE_shift)
    assume *: "zs ! i \<in> pos_Nshifts {f}"
    show ?thesis
    proof (rule assms(6))
      fix k
      assume "i \<le> k"
      moreover define l where "l = k - i"
      ultimately have k: "k = i + l" by simp
      moreover assume "k \<le> j"
      ultimately have "i + l \<le> j" by simp
      thus "zs ! k \<in> pos_Nshifts {f}" unfolding k
      proof (induct l)
        case 0
        from * show ?case by simp
      next
        case (Suc l)
        from Suc.prems have "i + l \<le> j" and "Suc (i + l) \<le> j" by simp_all
        from this(1) have **: "zs ! (i + l) \<in> pos_Nshifts {f}" by (rule Suc.hyps)
        note assms(1, 2)
        moreover from \<open>Suc (i + l) \<le> j\<close> assms(4) have "Suc (i + l) < length zs" by (rule le_less_trans)
        moreover from _ \<open>i + l \<le> j\<close> have "zs ! (i + l) \<in> Nshifts {f}" by (rule assms(5)) simp
        moreover from _ \<open>Suc (i + l) \<le> j\<close> have "zs ! Suc (i + l) \<in> Nshifts {f}" by (rule assms(5)) simp
        ultimately show ?case
        proof (rule lem_3_3_19)
          assume "zs ! (i + l) \<in> neg_Nshifts {f}"
          with ** have "pos_Nshifts {f} \<inter> neg_Nshifts {f} \<noteq> {}" by blast
          hence "pos_Nshifts {f} = neg_Nshifts {f}" by (rule pos_neg_Nshifts_not_disjointD)
          moreover assume "zs ! Suc (i + l) \<in> neg_Nshifts {f}"
          ultimately show "zs ! (i + Suc l) \<in> pos_Nshifts {f}" by simp
        qed simp
      qed
    qed
  next
    assume *: "zs ! i \<in> neg_Nshifts {f}"
    show ?thesis
    proof (rule assms(7))
      fix k
      assume "i \<le> k"
      moreover define l where "l = k - i"
      ultimately have k: "k = i + l" by simp
      moreover assume "k \<le> j"
      ultimately have "i + l \<le> j" by simp
      thus "zs ! k \<in> neg_Nshifts {f}" unfolding k
      proof (induct l)
        case 0
        from * show ?case by simp
      next
        case (Suc l)
        from Suc.prems have "i + l \<le> j" and "Suc (i + l) \<le> j" by simp_all
        from this(1) have **: "zs ! (i + l) \<in> neg_Nshifts {f}" by (rule Suc.hyps)
        note assms(1, 2)
        moreover from \<open>Suc (i + l) \<le> j\<close> assms(4) have "Suc (i + l) < length zs" by (rule le_less_trans)
        moreover from _ \<open>i + l \<le> j\<close> have "zs ! (i + l) \<in> Nshifts {f}" by (rule assms(5)) simp
        moreover from _ \<open>Suc (i + l) \<le> j\<close> have "zs ! Suc (i + l) \<in> Nshifts {f}" by (rule assms(5)) simp
        ultimately show ?case
        proof (rule lem_3_3_19)
          assume "zs ! (i + l) \<in> pos_Nshifts {f}"
          with ** have "pos_Nshifts {f} \<inter> neg_Nshifts {f} \<noteq> {}" by blast
          hence "pos_Nshifts {f} = neg_Nshifts {f}" by (rule pos_neg_Nshifts_not_disjointD)
          moreover assume "zs ! Suc (i + l) \<in> pos_Nshifts {f}"
          ultimately show "zs ! (i + Suc l) \<in> neg_Nshifts {f}" by simp
        qed simp
      qed
    qed
  qed
qed

lemma vpc_pos_Nshifts_conv_vect:
  assumes "is_vpc zs" and "i \<le> j" and "j < length zs"
    and "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> pos_Nshifts {f}"
  shows "snd (zs ! j) + rat i \<cdot> vect f = fst (zs ! i) + rat (Suc j) \<cdot> vect f"
proof -
  define l where "l = j - i"
  with assms(2) have j: "j = i + l" by simp
  from assms(3, 4) show ?thesis unfolding j
  proof (induct l)
    case 0
    from le_refl have "zs ! i \<in> pos_Nshifts {f}" by (rule 0) simp
    thus ?case by (simp add: pos_Nshifts_conv_vect map_scale_distrib_right)
  next
    case (Suc l)
    from Suc.prems(1) have "Suc (i + l) < length zs" by simp
    have eq: "snd (zs ! (i + l)) + rat i \<cdot> vect f = fst (zs ! i) + rat (Suc (i + l)) \<cdot> vect f"
    proof (rule Suc.hyps)
      from Suc.prems(1) show "i + l < length zs" by simp
    next
      fix k
      assume "i \<le> k"
      assume "k \<le> i + l"
      hence "k \<le> i + Suc l" by simp
      with \<open>i \<le> k\<close> show "zs ! k \<in> pos_Nshifts {f}" by (rule Suc.prems)
    qed
    have "zs ! Suc (i + l) \<in> pos_Nshifts {f}" by (rule Suc.prems) simp_all
    hence "snd (zs ! Suc (i + l)) = fst (zs ! Suc (i + l)) + vect f"
      by (simp add: pos_Nshifts_conv_vect)
    also from assms(1) have "fst (zs ! Suc (i + l)) = snd (zs ! (i + l))"
      by (rule is_vpcD(2)[symmetric]) fact
    finally have "snd (zs ! Suc (i + l)) = snd (zs ! (i + l)) + vect f" .
    hence "snd (zs ! (i + Suc l)) + rat i \<cdot> vect f =
            (snd (zs ! (i + l)) + rat i \<cdot> vect f) + vect f" by simp
    also have "\<dots> = fst (zs ! i) + rat (Suc (i + l)) \<cdot> vect f + vect f" by (simp only: eq)
    finally show ?case by (simp add: map_scale_distrib_right map_scale_two_left)
  qed
qed

lemma vpc_neg_Nshifts_conv_vect:
  assumes "is_vpc zs" and "i \<le> j" and "j < length zs"
    and "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> neg_Nshifts {f}"
  shows "snd (zs ! j) + rat (Suc j) \<cdot> vect f = fst (zs ! i) + rat i \<cdot> vect f"
proof -
  define l where "l = j - i"
  with assms(2) have j: "j = i + l" by simp
  from assms(3, 4) show ?thesis unfolding j
  proof (induct l)
    case 0
    from le_refl have "zs ! i \<in> neg_Nshifts {f}" by (rule 0) simp
    thus ?case by (simp add: neg_Nshifts_conv_vect map_scale_distrib_right)
  next
    case (Suc l)
    from Suc.prems(1) have "Suc (i + l) < length zs" by simp
    have eq: "snd (zs ! (i + l)) + rat (Suc (i + l)) \<cdot> vect f = fst (zs ! i) + rat i \<cdot> vect f"
    proof (rule Suc.hyps)
      from Suc.prems(1) show "i + l < length zs" by simp
    next
      fix k
      assume "i \<le> k"
      assume "k \<le> i + l"
      hence "k \<le> i + Suc l" by simp
      with \<open>i \<le> k\<close> show "zs ! k \<in> neg_Nshifts {f}" by (rule Suc.prems)
    qed
    have "zs ! Suc (i + l) \<in> neg_Nshifts {f}" by (rule Suc.prems) simp_all
    hence "snd (zs ! Suc (i + l)) + vect f = fst (zs ! Suc (i + l))"
      by (simp add: neg_Nshifts_conv_vect)
    also from assms(1) have "fst (zs ! Suc (i + l)) = snd (zs ! (i + l))"
      by (rule is_vpcD(2)[symmetric]) fact
    finally have "snd (zs ! Suc (i + l)) + vect f = snd (zs ! (i + l))" .
    hence "snd (zs ! (i + Suc l)) + rat (Suc (i + l)) \<cdot> vect f + vect f =
            snd (zs ! (i + l)) + rat (Suc (i + l)) \<cdot> vect f" by simp
    also have "\<dots> = fst (zs ! i) + rat i \<cdot> vect f" by (simp only: eq)
    finally show ?case by (simp add: map_scale_distrib_right map_scale_two_left ac_simps)
  qed
qed

corollary vpc_Nshifts_conv_vect:
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "i \<le> j" and "j < length zs"
    and "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> Nshifts {f}"
  obtains l where "is_int l" and "abs l = rat (Suc j - i)" and "snd (zs ! j) = fst (zs ! i) + l \<cdot> vect f"
  using assms
proof (rule lem_3_3_19')
  let ?l = "rat (Suc j - i)"
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  moreover note assms(3, 4)
  moreover assume "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> pos_Nshifts {f}"
  ultimately have "snd (zs ! j) + rat i \<cdot> vect f = fst (zs ! i) + rat (Suc j) \<cdot> vect f"
    by (rule vpc_pos_Nshifts_conv_vect)
  with assms(3) have eq: "snd (zs ! j) = fst (zs ! i) + ?l \<cdot> vect f"
    by (simp add: of_nat_diff algebra_simps)
  show ?thesis
  proof
    show "is_int ?l" by (intro nat_is_int of_nat_is_nat)
  qed (simp_all add: eq)
next
  let ?l = "- rat (Suc j - i)"
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  moreover note assms(3, 4)
  moreover assume "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> neg_Nshifts {f}"
  ultimately have "snd (zs ! j) + rat (Suc j) \<cdot> vect f = fst (zs ! i) + rat i \<cdot> vect f"
    by (rule vpc_neg_Nshifts_conv_vect)
  with assms(3) have eq: "snd (zs ! j) = fst (zs ! i) + ?l \<cdot> vect f"
    by (simp add: of_nat_diff algebra_simps)
  show ?thesis
  proof
    show "is_int ?l" by (intro uminus_is_int nat_is_int of_nat_is_nat)
  qed (simp_all add: eq)
qed

text \<open>A VPC of minimal length, which starts and ends in the overlap region, lies in that region
  entirely:\<close>

lemma thm_3_3_20:
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "overlap \<unlhd> fst (hd zs)"
    and "overlap \<unlhd> snd (last zs)" and "p \<in> set_of_vpc zs"
  shows "overlap \<unlhd> p"
proof -
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  hence "zs \<noteq> []" and "set_of_vpc zs = insert (snd (last zs)) (fst ` set zs)"
    by (rule is_vpcD, rule set_of_vpc_alt_2)
  from this(2) assms(5) have "p = snd (last zs) \<or> p \<in> fst ` set zs" by simp
  thus ?thesis
  proof
    assume "p = snd (last zs)"
    with assms(4) show ?thesis by simp
  next
    assume "p \<in> fst ` set zs"
    then obtain z where "z \<in> set zs" and p: "p = fst z" ..
    from this(1) obtain i where "i < length zs" and z: "z = zs ! i" by (metis in_set_conv_nth)
    from this(1) show ?thesis unfolding p z
    proof (induct i)
      case 0
      from assms(3) \<open>zs \<noteq> []\<close> show ?case by (simp add: hd_conv_nth)
    next
      case (Suc i)
      from Suc.prems have "i < length zs" by simp
      hence overlap_i: "overlap \<unlhd> fst (zs ! i)" by (rule Suc.hyps)
      from \<open>i < length zs\<close> have "zs ! i \<in> set zs" by simp
      also from \<open>is_vpc zs\<close> have "\<dots> \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
      finally obtain f where "f \<in> {f1, f2}" and "zs ! i \<in> Nshifts {f}" by (rule NshiftsE_poly)
      obtain j where "i \<le> j" and "j < length zs" and "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> Nshifts {f}"
        and "overlap \<unlhd> snd (zs ! j)"
      proof -
        let ?B = "{j\<in>{i..<length zs}. zs ! j \<notin> Nshifts {f}}"
        show ?thesis
        proof (cases "?B = {}")
          case True
          show ?thesis
          proof
            from \<open>i < length zs\<close> show "i \<le> length zs - 1" and "length zs - 1 < length zs" by simp_all
          next
            fix k
            assume "i \<le> k" and "k \<le> length zs - 1"
            with True \<open>i < length zs\<close> show "zs ! k \<in> Nshifts {f}" by simp
          next
            from \<open>zs \<noteq> []\<close> assms(4) show "overlap \<unlhd> snd (zs ! (length zs - 1))"
              by (simp del: One_nat_def flip: last_conv_nth)
          qed
        next
          case False
          define j where "j = Min ?B"
          have "finite ?B" by simp
          hence "j \<in> ?B" using False unfolding j_def by (rule Min_in)
          hence "i \<le> j" and "j < length zs" and "zs ! j \<notin> Nshifts {f}" by simp_all
          from \<open>zs ! i \<in> Nshifts {f}\<close> this(3) have "i \<noteq> j" by blast
          with \<open>i \<le> j\<close> have "i < j" by simp
          hence "i \<le> j - 1" by simp
          have 1: "zs ! k \<in> Nshifts {f}" if "i \<le> k" and "k \<le> j - 1" for k
          proof (rule ccontr)
            from that(2) \<open>i < j\<close> have "k < j" by simp
            assume "zs ! k \<notin> Nshifts {f}"
            moreover from \<open>k < j\<close> \<open>j < length zs\<close> have "k < length zs" by (rule less_trans)
            ultimately have "k \<in> ?B" using that(1) by simp
            with \<open>finite ?B\<close> have "j \<le> k" unfolding j_def by (rule Min_le)
            with \<open>k < j\<close> show False by simp
          qed
          show ?thesis
          proof
            from \<open>i < j\<close> show "i \<le> j - 1" by simp
          next
            from \<open>j < length zs\<close> show "j - 1 < length zs" by simp
          next
            fix k
            assume "i \<le> k" and "k \<le> j - 1"
            thus "zs ! k \<in> Nshifts {f}" by (rule 1)
          next
            from \<open>j < length zs\<close> have "zs ! j \<in> set zs" by simp
            also from \<open>is_vpc zs\<close> have "\<dots> \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
            finally obtain f' where "f' \<in> {f1, f2}" and *: "zs ! j \<in> Nshifts {f'}" by (rule NshiftsE_poly)
            from this(2) \<open>zs ! j \<notin> Nshifts {f}\<close> have "f \<noteq> f'" by blast
            with \<open>f \<in> {f1, f2}\<close> \<open>f' \<in> {f1, f2}\<close> have "{f, f'} = {f1, f2}" by blast
            note \<open>is_vpc zs\<close>
            moreover from \<open>i < j\<close> \<open>j < length zs\<close> have "Suc (j - 1) < length zs" by simp
            moreover from \<open>i \<le> j - 1\<close> le_refl have "zs ! (j - 1) \<in> Nshifts {f}" by (rule 1)
            moreover from \<open>i < j\<close> * have "zs ! Suc (j - 1) \<in> Nshifts {f'}" by simp
            ultimately show "overlap \<unlhd> snd (zs ! (j - 1))"
              using \<open>{f, f'} = {f1, f2}\<close> by (rule thm_3_3_18)
          qed
        qed
      qed
      from assms(1, 2) this(1, 2, 3) obtain v where "fst (zs ! i) + 1 \<cdot> v = snd (zs ! i)"
        and eq: "fst (zs ! i) + (rat (Suc j) - rat i) \<cdot> v = snd (zs ! j)"
      proof (rule lem_3_3_19')
        assume s: "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> neg_Nshifts {f}"
        have "snd (zs ! i) + rat (Suc i) \<cdot> vect f = fst (zs ! i) + rat i \<cdot> vect f"
          using \<open>is_vpc zs\<close> le_refl \<open>i < length zs\<close>
        proof (rule vpc_neg_Nshifts_conv_vect)
          fix k
          assume "i \<le> k"
          assume "k \<le> i"
          hence "k \<le> j" using \<open>i \<le> j\<close> by (rule le_trans)
          with \<open>i \<le> k\<close> show "zs ! k \<in> neg_Nshifts {f}" by (rule s)
        qed
        hence 1: "fst (zs ! i) + 1 \<cdot> (- vect f) = snd (zs ! i)" by (simp add: algebra_simps)
        have "snd (zs ! j) + rat (Suc j) \<cdot> vect f = fst (zs ! i) + rat i \<cdot> vect f"
          using \<open>is_vpc zs\<close> \<open>i \<le> j\<close> \<open>j < length zs\<close> s by (rule vpc_neg_Nshifts_conv_vect)
        hence "fst (zs ! i) + (rat (Suc j) - rat i) \<cdot> (- vect f) = snd (zs ! j)"
          by (simp add: algebra_simps map_scale_uminus_right)
        with 1 show ?thesis ..
      next
        assume s: "\<And>k. i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> zs ! k \<in> pos_Nshifts {f}"
        have "snd (zs ! i) + rat i \<cdot> vect f = fst (zs ! i) + rat (Suc i) \<cdot> vect f"
          using \<open>is_vpc zs\<close> le_refl \<open>i < length zs\<close>
        proof (rule vpc_pos_Nshifts_conv_vect)
          fix k
          assume "i \<le> k"
          assume "k \<le> i"
          hence "k \<le> j" using \<open>i \<le> j\<close> by (rule le_trans)
          with \<open>i \<le> k\<close> show "zs ! k \<in> pos_Nshifts {f}" by (rule s)
        qed
        hence 1: "fst (zs ! i) + 1 \<cdot> vect f = snd (zs ! i)" by (simp add: algebra_simps)
        have "snd (zs ! j) + rat i \<cdot> vect f = fst (zs ! i) + rat (Suc j) \<cdot> vect f"
          using \<open>is_vpc zs\<close> \<open>i \<le> j\<close> \<open>j < length zs\<close> s by (rule vpc_pos_Nshifts_conv_vect)
        hence "fst (zs ! i) + (rat (Suc j) - rat i) \<cdot> vect f = snd (zs ! j)"
          by (simp add: algebra_simps)
        with 1 show ?thesis ..
      qed
      from overlap_i have "overlap \<unlhd> fst (zs ! i) + 0 \<cdot> v" by simp
      moreover have "overlap \<unlhd> fst (zs ! i) + (rat (Suc j) - rat i) \<cdot> v" unfolding eq by fact
      moreover note _
      moreover from \<open>i \<le> j\<close> have "1 \<le> rat (Suc j) - rat i" by simp
      ultimately have "overlap \<unlhd> fst (zs ! i) + 1 \<cdot> v" by (rule map_scale_le_interval) simp
      also have "\<dots> = snd (zs ! i)" by fact
      also from \<open>is_vpc zs\<close> Suc.prems have "\<dots> = fst (zs ! Suc i)" by (rule is_vpcD)
      finally show ?case .
    qed
  qed
qed

lemma lem_3_3_21_1:
  assumes "overlap \<unlhd> p" and "overlap \<unlhd> p + vect f" and "is_int_pm p" and "f \<in> {f1, f2}"
  obtains z where "z \<in> pos_Nshifts {f}" and "is_vpc [z]" and "fst z = p" and "snd z = p + vect f"
proof -
  let ?l = "of_nat_pm (lp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?t = "of_nat_pm (tp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?p = "to_nat_pm p"
  from assms(3) overlap_is_nat_pm assms(1) have p_nat: "is_nat_pm p" by (rule int_pm_is_nat_pmI)
  from assms(1, 4) have 1: "gcs ?l ?t \<unlhd> p" by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)
  from assms(2, 4) have 2: "gcs ?l ?t \<unlhd> p + vect f"
    by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)
  have "tp f \<unlhd> ?p"
  proof (rule le_pmI)
    fix x
    show "lookup (tp f) x \<le> lookup ?p x"
    proof (rule ccontr)
      assume "\<not> lookup (tp f) x \<le> lookup ?p x"
      hence "rat (lookup ?p x) < rat (lookup (tp f) x)" by simp
      with p_nat have 3: "lookup p x < lookup ?t x"
        by (simp only: of_nat_pm_comp_to_nat_pm flip: lookup_of_nat_pm lookup_to_nat_pm)
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
  hence "tp f adds ?p" by (rule adds_pmI)
  with p_nat have eq: "of_nat_pm (?p - tp f) = p - ?t"
    by (simp only: of_nat_pm_minus of_nat_pm_comp_to_nat_pm)
  let ?z = "(?p - tp f) +\<^sub>N prod.swap (poly_point f)"
  show ?thesis
  proof
    show "?z \<in> pos_Nshifts {f}" by (simp add: pos_Nshifts_singleton)
    with assms(4) have "?z \<in> Nshifts {f1, f2}" by (intro NshiftsI1 NshiftsI_poly)
    thus "is_vpc [?z]" by simp
  next
    show "fst ?z = p" by (simp add: nat_plus_point_pair_def snd_poly_point eq)
  next
    show "snd ?z = p + vect f" by (simp add: nat_plus_point_pair_def fst_poly_point vect_alt eq)
  qed
qed

lemma lem_3_3_21_2:
  assumes "overlap \<unlhd> p" and "overlap \<unlhd> p - vect f" and "is_int_pm p" and "f \<in> {f1, f2}"
  obtains z where "z \<in> neg_Nshifts {f}" and "is_vpc [z]" and "fst z = p" and "snd z = p - vect f"
proof -
  let ?l = "of_nat_pm (lp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?t = "of_nat_pm (tp f) :: _ \<Rightarrow>\<^sub>0 rat"
  let ?p = "to_nat_pm p"
  from assms(3) overlap_is_nat_pm assms(1) have p_nat: "is_nat_pm p" by (rule int_pm_is_nat_pmI)
  from assms(1, 4) have 1: "gcs ?l ?t \<unlhd> p" by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)
  from assms(2, 4) have 2: "gcs ?l ?t \<unlhd> p - vect f"
    by (auto simp: overlap_alt intro: le_pm_trans lcs_ge_pm)
  have "lp f \<unlhd> ?p"
  proof (rule le_pmI)
    fix x
    show "lookup (lp f) x \<le> lookup ?p x"
    proof (rule ccontr)
      assume "\<not> lookup (lp f) x \<le> lookup ?p x"
      hence "rat (lookup ?p x) < rat (lookup (lp f) x)" by simp
      with p_nat have 3: "lookup p x < lookup ?l x"
        by (simp only: of_nat_pm_comp_to_nat_pm flip: lookup_of_nat_pm lookup_to_nat_pm)
      hence "lookup (p - vect f) x < lookup (?l - vect f) x" by (simp only: lookup_minus)
      also have "\<dots> = lookup ?t x" by (simp add: vect_alt)
      finally have 4: "lookup (p - vect f) x < lookup ?t x" .
      have *: "min (lookup ?l x) (lookup ?t x) = lookup (gcs ?l ?t) x"
        by (simp only: lookup_gcs_fun gcs_fun)
      also from 1 have "\<dots> \<le> lookup p x" by (rule le_pmD)
      finally have **: "lookup ?t x < lookup ?l x" using 3 by simp
      note *
      also from 2 have "lookup (gcs ?l ?t) x \<le> lookup (p - vect f) x" by (rule le_pmD)
      finally have "lookup ?l x < lookup ?t x" using 4 by simp
      with ** show False by simp
    qed
  qed
  hence "lp f adds ?p" by (rule adds_pmI)
  with p_nat have eq: "of_nat_pm (?p - lp f) = p - ?l"
    by (simp only: of_nat_pm_minus of_nat_pm_comp_to_nat_pm)
  let ?z = "(?p - lp f) +\<^sub>N poly_point f"
  show ?thesis
  proof
    show "?z \<in> neg_Nshifts {f}" by (simp add: neg_Nshifts_singleton)
    with assms(4) have "?z \<in> Nshifts {f1, f2}" by (intro NshiftsI2 NshiftsI_poly)
    thus "is_vpc [?z]" by simp
  next
    show "fst ?z = p" by (simp add: nat_plus_point_pair_def fst_poly_point eq)
  next
    show "snd ?z = p - vect f" by (simp add: nat_plus_point_pair_def snd_poly_point vect_alt eq)
  qed
qed

lemma lem_3_3_21:
  assumes "overlap \<unlhd> p" and "overlap \<unlhd> p + l \<cdot> vect f" and "is_int_pm p" and "f \<in> {f1, f2}"
    and "is_int l" and "l \<noteq> 0"
  obtains zs where "is_vpc zs" and "rat (length zs) = abs l"
    and "fst (hd zs) = p" and "snd (last zs) = p + l \<cdot> vect f"
    and "l < 0 \<Longrightarrow> set zs \<subseteq> neg_Nshifts {f}" and "0 < l \<Longrightarrow> set zs \<subseteq> pos_Nshifts {f}"
proof (rule linorder_cases)
  assume "l < 0"
  from assms(5) have "is_int (- l)" by (rule uminus_is_int)
  moreover from \<open>l < 0\<close> have "0 \<le> - l" by simp
  ultimately have "is_nat (- l)" by (rule int_is_nat)
  moreover define k0 where "k0 = to_nat (- l)"
  ultimately have l': "l = - rat k0" by (simp only: is_nat_def)
  with \<open>l < 0\<close> have "0 < k0" by simp
  then obtain k where "k0 = Suc k" using gr0_conv_Suc by blast
  hence l: "l = - rat (Suc k)" by (simp only: l')
  from assms(1, 2, 3) that show ?thesis unfolding l
  proof (induct k arbitrary: p thesis)
    case 0
    note 0(1)
    moreover from 0(2) have "overlap \<unlhd> p - vect f" by (simp add: map_scale_uminus_left)
    ultimately obtain z where z: "z \<in> neg_Nshifts {f}" and "is_vpc [z]" and eq1: "fst z = p"
      and eq2: "snd z = p - vect f" using 0(3) assms(4) by (rule lem_3_3_21_2)
    from this(2) show ?case by (rule 0) (simp_all add: eq1 eq2 map_scale_uminus_left z)
  next
    case (Suc k)
    have eq: "p + - rat (Suc (Suc k)) \<cdot> vect f = p - vect f + - rat (Suc k) \<cdot> vect f"
      by (simp add: algebra_simps map_scale_uminus_left map_scale_two_left)
    note Suc.prems(2)
    moreover from Suc.prems(1) have "overlap \<unlhd> p + 0 \<cdot> vect f" by simp
    ultimately have "overlap \<unlhd> p + (- 1) \<cdot> vect f" by (rule map_scale_le_interval) simp_all
    hence "overlap \<unlhd> p - vect f" (is "_ \<unlhd> ?p") by (simp add: map_scale_uminus_left)
    moreover from Suc.prems(2) have "overlap \<unlhd> ?p + - rat (Suc k) \<cdot> vect f" by (simp only: eq)
    moreover from Suc.prems(3) have "is_int_pm ?p" by (intro minus_is_int_pm vect_is_int_pm)
    ultimately obtain zs where "is_vpc zs" and len_zs: "rat (length zs) = \<bar>- rat (Suc k)\<bar>"
      and hd_zs: "fst (hd zs) = ?p" and last_zs: "snd (last zs) = ?p + - rat (Suc k) \<cdot> vect f"
      and zs: "- rat (Suc k) < 0 \<Longrightarrow> set zs \<subseteq> neg_Nshifts {f}" by (rule Suc.hyps) blast
    from this(1) have "zs \<noteq> []" by (rule is_vpcD)
    from Suc.prems(1) \<open>overlap \<unlhd> ?p\<close> Suc.prems(3) assms(4) obtain z where z: "z \<in> neg_Nshifts {f}"
      and "is_vpc [z]" and fst_z: "fst z = p" and snd_z: "snd z = ?p" by (rule lem_3_3_21_2)
    show ?case
    proof (rule Suc.prems)
      from z assms(4) have "z \<in> Nshifts {f1, f2}" by (intro NshiftsI2 NshiftsI_poly)
      with \<open>is_vpc zs\<close> show "is_vpc (z # zs)" by (rule is_vpc_ConsI) (simp only: hd_zs snd_z)
    next
      have "set zs \<subseteq> neg_Nshifts {f}" by (rule zs) simp
      with z show "set (z # zs) \<subseteq> neg_Nshifts {f}" by simp
    qed (simp_all add: len_zs fst_z \<open>zs \<noteq> []\<close> last_zs algebra_simps map_scale_two_left map_scale_uminus_left)
  qed
next
  assume "0 < l"
  hence "0 \<le> l" by simp
  with assms(5) have "is_nat l" by (rule int_is_nat)
  moreover define k0 where "k0 = to_nat l"
  ultimately have l': "l = rat k0" by (simp only: is_nat_def)
  with \<open>0 < l\<close> have "0 < k0" by simp
  then obtain k where "k0 = Suc k" using gr0_conv_Suc by blast
  hence l: "l = rat (Suc k)" by (simp only: l')
  from assms(1, 2, 3) that show ?thesis unfolding l
  proof (induct k arbitrary: p thesis)
    case 0
    note 0(1)
    moreover from 0(2) have "overlap \<unlhd> p + vect f" by simp
    ultimately obtain z where z: "z \<in> pos_Nshifts {f}" and "is_vpc [z]" and eq1: "fst z = p"
      and eq2: "snd z = p + vect f" using 0(3) assms(4) by (rule lem_3_3_21_1)
    from this(2) show ?case by (rule 0) (simp_all add: eq1 eq2 map_scale_uminus_left z)
  next
    case (Suc k)
    have eq: "p + rat (Suc (Suc k)) \<cdot> vect f = p + vect f + rat (Suc k) \<cdot> vect f"
      by (simp add: algebra_simps map_scale_two_left)
    from Suc.prems(1) have "overlap \<unlhd> p + 0 \<cdot> vect f" by simp
    hence "overlap \<unlhd> p + 1 \<cdot> vect f" using Suc.prems(2) by (rule map_scale_le_interval) simp_all
    hence "overlap \<unlhd> p + vect f" (is "_ \<unlhd> ?p") by simp
    moreover from Suc.prems(2) have "overlap \<unlhd> ?p + rat (Suc k) \<cdot> vect f" by (simp only: eq)
    moreover from Suc.prems(3) have "is_int_pm ?p" by (intro plus_is_int_pm vect_is_int_pm)
    ultimately obtain zs where "is_vpc zs" and len_zs: "rat (length zs) = \<bar>rat (Suc k)\<bar>"
      and hd_zs: "fst (hd zs) = ?p" and last_zs: "snd (last zs) = ?p + rat (Suc k) \<cdot> vect f"
      and zs: "0 < rat (Suc k) \<Longrightarrow> set zs \<subseteq> pos_Nshifts {f}" by (rule Suc.hyps) blast
    from this(1) have "zs \<noteq> []" by (rule is_vpcD)
    from Suc.prems(1) \<open>overlap \<unlhd> ?p\<close> Suc.prems(3) assms(4) obtain z where z: "z \<in> pos_Nshifts {f}"
      and "is_vpc [z]" and fst_z: "fst z = p" and snd_z: "snd z = ?p" by (rule lem_3_3_21_1)
    show ?case
    proof (rule Suc.prems)
      from z assms(4) have "z \<in> Nshifts {f1, f2}" by (intro NshiftsI1 NshiftsI_poly)
      with \<open>is_vpc zs\<close> show "is_vpc (z # zs)" by (rule is_vpc_ConsI) (simp only: hd_zs snd_z)
    next
      have "set zs \<subseteq> pos_Nshifts {f}" by (rule zs) simp
      with z show "set (z # zs) \<subseteq> pos_Nshifts {f}" by simp
    qed (simp_all add: len_zs fst_z \<open>zs \<noteq> []\<close> last_zs algebra_simps map_scale_two_left)
  qed
next
  assume "l = 0"
  with assms(6) show ?thesis ..
qed

lemma thm_3_3_22:
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "overlap \<unlhd> fst (hd zs)"
    and "overlap \<unlhd> snd (last zs)" and "f \<in> {f1, f2}"
  assumes "set zs \<inter> Nshifts {f} \<subseteq> pos_Nshifts {f} \<Longrightarrow> thesis"
  assumes "set zs \<inter> Nshifts {f} \<subseteq> neg_Nshifts {f} \<Longrightarrow> thesis"
  shows thesis
proof (cases "set zs \<inter> Nshifts {f} \<subseteq> pos_Nshifts {f}")
  case True
  thus ?thesis by (rule assms(6))
next
  case False
  have disjnt: "pos_Nshifts {f} \<inter> neg_Nshifts {f} = {}"
  proof (rule ccontr)
    assume "pos_Nshifts {f} \<inter> neg_Nshifts {f} \<noteq> {}"
    hence "pos_Nshifts {f} = neg_Nshifts {f}" by (rule pos_neg_Nshifts_not_disjointD)
    with False show False unfolding Nshifts_def by blast
  qed
  obtain i where "i < length zs" and i_neg: "zs ! i \<in> neg_Nshifts {f}"
    and i_min: "\<And>a. a < i \<Longrightarrow> zs ! a \<notin> neg_Nshifts {f}"
  proof -
    let ?A = "{k\<in>{..<length zs}. zs ! k \<in> neg_Nshifts {f}}"
    define i where "i = Min ?A"
    have "finite ?A" by simp
    moreover have "?A \<noteq> {}"
    proof
      from False obtain z where "z \<in> set zs" and z_neg: "z \<in> neg_Nshifts {f}"
        by (auto simp: Nshifts_def)
      moreover from this(1) obtain j where "j < length zs" and z: "z = zs ! j"
        by (metis in_set_conv_nth)
      ultimately have "j \<in> ?A" by simp
      also assume "?A = {}"
      finally show False ..
    qed
    ultimately have "i \<in> ?A" unfolding i_def by (rule Min_in)
    hence "i < length zs" and "zs ! i \<in> neg_Nshifts {f}" by simp_all
    thus ?thesis
    proof
      fix a
      assume "a < i"
      show "zs ! a \<notin> neg_Nshifts {f}"
      proof
        assume "zs ! a \<in> neg_Nshifts {f}"
        moreover from \<open>a < i\<close> \<open>i < length zs\<close> have "a < length zs" by (rule less_trans)
        ultimately have "a \<in> ?A" by simp
        with \<open>finite ?A\<close> have "i \<le> a" unfolding i_def by (rule Min_le)
        with \<open>a < i\<close> show False by simp
      qed
    qed
  qed
  show ?thesis
  proof (cases "set zs \<inter> Nshifts {f} \<subseteq> neg_Nshifts {f}")
    case True
    thus ?thesis by (rule assms(7))
  next
    case False
    obtain j where "j < length zs" and j_pos: "zs ! j \<in> pos_Nshifts {f}"
      and j_min: "\<And>a. a < j \<Longrightarrow> zs ! a \<notin> pos_Nshifts {f}"
    proof -
      let ?A = "{k\<in>{..<length zs}. zs ! k \<in> pos_Nshifts {f}}"
      define j where "j = Min ?A"
      have "finite ?A" by simp
      moreover have "?A \<noteq> {}"
      proof
        from False obtain z where "z \<in> set zs" and z_neg: "z \<in> pos_Nshifts {f}"
          by (auto simp: Nshifts_def)
        moreover from this(1) obtain k where "k < length zs" and z: "z = zs ! k"
          by (metis in_set_conv_nth)
        ultimately have "k \<in> ?A" by simp
        also assume "?A = {}"
        finally show False ..
      qed
      ultimately have "j \<in> ?A" unfolding j_def by (rule Min_in)
      hence "j < length zs" and "zs ! j \<in> pos_Nshifts {f}" by simp_all
      thus ?thesis
      proof
        fix a
        assume "a < j"
        show "zs ! a \<notin> pos_Nshifts {f}"
        proof
          assume "zs ! a \<in> pos_Nshifts {f}"
          moreover from \<open>a < j\<close> \<open>j < length zs\<close> have "a < length zs" by (rule less_trans)
          ultimately have "a \<in> ?A" by simp
          with \<open>finite ?A\<close> have "j \<le> a" unfolding j_def by (rule Min_le)
          with \<open>a < j\<close> show False by simp
        qed
      qed
    qed
    from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
    obtain m1 m2 f' l where "Suc m1 < m2" and "m2 < length zs" and "f' \<in> {f1, f2}" and "is_int l"
      and abs_l: "\<bar>l\<bar> = rat (m2 - Suc m1)" and snd_m2: "snd (zs ! m2) = fst (zs ! m1) + l \<cdot> vect f'"
    proof (rule linorder_cases)
      \<comment>\<open>Case 1: First a negative shift of \<open>f\<close>, then a positive one.\<close>
      let ?A = "{k\<in>{..<j}. zs ! k \<in> neg_Nshifts {f}}"
      have "finite ?A" by simp
      define k where "k = Max ?A"
      assume "i < j"
      with i_neg have "i \<in> ?A" by simp
      hence "?A \<noteq> {}" by blast
      with \<open>finite ?A\<close> have "k \<in> ?A" unfolding k_def by (rule Max_in)
      hence "k < j" and k_neg: "zs ! k \<in> neg_Nshifts {f}" by simp_all
      have "Suc k \<le> j - 1"
      proof (rule ccontr)
        assume "\<not> Suc k \<le> j - 1"
        with \<open>k < j\<close> have j: "j = Suc k" by simp
        note assms(1, 2)
        moreover from \<open>j < length zs\<close> have "Suc k < length zs" by (simp only: j)
        moreover from k_neg have "zs ! k \<in> Nshifts {f}" by (rule NshiftsI2)
        moreover from j_pos have "zs ! Suc k \<in> Nshifts {f}" unfolding j by (rule NshiftsI1)
        ultimately show False
        proof (rule lem_3_3_19)
          assume "zs ! k \<in> pos_Nshifts {f}"
          with k_neg have "pos_Nshifts {f} \<inter> neg_Nshifts {f} \<noteq> {}" by blast
          thus ?thesis using disjnt ..
        next
          assume "zs ! Suc k \<in> neg_Nshifts {f}"
          with j_pos disjnt show ?thesis unfolding j by blast
        qed
      qed
      hence Suc_j: "Suc (j - Suc 0) = j" by simp
      from \<open>j < length zs\<close> have "j - 1 < length zs" by simp
      have 1: "zs ! a \<in> Nshifts {f1, f2} - Nshifts {f}" if "Suc k \<le> a" and "a \<le> j - 1" for a
      proof -
        from that(2) \<open>j - 1 < length zs\<close> have "a < length zs" by (rule le_less_trans)
        hence "zs ! a \<in> set zs" by simp
        also from \<open>is_vpc zs\<close> have "\<dots> \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
        finally have "zs ! a \<in> Nshifts {f1, f2}" .
        moreover have "zs ! a \<notin> Nshifts {f}"
        proof
          assume "zs ! a \<in> Nshifts {f}"
          thus False
          proof (rule NshiftsE_shift)
            from that(2) \<open>Suc k \<le> j - 1\<close> have "a < j" by simp
            hence "zs ! a \<notin> pos_Nshifts {f}" by (rule j_min)
            moreover assume "zs ! a \<in> pos_Nshifts {f}"
            ultimately show ?thesis ..
          next
            assume "zs ! a \<in> neg_Nshifts {f}"
            with that(2) \<open>Suc k \<le> j - 1\<close> have "a \<in> ?A" by simp
            with \<open>finite ?A\<close> have "a \<le> k" unfolding k_def by (rule Max_ge)
            with that(1) show ?thesis by simp
          qed
        qed
        ultimately show ?thesis by simp
      qed
      from le_refl \<open>Suc k \<le> j - 1\<close> have "zs ! Suc k \<in> Nshifts {f1, f2} - Nshifts {f}" by (rule 1)
      then obtain f' where "f' \<in> {f1, f2}" and "f' \<noteq> f" and "zs ! Suc k \<in> Nshifts {f'}"
        by (auto elim: NshiftsE_poly)
      have "zs ! a \<in> Nshifts {f'}" if "Suc k \<le> a" and "a \<le> j - 1" for a
        using that assms(5) \<open>f' \<in> {f1, f2}\<close> \<open>f' \<noteq> f\<close> by (auto simp only: dest: 1 elim: NshiftsE_poly)
      with assms(1, 2) \<open>Suc k \<le> j - 1\<close> \<open>j - 1 < length zs\<close> obtain l where "is_int l"
        and abs_l: "\<bar>l\<bar> = rat (Suc (j - 1) - Suc k)"
        and eq: "snd (zs ! (j - 1)) = fst (zs ! Suc k) + l \<cdot> vect f'" by (rule vpc_Nshifts_conv_vect)
      from j_pos have "snd (zs ! j) = fst (zs ! j) + vect f" by (rule pos_Nshifts_conv_vect)
      also have "fst (zs ! j) = fst (zs ! Suc (j - 1))" by (simp add: Suc_j)
      also from \<open>is_vpc zs\<close> have "\<dots> = snd (zs ! (j - 1))"
        by (rule is_vpcD(2)[symmetric]) (simp add: Suc_j \<open>j < length zs\<close>)
      finally have "snd (zs ! j) = fst (zs ! Suc k) + l \<cdot> vect f' + vect f" by (simp only: eq)
      also from \<open>is_vpc zs\<close> have "fst (zs ! Suc k) = snd (zs ! k)"
        by (rule is_vpcD(2)[symmetric]) (rule le_less_trans, fact+)
      also from k_neg have "\<dots> = fst (zs ! k) - vect f" by (rule neg_Nshifts_conv_vect)
      finally have "snd (zs ! j) = fst (zs ! k) + l \<cdot> vect f'" by simp
      with _ \<open>j < length zs\<close> \<open>f' \<in> {f1, f2}\<close> \<open>is_int l\<close> _ show ?thesis
      proof (rule that)
        from \<open>Suc k \<le> j - 1\<close> show "Suc k < j" by simp
      next
        from abs_l show "\<bar>l\<bar> = rat (j - Suc k)" by (simp only: Suc_j)
      qed
    next
      \<comment>\<open>Case 2: First a positive shift of \<open>f\<close>, then a negative one.\<close>
      let ?A = "{k\<in>{..<i}. zs ! k \<in> pos_Nshifts {f}}"
      have "finite ?A" by simp
      define k where "k = Max ?A"
      assume "j < i"
      with j_pos have "j \<in> ?A" by simp
      hence "?A \<noteq> {}" by blast
      with \<open>finite ?A\<close> have "k \<in> ?A" unfolding k_def by (rule Max_in)
      hence "k < i" and k_pos: "zs ! k \<in> pos_Nshifts {f}" by simp_all
      have "Suc k \<le> i - 1"
      proof (rule ccontr)
        assume "\<not> Suc k \<le> i - 1"
        with \<open>k < i\<close> have i: "i = Suc k" by simp
        note assms(1, 2)
        moreover from \<open>i < length zs\<close> have "Suc k < length zs" by (simp only: i)
        moreover from k_pos have "zs ! k \<in> Nshifts {f}" by (rule NshiftsI1)
        moreover from i_neg have "zs ! Suc k \<in> Nshifts {f}" unfolding i by (rule NshiftsI2)
        ultimately show False
        proof (rule lem_3_3_19)
          assume "zs ! k \<in> neg_Nshifts {f}"
          with k_pos have "pos_Nshifts {f} \<inter> neg_Nshifts {f} \<noteq> {}" by blast
          thus ?thesis using disjnt ..
        next
          assume "zs ! Suc k \<in> pos_Nshifts {f}"
          with i_neg disjnt show ?thesis unfolding i by blast
        qed
      qed
      hence Suc_i: "Suc (i - Suc 0) = i" by simp
      from \<open>i < length zs\<close> have "i - 1 < length zs" by simp
      have 1: "zs ! a \<in> Nshifts {f1, f2} - Nshifts {f}" if "Suc k \<le> a" and "a \<le> i - 1" for a
      proof -
        from that(2) \<open>i - 1 < length zs\<close> have "a < length zs" by (rule le_less_trans)
        hence "zs ! a \<in> set zs" by simp
        also from \<open>is_vpc zs\<close> have "\<dots> \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
        finally have "zs ! a \<in> Nshifts {f1, f2}" .
        moreover have "zs ! a \<notin> Nshifts {f}"
        proof
          assume "zs ! a \<in> Nshifts {f}"
          thus False
          proof (rule NshiftsE_shift)
            from that(2) \<open>Suc k \<le> i - 1\<close> have "a < i" by simp
            hence "zs ! a \<notin> neg_Nshifts {f}" by (rule i_min)
            moreover assume "zs ! a \<in> neg_Nshifts {f}"
            ultimately show ?thesis ..
          next
            assume "zs ! a \<in> pos_Nshifts {f}"
            with that(2) \<open>Suc k \<le> i - 1\<close> have "a \<in> ?A" by simp
            with \<open>finite ?A\<close> have "a \<le> k" unfolding k_def by (rule Max_ge)
            with that(1) show ?thesis by simp
          qed
        qed
        ultimately show ?thesis by simp
      qed
      from le_refl \<open>Suc k \<le> i - 1\<close> have "zs ! Suc k \<in> Nshifts {f1, f2} - Nshifts {f}" by (rule 1)
      then obtain f' where "f' \<in> {f1, f2}" and "f' \<noteq> f" and "zs ! Suc k \<in> Nshifts {f'}"
        by (auto elim: NshiftsE_poly)
      have "zs ! a \<in> Nshifts {f'}" if "Suc k \<le> a" and "a \<le> i - 1" for a
        using that assms(5) \<open>f' \<in> {f1, f2}\<close> \<open>f' \<noteq> f\<close> by (auto simp only: dest: 1 elim: NshiftsE_poly)
      with assms(1, 2) \<open>Suc k \<le> i - 1\<close> \<open>i - 1 < length zs\<close> obtain l where "is_int l"
        and abs_l: "\<bar>l\<bar> = rat (Suc (i - 1) - Suc k)"
        and eq: "snd (zs ! (i - 1)) = fst (zs ! Suc k) + l \<cdot> vect f'" by (rule vpc_Nshifts_conv_vect)
      from i_neg have "snd (zs ! i) = fst (zs ! i) - vect f" by (rule neg_Nshifts_conv_vect)
      also have "fst (zs ! i) = fst (zs ! Suc (i - 1))" by (simp add: Suc_i)
      also from \<open>is_vpc zs\<close> have "\<dots> = snd (zs ! (i - 1))"
        by (rule is_vpcD(2)[symmetric]) (simp add: Suc_i \<open>i < length zs\<close>)
      finally have "snd (zs ! i) = fst (zs ! Suc k) + l \<cdot> vect f' - vect f" by (simp only: eq)
      also from \<open>is_vpc zs\<close> have "fst (zs ! Suc k) = snd (zs ! k)"
        by (rule is_vpcD(2)[symmetric]) (rule le_less_trans, fact+)
      also from k_pos have "\<dots> = fst (zs ! k) + vect f" by (rule pos_Nshifts_conv_vect)
      finally have "snd (zs ! i) = fst (zs ! k) + l \<cdot> vect f'" by simp
      with _ \<open>i < length zs\<close> \<open>f' \<in> {f1, f2}\<close> \<open>is_int l\<close> _ show ?thesis
      proof (rule that)
        from \<open>Suc k \<le> i - 1\<close> show "Suc k < i" by simp
      next
        from abs_l show "\<bar>l\<bar> = rat (i - Suc k)" by (simp only: Suc_i)
      qed
    next
      assume "i = j"
      with i_neg j_pos disjnt show ?thesis by blast
    qed
    from \<open>Suc m1 < m2\<close> \<open>m2 < length zs\<close> have m1_in: "fst (zs ! m1) \<in> set_of_vpc zs"
      by (simp add: set_of_vpc_def)
    with assms(1-4) have "overlap \<unlhd> fst (zs ! m1)" by (rule thm_3_3_20)
    moreover from assms(1-4) have "overlap \<unlhd> fst (zs ! m1) + l \<cdot> vect f'" unfolding snd_m2[symmetric]
      by (rule thm_3_3_20) (simp add: set_of_vpc_def \<open>m2 < length zs\<close>)
    moreover from \<open>is_vpc zs\<close> m1_in have "is_int_pm (fst (zs ! m1))"
      by (intro nat_pm_is_int_pm vpc_is_nat_pm)
    moreover note \<open>f' \<in> {f1, f2}\<close> \<open>is_int l\<close>
    moreover from \<open>Suc m1 < m2\<close> abs_l have "l \<noteq> 0" by simp
    ultimately obtain zs2 where "is_vpc zs2" and len_zs2': "rat (length zs2) = \<bar>l\<bar>"
      and hd_zs2: "fst (hd zs2) = fst (zs ! m1)" and "snd (last zs2) = fst (zs ! m1) + l \<cdot> vect f'"
      by (rule lem_3_3_21)
    from this(4) have last_zs2: "snd (last zs2) = snd (zs ! m2)" by (simp only: snd_m2)
    from len_zs2' have len_zs2: "length zs2 = m2 - Suc m1" by (simp add: abs_l)
    from \<open>Suc m1 < m2\<close> have "m1 \<le> m2" by simp
    with \<open>is_vpc zs\<close> obtain zs' where "is_vpc zs'" and hd_zs': "fst (hd zs') = fst (hd zs)"
      and last_zs': "snd (last zs') = snd (last zs)"
      and "length zs + length zs2 = length zs' + (Suc m2 - m1)"
      using \<open>m2 < length zs\<close> \<open>is_vpc zs2\<close> hd_zs2 last_zs2
    proof (rule replace_vpc)
      from \<open>is_vpc zs2\<close> have "zs2 \<noteq> []" by (rule is_vpcD)
      moreover assume "zs2 = []"
      ultimately show False and "fst (zs ! m1) = snd (zs ! m2)" by (rule notE)+
    qed
    from this(4) \<open>Suc m1 < m2\<close> have "length zs' < length zs" by (simp add: len_zs2)
    also from assms(1) \<open>is_vpc zs'\<close> hd_zs' last_zs' have "\<dots> \<le> length zs'" by (rule min_length_vpcD)
    finally show ?thesis ..
  qed
qed

lemma vpc_subset_shifts_of:
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "overlap \<unlhd> fst (hd zs)"
    and "overlap \<unlhd> snd (last zs)" and "f \<in> shifts {f1, f2}" and "f' \<in> shifts {f1, f2}" and "f \<noteq> f'"
    and "set zs \<inter> shifts_of {f} \<noteq> {}" and "set zs \<inter> shifts_of {f'} \<noteq> {}"
  obtains g g' where "{f1, f2} = {g, g'}" and "g \<noteq> g'" and "f \<in> shifts {g}" and "f' \<in> shifts {g'}"
    and "set zs \<subseteq> shifts_of {f} \<union> shifts_of {f'}"
proof -
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  hence sub1: "set zs \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  from assms(5) obtain g where g_in: "g \<in> {f1, f2}" and f_in: "f \<in> shifts {g}" by (rule shiftsE_poly)
  have "shifts_of {f} \<subseteq> Nshifts {g}" unfolding Nshifts_alt by (rule shifts_of_mono) (simp add: f_in)
  from g_in f1_pbinomial f2_pbinomial have "is_proper_binomial g" by blast
  hence g_disjnt: "pos_Nshifts {g} \<inter> neg_Nshifts {g} = {}" by (rule pos_neg_Nshifts_disjointI)
  from assms(6) obtain g' where g'_in: "g' \<in> {f1, f2}" and f'_in: "f' \<in> shifts {g'}" by (rule shiftsE_poly)
  have "shifts_of {f'} \<subseteq> Nshifts {g'}" unfolding Nshifts_alt by (rule shifts_of_mono) (simp add: f'_in)
  from g'_in f1_pbinomial f2_pbinomial have "is_proper_binomial g'" by blast
  hence g'_disjnt: "pos_Nshifts {g'} \<inter> neg_Nshifts {g'} = {}" by (rule pos_neg_Nshifts_disjointI)
  from assms(8) obtain z where "z \<in> set zs" and "z \<in> shifts_of {f}" by blast
  from this(2) \<open>shifts_of {f} \<subseteq> Nshifts {g}\<close> have "z \<in> Nshifts {g}" ..
  with \<open>z \<in> set zs\<close> have z_in: "z \<in> set zs \<inter> Nshifts {g}" by (rule IntI)
  from assms(9) obtain z' where "z' \<in> set zs" and "z' \<in> shifts_of {f'}" by blast
  from this(2) \<open>shifts_of {f'} \<subseteq> Nshifts {g'}\<close> have "z' \<in> Nshifts {g'}" ..
  with \<open>z' \<in> set zs\<close> have z'_in: "z' \<in> set zs \<inter> Nshifts {g'}" by (rule IntI)
  from _ _ f_in f'_in show ?thesis
  proof
    from assms(1-4) g_in have "g \<noteq> g' \<and> {f1, f2} = {g, g'} \<and> set zs \<subseteq> shifts_of {f} \<union> shifts_of {f'}"
    proof (rule thm_3_3_22)
      assume sub2: "set zs \<inter> Nshifts {g} \<subseteq> pos_Nshifts {g}"
      with z_in have "z \<in> pos_Nshifts {g}" ..
      with g_disjnt have "z \<notin> neg_Nshifts {g}" by blast
      from f_in have f: "f = prod.swap (poly_point g)" unfolding shifts_def
      proof
        assume "f \<in> poly_point ` {g}"
        with \<open>z \<in> shifts_of {f}\<close> have "z \<in> neg_Nshifts {g}"
          by (simp add: neg_Nshifts_singleton shifts_of_singleton)
        with \<open>z \<notin> neg_Nshifts {g}\<close> show ?thesis ..
      qed simp
      hence pos_g: "pos_Nshifts {g} = shifts_of {f}"
        by (simp only: pos_Nshifts_singleton shifts_of_singleton)
      from assms(1-4) g'_in show ?thesis
      proof (rule thm_3_3_22)
        assume sub3: "set zs \<inter> Nshifts {g'} \<subseteq> pos_Nshifts {g'}"
        with z'_in have "z' \<in> pos_Nshifts {g'}" ..
        with g'_disjnt have "z' \<notin> neg_Nshifts {g'}" by blast
        from f'_in have f': "f' = prod.swap (poly_point g')" unfolding shifts_def
        proof
          assume "f' \<in> poly_point ` {g'}"
          with \<open>z' \<in> shifts_of {f'}\<close> have "z' \<in> neg_Nshifts {g'}"
            by (simp add: neg_Nshifts_singleton shifts_of_singleton)
          with \<open>z' \<notin> neg_Nshifts {g'}\<close> show ?thesis ..
        qed simp
        hence pos_g': "pos_Nshifts {g'} = shifts_of {f'}"
          by (simp only: pos_Nshifts_singleton shifts_of_singleton)
        show ?thesis
        proof (intro conjI subsetI)
          from assms(7) show "g \<noteq> g'" by (auto simp: f f')
          with g_in g'_in show eq1: "{f1, f2} = {g, g'}" by blast

          fix z0
          assume "z0 \<in> set zs"
          with sub1 have "z0 \<in> Nshifts {f1, f2}" ..
          hence "z0 \<in> Nshifts {g} \<union> Nshifts {g'}" by (auto simp: eq1 elim: NshiftsE_poly)
          thus "z0 \<in> shifts_of {f} \<union> shifts_of {f'}"
          proof
            assume "z0 \<in> Nshifts {g}"
            with \<open>z0 \<in> set zs\<close> sub2 have "z0 \<in> pos_Nshifts {g}" by blast
            thus ?thesis by (simp add: pos_g)
          next
            assume "z0 \<in> Nshifts {g'}"
            with \<open>z0 \<in> set zs\<close> sub3 have "z0 \<in> pos_Nshifts {g'}" by blast
            thus ?thesis by (simp add: pos_g')
          qed
        qed
      next
        assume sub3: "set zs \<inter> Nshifts {g'} \<subseteq> neg_Nshifts {g'}"
        with z'_in have "z' \<in> neg_Nshifts {g'}" ..
        with g'_disjnt have "z' \<notin> pos_Nshifts {g'}" by blast
        from f'_in have f': "f' = poly_point g'" unfolding shifts_def
        proof
          assume "f' \<in> prod.swap ` poly_point ` {g'}"
          with \<open>z' \<in> shifts_of {f'}\<close> have "z' \<in> pos_Nshifts {g'}"
            by (simp add: pos_Nshifts_singleton shifts_of_singleton)
          with \<open>z' \<notin> pos_Nshifts {g'}\<close> show ?thesis ..
        qed simp
        hence neg_g': "neg_Nshifts {g'} = shifts_of {f'}"
          by (simp only: neg_Nshifts_singleton shifts_of_singleton)
        show ?thesis
        proof (intro conjI subsetI)
          show "g \<noteq> g'"
          proof
            assume "g = g'"
            with sub2 sub3 g'_disjnt z'_in show False by blast
          qed
          with g_in g'_in show eq1: "{f1, f2} = {g, g'}" by blast

          fix z0
          assume "z0 \<in> set zs"
          with sub1 have "z0 \<in> Nshifts {f1, f2}" ..
          hence "z0 \<in> Nshifts {g} \<union> Nshifts {g'}" by (auto simp: eq1 elim: NshiftsE_poly)
          thus "z0 \<in> shifts_of {f} \<union> shifts_of {f'}"
          proof
            assume "z0 \<in> Nshifts {g}"
            with \<open>z0 \<in> set zs\<close> sub2 have "z0 \<in> pos_Nshifts {g}" by blast
            thus ?thesis by (simp add: pos_g)
          next
            assume "z0 \<in> Nshifts {g'}"
            with \<open>z0 \<in> set zs\<close> sub3 have "z0 \<in> neg_Nshifts {g'}" by blast
            thus ?thesis by (simp add: neg_g')
          qed
        qed
      qed
    next
      assume sub2: "set zs \<inter> Nshifts {g} \<subseteq> neg_Nshifts {g}"
      with z_in have "z \<in> neg_Nshifts {g}" ..
      with g_disjnt have "z \<notin> pos_Nshifts {g}" by blast
      from f_in have f: "f = poly_point g" unfolding shifts_def
      proof
        assume "f \<in> prod.swap ` poly_point ` {g}"
        with \<open>z \<in> shifts_of {f}\<close> have "z \<in> pos_Nshifts {g}"
          by (simp add: pos_Nshifts_singleton shifts_of_singleton)
        with \<open>z \<notin> pos_Nshifts {g}\<close> show ?thesis ..
      qed simp
      hence neg_g: "neg_Nshifts {g} = shifts_of {f}"
        by (simp only: neg_Nshifts_singleton shifts_of_singleton)
      from assms(1-4) g'_in show ?thesis
      proof (rule thm_3_3_22)
        assume sub3: "set zs \<inter> Nshifts {g'} \<subseteq> pos_Nshifts {g'}"
        with z'_in have "z' \<in> pos_Nshifts {g'}" ..
        with g'_disjnt have "z' \<notin> neg_Nshifts {g'}" by blast
        from f'_in have f': "f' = prod.swap (poly_point g')" unfolding shifts_def
        proof
          assume "f' \<in> poly_point ` {g'}"
          with \<open>z' \<in> shifts_of {f'}\<close> have "z' \<in> neg_Nshifts {g'}"
            by (simp add: neg_Nshifts_singleton shifts_of_singleton)
          with \<open>z' \<notin> neg_Nshifts {g'}\<close> show ?thesis ..
        qed simp
        hence pos_g': "pos_Nshifts {g'} = shifts_of {f'}"
          by (simp only: pos_Nshifts_singleton shifts_of_singleton)
        show ?thesis
        proof (intro conjI subsetI)
          show "g \<noteq> g'"
          proof
            assume "g = g'"
            with sub2 sub3 g'_disjnt z'_in show False by blast
          qed
          with g_in g'_in show eq1: "{f1, f2} = {g, g'}" by blast

          fix z0
          assume "z0 \<in> set zs"
          with sub1 have "z0 \<in> Nshifts {f1, f2}" ..
          hence "z0 \<in> Nshifts {g} \<union> Nshifts {g'}" by (auto simp: eq1 elim: NshiftsE_poly)
          thus "z0 \<in> shifts_of {f} \<union> shifts_of {f'}"
          proof
            assume "z0 \<in> Nshifts {g}"
            with \<open>z0 \<in> set zs\<close> sub2 have "z0 \<in> neg_Nshifts {g}" by blast
            thus ?thesis by (simp add: neg_g)
          next
            assume "z0 \<in> Nshifts {g'}"
            with \<open>z0 \<in> set zs\<close> sub3 have "z0 \<in> pos_Nshifts {g'}" by blast
            thus ?thesis by (simp add: pos_g')
          qed
        qed
      next
        assume sub3: "set zs \<inter> Nshifts {g'} \<subseteq> neg_Nshifts {g'}"
        with z'_in have "z' \<in> neg_Nshifts {g'}" ..
        with g'_disjnt have "z' \<notin> pos_Nshifts {g'}" by blast
        from f'_in have f': "f' = poly_point g'" unfolding shifts_def
        proof
          assume "f' \<in> prod.swap ` poly_point ` {g'}"
          with \<open>z' \<in> shifts_of {f'}\<close> have "z' \<in> pos_Nshifts {g'}"
            by (simp add: pos_Nshifts_singleton shifts_of_singleton)
          with \<open>z' \<notin> pos_Nshifts {g'}\<close> show ?thesis ..
        qed simp
        hence neg_g': "neg_Nshifts {g'} = shifts_of {f'}"
          by (simp only: neg_Nshifts_singleton shifts_of_singleton)
        show ?thesis
        proof (intro conjI subsetI)
          from assms(7) show "g \<noteq> g'" by (auto simp: f f')
          with g_in g'_in show eq1: "{f1, f2} = {g, g'}" by blast

          fix z0
          assume "z0 \<in> set zs"
          with sub1 have "z0 \<in> Nshifts {f1, f2}" ..
          hence "z0 \<in> Nshifts {g} \<union> Nshifts {g'}" by (auto simp: eq1 elim: NshiftsE_poly)
          thus "z0 \<in> shifts_of {f} \<union> shifts_of {f'}"
          proof
            assume "z0 \<in> Nshifts {g}"
            with \<open>z0 \<in> set zs\<close> sub2 have "z0 \<in> neg_Nshifts {g}" by blast
            thus ?thesis by (simp add: neg_g)
          next
            assume "z0 \<in> Nshifts {g'}"
            with \<open>z0 \<in> set zs\<close> sub3 have "z0 \<in> neg_Nshifts {g'}" by blast
            thus ?thesis by (simp add: neg_g')
          qed
        qed
      qed
    qed
    thus "{f1, f2} = {g, g'}" and "g \<noteq> g'" and "set zs \<subseteq> shifts_of {f} \<union> shifts_of {f'}" by simp_all
  qed
qed

lemma vpc_snd_nth_conv_shifts_of:
  assumes "min_length_vpc zs" and "set zs \<subseteq> shifts_of {f} \<union> shifts_of {f'}"
    and "shifts_of {f} \<inter> shifts_of {f'} = {}" and "i < length zs"
  shows "snd (zs ! i) =
            fst (hd zs) + rat (card (set (take (Suc i) zs) \<inter> shifts_of {f})) \<cdot> (snd f - fst f) +
                          rat (card (set (take (Suc i) zs) \<inter> shifts_of {f'})) \<cdot> (snd f' - fst f')"
  using assms(4)
proof (induct i)
  case 0
  define k where "k = card ({zs ! 0} \<inter> shifts_of {f})"
  define k' where "k' = card ({zs ! 0} \<inter> shifts_of {f'})"
  from 0 have "zs \<noteq> []" by simp
  hence "zs ! 0 \<in> set zs" by simp
  with assms(2) have "zs ! 0 \<in> shifts_of {f} \<union> shifts_of {f'}" ..
  hence "snd (zs ! 0) = fst (zs ! 0) + rat k \<cdot> (snd f - fst f) + rat k' \<cdot> (snd f' - fst f')"
  proof
    assume *: "zs ! 0 \<in> shifts_of {f}"
    hence "k = 1" by (simp add: k_def)
    from * assms(3) have "zs ! 0 \<notin> shifts_of {f'}" by blast
    hence "k' = 0" by (simp add: k'_def)
    from * have "snd (zs ! 0) = fst (zs ! 0) + snd f - fst f" by (rule shifts_of_singletonD)
    also have "\<dots> = fst (zs ! 0) + rat k \<cdot> (snd f - fst f) + rat k' \<cdot> (snd f' - fst f')"
      by (simp add: \<open>k = 1\<close> \<open>k' = 0\<close>)
    finally show ?thesis .
  next
    assume *: "zs ! 0 \<in> shifts_of {f'}"
    hence "k' = 1" by (simp add: k'_def)
    from * assms(3) have "zs ! 0 \<notin> shifts_of {f}" by blast
    hence "k = 0" by (simp add: k_def)
    from * have "snd (zs ! 0) = fst (zs ! 0) + snd f' - fst f'" by (rule shifts_of_singletonD)
    also have "\<dots> = fst (zs ! 0) + rat k \<cdot> (snd f - fst f) + rat k' \<cdot> (snd f' - fst f')"
      by (simp add: \<open>k = 0\<close> \<open>k' = 1\<close>)
    finally show ?thesis .
  qed
  with \<open>zs \<noteq> []\<close> show ?case by (simp add: k_def k'_def take_Suc_conv_app_nth[OF 0] hd_conv_nth)
next
  case (Suc i)
  define k where "k = card (set (take (Suc i) zs) \<inter> shifts_of {f})"
  define k' where "k' = card (set (take (Suc i) zs) \<inter> shifts_of {f'})"
  define l where "l = card (set (take (Suc (Suc i)) zs) \<inter> shifts_of {f})"
  define l' where "l' = card (set (take (Suc (Suc i)) zs) \<inter> shifts_of {f'})"
  from Suc.prems have "i < length zs" by simp
  hence eq1: "snd (zs ! i) = fst (hd zs) + rat k \<cdot> (snd f - fst f) + rat k' \<cdot> (snd f' - fst f')"
    unfolding k_def k'_def by (rule Suc.hyps)
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  hence "snd (zs ! i) = fst (zs ! Suc i)" using Suc.prems by (rule is_vpcD)
  hence eq2: "fst (zs ! Suc i) = fst (hd zs) + rat k \<cdot> (snd f - fst f) + rat k' \<cdot> (snd f' - fst f')"
    by (simp only: eq1)
  from Suc.prems have "zs ! Suc i \<in> set zs" by simp
  with assms(2) have "zs ! Suc i \<in> shifts_of {f} \<union> shifts_of {f'}" ..
  thus "snd (zs ! Suc i) = fst (hd zs) + rat l \<cdot> (snd f - fst f) + rat l' \<cdot> (snd f' - fst f')"
  proof
    assume *: "zs ! Suc i \<in> shifts_of {f}"
    hence "set (take (Suc (Suc i)) zs) \<inter> shifts_of {f} =
                  insert (zs ! Suc i) (set (take (Suc i) zs) \<inter> shifts_of {f})" (is "?A = insert ?z ?B")
      by (simp add: take_Suc_conv_app_nth[OF Suc.prems])
    have "finite ?B" by simp
    moreover have "?z \<notin> ?B"
    proof (intro notI, elim IntE)
      assume "zs ! Suc i \<in> set (take (Suc i) zs)"
      then obtain j where "j < length (take (Suc i) zs)" and "zs ! Suc i = (take (Suc i) zs) ! j"
        by (metis in_set_conv_nth)
      with Suc.prems have "j < Suc i" and "zs ! Suc i = zs ! j" by simp_all
      moreover from assms(1) have "distinct zs" by (rule min_length_vpc_distinct)
      ultimately show False using Suc.prems by (simp add: nth_eq_iff_index_eq)
    qed
    ultimately have "l = Suc k" unfolding l_def k_def \<open>?A = insert ?z ?B\<close> by (rule card_insert_disjoint)
    from * assms(3) have "zs ! Suc i \<notin> shifts_of {f'}" by blast
    hence "l' = k'" by (simp add: l'_def k'_def take_Suc_conv_app_nth[OF Suc.prems])
    from * have "snd (zs ! Suc i) = fst (zs ! Suc i) + snd f - fst f" by (rule shifts_of_singletonD)
    also have "\<dots> = fst (hd zs) + rat l \<cdot> (snd f - fst f) + rat l' \<cdot> (snd f' - fst f')"
      by (simp add: eq2 \<open>l = Suc k\<close> \<open>l' = k'\<close> map_scale_distrib_right)
    finally show ?thesis .
  next
    assume *: "zs ! Suc i \<in> shifts_of {f'}"
    hence "set (take (Suc (Suc i)) zs) \<inter> shifts_of {f'} =
                  insert (zs ! Suc i) (set (take (Suc i) zs) \<inter> shifts_of {f'})" (is "?A = insert ?z ?B")
      by (simp add: take_Suc_conv_app_nth[OF Suc.prems])
    have "finite ?B" by simp
    moreover have "?z \<notin> ?B"
    proof (intro notI, elim IntE)
      assume "zs ! Suc i \<in> set (take (Suc i) zs)"
      then obtain j where "j < length (take (Suc i) zs)" and "zs ! Suc i = (take (Suc i) zs) ! j"
        by (metis in_set_conv_nth)
      with Suc.prems have "j < Suc i" and "zs ! Suc i = zs ! j" by simp_all
      moreover from assms(1) have "distinct zs" by (rule min_length_vpc_distinct)
      ultimately show False using Suc.prems by (simp add: nth_eq_iff_index_eq)
    qed
    ultimately have "l' = Suc k'" unfolding l'_def k'_def \<open>?A = insert ?z ?B\<close>
      by (rule card_insert_disjoint)
    from * assms(3) have "zs ! Suc i \<notin> shifts_of {f}" by blast
    hence "l = k" by (simp add: l_def k_def take_Suc_conv_app_nth[OF Suc.prems])
    from * have "snd (zs ! Suc i) = fst (zs ! Suc i) + snd f' - fst f'" by (rule shifts_of_singletonD)
    also have "\<dots> = fst (hd zs) + rat l \<cdot> (snd f - fst f) + rat l' \<cdot> (snd f' - fst f')"
      by (simp add: eq2 \<open>l' = Suc k'\<close> \<open>l = k\<close> map_scale_distrib_right)
    finally show ?thesis .
  qed
qed

corollary vpc_snd_last_conv_shifts_of:
  assumes "min_length_vpc zs" and "set zs \<subseteq> shifts_of {f} \<union> shifts_of {f'}"
    and "shifts_of {f} \<inter> shifts_of {f'} = {}"
  shows "snd (last zs) = fst (hd zs) + rat (card (set zs \<inter> shifts_of {f})) \<cdot> (snd f - fst f) +
                                       rat (card (set zs \<inter> shifts_of {f'})) \<cdot> (snd f' - fst f')"
proof -
  define i where "i = length zs - 1"
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  hence "zs \<noteq> []" by (rule is_vpcD)
  hence "i < length zs" and eq: "take (Suc i) zs = zs" by (simp_all add: i_def)
  from \<open>zs \<noteq> []\<close> have "snd (last zs) = snd (zs ! i)" by (simp add: i_def last_conv_nth)
  also have "\<dots> = fst (hd zs) + rat (card (set (take (Suc i) zs) \<inter> shifts_of {f})) \<cdot> (snd f - fst f) +
                                rat (card (set (take (Suc i) zs) \<inter> shifts_of {f'})) \<cdot> (snd f' - fst f')"
    using assms \<open>i < length zs\<close> by (rule vpc_snd_nth_conv_shifts_of)
  also have "\<dots> = fst (hd zs) + rat (card (set zs \<inter> shifts_of {f})) \<cdot> (snd f - fst f) +
                                rat (card (set zs \<inter> shifts_of {f'})) \<cdot> (snd f' - fst f')"
    by (simp only: eq)
  finally show ?thesis .
qed

subsection \<open>Degree Bounds on VPCs\<close>

lemma deg_vpc_eq_hdI:
  assumes "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (snd z) \<le> deg_pm (fst z)"
  shows "deg_vpc zs = deg_pm (fst (hd zs))"
proof (rule antisym)
  from assms(1) show "deg_vpc zs \<le> deg_pm (fst (hd zs))"
  proof (rule deg_vpc_leI)
    fix p
    have "transp (\<lambda>x y. deg_pm y \<le> (deg_pm x :: rat))" by (rule transpI) (drule order.trans)
    moreover from order.refl have "reflp (\<lambda>x y. deg_pm y \<le> (deg_pm x :: rat))" by (rule reflpI)
    moreover note assms
    moreover assume "p \<in> set_of_vpc zs"
    ultimately show "deg_pm p \<le> deg_pm (fst (hd zs))" by (rule vpc_trans_hd)
  qed
next
  from assms(1) have "zs \<noteq> []" by (rule is_vpcD)
  hence "fst (hd zs) \<in> set_of_vpc zs" by (simp add: set_of_vpc_def)
  thus "deg_pm (fst (hd zs)) \<le> deg_vpc zs" by (rule deg_vpc_max)
qed

lemma deg_vpc_eq_lastI:
  assumes "is_vpc zs" and "\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (fst z) \<le> deg_pm (snd z)"
  shows "deg_vpc zs = deg_pm (snd (last zs))"
proof (rule antisym)
  from assms(1) show "deg_vpc zs \<le> deg_pm (snd (last zs))"
  proof (rule deg_vpc_leI)
    fix p
    have "transp (\<lambda>x y. deg_pm x \<le> (deg_pm y :: rat))" by (rule transpI) (drule order.trans)
    moreover from order.refl have "reflp (\<lambda>x y. deg_pm x \<le> (deg_pm y :: rat))" by (rule reflpI)
    moreover note assms
    moreover assume "p \<in> set_of_vpc zs"
    ultimately show "deg_pm p \<le> deg_pm (snd (last zs))" by (rule vpc_trans_last)
  qed
next
  from assms(1) have "zs \<noteq> []" by (rule is_vpcD)
  hence "snd (last zs) \<in> set_of_vpc zs" by (simp add: set_of_vpc_def)
  thus "deg_pm (snd (last zs)) \<le> deg_vpc zs" by (rule deg_vpc_max)
qed

lemma vpc_deg_cases:
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "overlap \<unlhd> fst (hd zs)"
    and "overlap \<unlhd> snd (last zs)"
  assumes "(\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (fst z) \<le> deg_pm (snd z)) \<Longrightarrow> thesis"
  assumes "(\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (snd z) \<le> deg_pm (fst z)) \<Longrightarrow> thesis"
  assumes "\<And>f f'. {f1, f2} = {f, f'} \<Longrightarrow> f \<noteq> f' \<Longrightarrow>
            (\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (fst z) < deg_pm (snd z) \<longleftrightarrow> z \<in> Nshifts {f}) \<Longrightarrow>
            (\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (snd z) < deg_pm (fst z) \<longleftrightarrow> z \<in> Nshifts {f'}) \<Longrightarrow>
            (\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (fst z) \<noteq> deg_pm (snd z)) \<Longrightarrow> thesis"
  shows thesis
proof (cases "\<forall>z\<in>set zs. deg_pm (fst z) \<le> deg_pm (snd z)")
  case True
  hence "\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (fst z) \<le> deg_pm (snd z)" by simp
  thus ?thesis by (rule assms(5))
next
  case *: False
  show ?thesis
  proof (cases "\<forall>z\<in>set zs. deg_pm (snd z) \<le> deg_pm (fst z)")
    case True
    hence "\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (snd z) \<le> deg_pm (fst z)" by simp
    thus ?thesis by (rule assms(6))
  next
    case False
    then obtain z1 where "z1 \<in> set zs" and deg_z1: "deg_pm (fst z1) < deg_pm (snd z1)" by auto
    from * obtain z2 where "z2 \<in> set zs" and deg_z2: "deg_pm (snd z2) < deg_pm (fst z2)" by auto

    from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
    hence sub: "set zs \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
    from \<open>z1 \<in> set zs\<close> sub have "z1 \<in> Nshifts {f1, f2}" ..
    then obtain f where "f \<in> {f1, f2}" and "z1 \<in> Nshifts {f}" by (rule NshiftsE_poly)
    from assms(1-4) this(1) have 1: "deg_pm (fst z) < deg_pm (snd z)"
      if "z \<in> set zs" and "z \<in> Nshifts {f}" for z
    proof (rule thm_3_3_22)
      assume sub2: "set zs \<inter> Nshifts {f} \<subseteq> pos_Nshifts {f}"
      from \<open>z1 \<in> set zs\<close> \<open>z1 \<in> Nshifts {f}\<close> have "z1 \<in> set zs \<inter> Nshifts {f}" ..
      hence z1: "z1 \<in> pos_Nshifts {f}" using sub2 ..
      from that have "z \<in> set zs \<inter> Nshifts {f}" ..
      hence "z \<in> pos_Nshifts {f}" using sub2 ..
      with deg_z1 z1 show ?thesis
        by (auto simp: pos_Nshifts_singleton nat_plus_point_pair_def deg_pm_plus)
    next
      assume sub2: "set zs \<inter> Nshifts {f} \<subseteq> neg_Nshifts {f}"
      from \<open>z1 \<in> set zs\<close> \<open>z1 \<in> Nshifts {f}\<close> have "z1 \<in> set zs \<inter> Nshifts {f}" ..
      hence z1: "z1 \<in> neg_Nshifts {f}" using sub2 ..
      from that have "z \<in> set zs \<inter> Nshifts {f}" ..
      hence "z \<in> neg_Nshifts {f}" using sub2 ..
      with deg_z1 z1 show ?thesis
        by (auto simp: neg_Nshifts_singleton nat_plus_point_pair_def deg_pm_plus)
    qed

    from \<open>z2 \<in> set zs\<close> sub have "z2 \<in> Nshifts {f1, f2}" ..
    then obtain f' where "f' \<in> {f1, f2}" and "z2 \<in> Nshifts {f'}" by (rule NshiftsE_poly)
    from assms(1-4) this(1) have 2: "deg_pm (snd z) < deg_pm (fst z)"
      if "z \<in> set zs" and "z \<in> Nshifts {f'}" for z
    proof (rule thm_3_3_22)
      assume sub2: "set zs \<inter> Nshifts {f'} \<subseteq> pos_Nshifts {f'}"
      from \<open>z2 \<in> set zs\<close> \<open>z2 \<in> Nshifts {f'}\<close> have "z2 \<in> set zs \<inter> Nshifts {f'}" ..
      hence z2: "z2 \<in> pos_Nshifts {f'}" using sub2 ..
      from that have "z \<in> set zs \<inter> Nshifts {f'}" ..
      hence "z \<in> pos_Nshifts {f'}" using sub2 ..
      with deg_z2 z2 show ?thesis
        by (auto simp: pos_Nshifts_singleton nat_plus_point_pair_def deg_pm_plus)
    next
      assume sub2: "set zs \<inter> Nshifts {f'} \<subseteq> neg_Nshifts {f'}"
      from \<open>z2 \<in> set zs\<close> \<open>z2 \<in> Nshifts {f'}\<close> have "z2 \<in> set zs \<inter> Nshifts {f'}" ..
      hence z2: "z2 \<in> neg_Nshifts {f'}" using sub2 ..
      from that have "z \<in> set zs \<inter> Nshifts {f'}" ..
      hence "z \<in> neg_Nshifts {f'}" using sub2 ..
      with deg_z2 z2 show ?thesis
        by (auto simp: neg_Nshifts_singleton nat_plus_point_pair_def deg_pm_plus)
    qed

    show ?thesis
    proof (rule assms(7))
      show "f \<noteq> f'"
      proof
        assume "f = f'"
        with \<open>z1 \<in> Nshifts {f}\<close> have "z1 \<in> Nshifts {f'}" by simp
        with \<open>z1 \<in> set zs\<close> have "deg_pm (snd z1) < deg_pm (fst z1)" by (rule 2)
        also from \<open>z1 \<in> set zs\<close> \<open>z1 \<in> Nshifts {f}\<close> have "\<dots> < deg_pm (snd z1)" by (rule 1)
        finally show False .
      qed
      with \<open>f \<in> {f1, f2}\<close> \<open>f' \<in> {f1, f2}\<close> show eq: "{f1, f2} = {f, f'}" by blast
  
      fix z
      assume "z \<in> set zs"
      hence "z \<in> Nshifts {f1, f2}" using sub ..
      then obtain g where "g \<in> {f, f'}" and "z \<in> Nshifts {g}" unfolding eq by (rule NshiftsE_poly)
      thus "deg_pm (fst z) < deg_pm (snd z) \<longleftrightarrow> z \<in> Nshifts {f}"
        and "deg_pm (snd z) < deg_pm (fst z) \<longleftrightarrow> z \<in> Nshifts {f'}"
        and "deg_pm (fst z) \<noteq> deg_pm (snd z)"
        using \<open>z \<in> set zs\<close> by (auto dest: 1 2)
    qed
  qed
qed

definition is_peak :: "('x point \<times> 'x point) list \<Rightarrow> nat \<Rightarrow> bool"
  where "is_peak zs i \<longleftrightarrow> (Suc i < length zs \<and> deg_pm (fst (zs ! i)) < deg_pm (snd (zs ! i)) \<and>
                        deg_pm (snd (zs ! Suc i)) < deg_pm (snd (zs ! i)))"

lemma is_peakI:
  "Suc i < length zs \<Longrightarrow> deg_pm (fst (zs ! i)) < deg_pm (snd (zs ! i)) \<Longrightarrow>
    deg_pm (snd (zs ! Suc i)) < deg_pm (snd (zs ! i)) \<Longrightarrow> is_peak zs i"
  by (simp add: is_peak_def)

lemma is_peakD:
  assumes "is_peak zs i"
  shows "i < length zs" and "Suc i < length zs" and "deg_pm (fst (zs ! i)) < deg_pm (snd (zs ! i))"
    and "deg_pm (snd (zs ! Suc i)) < deg_pm (snd (zs ! i))"
  using assms by (simp_all add: is_peak_def)

lemma is_peakE:
  assumes "is_vpc zs" and "is_peak zs i"
  obtains f f' where "f \<in> shifts {f1, f2}" and "f' \<in> shifts {f1, f2}" and "f \<noteq> f'"
    and "zs ! i \<in> shifts_of {f}" and "zs ! Suc i \<in> shifts_of {f'}"
    and "snd (zs ! Suc i) + fst f - snd f = fst (zs ! i) + snd f' - fst f'"
    and "deg_pm (fst f) < deg_pm (snd f)" and "deg_pm (snd f') < deg_pm (fst f')"
    and "shifts_of {f} \<inter> shifts_of {f'} = {}"
proof -
  from assms(2) have "Suc i < length zs" by (rule is_peakD)
  hence "zs ! i \<in> set zs" and "zs ! Suc i \<in> set zs" by simp_all
  moreover from assms(1) have "set zs \<subseteq> Nshifts {f1, f2}" by (rule is_vpcD)
  ultimately have "zs ! i \<in> Nshifts {f1, f2}" and *: "zs ! Suc i \<in> Nshifts {f1, f2}" by blast+
  from this(1) obtain f where f_in: "f \<in> shifts {f1, f2}" and i_in: "zs ! i \<in> shifts_of {f}"
    unfolding Nshifts_alt by (rule shifts_ofE_poly)
  from this(2) have snd_i: "snd (zs ! i) = fst (zs ! i) + snd f - fst f" by (rule shifts_of_singletonD)
  from * obtain f' where f'_in: "f' \<in> shifts {f1, f2}" and Si_in: "zs ! Suc i \<in> shifts_of {f'}"
    unfolding Nshifts_alt by (rule shifts_ofE_poly)
  from this(2) have snd_Si: "snd (zs ! Suc i) = fst (zs ! Suc i) + snd f' - fst f'"
    by (rule shifts_of_singletonD)

  from f_in f'_in _ i_in Si_in show ?thesis
  proof
    from assms(1) \<open>Suc i < length zs\<close> have eq: "snd (zs ! i) = fst (zs ! Suc i)" by (rule is_vpcD)
    also from snd_Si have "\<dots> = snd (zs ! Suc i) + fst f' - snd f'" by simp
    finally have "snd (zs ! Suc i) = snd (zs ! i) + snd f' - fst f'" by simp
    thus "snd (zs ! Suc i) + fst f - snd f = fst (zs ! i) + snd f' - fst f'" by (simp add: snd_i)

    from assms(2) have "deg_pm (fst (zs ! i)) < deg_pm (snd (zs ! i))" by (rule is_peakD)
    thus deg_f: "deg_pm (fst f) < deg_pm (snd f)"
      by (simp add: snd_i shifts_of_singletonD deg_pm_plus deg_pm_minus)

    from assms(2) have "deg_pm (snd (zs ! Suc i)) < deg_pm (snd (zs ! i))" by (rule is_peakD)
    thus deg_f': "deg_pm (snd f') < deg_pm (fst f')"
      by (simp add: snd_Si shifts_of_singletonD deg_pm_plus deg_pm_minus eq)

    with deg_f show "f \<noteq> f'" by auto

    show "shifts_of {f} \<inter> shifts_of {f'} = {}"
    proof (intro set_eqI iffI, elim IntE)
      fix z
      assume "z \<in> shifts_of {f}"
      hence "snd z = fst z + snd f - fst f" by (rule shifts_of_singletonD)
      with deg_f have "deg_pm (fst z) < deg_pm (snd z)" by (simp add: deg_pm_plus deg_pm_minus)
      assume "z \<in> shifts_of {f'}"
      hence "snd z = fst z + snd f' - fst f'" by (rule shifts_of_singletonD)
      with deg_f' have "deg_pm (snd z) < deg_pm (fst z)" by (simp add: deg_pm_plus deg_pm_minus)
      also have "\<dots> < deg_pm (snd z)" by fact
      finally show "z \<in> {}" .
    qed simp
  qed
qed

lemma finite_peaks: "finite {i. is_peak zs i}"
proof (rule finite_subset)
  show "{i. is_peak zs i} \<subseteq> {..length zs}" by (auto simp: is_peak_def)
qed (fact finite_atMost)

lemma peak_deg_gr_zero:
  assumes "is_vpc zs" and "is_peak zs i"
  shows "0 < to_nat (deg_pm (snd (zs ! i)))"
proof -
  from assms(2) have "i < length zs" and "deg_pm (fst (zs ! i)) < deg_pm (snd (zs ! i))" (is "?a < ?b")
    by (rule is_peakD)+
  from this(1) have "zs ! i \<in> set zs" by simp
  with assms(1) have "is_nat_pm_pair (zs ! i)" by (rule vpc_is_nat_pm_pair)
  hence "is_nat ?a" and "is_nat ?b" by (simp_all add: is_nat_pm_pair_def deg_is_nat)
  from this(1) have "rat (to_nat ?a) = ?a" by (simp only: is_nat_def)
  also have "\<dots> < ?b" by fact
  also from \<open>is_nat ?b\<close> have "\<dots> = rat (to_nat ?b)" by (simp only: is_nat_def)
  finally have "to_nat ?a < to_nat ?b" by (simp only: of_nat_less_iff)
  with le0 show ?thesis by (rule le_less_trans)
qed

lemma deg_vpc_cases:
  assumes "min_length_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "overlap \<unlhd> fst (hd zs)"
    and "overlap \<unlhd> snd (last zs)"
  assumes "deg_vpc zs = deg_pm (fst (hd zs)) \<Longrightarrow> thesis"
  assumes "deg_vpc zs = deg_pm (snd (last zs)) \<Longrightarrow> thesis"
  assumes "\<And>i. i < length zs \<Longrightarrow> is_peak zs i \<Longrightarrow> deg_vpc zs = deg_pm (snd (zs ! i)) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "is_vpc zs" by (rule min_length_vpcD)
  from assms(1-4) show ?thesis
  proof (rule vpc_deg_cases)
    assume "\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (fst z) \<le> deg_pm (snd z)"
    with \<open>is_vpc zs\<close> have "deg_vpc zs = deg_pm (snd (last zs))" by (rule deg_vpc_eq_lastI)
    thus ?thesis by (rule assms(6))
  next
    assume "\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (snd z) \<le> deg_pm (fst z)"
    with \<open>is_vpc zs\<close> have "deg_vpc zs = deg_pm (fst (hd zs))" by (rule deg_vpc_eq_hdI)
    thus ?thesis by (rule assms(5))
  next
    assume rl: "\<And>z. z \<in> set zs \<Longrightarrow> deg_pm (fst z) \<noteq> deg_pm (snd z)"
    from \<open>is_vpc zs\<close> have "zs \<noteq> []" by (rule is_vpcD)
    hence "deg_pm ` set_of_vpc zs \<noteq> {}" by (simp add: set_of_vpc_def)
    with finite_imageI have "Max (deg_pm ` set_of_vpc zs) \<in> deg_pm ` set_of_vpc zs"
      by (rule Max_in) (fact finite_set_of_vpc)
    with \<open>zs \<noteq> []\<close> have "deg_vpc zs \<in> deg_pm ` set_of_vpc zs" by (simp add: deg_vpc_def)
    then obtain p where "p \<in> set_of_vpc zs" and eq: "deg_vpc zs = deg_pm p" ..
    from \<open>is_vpc zs\<close> this(1) show ?thesis
    proof (rule set_of_vpcE_vpc)
      assume "p = fst (hd zs)"
      hence "deg_vpc zs = deg_pm (fst (hd zs))" by (simp only: eq)
      thus ?thesis by (rule assms(5))
    next
      assume "p = snd (last zs)"
      hence "deg_vpc zs = deg_pm (snd (last zs))" by (simp only: eq)
      thus ?thesis by (rule assms(6))
    next
      fix i
      assume "i < length zs" and *: "Suc i < length zs" and p1[symmetric]: "p = fst (zs ! Suc i)"
        and p2: "p = snd (zs ! i)"
      note this(1)
      moreover from * have "is_peak zs i"
      proof (rule is_peakI)
        from \<open>i < length zs\<close> have "zs ! i \<in> set zs" by simp
        hence "fst (zs ! i) \<in> set_of_vpc zs" by (simp add: set_of_vpc_def)
        hence "deg_pm (fst (zs ! i)) \<le> deg_vpc zs" by (rule deg_vpc_max)
        hence "deg_pm (fst (zs ! i)) \<le> deg_pm (snd (zs ! i))" by (simp only: eq p2)
        moreover from \<open>zs ! i \<in> set zs\<close> have "deg_pm (fst (zs ! i)) \<noteq> deg_pm (snd (zs ! i))"
          by (rule rl)
        ultimately show "deg_pm (fst (zs ! i)) < deg_pm (snd (zs ! i))" by (rule le_neq_trans)
      next
        from * have "zs ! Suc i \<in> set zs" by simp
        hence "snd (zs ! Suc i) \<in> set_of_vpc zs" by (simp add: set_of_vpc_def)
        hence "deg_pm (snd (zs ! Suc i)) \<le> deg_vpc zs" by (rule deg_vpc_max)
        hence "deg_pm (snd (zs ! Suc i)) \<le> deg_pm (snd (zs ! i))" by (simp only: eq p2)
        moreover from \<open>zs ! Suc i \<in> set zs\<close> have "deg_pm (snd (zs ! Suc i)) \<noteq> deg_pm (fst (zs ! Suc i))"
          by (rule rl[symmetric])
        ultimately show "deg_pm (snd (zs ! Suc i)) < deg_pm (snd (zs ! i))"
          unfolding p1 p2 by (rule le_neq_trans)
      qed
      moreover have "deg_vpc zs = deg_pm (snd (zs ! i))" by (simp only: eq p2)
      ultimately show ?thesis by (rule assms(7))
    qed
  qed
qed

definition repl_peaks :: "('x point \<times> 'x point) list \<Rightarrow> nat set"
  where "repl_peaks zs = {i. is_peak zs i \<and>
                                    (\<exists>f\<in>shifts {f1, f2}. \<exists>f'\<in>shifts {f1, f2}.
                                        zs ! i \<in> shifts_of {f} \<and> zs ! Suc i \<in> shifts_of {f'} \<and>
                                        lcs (fst f) (snd f') \<unlhd> fst (zs ! i) + snd f' - fst f')}"

definition maxdeg_repl_peaks :: "('x point \<times> 'x point) list \<Rightarrow> nat"
  where "maxdeg_repl_peaks zs = (if repl_peaks zs = {} then 0
                                else to_nat (Max (deg_pm ` snd ` (!) zs ` repl_peaks zs)))"

definition mrepl_peaks :: "('x point \<times> 'x point) list \<Rightarrow> nat set"
  where "mrepl_peaks zs = {i\<in>repl_peaks zs. deg_pm (snd (zs ! i)) = rat (maxdeg_repl_peaks zs)}"

text \<open>@{const repl_peaks} stands for `replaceable peaks', because any such peak can be replaced by
  something else, as will be shown below.\<close>

lemma repl_peaksI:
  "is_peak zs i \<Longrightarrow> f \<in> shifts {f1, f2} \<Longrightarrow> f' \<in> shifts {f1, f2} \<Longrightarrow> zs ! i \<in> shifts_of {f} \<Longrightarrow>
    zs ! Suc i \<in> shifts_of {f'} \<Longrightarrow> lcs (fst f) (snd f') \<unlhd> fst (zs ! i) + snd f' - fst f' \<Longrightarrow>
    i \<in> repl_peaks zs"
  by (auto simp: repl_peaks_def)

lemma repl_peaksD:
  assumes "i \<in> repl_peaks zs"
  shows "i < length zs" and "Suc i < length zs" and "is_peak zs i"
  using assms by (auto simp: repl_peaks_def dest: is_peakD)

lemma repl_peaksE:
  assumes "is_vpc zs" and "i \<in> repl_peaks zs"
  obtains f f' where "f \<in> shifts {f1, f2}" and "f' \<in> shifts {f1, f2}"
    and "zs ! i \<in> shifts_of {f}" and "zs ! Suc i \<in> shifts_of {f'}"
    and "lcs (fst f) (snd f') \<unlhd> fst (zs ! i) + snd f' - fst f'"
    and "snd (zs ! Suc i) + fst f - snd f = fst (zs ! i) + snd f' - fst f'"
    and "deg_pm (fst f) < deg_pm (snd f)" and "deg_pm (snd f') < deg_pm (fst f')"
proof -
  from assms(2) obtain f f' where "f \<in> shifts {f1, f2}" and "f' \<in> shifts {f1, f2}"
    and 1: "zs ! i \<in> shifts_of {f}" and 2: "zs ! Suc i \<in> shifts_of {f'}"
    and "lcs (fst f) (snd f') \<unlhd> fst (zs ! i) + snd f' - fst f'" by (auto simp: repl_peaks_def)
  thus ?thesis
  proof
    from assms(2) have *: "Suc i < length zs" by (rule repl_peaksD)
    from 1 have "fst (zs ! i) + snd f - fst f = snd (zs ! i)" by (simp only: shifts_of_singletonD)
    also from assms(1) * have eq: "\<dots> = fst (zs ! Suc i)" by (rule is_vpcD)
    also from 2 have "\<dots> = snd (zs ! Suc i) + fst f' - snd f'" by (simp add: shifts_of_singletonD)
    finally show "snd (zs ! Suc i) + fst f - snd f = fst (zs ! i) + snd f' - fst f'"
      by (smt add_diff_eq diff_add_eq_diff_diff_swap diff_diff_eq2 group_eq_aux)

    from assms(2) have "is_peak zs i" by (rule repl_peaksD)
    hence "deg_pm (fst (zs ! i)) < deg_pm (snd (zs ! i))" by (rule is_peakD)
    with 1 show "deg_pm (fst f) < deg_pm (snd f)"
      by (simp add: shifts_of_singletonD deg_pm_plus deg_pm_minus)

    from assms(2) have "is_peak zs i" by (rule repl_peaksD)
    hence "deg_pm (snd (zs ! Suc i)) < deg_pm (snd (zs ! i))" by (rule is_peakD)
    with 2 show "deg_pm (snd f') < deg_pm (fst f')"
      by (simp add: eq shifts_of_singletonD deg_pm_plus deg_pm_minus)
  qed
qed

lemma repl_peaks_cong:
  assumes "i \<in> repl_peaks zs" and "length zs \<le> length zs'" and "zs' ! i = zs ! i"
    and "zs' ! Suc i = zs ! Suc i"
  shows "i \<in> repl_peaks zs'"
proof -
  from assms(1) have "Suc i < length zs" and "is_peak zs i" by (rule repl_peaksD)+
  from this(1) assms(2) have "Suc i < length zs'" by simp
  hence "is_peak zs' i"
  proof (rule is_peakI)
    show "deg_pm (fst (zs' ! i)) < deg_pm (snd (zs' ! i))"
      unfolding assms(3) using \<open>is_peak zs i\<close> by (rule is_peakD)
  next
    show "deg_pm (snd (zs' ! Suc i)) < deg_pm (snd (zs' ! i))"
      unfolding assms(3, 4) using \<open>is_peak zs i\<close> by (rule is_peakD)
  qed
  moreover from assms(1) obtain f f' where "f \<in> shifts {f1, f2}" and "f' \<in> shifts {f1, f2}"
    and "zs' ! i \<in> shifts_of {f}" and "zs' ! Suc i \<in> shifts_of {f'}"
    and "lcs (fst f) (snd f') \<unlhd> fst (zs' ! i) + snd f' - fst f'"
    by (auto simp: assms(3, 4) repl_peaks_def)
  ultimately show ?thesis by (rule repl_peaksI)
qed

lemma finite_repl_peaks: "finite (repl_peaks zs)"
proof (rule finite_subset)
  show "repl_peaks zs \<subseteq> {i. is_peak zs i}" by (auto simp: repl_peaks_def)
qed (fact finite_peaks)

lemma finite_mrepl_peaks: "finite (mrepl_peaks zs)"
proof (rule finite_subset)
  show "mrepl_peaks zs \<subseteq> repl_peaks zs" by (auto simp: mrepl_peaks_def)
qed (fact finite_repl_peaks)

lemma maxdeg_repl_peaks_max:
  assumes "is_vpc zs" and "i \<in> repl_peaks zs"
  shows "deg_pm (snd (zs ! i)) \<le> rat (maxdeg_repl_peaks zs)"
proof -
  from assms(2) have "i < length zs" by (rule repl_peaksD)
  hence "snd (zs ! i) \<in> set_of_vpc zs" by (simp add: set_of_vpc_def)
  with assms(1) have "is_nat_pm (snd (zs ! i))" by (rule vpc_is_nat_pm)
  hence "is_nat (deg_pm (snd (zs ! i)))" (is "is_nat ?d") by (rule deg_is_nat)
  hence eq: "rat (to_nat ?d) = ?d" by (simp only: is_nat_def)
  from finite_repl_peaks have "finite (deg_pm ` snd ` (!) zs ` repl_peaks zs)" by (intro finite_imageI)
  moreover from assms(2) have "?d \<in> deg_pm ` snd ` (!) zs ` repl_peaks zs" by (intro imageI)
  ultimately have "?d \<le> Max (deg_pm ` snd ` (!) zs ` repl_peaks zs)" by (rule Max_ge)
  with assms(2) have "to_nat ?d \<le> maxdeg_repl_peaks zs"
    by (auto simp: maxdeg_repl_peaks_def dest: to_nat_mono)
  hence "rat (to_nat ?d) \<le> rat (maxdeg_repl_peaks zs)" by (rule of_nat_mono)
  thus ?thesis by (simp only: eq)
qed

lemma maxdeg_repl_peaksE:
  assumes "is_vpc zs" and "repl_peaks zs \<noteq> {}"
  obtains i where "i \<in> repl_peaks zs" and "deg_pm (snd (zs ! i)) = rat (maxdeg_repl_peaks zs)"
proof -
  from finite_repl_peaks have "finite (deg_pm ` snd ` (!) zs ` repl_peaks zs)" (is "finite ?A")
    by (intro finite_imageI)
  moreover from assms(2) have "?A \<noteq> {}" by simp
  ultimately have "Max ?A \<in> ?A" by (rule Max_in)
  then obtain i where "i \<in> repl_peaks zs" and "Max ?A = deg_pm (snd (zs ! i))" (is "_ = ?d") by blast
  from assms(2) this(2) have eq: "rat (to_nat ?d) = rat (maxdeg_repl_peaks zs)"
    by (simp add: maxdeg_repl_peaks_def)
  from \<open>i \<in> repl_peaks zs\<close> have "i < length zs" by (rule repl_peaksD)
  hence "snd (zs ! i) \<in> set_of_vpc zs" by (simp add: set_of_vpc_def)
  with assms(1) have "is_nat_pm (snd (zs ! i))" by (rule vpc_is_nat_pm)
  hence "is_nat (deg_pm (snd (zs ! i)))" (is "is_nat ?d") by (rule deg_is_nat)
  hence "?d = rat (maxdeg_repl_peaks zs)" by (simp only: eq is_nat_def)
  with \<open>i \<in> repl_peaks zs\<close> show ?thesis ..
qed

lemma maxdeg_repl_peaks_le:
  assumes "is_vpc zs" and "\<And>i. i \<in> repl_peaks zs \<Longrightarrow> deg_pm (snd (zs ! i)) \<le> rat n"
  shows "maxdeg_repl_peaks zs \<le> n"
proof (cases "repl_peaks zs = {}")
  case True
  thus ?thesis by (simp add: maxdeg_repl_peaks_def)
next
  case False
  with assms(1) obtain i where "i \<in> repl_peaks zs"
    and eq: "deg_pm (snd (zs ! i)) = rat (maxdeg_repl_peaks zs)" by (rule maxdeg_repl_peaksE)
  from this(1) have "deg_pm (snd (zs ! i)) \<le> rat n" by (rule assms(2))
  thus ?thesis by (simp add: eq)
qed

lemma mrepl_peaks_empty_iff:
  assumes "is_vpc zs"
  shows "mrepl_peaks zs = {} \<longleftrightarrow> repl_peaks zs = {}"
proof
  assume a: "mrepl_peaks zs = {}"
  show "repl_peaks zs = {}"
  proof (rule ccontr)
    assume "repl_peaks zs \<noteq> {}"
    with assms obtain i where "i \<in> repl_peaks zs" and "deg_pm (snd (zs ! i)) = rat (maxdeg_repl_peaks zs)"
      by (rule maxdeg_repl_peaksE)
    hence "i \<in> mrepl_peaks zs" by (simp add: mrepl_peaks_def)
    thus False by (simp add: a)
  qed
qed (simp add: mrepl_peaks_def)

lemma maxdeg_repl_peaks_eq_zero_iff:
  assumes "is_vpc zs"
  shows "maxdeg_repl_peaks zs = 0 \<longleftrightarrow> repl_peaks zs = {}"
proof
  assume a: "maxdeg_repl_peaks zs = 0"
  show "repl_peaks zs = {}"
  proof (rule ccontr)
    assume "repl_peaks zs \<noteq> {}"
    with assms obtain i where "i \<in> repl_peaks zs" and "deg_pm (snd (zs ! i)) = rat (maxdeg_repl_peaks zs)"
      by (rule maxdeg_repl_peaksE)
    from this(2) have "to_nat (deg_pm (snd (zs ! i))) = 0" by (simp add: a to_nat_def)
    also from assms have "\<dots> < to_nat (deg_pm (snd (zs ! i)))"
    proof (rule peak_deg_gr_zero)
      from \<open>i \<in> repl_peaks zs\<close> show "is_peak zs i" by (rule repl_peaksD)
    qed
    finally show False ..
  qed
qed (simp add: maxdeg_repl_peaks_def)

lemma thm_3_3_25:
  assumes "is_vpc zs" and "repl_peaks zs \<noteq> {}"
  obtains zs' where "is_vpc zs'" and "fst (hd zs') = fst (hd zs)" and "snd (last zs') = snd (last zs)"
    and "length zs' = length zs"
    and "maxdeg_repl_peaks zs' < maxdeg_repl_peaks zs \<or>
          (maxdeg_repl_peaks zs' = maxdeg_repl_peaks zs \<and> card (mrepl_peaks zs') < card (mrepl_peaks zs))"
proof -
  from assms obtain i where "i \<in> repl_peaks zs"
    and deg_i: "deg_pm (snd (zs ! i)) = rat (maxdeg_repl_peaks zs)" by (rule maxdeg_repl_peaksE)
  from assms(1) this(1) obtain f f' where f_in: "f \<in> shifts {f1, f2}" and f'_in: "f' \<in> shifts {f1, f2}"
    and i_in: "zs ! i \<in> shifts_of {f}" and Si_in: "zs ! Suc i \<in> shifts_of {f'}"
    and lcs: "lcs (fst f) (snd f') \<unlhd> fst (zs ! i) + snd f' - fst f'"
    and eq: "snd (zs ! Suc i) + fst f - snd f = fst (zs ! i) + snd f' - fst f'"
    and deg_f: "deg_pm (fst f) < deg_pm (snd f)" and deg_f': "deg_pm (snd f') < deg_pm (fst f')"
    by (rule repl_peaksE)
  let ?y = "(fst (zs ! i), fst (zs ! i) + snd f' - fst f')"
  let ?z = "(snd (zs ! Suc i) + fst f - snd f, snd (zs ! Suc i))"
  from \<open>i \<in> repl_peaks zs\<close> have *: "Suc i < length zs" and "is_peak zs i" by (rule repl_peaksD)+
  from assms(1) obtain zs' where "is_vpc zs'" and "fst (hd zs') = fst (hd zs)"
    and "snd (last zs') = snd (last zs)" and zs': "zs' = take i zs @ [?y, ?z] @ drop (Suc (Suc i)) zs"
  proof (rule replace_vpc)
    show "i \<le> Suc i" by simp
  next
    show "Suc i < length zs" by fact
  next
    have "?z \<in> Nshifts {f1, f2}"
    proof -
      define t' where "t' = snd (zs ! Suc i) - snd f"
      from * have "zs ! Suc i \<in> set zs" by simp
      with assms(1) have "is_nat_pm_pair (zs ! Suc i)" by (rule vpc_is_nat_pm_pair)
      moreover from f_in have "is_nat_pm_pair f" by (rule shifts_is_nat_pm_pair)
      ultimately have "is_int_pm t'"
        by (simp add: t'_def is_nat_pm_pair_def minus_is_int_pm nat_pm_is_int_pm)
      from lcs have "lcs (fst f) (snd f') \<unlhd> snd (zs ! Suc i) + fst f - snd f" by (simp only: eq)
      with lcs_ge_pm(1) have "fst f \<unlhd> snd (zs ! Suc i) + fst f - snd f" by (rule le_pm_trans)
      hence "fst f - fst f \<unlhd> snd (zs ! Suc i) + fst f - snd f - fst f" by (rule le_pm_mono_minus)
      hence "0 \<unlhd> t'" by (simp add: t'_def)
      with \<open>is_int_pm t'\<close> zero_is_nat_pm have "is_nat_pm t'" by (rule int_pm_is_nat_pmI)
      moreover define t where "t = to_nat_pm t'"
      ultimately have t: "of_nat_pm t = t'" by (simp only: of_nat_pm_comp_to_nat_pm)
      have "snd (zs ! Suc i) + fst f - snd f = t' + fst f" by (simp add: t'_def)
      moreover from this have "snd (zs ! Suc i) = t' + snd f"
        by (simp add: linordered_field_class.sign_simps)
      ultimately have "?z = t +\<^sub>N f" by (simp add: t nat_plus_point_pair_def)
      with f_in show ?thesis by (auto simp: Nshifts_alt shifts_of_def)
    qed
    hence "is_vpc [?z]" by (simp only: is_vpc_singleton)
    moreover have "?y \<in> Nshifts {f1, f2}"
    proof -
      define t' where "t' = fst (zs ! i) - fst f'"
      from * have "zs ! i \<in> set zs" by simp
      with assms(1) have "is_nat_pm_pair (zs ! i)" by (rule vpc_is_nat_pm_pair)
      moreover from f'_in have "is_nat_pm_pair f'" by (rule shifts_is_nat_pm_pair)
      ultimately have "is_int_pm t'"
        by (simp add: t'_def is_nat_pm_pair_def minus_is_int_pm nat_pm_is_int_pm)
      from lcs_ge_pm(2) lcs have "snd f' \<unlhd> fst (zs ! i) + snd f' - fst f'" by (rule le_pm_trans)
      hence "snd f' - snd f' \<unlhd> fst (zs ! i) + snd f' - fst f' - snd f'" by (rule le_pm_mono_minus)
      hence "0 \<unlhd> t'" by (simp add: t'_def)
      with \<open>is_int_pm t'\<close> zero_is_nat_pm have "is_nat_pm t'" by (rule int_pm_is_nat_pmI)
      moreover define t where "t = to_nat_pm t'"
      ultimately have t: "of_nat_pm t = t'" by (simp only: of_nat_pm_comp_to_nat_pm)
      have "fst (zs ! i) + snd f' - fst f' = t' + snd f'" by (simp add: t'_def)
      moreover from this have "fst (zs ! i) = t' + fst f'"
        by (simp add: linordered_field_class.sign_simps)
      ultimately have "?y = t +\<^sub>N f'" by (simp add: t nat_plus_point_pair_def)
      with f'_in show ?thesis by (auto simp: Nshifts_alt shifts_of_def)
    qed
    ultimately show "is_vpc [?y, ?z]" by (rule is_vpc_ConsI) (simp add: eq)
  next
    show "fst (hd [?y, ?z]) = fst (zs ! i)" by simp
  next
    show "snd (last [?y, ?z]) = snd (zs ! Suc i)" by simp
  next
    assume "[?y, ?z] = []"
    thus False by simp
    thus "fst (zs ! i) = snd (zs ! Suc i)" ..
  qed
  note this(1, 2, 3)
  moreover from * have len_zs': "length zs' = length zs" by (simp add: zs')
  moreover have "maxdeg_repl_peaks zs' < maxdeg_repl_peaks zs \<or>
      (maxdeg_repl_peaks zs' = maxdeg_repl_peaks zs \<and> card (mrepl_peaks zs') < card (mrepl_peaks zs))"
  proof -
    from \<open>Suc i < length zs\<close> have min_i: "min (length zs) i = i" by simp
    have zs'_nth: "zs' ! j = zs ! j" if "j < length zs" and "j \<noteq> i" and "j \<noteq> Suc i" for j
    proof -
      {
        assume "\<not> j < i"
        with that(2, 3) have "Suc (Suc i) \<le> j" by linarith
        hence "Suc (Suc (j - 2)) = j" by simp
      }
      with that show ?thesis by (simp add: min_i zs' nth_append)
    qed
    have fst_zs': "fst (zs' ! j) = fst (zs ! j)" if "j < length zs" and "j \<noteq> Suc i" for j
    proof (cases "j = i")
      case True
      thus ?thesis by (simp add: min_i zs' nth_append)
    next
      case False
      with that show ?thesis by (simp add: zs'_nth)
    qed
    have snd_zs': "snd (zs' ! j) = snd (zs ! j)" if "j < length zs" and "j \<noteq> i" for j
    proof (cases "j = Suc i")
      case True
      thus ?thesis by (simp add: min_i zs' nth_append)
    next
      case False
      with that show ?thesis by (simp add: zs'_nth)
    qed
    have "i \<notin> repl_peaks zs'"
    proof
      assume "i \<in> repl_peaks zs'"
      hence "is_peak zs' i" by (rule repl_peaksD)
      hence **: "deg_pm (fst (zs' ! i)) < deg_pm (snd (zs' ! i))" by (rule is_peakD)
      from * have "zs' ! i = ?y" by (simp add: zs' nth_append)
      moreover from * have "zs' ! Suc i = ?z" by (simp add: zs' nth_append)
      ultimately have "deg_pm (snd (zs' ! i)) < deg_pm (fst (zs' ! i))" using deg_f'
        by (simp add: deg_pm_plus deg_pm_minus)
      with ** show False by (rule order.asym)
    qed
    moreover have "repl_peaks zs' \<subseteq> insert (Suc i) (insert (i - 1) (repl_peaks zs))"
    proof
      fix j
      assume j_in: "j \<in> repl_peaks zs'"
      with \<open>i \<notin> repl_peaks zs'\<close> have "j \<noteq> i" by blast
      {
        assume "j \<noteq> Suc i" and "j \<noteq> i - 1"
        from j_in have "j \<in> repl_peaks zs"
        proof (rule repl_peaks_cong)
          from j_in have "j < length zs'" by (rule repl_peaksD)
          hence "j < length zs" by (simp only: len_zs')
          thus "zs ! j = zs' ! j" using \<open>j \<noteq> i\<close> \<open>j \<noteq> Suc i\<close> by (rule zs'_nth[symmetric])
        next
          from j_in have "Suc j < length zs'" by (rule repl_peaksD)
          hence "Suc j < length zs" by (simp only: len_zs')
          moreover from \<open>j \<noteq> i - 1\<close> have "Suc j \<noteq> i" by simp
          moreover from \<open>j \<noteq> i\<close> have "Suc j \<noteq> Suc i" by simp
          ultimately show "zs ! Suc j = zs' ! Suc j" by (rule zs'_nth[symmetric])
        qed (simp add: len_zs')
      }
      thus "j \<in> insert (Suc i) (insert (i - 1) (repl_peaks zs))" by blast
    qed
    ultimately have sub: "repl_peaks zs' \<subseteq> insert (Suc i) (insert (i - 1) (repl_peaks zs)) - {i}"
      by blast
    have less1: "deg_pm (snd (zs' ! Suc i)) < rat (maxdeg_repl_peaks zs)" if "Suc i \<in> repl_peaks zs'"
    proof -
      from that have "Suc i < length zs'" by (rule repl_peaksD)
      hence "Suc i < length zs" by (simp only: len_zs')
      hence "snd (zs' ! Suc i) = snd (zs ! Suc i)" by (rule snd_zs') simp
      also from \<open>is_peak zs i\<close> have "deg_pm \<dots> < deg_pm (snd (zs ! i))" by (rule is_peakD)
      also have "\<dots> = rat (maxdeg_repl_peaks zs)" by fact
      finally show ?thesis .
    qed
    have less2: "deg_pm (snd (zs' ! (i - 1))) < rat (maxdeg_repl_peaks zs)" if "i - 1 \<in> repl_peaks zs'"
    proof -
      from that sub have "i - 1 \<noteq> i" by blast
      hence "Suc (i - 1) = i" by simp
      from that have "Suc (i - 1) < length zs'" by (rule repl_peaksD)
      hence "Suc (i - 1) < length zs" by (simp only: len_zs')
      hence "i - 1 < length zs" by simp
      hence "snd (zs' ! (i - 1)) = snd (zs ! (i - 1))" using \<open>i - 1 \<noteq> i\<close> by (rule snd_zs')
      also from assms(1) \<open>Suc (i - 1) < length zs\<close> have "\<dots> = fst (zs ! Suc (i - 1))" by (rule is_vpcD)
      also have "deg_pm \<dots> < deg_pm (snd (zs ! i))" unfolding \<open>Suc (i - 1) = i\<close> using \<open>is_peak zs i\<close>
        by (rule is_peakD)
      also have "\<dots> = rat (maxdeg_repl_peaks zs)" by fact
      finally show ?thesis .
    qed
    from \<open>is_vpc zs'\<close> have "maxdeg_repl_peaks zs' \<le> maxdeg_repl_peaks zs"
    proof (rule maxdeg_repl_peaks_le)
      fix j
      assume j_in: "j \<in> repl_peaks zs'"
      with sub have "j \<in> insert (Suc i) (insert (i - 1) (repl_peaks zs))" and "j \<noteq> i" by blast+
      thus "deg_pm (snd (zs' ! j)) \<le> rat (maxdeg_repl_peaks zs)"
      proof (elim insertE)
        assume j: "j = Suc i"
        from j_in have "deg_pm (snd (zs' ! j)) < rat (maxdeg_repl_peaks zs)"
          unfolding j by (rule less1)
        thus ?thesis by simp
      next
        assume j: "j = i - 1"
        from j_in have "deg_pm (snd (zs' ! j)) < rat (maxdeg_repl_peaks zs)"
          unfolding j by (rule less2)
        thus ?thesis by simp
      next
        assume j: "j \<in> repl_peaks zs"
        hence "j < length zs" by (rule repl_peaksD)
        hence eq2: "snd (zs' ! j) = snd (zs ! j)" using \<open>j \<noteq> i\<close> by (rule snd_zs')
        from \<open>is_vpc zs\<close> j show ?thesis unfolding eq2 by (rule maxdeg_repl_peaks_max)
      qed
    qed
    hence "maxdeg_repl_peaks zs' < maxdeg_repl_peaks zs \<or> maxdeg_repl_peaks zs' = maxdeg_repl_peaks zs"
      by (simp only: order.order_iff_strict)
    thus ?thesis
    proof
      assume "maxdeg_repl_peaks zs' < maxdeg_repl_peaks zs"
      thus ?thesis ..
    next
      assume eq1: "maxdeg_repl_peaks zs' = maxdeg_repl_peaks zs"
      from sub less1 less2 have "mrepl_peaks zs' \<subseteq> mrepl_peaks zs - {i}"
        by (auto simp: mrepl_peaks_def eq1 snd_zs' dest!: subsetD dest: repl_peaksD)
      moreover from \<open>i \<in> repl_peaks zs\<close> have "i \<in> mrepl_peaks zs" by (simp add: mrepl_peaks_def deg_i)
      ultimately have "mrepl_peaks zs' \<subset> mrepl_peaks zs" by blast
      with finite_mrepl_peaks have "card (mrepl_peaks zs') < card (mrepl_peaks zs)"
        by (rule psubset_card_mono)
      with eq1 show ?thesis by blast
    qed
  qed
  ultimately show ?thesis ..
qed

corollary thm_3_3_25':
  assumes "is_vpc zs"
  obtains zs' where "is_vpc zs'" and "fst (hd zs') = fst (hd zs)" and "snd (last zs') = snd (last zs)"
    and "length zs' = length zs" and "repl_peaks zs' = {}"
proof -
  define A where "A = {zs'. is_vpc zs' \<and> fst (hd zs') = fst (hd zs) \<and> snd (last zs') = snd (last zs) \<and>
                            length zs' = length zs}"
  define m where "m = (LEAST x. x \<in> maxdeg_repl_peaks ` A)"
  from assms have "zs \<in> A" by (simp add: A_def)
  hence "maxdeg_repl_peaks zs \<in> maxdeg_repl_peaks ` A" by (rule imageI)
  hence "m \<in> maxdeg_repl_peaks ` A" unfolding m_def by (rule LeastI)
  then obtain zs0 where "zs0 \<in> A" and m: "m = maxdeg_repl_peaks zs0" ..
  define B where "B = {zs'\<in>A. maxdeg_repl_peaks zs' = m}"
  define c where "c = (LEAST x. x \<in> card ` mrepl_peaks ` B)"
  from \<open>zs0 \<in> A\<close> have "zs0 \<in> B" by (simp add: B_def m)
  hence "card (mrepl_peaks zs0) \<in> card ` mrepl_peaks ` B" by (intro imageI)
  hence "c \<in> card ` mrepl_peaks ` B" unfolding c_def by (rule LeastI)
  then obtain zs' where "zs' \<in> B" and c: "c = card (mrepl_peaks zs')" by blast
  from this(1) have "zs' \<in> A" and m_zs': "maxdeg_repl_peaks zs' = m" by (simp_all add: B_def)
  hence "is_vpc zs'" and hd_zs': "fst (hd zs') = fst (hd zs)"
    and last_zs': "snd (last zs') = snd (last zs)" and len_zs': "length zs' = length zs"
    by (simp_all add: A_def)
  thus ?thesis
  proof
    show "repl_peaks zs' = {}"
    proof (rule ccontr)
      assume "repl_peaks zs' \<noteq> {}"
      with \<open>is_vpc zs'\<close> obtain zs2 where "is_vpc zs2" and "fst (hd zs2) = fst (hd zs')"
        and "snd (last zs2) = snd (last zs')" and "length zs2 = length zs'"
        and disj: "maxdeg_repl_peaks zs2 < maxdeg_repl_peaks zs' \<or>
          (maxdeg_repl_peaks zs2 = maxdeg_repl_peaks zs' \<and> card (mrepl_peaks zs2) < card (mrepl_peaks zs'))"
        by (rule thm_3_3_25)
      from this(1-4) have "zs2 \<in> A" by (simp add: A_def hd_zs' last_zs' len_zs')
      from disj have "maxdeg_repl_peaks zs2 < m \<or> (maxdeg_repl_peaks zs2 = m \<and> card (mrepl_peaks zs2) < c)"
        by (simp only: m_zs' c)
      thus False
      proof (elim disjE conjE)
        from \<open>zs2 \<in> A\<close> have "maxdeg_repl_peaks zs2 \<in> maxdeg_repl_peaks ` A" by (rule imageI)
        hence "m \<le> maxdeg_repl_peaks zs2" unfolding m_def by (rule Least_le)
        also assume "\<dots> < m"
        finally show ?thesis ..
      next
        assume "maxdeg_repl_peaks zs2 = m"
        with \<open>zs2 \<in> A\<close> have "zs2 \<in> B" by (simp add: B_def)
        hence "card (mrepl_peaks zs2) \<in> card ` mrepl_peaks ` B" by (intro imageI)
        hence "c \<le> card (mrepl_peaks zs2)" unfolding c_def by (rule Least_le)
        also assume "\<dots> < c"
        finally show ?thesis ..
      qed
    qed
  qed
qed

lemma lem_3_3_30:
  assumes "f \<in> shifts {f1, f2}" and "f' \<in> shifts {f1, f2}" and "\<not> lcs (fst f) (snd f') \<unlhd> r"
    and "overlap \<unlhd> r + snd f - fst f" and "overlap \<unlhd> r + fst f' - snd f'"
  shows "\<not> overlap \<unlhd> r"
proof
  assume a: "overlap \<unlhd> r"
  have "lcs (fst f) (snd f') \<unlhd> r"
  proof (rule lcs_le_pm)
    from assms(1) have "gcs (fst f) (snd f) \<unlhd> overlap" (is "?g \<unlhd> _")
      by (auto simp: shifts_def overlap_def gcs_comm lcs_ge_pm)
    hence "?g \<unlhd> r" using a by (rule le_pm_trans)
    moreover from \<open>?g \<unlhd> overlap\<close> assms(4) have "?g \<unlhd> r + snd f - fst f" by (rule le_pm_trans)
    ultimately have "?g \<unlhd> gcs r (r + snd f - fst f)" by (rule gcs_ge_pm)
    hence "fst f + ?g \<unlhd> fst f + gcs r (r + snd f - fst f)" by (rule le_pm_mono_plus_left)
    also have "\<dots> = r + ?g" by (simp add: gcs_add_distrib_right add.commute)
    finally have "fst f + ?g - ?g \<unlhd> r + ?g - ?g" by (rule le_pm_mono_minus)
    thus "fst f \<unlhd> r" by simp
  next
    from assms(2) have "gcs (fst f') (snd f') \<unlhd> overlap" (is "?g \<unlhd> _")
      by (auto simp: shifts_def overlap_def gcs_comm lcs_ge_pm)
    hence "?g \<unlhd> r" using a by (rule le_pm_trans)
    moreover from \<open>?g \<unlhd> overlap\<close> assms(5) have "?g \<unlhd> r + fst f' - snd f'" by (rule le_pm_trans)
    ultimately have "?g \<unlhd> gcs r (r + fst f' - snd f')" by (rule gcs_ge_pm)
    hence "snd f' + ?g \<unlhd> snd f' + gcs r (r + fst f' - snd f')" by (rule le_pm_mono_plus_left)
    also have "\<dots> = r + ?g" by (simp add: gcs_add_distrib_right add.commute gcs_comm)
    finally have "snd f' + ?g - ?g \<unlhd> r + ?g - ?g" by (rule le_pm_mono_minus)
    thus "snd f' \<unlhd> r" by simp
  qed
  with assms(3) show False ..
qed

definition coneN :: "'x point \<Rightarrow> 'x point \<Rightarrow> 'x point \<Rightarrow> 'x point set"
  where "coneN h a b = {h + rat l \<cdot> a + rat l' \<cdot> b | l l'. 0 < l \<and> 0 < l'}"

definition coneQ :: "'x point \<Rightarrow> 'x point \<Rightarrow> 'x point \<Rightarrow> 'x point set"
  where "coneQ h a b = {h + l \<cdot> a + l' \<cdot> b | l l'. 0 < l \<and> 0 < l'}"

definition conn :: "'x point \<Rightarrow> 'x point \<Rightarrow> 'x point set"
  where "conn a b = {a + l \<cdot> (b - a) | l. 0 \<le> l \<and> l \<le> 1}"

lemma coneN_I: "p = h + rat l \<cdot> a + rat l' \<cdot> b \<Longrightarrow> 0 < l \<Longrightarrow> 0 < l' \<Longrightarrow> p \<in> coneN h a b"
  by (auto simp: coneN_def)

lemma coneN_E:
  assumes "p \<in> coneN h a b"
  obtains l l' where "0 < l" and "0 < l'" and "p = h + rat l \<cdot> a + rat l' \<cdot> b"
  using assms by (auto simp: coneN_def)

lemma coneQ_I: "p = h + l \<cdot> a + l' \<cdot> b \<Longrightarrow> 0 < l \<Longrightarrow> 0 < l' \<Longrightarrow> p \<in> coneQ h a b"
  by (auto simp: coneQ_def)

lemma coneQ_E:
  assumes "p \<in> coneQ h a b"
  obtains l l' where "0 < l" and "0 < l'" and "p = h + l \<cdot> a + l' \<cdot> b"
  using assms by (auto simp: coneQ_def)

lemma coneN_subset_coneQ: "coneN h a b \<subseteq> coneQ h a b"
  by (auto elim!: coneN_E intro: coneQ_I)

lemma connI: "p = a + l \<cdot> (b - a) \<Longrightarrow> 0 \<le> l \<Longrightarrow> l \<le> 1 \<Longrightarrow> p \<in> conn a b"
  by (auto simp: conn_def)

lemma connE:
  assumes "p \<in> conn a b"
  obtains l where "0 \<le> l" and "l \<le> 1" and "p = a + l \<cdot> (b - a)"
  using assms by (auto simp: conn_def)

lemma conn_geI: "x \<unlhd> a \<Longrightarrow> x \<unlhd> b \<Longrightarrow> p \<in> conn a b \<Longrightarrow> x \<unlhd> p"
  by (auto elim!: connE intro: map_scale_le_interval[of x a 0 "b - a" 1])

lemma conn_deg_leI:
  assumes "p \<in> conn a b"
  shows "deg_pm p \<le> max (deg_pm a) (deg_pm b)"
proof -
  have "0 \<le> l \<Longrightarrow> l \<le> 1 \<Longrightarrow> deg_pm a + l * (deg_pm b - deg_pm a) \<le> max (deg_pm a) (deg_pm b)" for l
    by (metis add.commute add_decreasing2 le_diff_eq max.cobounded1 max.coboundedI2 mult_left_le_one_le
          mult_nonneg_nonpos zero_le_mult_iff zero_le_square)
  with assms show ?thesis by (auto elim!: connE simp: deg_pm_plus deg_pm_map_scale deg_pm_minus)
qed

lemma lem_3_3_33:
  assumes "r \<in> coneQ h a b" and "0 < k" and "0 < k'" and "c = h + k \<cdot> a" and "d = h + k' \<cdot> b"
  obtains L l where "L \<in> conn c d" and "0 < l" and "r = h + l \<cdot> (L - h)"
proof -
  from assms(1) obtain la lb where "0 < la" and "0 < lb" and r: "r = h + la \<cdot> a + lb \<cdot> b"
    by (rule coneQ_E)
  let ?c = "k' * la + k * lb"
  define m where "m = k * lb / ?c"
  let ?L = "c + m \<cdot> (d - c)"
  define l where "l = ?c / (k * k')"
  from assms(2, 3) have "0 < k * k'" by simp
  from assms(2) \<open>0 < lb\<close> have "0 < k * lb" by simp
  moreover from assms(3) \<open>0 < la\<close> have "0 < k' * la" by simp
  ultimately have "0 < ?c" by simp
  with \<open>0 < k * lb\<close> \<open>0 < k' * la\<close> have "0 \<le> m" and "m \<le> 1" by (simp_all add: m_def)
  with refl have "?L \<in> conn c d" by (rule connI)
  moreover from \<open>0 < ?c\<close> \<open>0 < k * k'\<close> have "0 < l" by (simp add: l_def)
  moreover have "r = h + l \<cdot> (?L - h)"
  proof -
    from \<open>0 < ?c\<close> assms(2, 3) have la: "la = (1 - m) * l * k" unfolding l_def m_def
      by (smt add_diff_cancel_right' diff_divide_eq_iff less_irrefl mult.commute mult_numeral_1
            nonzero_eq_divide_eq nonzero_mult_divide_mult_cancel_right numeral_One times_divide_eq_right)
    from \<open>0 < ?c\<close> assms(2, 3) have lb: "lb = m * l * k'" by (simp add: l_def m_def)
    have "la \<cdot> a + lb \<cdot> b = ((1 - m) * l * k) \<cdot> a + (m * l * k') \<cdot> b + (1 - m) \<cdot> h + m \<cdot> h - h"
      by (simp add: map_scale_minus_distrib_right la lb)
    also have "\<dots> = l \<cdot> (?L - h)" by (simp add: assms(4, 5) algebra_simps map_scale_assoc)
    finally show ?thesis by (simp add: r)
  qed
  ultimately show ?thesis ..
qed

lemma thm_3_3_26:
  assumes "min_vpc zs" and "fst (hd zs) \<noteq> snd (last zs)" and "overlap \<unlhd> fst (hd zs)"
    and "overlap \<unlhd> snd (last zs)"
  shows "deg_vpc zs \<le> max (deg_pm (fst (hd zs))) (deg_pm (snd (last zs))) +
                        (\<bar>deg_pm (vect f1)\<bar> + \<bar>deg_pm (vect f2)\<bar>)"
proof -
  from assms(1) have "is_vpc zs" and "min_length_vpc zs" by (rule min_vpcD)+
  from this(1) obtain zs' where "is_vpc zs'" and hd_zs': "fst (hd zs') = fst (hd zs)"
    and last_zs': "snd (last zs') = snd (last zs)" and len_zs': "length zs' = length zs"
    and "repl_peaks zs' = {}" by (rule thm_3_3_25')
  from assms(1) this(1, 2, 3) have "deg_vpc zs \<le> deg_vpc zs'"
    by (rule min_vpc_cases) (simp add: len_zs')
  also have "\<dots> \<le> max (deg_pm (fst (hd zs'))) (deg_pm (snd (last zs'))) +
                        (\<bar>deg_pm (vect f1)\<bar> + \<bar>deg_pm (vect f2)\<bar>)" (is "_ \<le> ?m + (\<bar>?d1\<bar> + \<bar>?d2\<bar>)")
  proof (rule deg_vpc_cases)
    assume "deg_vpc zs' = deg_pm (fst (hd zs'))"
    also have "\<dots> \<le> ?m" by (rule max.cobounded1)
    also have "\<dots> \<le> ?m + (\<bar>?d1\<bar> + \<bar>?d2\<bar>)" by linarith
    finally show ?thesis .
  next
    assume "deg_vpc zs' = deg_pm (snd (last zs'))"
    also have "\<dots> \<le> ?m" by (rule max.cobounded2)
    also have "\<dots> \<le> ?m + (\<bar>?d1\<bar> + \<bar>?d2\<bar>)" by linarith
    finally show ?thesis .
  next
    from \<open>is_vpc zs'\<close> show mlvpc: "min_length_vpc zs'"
    proof (rule min_length_vpcI)
      fix zs0
      assume "is_vpc zs0"
      assume "fst (hd zs0) = fst (hd zs')" and "snd (last zs0) = snd (last zs')"
      hence "fst (hd zs0) = fst (hd zs)" and "snd (last zs0) = snd (last zs)"
        by (simp_all only: hd_zs' last_zs')
      with \<open>min_length_vpc zs\<close> \<open>is_vpc zs0\<close> show "length zs' \<le> length zs0"
        unfolding len_zs' by (rule min_length_vpcD)
    qed
    define A where "A = fst (hd zs')"
    define B where "B = snd (last zs')"
    from assms(2) show 1: "A \<noteq> B" by (simp add: hd_zs' last_zs' A_def B_def)
    from assms(3) show 2: "overlap \<unlhd> A" by (simp add: hd_zs' A_def)
    from assms(4) show 3: "overlap \<unlhd> B" by (simp add: last_zs' B_def)

    fix i
    assume "i < length zs'"
    assume "is_peak zs' i"
    moreover from \<open>is_vpc zs'\<close> this obtain f f' where f_in: "f \<in> shifts {f1, f2}"
      and f'_in: "f' \<in> shifts {f1, f2}" and "f \<noteq> f'" and i_in: "zs' ! i \<in> shifts_of {f}"
      and Si_in: "zs' ! Suc i \<in> shifts_of {f'}"
      and eq0: "snd (zs' ! Suc i) + fst f - snd f = fst (zs' ! i) + snd f' - fst f'"
      and deg_f: "deg_pm (fst f) < deg_pm (snd f)" and deg_f': "deg_pm (snd f') < deg_pm (fst f')"
      and disjnt: "shifts_of {f} \<inter> shifts_of {f'} = {}" by (rule is_peakE)
    moreover have "i \<notin> repl_peaks zs'" by (simp add: \<open>repl_peaks zs' = {}\<close>)
    moreover define R where "R = fst (zs' ! i) + snd f' - fst f'"
    ultimately have a_13: "\<not> lcs (fst f) (snd f') \<unlhd> R" by (simp add: repl_peaks_def)
    from i_in have a_12: "snd (zs' ! i) = R + snd f - fst f + fst f' - snd f'"
      by (simp add: shifts_of_singletonD R_def)
    from \<open>i < length zs'\<close> have "fst (zs' ! i) \<in> set_of_vpc zs'" by (simp add: set_of_vpc_def)
    with mlvpc 1 2 3 have "overlap \<unlhd> fst (zs' ! i)" unfolding A_def B_def by (rule thm_3_3_20)
    hence a_15: "overlap \<unlhd> R + fst f' - snd f'" by (simp add: R_def)
    from \<open>is_peak zs' i\<close> have Si_less: "Suc i < length zs'" by (rule is_peakD)
    hence "snd (zs' ! Suc i) \<in> set_of_vpc zs'" by (simp add: set_of_vpc_def)
    with mlvpc 1 2 3 have "overlap \<unlhd> snd (zs' ! Suc i)" unfolding A_def B_def by (rule thm_3_3_20)
    also have "\<dots> = fst (zs' ! i) + snd f' - fst f' + (snd f - fst f)" by (simp flip: eq0)
    finally have a_14: "overlap \<unlhd> R + snd f - fst f" by (simp add: R_def algebra_simps)

    let ?S = "set zs' \<inter> shifts_of {f}"
    let ?S' = "set zs' \<inter> shifts_of {f'}"
    have "finite ?S" and "finite ?S'" by simp_all
    define k where "k = card ?S"
    define k' where "k' = card ?S'"
    from \<open>i < length zs'\<close> i_in have "zs' ! i \<in> ?S" by simp
    hence "?S \<noteq> {}" by blast
    hence "0 < k" by (simp add: k_def card_gt_0_iff)
    from Si_less have "zs' ! Suc i \<in> ?S'" using Si_in by simp
    hence "?S' \<noteq> {}" by blast
    hence "0 < k'" by (simp add: k'_def card_gt_0_iff)
    from mlvpc 1 2 3 f_in f'_in \<open>f \<noteq> f'\<close> \<open>?S \<noteq> {}\<close> \<open>?S' \<noteq> {}\<close> obtain g g'
      where "{f1, f2} = {g, g'}" and "g \<noteq> g'" and "f \<in> shifts {g}" and "f' \<in> shifts {g'}"
      and zs'_sub: "set zs' \<subseteq> shifts_of {f} \<union> shifts_of {f'}"
      unfolding A_def B_def by (rule vpc_subset_shifts_of)
    from \<open>f \<in> shifts {g}\<close> have "\<bar>deg_pm (snd f - fst f)\<bar> = \<bar>deg_pm (vect g)\<bar>"
      by (auto simp: shifts_def vect_def deg_pm_minus)
    moreover from \<open>f' \<in> shifts {g'}\<close> have "\<bar>deg_pm (snd f' - fst f')\<bar> = \<bar>deg_pm (vect g')\<bar>"
      by (auto simp: shifts_def vect_def deg_pm_minus)
    moreover from \<open>{f1, f2} = {g, g'}\<close> have "(f1 = g \<and> f2 = g') \<or> (f1 = g' \<and> f2 = g)" by fastforce
    ultimately have eq3: "\<bar>deg_pm (snd f - fst f)\<bar> + \<bar>deg_pm (snd f' - fst f')\<bar> = \<bar>?d1\<bar> + \<bar>?d2\<bar>"
      by auto
    from zs'_sub have set_zs': "?S \<union> ?S' = set zs'" by blast
    from disjnt have "?S \<inter> ?S' = {}" by (simp add: ac_simps)
    with \<open>finite ?S\<close> \<open>finite ?S'\<close> have "card (?S \<union> ?S') = k + k'" unfolding k_def k'_def
      by (rule card_Un_disjoint)
    hence "k + k' = card (set zs')" by (simp only: set_zs')
    also from min_length_vpc_distinct(3) have "\<dots> = length zs'" by (rule distinct_card) fact
    finally have "k + k' = length zs'" .
    have eq1: "B = A + rat k \<cdot> (snd f - fst f) + rat k' \<cdot> (snd f' - fst f')"
      unfolding k_def k'_def A_def B_def using mlvpc zs'_sub disjnt by (rule vpc_snd_last_conv_shifts_of)
    define H where "H = A + rat k \<cdot> (snd f - fst f)"
    have H_alt: "H = B - rat k' \<cdot> (snd f' - fst f')" by (simp add: H_def eq1)
    hence a_11: "R \<in> coneN H (fst f - snd f) (snd f' - fst f')"
    proof -
      define l where "l = card (set (take (Suc i) zs') \<inter> shifts_of {f})"
      define l' where "l' = card (set (take (Suc i) zs') \<inter> shifts_of {f'})"
      from set_take_subset[of "Suc i" zs'] have "l \<le> k" by (auto simp: l_def k_def intro!: card_mono)
      have "snd (zs' ! i) = A + rat l \<cdot> (snd f - fst f) + rat l' \<cdot> (snd f' - fst f')"
        unfolding l_def l'_def A_def using mlvpc zs'_sub disjnt \<open>i < length zs'\<close>
        by (rule vpc_snd_nth_conv_shifts_of)
      also have "\<dots> = H + rat l \<cdot> (snd f - fst f) + rat l' \<cdot> (snd f' - fst f') - rat k \<cdot> (snd f - fst f)"
        by (simp add: H_def)
      finally have "snd (zs' ! i) + fst f - snd f + snd f' - fst f' =
                      H + rat (Suc (k - l)) \<cdot> (fst f - snd f) + rat (Suc l') \<cdot> (snd f' - fst f')"
        using \<open>l \<le> k\<close> by (simp add: of_nat_diff algebra_simps)
      hence "R = H + rat (Suc (k - l)) \<cdot> (fst f - snd f) + rat (Suc l') \<cdot> (snd f' - fst f')"
        by (simp add: a_12)
      thus ?thesis by (rule coneN_I) simp_all
    qed
    from f_in f'_in a_13 a_14 a_15 have a_16: "\<not> overlap \<unlhd> R" by (rule lem_3_3_30)

    from \<open>overlap \<unlhd> A\<close> \<open>overlap \<unlhd> B\<close> have a_17: "overlap \<unlhd> l" if "l \<in> conn A B" for l
      using that by (rule conn_geI)
    have a_18: "deg_pm l \<le> max (deg_pm A) (deg_pm B)" if "l \<in> conn A B" for l
      using that by (rule conn_deg_leI)
    from a_11 coneN_subset_coneQ have "R \<in> coneQ H (fst f - snd f) (snd f' - fst f')" ..
    moreover from \<open>0 < k\<close> have "0 < rat k" by simp
    moreover from \<open>0 < k'\<close> have "0 < rat k'" by simp
    moreover have "A = H + rat k \<cdot> (fst f - snd f)" by (simp add: A_def H_def algebra_simps)
    moreover have "B = H + rat k' \<cdot> (snd f' - fst f')" by (simp add: B_def H_alt algebra_simps)
    ultimately obtain L l where L_in: "L \<in> conn A B" and "0 < l" and R: "R = H + l \<cdot> (L - H)"
      by (rule lem_3_3_33)

    have "1 < l"
    proof (rule ccontr)
      assume "\<not> 1 < l"
      note R
      moreover from \<open>0 < l\<close> have "0 \<le> l" by simp
      moreover from \<open>\<not> 1 < l\<close> have "l \<le> 1" by simp
      ultimately have "R \<in> conn H L" by (rule connI)
      have "\<not> overlap \<unlhd> H"
      proof
        assume "overlap \<unlhd> H"
        moreover from L_in have "overlap \<unlhd> L" by (rule a_17)
        ultimately have "overlap \<unlhd> R" using \<open>R \<in> conn H L\<close> by (rule conn_geI)
        with a_16 show False ..
      qed
      let ?L = "conn (R + snd f - fst f) (R + fst f' - snd f')"
      
      have "R \<in> coneQ H (R + snd f - fst f - H) (R + fst f' - snd f' - H)"
      proof -
        from a_11 obtain r r' where "0 < r" and "0 < r'"
          and R_alt: "R = H + rat r \<cdot> (fst f - snd f) + rat r' \<cdot> (snd f' - fst f')" by (rule coneN_E)
        let ?d = "rat r + rat r' - 1"
        let ?r = "rat r / ?d"
        let ?r' = "rat r' / ?d"
        from \<open>0 < r\<close> \<open>0 < r'\<close> have "0 < ?d" by simp
        have "?d \<cdot> R = ?d \<cdot> H + rat r \<cdot> (R + snd f - fst f - H) + rat r' \<cdot> (R + fst f' - snd f' - H)"
          by (simp add: R_alt algebra_simps)
        hence "inverse ?d \<cdot> ?d \<cdot> R =
            inverse ?d \<cdot> (?d \<cdot> H + rat r \<cdot> (R + snd f - fst f - H) + rat r' \<cdot> (R + fst f' - snd f' - H))"
          by simp
        with \<open>0 < ?d\<close> have "R = H + ?r \<cdot> (R + snd f - fst f - H) + ?r' \<cdot> (R + fst f' - snd f' - H)"
          by (simp add: map_scale_assoc map_scale_distrib_left divide_rat_def mult.commute)
        moreover from \<open>0 < r\<close> \<open>0 < ?d\<close> have "0 < ?r" by simp
        moreover from \<open>0 < r'\<close> \<open>0 < ?d\<close> have "0 < ?r'" by simp
        ultimately show ?thesis by (rule coneQ_I)
      qed
      moreover have "0 < (1::rat)" and "0 < (1::rat)" by simp_all
      moreover have "R + snd f - fst f = H + 1 \<cdot> (R + snd f - fst f - H)" by simp
      moreover have "R + fst f' - snd f' = H + 1 \<cdot> (R + fst f' - snd f' - H)" by simp
      ultimately obtain L' l' where "L' \<in> ?L" and "0 < l'" and R_alt: "R = H + l' \<cdot> (L' - H)"
        by (rule lem_3_3_33)
      from a_14 a_15 \<open>L' \<in> ?L\<close> have "overlap \<unlhd> L'" by (rule conn_geI)
      have "l' < 1"
      proof (rule ccontr)
        assume "\<not> l' < 1"
        moreover from a_16 \<open>overlap \<unlhd> L'\<close> have "l' \<noteq> 1" by (intro notI) (simp add: R_alt)
        ultimately have "1 < l'" by simp
        with \<open>l \<le> 1\<close> have "l < l'" by (rule le_less_trans)
        from R_alt have "H + l' \<cdot> (L' - H) = R" by (rule sym)
        also have "\<dots> = H + l \<cdot> (L - H)" by (fact R)
        finally have "(l' - l) \<cdot> H = l' \<cdot> L' - l \<cdot> L" by (simp add: algebra_simps)
        hence "inverse (l' - l) \<cdot> (l' - l) \<cdot> H = inverse (l' - l) \<cdot> (l' \<cdot> L' - l \<cdot> L)" by simp
        with \<open>l < l'\<close> have "H = (l' / (l' - l)) \<cdot> L' - (l / (l' - l)) \<cdot> L"
          by (simp add: map_scale_assoc map_scale_minus_distrib_left divide_rat_def mult.commute)
        also from \<open>l < l'\<close> have "l / (l' - l) = l' / (l' - l) - 1" by (simp add: field_simps)
        finally have H: "H = L + (l' / (l' - l)) \<cdot> (L' - L)" by (simp add: algebra_simps)
        have "R = L + ((1 - l) * l' / (l' - l)) \<cdot> (L' - L)"
          by (simp add: H R map_scale_assoc divide_rat_def algebra_simps)
        moreover from \<open>l < l'\<close> \<open>0 < l'\<close> \<open>l \<le> 1\<close> have "0 \<le> (1 - l) * l' / (l' - l)" by simp
        moreover from \<open>0 < l\<close> \<open>1 < l'\<close> \<open>l < l'\<close> have "(1 - l) * l' / (l' - l) \<le> 1"
          by (simp add: algebra_simps)
        ultimately have "R \<in> conn L L'" by (rule connI)
        with a_17 \<open>overlap \<unlhd> L'\<close> have "overlap \<unlhd> R" by (rule conn_geI) fact
        with a_16 show False ..
      qed

      from \<open>L' \<in> ?L\<close> obtain m where "0 \<le> m" and "m \<le> 1"
        and "L' = (R + snd f - fst f) + m \<cdot> ((R + fst f' - snd f') - (R + snd f - fst f))" by (rule connE)
      from this(3) have L': "L' = R + snd f - fst f + m \<cdot> (fst f - snd f + fst f' - snd f')"
        by (simp add: algebra_simps)
      note R_alt
      also have "l' \<cdot> (L' - H) = l' \<cdot> R + (- l' * (1 - m)) \<cdot> (fst f - snd f) +
                                (- l' * m) \<cdot> (snd f' - fst f') - l' \<cdot> H"
        by (simp add: L' map_scale_assoc map_scale_uminus_left algebra_simps)
      finally have "(1 - l') \<cdot> R = (1 - l') \<cdot> H + (- l' * (1 - m)) \<cdot> (fst f - snd f) +
                                (- l' * m) \<cdot> (snd f' - fst f')" by (simp add: algebra_simps)
      hence "inverse (1 - l') \<cdot> (1 - l') \<cdot> R = inverse (1 - l') \<cdot> ((1 - l') \<cdot> H +
                                  (- l' * (1 - m)) \<cdot> (fst f - snd f) + (- l' * m) \<cdot> (snd f' - fst f'))"
        by simp
      with \<open>l' < 1\<close> have R_1: "R = H + (- l' * (1 - m) / (1 - l')) \<cdot> (fst f - snd f) +
                                    (- l' * m / (1 - l')) \<cdot> (snd f' - fst f')"
        by (simp add: map_scale_assoc map_scale_distrib_left divide_rat_def mult.commute)
      from \<open>0 < l'\<close> \<open>m \<le> 1\<close> \<open>l' < 1\<close> have "- l' * (1 - m) / (1 - l') \<le> 0" (is "?j \<le> _") by simp
      from \<open>0 < l'\<close> \<open>0 \<le> m\<close> \<open>l' < 1\<close> have "- l' * m / (1 - l') \<le> 0" (is "?j' \<le> _") by simp
      from a_11 obtain j j' where "0 < j" and "0 < j'"
        and "R = H + rat j \<cdot> (fst f - snd f) + rat j' \<cdot> (snd f' - fst f')" by (rule coneN_E)
      from this(3) have "rat j \<cdot> (fst f - snd f) + rat j' \<cdot> (snd f' - fst f') =
                          ?j \<cdot> (fst f - snd f) + ?j' \<cdot> (snd f' - fst f')"
        by (simp add: R_1)
      hence "(?j' - rat j') \<cdot> (snd f' - fst f') = (?j - rat j) \<cdot> (snd f - fst f)"
        by (simp add: algebra_simps)
      hence "inverse (?j' - rat j') \<cdot> ((?j' - rat j') \<cdot> (snd f' - fst f')) =
              inverse (?j' - rat j') \<cdot> ((?j - rat j) \<cdot> (snd f - fst f))" by (rule arg_cong)
      moreover from \<open>?j' \<le> 0\<close> \<open>0 < j'\<close> have "?j' - rat j' < 0" by simp
      moreover define q where "q = (?j - rat j) / (?j' - rat j')"
      ultimately have eq2: "snd f' - fst f' = q \<cdot> (snd f - fst f)"
        by (simp add: map_scale_assoc divide_rat_def mult.commute)
      from \<open>0 < j\<close> \<open>?j \<le> 0\<close> have "?j - rat j < 0" by simp
      hence "0 < q" unfolding q_def using \<open>?j' - rat j' < 0\<close> by (rule divide_neg_neg)
      with deg_f have "0 < deg_pm (q \<cdot> (snd f - fst f))" by (simp add: deg_pm_map_scale deg_pm_minus)
      also have "\<dots> = deg_pm (snd f' - fst f')" by (simp only: eq2)
      also from deg_f' have "\<dots> < 0" by (simp only: deg_pm_minus_group)
      finally show False .
    qed

    from L_in have a_19: "deg_pm L \<le> max (deg_pm A) (deg_pm B)" by (rule a_18)
    also have "\<dots> \<le> deg_pm H"
    proof (rule max.boundedI)
      from deg_f show "deg_pm A \<le> deg_pm H"
        by (simp add: H_def deg_pm_plus deg_pm_map_scale deg_pm_minus)
    next
      from deg_f' show "deg_pm B \<le> deg_pm H"
        by (simp add: H_alt deg_pm_plus deg_pm_map_scale deg_pm_minus mult_le_0_iff)
    qed
    finally have "deg_pm (L - H) \<le> 0" by (simp add: deg_pm_minus)
    have "deg_pm R = deg_pm H + l * deg_pm (L - H)" by (simp only: R deg_pm_plus deg_pm_map_scale)
    also from \<open>deg_pm (L - H) \<le> 0\<close> \<open>1 < l\<close> have "\<dots> \<le> deg_pm H + deg_pm (L - H)"
      by (metis add_diff_cancel_left diff_gt_0_iff_gt left_diff_distrib mult.left_neutral not_le
              zero_less_mult_pos)
    also have "\<dots> = deg_pm L" by (simp add: deg_pm_minus)
    also from a_19 have "\<dots> \<le> ?m" by (simp only: A_def B_def)
    finally have "deg_pm R \<le> ?m" .

    assume "deg_vpc zs' = deg_pm (snd (zs' ! i))"
    also have "\<dots> = deg_pm R + (deg_pm (snd f - fst f) - deg_pm (snd f' - fst f'))"
      by (simp add: a_12 deg_pm_plus deg_pm_minus)
    also from \<open>deg_pm R \<le> ?m\<close> have "\<dots> \<le> ?m + (\<bar>deg_pm (snd f - fst f)\<bar> + \<bar>deg_pm (snd f' - fst f')\<bar>)"
      by linarith
    also have "\<dots> = ?m + (\<bar>?d1\<bar> + \<bar>?d2\<bar>)" by (simp only: eq3)
    finally show ?thesis .
  qed
  finally show ?thesis by (simp only: hd_zs' last_zs')
qed

end

end (* two_polys *)

end (* theory *)
