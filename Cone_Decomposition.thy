section \<open>Cone Decompositions\<close>

theory Cone_Decomposition
  imports MPoly_PM
begin

subsection \<open>Preliminaries\<close>
  
lemma plus_minus_assoc_pm_nat_1: "s + t - u = (s - (u - t)) + (t - (u::_ \<Rightarrow>\<^sub>0 nat))"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_minus)

lemma plus_minus_assoc_pm_nat_2:
  "s + (t - u) = (s + (truncate_poly_mapping (keys s) (u - t))) + t - (u::_ \<Rightarrow>\<^sub>0 nat)"
proof (rule poly_mapping_eqI)
  fix x
  show "lookup (s + (t - u)) x = lookup (s + truncate_poly_mapping (keys s) (u - t) + t - u) x"
  proof (cases "x \<in> keys s")
    case True
    thus ?thesis
      by (simp add: plus_minus_assoc_pm_nat_1 lookup_truncate_fun truncate_fun_def lookup_add lookup_minus)
  next
    case False
    hence "lookup s x = 0" by simp
    with False show ?thesis
      by (simp add: lookup_add lookup_minus lookup_truncate_fun truncate_fun_def del: not_in_keys_iff_lookup_eq_zero)
  qed
qed

lemma deg_pm_mono: "s adds t \<Longrightarrow> deg_pm s \<le> deg_pm (t::_ \<Rightarrow>\<^sub>0 _::add_linorder_min)"
  unfolding adds_poly_mapping by (transfer) (auto intro!: deg_fun_leq simp: supp_fun_def)

lemma deg_pm_minus:
  assumes "s adds (t::_ \<Rightarrow>\<^sub>0 _::comm_monoid_add)"
  shows "deg_pm (t - s) = deg_pm t - deg_pm s"
proof -
  from assms have "(t - s) + s = t" by (rule adds_minus)
  hence "deg_pm t = deg_pm ((t - s) + s)" by simp
  also have "\<dots> = deg_pm (t - s) + deg_pm s" by (simp only: deg_pm_plus)
  finally show ?thesis by simp
qed

lemma deg_pm_minus_le: "deg_pm (t - s) \<le> deg_pm (t::_ \<Rightarrow>\<^sub>0 nat)"
proof -
  have "keys (t - s) \<subseteq> keys t" by (rule, simp add: lookup_minus in_keys_iff)
  hence "deg_pm (t - s) = (\<Sum>x\<in>keys t. lookup (t - s) x)" using finite_keys by (rule deg_pm_superset)
  also have "\<dots> \<le> (\<Sum>x\<in>keys t. lookup t x)" by (rule sum_mono) (simp add: lookup_minus)
  also have "\<dots> = deg_pm t" by (rule sym, rule deg_pm_superset, fact subset_refl, fact finite_keys)
  finally show ?thesis .
qed

lemma minus_id_iff: "t - s = t \<longleftrightarrow> keys t \<inter> keys (s::_ \<Rightarrow>\<^sub>0 nat) = {}"
proof
  assume "t - s = t"
  {
    fix x
    assume "x \<in> keys t" and "x \<in> keys s"
    hence "0 < lookup t x" and "0 < lookup s x" by (simp_all add: in_keys_iff)
    hence "lookup (t - s) x \<noteq> lookup t x" by (simp add: lookup_minus)
    with \<open>t - s = t\<close> have False by simp
  }
  thus "keys t \<inter> keys s = {}" by blast
next
  assume *: "keys t \<inter> keys s = {}"
  show "t - s = t"
  proof (rule poly_mapping_eqI)
    fix x
    have "lookup t x - lookup s x = lookup t x"
    proof (cases "x \<in> keys t")
      case True
      with * have "x \<notin> keys s" by blast
      thus ?thesis by simp
    next
      case False
      thus ?thesis by simp
    qed
    thus "lookup (t - s) x = lookup t x" by (simp only: lookup_minus)
  qed
qed

lemma deg_pm_minus_id_iff: "deg_pm (t - s) = deg_pm t \<longleftrightarrow> keys t \<inter> keys (s::_ \<Rightarrow>\<^sub>0 nat) = {}"
proof
  assume eq: "deg_pm (t - s) = deg_pm t"
  {
    fix x
    assume "x \<in> keys t" and "x \<in> keys s"
    hence "0 < lookup t x" and "0 < lookup s x" by (simp_all add: in_keys_iff)
    hence *: "lookup (t - s) x < lookup t x" by (simp add: lookup_minus)
    have "keys (t - s) \<subseteq> keys t" by (rule, simp add: lookup_minus in_keys_iff)
    hence "deg_pm (t - s) = (\<Sum>x\<in>keys t. lookup (t - s) x)" using finite_keys by (rule deg_pm_superset)
    also from finite_keys have "\<dots> < (\<Sum>x\<in>keys t. lookup t x)"
    proof (rule sum_strict_mono_ex1)
      show "\<forall>x\<in>keys t. lookup (t - s) x \<le> lookup t x" by (simp add: lookup_minus)
    next
      from \<open>x \<in> keys t\<close> * show "\<exists>x\<in>keys t. lookup (t - s) x < lookup t x" ..
    qed
    also have "\<dots> = deg_pm t" by (rule sym, rule deg_pm_superset, fact subset_refl, fact finite_keys)
    finally have False by (simp add: eq)
  }
  thus "keys t \<inter> keys s = {}" by blast
next
  assume "keys t \<inter> keys s = {}"
  hence "t - s = t" by (simp only: minus_id_iff)
  thus "deg_pm (t - s) = deg_pm t" by (simp only:)
qed

subsubsection \<open>Direct Decompositions\<close>

definition direct_decomposition :: "'a set \<Rightarrow> 'a::comm_monoid_add set set \<Rightarrow> bool"
  where "direct_decomposition A Q \<longleftrightarrow>
          (\<forall>a\<in>A. \<exists>P f. finite P \<and> P \<subseteq> Q \<and> (\<forall>p\<in>P. f p \<in> p \<and> f p \<noteq> 0) \<and> a = sum f P \<and>
            (\<forall>P' f'. finite P' \<longrightarrow> P' \<subseteq> Q \<longrightarrow> (\<forall>p\<in>P'. f' p \<in> p \<and> f' p \<noteq> 0) \<longrightarrow> a = sum f' P' \<longrightarrow>
              (P' = P \<and> (\<forall>p\<in>P. f' p = f p))))"

subsection \<open>Basic Cone Decompositions\<close>

definition Hilbert_fun :: "('x::countable \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> nat \<Rightarrow> nat"
  where "Hilbert_fun T d = card {t \<in> T. deg_pm t = d}"

definition cone :: "('x::countable \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) set"
  where "cone t U = (\<lambda>s. s + t) ` .[U]"

lemma coneI: "v = s + t \<Longrightarrow> s \<in> .[U] \<Longrightarrow> v \<in> cone t U"
  by (auto simp: cone_def)

lemma coneE:
  assumes "v \<in> cone t U"
  obtains s where "s \<in> .[U]" and "v = s + t"
  using assms by (auto simp: cone_def)

lemma cone_empty [simp]: "cone t {} = {t}"
  by (simp add: cone_def)

lemma cone_zero [simp]: "cone 0 U = .[U]"
  by (simp add: cone_def)

lemma zero_in_cone_iff: "0 \<in> cone t U \<longleftrightarrow> t = 0"
proof
  assume "0 \<in> cone t U"
  then obtain s where "0 = s + t" by (rule coneE)
  thus "t = 0" using plus_eq_zero_2 by auto
qed (simp add: zero_in_PPs)

lemma tip_in_cone: "t \<in> cone t U"
  using _ zero_in_PPs by (rule coneI) simp

lemma cone_mono_1:
  assumes "s \<in> .[U]"
  shows "cone (s + t) U \<subseteq> cone t U"
proof
  fix v
  assume "v \<in> cone (s + t) U"
  then obtain s' where "s' \<in> .[U]" and "v = s' + (s + t)" by (rule coneE)
  from this(2) have "v = s' + s + t" by (simp only: add.assoc)
  moreover from \<open>s' \<in> .[U]\<close> assms have "s' + s \<in> .[U]" by (rule PPs_closed_plus)
  ultimately show "v \<in> cone t U" by (rule coneI)
qed

lemma cone_mono_1':
  assumes "t adds s" and "s \<in> .[U]"
  shows "cone s U \<subseteq> cone t U"
proof -
  from assms(1) obtain s' where s: "s = s' + t" unfolding add.commute[of _ t] ..
  with assms(2) have "s' + t \<in> .[U]" by simp
  hence "s' + t - t \<in> .[U]" by (rule PPs_closed_minus)
  hence "s' \<in> .[U]" by simp
  thus ?thesis unfolding s by (rule cone_mono_1)
qed

lemma cone_mono_2:
  assumes "U1 \<subseteq> U2"
  shows "cone t U1 \<subseteq> cone t U2"
proof
  from assms have ".[U1] \<subseteq> .[U2]" by (rule PPs_mono)
  fix v
  assume "v \<in> cone t U1"
  then obtain s where "s \<in> .[U1]" and "v = s + t" by (rule coneE)
  note this(2)
  moreover from \<open>s \<in> .[U1]\<close> \<open>.[U1] \<subseteq> .[U2]\<close> have "s \<in> .[U2]" ..
  ultimately show "v \<in> cone t U2" by (rule coneI)
qed

lemma cone_subsetD:
  assumes "cone t1 U1 \<subseteq> cone t2 U2"
  shows "t2 adds t1" and "U1 \<subseteq> U2"
proof -
  from tip_in_cone assms have "t1 \<in> cone t2 U2" ..
  then obtain t1' where "t1' \<in> .[U2]" and t1: "t1 = t1' + t2" by (rule coneE)
  from this(2) have "t1 = t2 + t1'" by (simp only: add.commute)
  thus "t2 adds t1" ..
  show "U1 \<subseteq> U2"
  proof
    fix x
    assume "x \<in> U1"
    hence "Poly_Mapping.single x 1 \<in> .[U1]" (is "?s \<in> _") by (rule PPs_closed_single)
    with refl have "?s + t1 \<in> cone t1 U1" by (rule coneI)
    hence "?s + t1 \<in> cone t2 U2" using assms ..
    then obtain s where "s \<in> .[U2]" and "?s + t1 = s + t2" by (rule coneE)
    from this(2) have "(?s + t1') + t2 = s + t2" by (simp only: t1 ac_simps)
    hence "?s + t1' = s" by simp
    with \<open>s \<in> .[U2]\<close> have "?s + t1' \<in> .[U2]" by simp
    hence "?s + t1' - t1' \<in> .[U2]" by (rule PPs_closed_minus)
    hence "?s \<in> .[U2]" by simp
    thus "x \<in> U2" by (simp add: PPs_def)
  qed
qed

lemma cone_insert:
  "cone t (insert x U) = cone t U \<union> cone (Poly_Mapping.single x 1 + t) (insert x U)" (is "?A = ?B \<union> ?C")
proof (rule Set.set_eqI)
  fix v
  show "v \<in> ?A \<longleftrightarrow> (v \<in> ?B \<union> ?C)"
  proof
    assume "v \<in> ?A"
    then obtain s where "s \<in> .[insert x U]" and v: "v = s + t" by (rule coneE)
    from this(1) obtain e s' where "s' \<in> .[U]" and s: "s = Poly_Mapping.single x e + s'"
      by (rule PPs_insertE)
    show "v \<in> ?B \<union> ?C"
    proof (cases "e = 0")
      case True
      hence "v = s' + t" by (simp add: v s)
      hence "v \<in> ?B" using \<open>s' \<in> .[U]\<close> by (rule coneI)
      thus ?thesis ..
    next
      case False
      then obtain e' where "e = Suc e'" using not0_implies_Suc by blast
      hence "v = (Poly_Mapping.single x e' + s') + (Poly_Mapping.single x 1 + t)"
        by (simp add: v s ac_simps single_add[symmetric])
      moreover have "Poly_Mapping.single x e' + s' \<in> .[insert x U]"
      proof (rule PPs_closed_plus)
        from insertI1 show "Poly_Mapping.single x e' \<in> .[insert x U]" by (rule PPs_closed_single)
      next
        from subset_insertI have ".[U] \<subseteq> .[insert x U]" by (rule PPs_mono)
        with \<open>s' \<in> .[U]\<close> show "s' \<in> .[insert x U]" ..
      qed
      ultimately have "v \<in> ?C" by (rule coneI)
      thus ?thesis ..
    qed
  next
    assume "v \<in> ?B \<union> ?C"
    thus "v \<in> ?A"
    proof
      assume "v \<in> ?B"
      also from subset_insertI have "... \<subseteq> ?A" by (rule cone_mono_2)
      finally show ?thesis .
    next
      assume "v \<in> ?C"
      also have "... \<subseteq> ?A" by (intro cone_mono_1 PPs_closed_single insertI1)
      finally show ?thesis .
    qed
  qed
qed

lemma cone_insert_disjoint:
  assumes "x \<notin> U"
  shows "cone t U \<inter> cone (Poly_Mapping.single x 1 + t) (insert x U) = {}"
proof -
  {
    fix v
    assume "v \<in> cone t U"
    then obtain s1 where "s1 \<in> .[U]" and s1: "v = s1 + t" by (rule coneE)
    from this(1) have "keys s1 \<subseteq> U" by (rule PPsD)
    with assms have "x \<notin> keys s1" by blast
    hence "lookup v x = lookup t x" by (simp add: s1 lookup_add)
    assume "v \<in> cone (Poly_Mapping.single x 1 + t) (insert x U)"
    then obtain s2 where "v = s2 + (Poly_Mapping.single x 1 + t)" by (rule coneE)
    hence "lookup v x = lookup s2 x + Suc (lookup t x)" by (simp add: lookup_add)
    also have "lookup t x < ..." by simp
    finally have "lookup v x \<noteq> lookup t x" by simp
    hence False using \<open>lookup v x = lookup t x\<close> ..
  }
  thus ?thesis by blast
qed

lemma cone_indets:
  assumes "cone t U \<subseteq> .[X]"
  shows "t \<in> .[X]" and "U \<subseteq> X"
proof -
  from tip_in_cone assms show "t \<in> .[X]" ..
  show "U \<subseteq> X"
  proof
    fix x
    assume "x \<in> U"
    hence "Poly_Mapping.single x 1 \<in> .[U]"by (rule PPs_closed_single)
    with refl have "Poly_Mapping.single x 1 + t \<in> cone t U" by (rule coneI)
    hence "Poly_Mapping.single x 1 + t \<in> .[X]" using assms ..
    hence "(Poly_Mapping.single x 1 + t) - t \<in> .[X]" by (rule PPs_closed_minus)
    hence "Poly_Mapping.single x 1 \<in> .[X]" by simp
    hence "keys (Poly_Mapping.single x (1::nat)) \<subseteq> X" by (rule PPsD)
    thus "x \<in> X" by simp
  qed
qed

lemma PPs_Int_cone: ".[X] \<inter> cone t U = (if t \<in> .[X] then cone t (X \<inter> U) else {})"
proof (cases "t \<in> .[X]")
  case True
  have ".[X] \<inter> cone t U = cone t (X \<inter> U)"
  proof (rule Set.set_eqI)
    fix s
    show "s \<in> .[X] \<inter> cone t U \<longleftrightarrow> s \<in> cone t (X \<inter> U)"
    proof
      assume "s \<in> .[X] \<inter> cone t U"
      hence "s \<in> .[X]" and "s \<in> cone t U" by simp_all
      from this(2) obtain s' where "s' \<in> .[U]" and s: "s = s' + t" by (rule coneE)
      from \<open>s \<in> .[X]\<close> have "s' + t \<in> .[X]" by (simp only: s)
      hence "s' + t - t \<in> .[X]" by (rule PPs_closed_minus)
      hence "keys s' \<subseteq> X" by (simp add: PPs_def)
      moreover from \<open>s' \<in> .[U]\<close> have "keys s' \<subseteq> U" by (rule PPsD)
      ultimately have "keys s' \<subseteq> X \<inter> U" by blast
      hence "s' \<in> .[X \<inter> U]" by (rule PPsI)
      with s show "s \<in> cone t (X \<inter> U)" by (rule coneI)
    next
      assume "s \<in> cone t (X \<inter> U)"
      then obtain s' where "s' \<in> .[X \<inter> U]" and s: "s = s' + t" by (rule coneE)
      from this(1) have "s' \<in> .[X]" and "s' \<in> .[U]" by (simp_all add: PPs_def)
      from this(1) True have "s \<in> .[X]" unfolding s by (rule PPs_closed_plus)
      moreover from s \<open>s' \<in> .[U]\<close> have "s \<in> cone t U" by (rule coneI)
      ultimately show "s \<in> .[X] \<inter> cone t U" ..
    qed
  qed
  with True show ?thesis by simp
next
  case False
  {
    fix s
    assume "s \<in> cone t U"
    then obtain s' where "s = s' + t" by (rule coneE)
    moreover assume "s \<in> .[X]"
    ultimately have "s' + t \<in> .[X]" by simp
    hence "(s' + t) - s' \<in> .[X]" by (rule PPs_closed_minus)
    hence "t \<in> .[X]" by simp
    with False have False ..
  }
  hence ".[X] \<inter> cone t U = {}" by blast
  with False show ?thesis by simp
qed

lemma image_plus_cone: "(+) s ` cone t U = cone (s + t) U"
  by (auto simp: cone_def ac_simps image_image)

lemma image_minus_cone: "(\<lambda>s. s - v) ` cone t U = cone (t - v) U"
proof (rule Set.set_eqI)
  fix u
  show "u \<in> (\<lambda>s. s - v) ` cone t U \<longleftrightarrow> u \<in> cone (t - v) U"
  proof
    assume "u \<in> (\<lambda>s. s - v) ` cone t U"
    then obtain s where "s \<in> cone t U" and u: "u = s - v" ..
    from this(1) obtain s' where "s' \<in> .[U]" and s: "s = s' + t" by (rule coneE)
    show "u \<in> cone (t - v) U"
    proof (rule coneI)
      show "u = s' - (v - t) + (t - v)" by (simp add: u s plus_minus_assoc_pm_nat_1)
    next
      from \<open>s' \<in> .[U]\<close> show "s' - (v - t) \<in> .[U]" by (rule PPs_closed_minus)
    qed
  next
    assume "u \<in> cone (t - v) U"
    then obtain s' where "s' \<in> .[U]" and u: "u = s' + (t - v)" by (rule coneE)
    from this(2) have "u = (s' + (v - t)) + t - v" by (simp add: plus_minus_assoc_pm_nat_1)
    have "u = (s' + (truncate_poly_mapping (keys s') (v - t))) + t - v"
      unfolding u by (fact plus_minus_assoc_pm_nat_2)
    moreover from refl have "(s' + (truncate_poly_mapping (keys s') (v - t))) + t \<in> cone t U"
    proof (rule coneI)
      from sub_keys_truncate[of "keys s'" "v - t"]
      have "keys (truncate_poly_mapping (keys s') (v - t)) \<subseteq> keys s'" by (simp only: sub_keys_def)
      also from \<open>s' \<in> .[U]\<close> have "\<dots> \<subseteq> U" by (rule PPsD)
      finally have "truncate_poly_mapping (keys s') (v - t) \<in> .[U]" by (rule PPsI)
      with \<open>s' \<in> .[U]\<close> show "s' + truncate_poly_mapping (keys s') (v - t) \<in> .[U]"
        by (rule PPs_closed_plus)
    qed
    ultimately show "u \<in> (\<lambda>s. s - v) ` cone t U" by (rule image_eqI)
  qed
qed

lemma inj_on_minus_cone:
  assumes "A \<subseteq> cone t U"
  shows "inj_on (\<lambda>s. s - t) A"
proof
  fix v1 v2
  assume "v1 \<in> A"
  hence "v1 \<in> cone t U" using assms ..
  then obtain s1 where v1: "v1 = s1 + t" by (rule coneE)
  assume "v2 \<in> A"
  hence "v2 \<in> cone t U" using assms ..
  then obtain s2 where v2: "v2 = s2 + t" by (rule coneE)
  assume "v1 - t = v2 - t"
  thus "v1 = v2" by (simp add: v1 v2)
qed

lemma image_minus_tip_cone: "(\<lambda>s. s - t) ` cone t U = .[U]"
  by (auto simp: cone_def image_comp)

lemma image_minus_tip_cone_deg_sect:
  "(\<lambda>s. s - t) ` {v \<in> cone t U. deg_pm v = deg_pm t + d} = deg_sect U d"
proof
  show "deg_sect U d \<subseteq> (\<lambda>s. s - t) ` {v \<in> cone t U. deg_pm v = deg_pm t + d}" (is "_ \<subseteq> _ ` ?A")
  proof
    fix s
    assume "s \<in> deg_sect U d"
    hence "s \<in> .[U]" and "deg_pm s = d" by (rule deg_sectD)+
    from refl this(1) have "s + t \<in> cone t U" by (rule coneI)
    moreover have "deg_pm (s + t) = deg_pm t + d" by (simp add: \<open>deg_pm s = d\<close> deg_pm_plus)
    ultimately have "s + t \<in> ?A" by simp
    moreover have "s = s + t - t" by simp
    ultimately show "s \<in> (\<lambda>s. s - t) ` ?A" by (rule rev_image_eqI)
  qed
qed (auto simp: cone_def deg_pm_plus deg_sect_def)

lemma image_minus_tip_cone_deg_le_sect:
  "(\<lambda>s. s - t) ` {v \<in> cone t U. deg_pm v \<le> deg_pm t + d} = deg_le_sect U d"
proof
  show "deg_le_sect U d \<subseteq> (\<lambda>s. s - t) ` {v \<in> cone t U. deg_pm v \<le> deg_pm t + d}" (is "_ \<subseteq> _ ` ?A")
  proof
    fix s
    assume "s \<in> deg_le_sect U d"
    hence "s \<in> .[U]" and "deg_pm s \<le> d" by (rule deg_le_sectD)+
    from refl this(1) have "s + t \<in> cone t U" by (rule coneI)
    moreover have "deg_pm (s + t) \<le> deg_pm t + d" by (simp add: \<open>deg_pm s \<le> d\<close> deg_pm_plus)
    ultimately have "s + t \<in> ?A" by simp
    moreover have "s = s + t - t" by simp
    ultimately show "s \<in> (\<lambda>s. s - t) ` ?A" by (rule rev_image_eqI)
  qed
qed (auto simp: cone_def deg_pm_plus deg_le_sect_alt)

lemma cone_deg_empty:
  assumes "z < deg_pm t"
  shows "{v \<in> cone t U. deg_pm v = z} = {}"
proof -
  {
    fix v
    assume "v \<in> cone t U"
    then obtain s where "v = s + t" by (rule coneE)
    hence "deg_pm v = deg_pm s + deg_pm t" by (simp add: deg_pm_plus)
    also have "deg_pm t \<le> ..." by simp
    finally have "deg_pm t \<le> deg_pm v" .
    with \<open>z < deg_pm t\<close> have "z < deg_pm v" by (rule less_le_trans)
    moreover assume "deg_pm v = z"
    ultimately have False by simp
  }
  thus ?thesis by blast
qed

lemma finite_cone_deg:
  assumes "finite U"
  shows "finite {v \<in> cone t U. deg_pm v = z}"
proof (cases "deg_pm t \<le> z")
  case True
  then obtain d where z: "z = deg_pm t + d" using le_imp_add by blast
  from assms have "finite (deg_sect U d)" by (rule finite_deg_sect)
  hence "finite ((\<lambda>s. s - t) ` {v \<in> cone t U. deg_pm v = z})"
    by (simp only: z image_minus_tip_cone_deg_sect)
  moreover have "inj_on (\<lambda>s. s - t) {v \<in> cone t U. deg_pm v = z}"
    by (rule inj_on_minus_cone) blast
  ultimately show ?thesis by (rule finite_imageD)
next
  case False
  hence "z < deg_pm t" by simp
  hence "{v \<in> cone t U. deg_pm v = z} = {}" by (rule cone_deg_empty)
  also have "finite ..." ..
  finally show ?thesis .
qed

lemma Hilbert_fun_cone:
  assumes "finite U" and "U \<noteq> ({}::'x::countable set)"
  shows "Hilbert_fun (cone t U) z =
          (if deg_pm t \<le> z then ((z - deg_pm t) + (card U - 1)) choose (card U - 1) else 0)"
proof (cases "deg_pm t \<le> z")
  case True
  then obtain d where z: "z = deg_pm t + d" using le_imp_add by blast
  have "Hilbert_fun (cone t U) z = card {v \<in> cone t U. deg_pm v = z}"
    by (simp only: Hilbert_fun_def)
  also have "... = card ((\<lambda>s. s - t) ` {v \<in> cone t U. deg_pm v = z})"
  proof (rule sym, rule card_image, rule inj_on_minus_cone)
    show "{v \<in> cone t U. deg_pm v = z} \<subseteq> cone t U" by blast
  qed
  also have "... = card (deg_sect U d)" by (simp only: z image_minus_tip_cone_deg_sect)
  also from assms have "... = (d + (card U - 1)) choose (card U - 1)" by (rule card_deg_sect)
  finally show ?thesis by (simp add: True z)
next
  case False
  hence "z < deg_pm t" by simp
  hence "{v \<in> cone t U. deg_pm v = z} = {}" by (rule cone_deg_empty)
  hence "card {v \<in> cone t U. deg_pm v = z} = card ({}::('x \<Rightarrow>\<^sub>0 nat) set)" by (rule arg_cong)
  with False show ?thesis by (simp add: Hilbert_fun_def)
qed

definition finite_decomp :: "(('x::countable \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> bool"
  where "finite_decomp P \<longleftrightarrow> (finite P \<and> (\<forall>(t, U)\<in>P. finite U))"

definition cone_decomp :: "('x::countable \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> bool"
  where "cone_decomp T P \<longleftrightarrow>
              (finite P \<and> T = (\<Union>(t, U)\<in>P. cone t U) \<and>
                (\<forall>(t1, U1)\<in>P. \<forall>(t2, U2)\<in>P. (t1, U1) \<noteq> (t2, U2) \<longrightarrow> cone t1 U1 \<inter> cone t2 U2 = {}))"

text \<open>The above definition of cone decomposition for power-products yields a cone decomposition for
  polynomials. Namely, for proving that the decomposition is direct, simply take the largest power-product
  \<open>t\<close> appearing in the given polynomial and subtract the unique polynomial in the cone decomposition
  whose leading power-product equals \<open>t\<close>. Apply this procedure repeatedly, until \<open>0\<close> is reached.\<close>

lemma finite_decompI: "finite P \<Longrightarrow> (\<And>t U. (t, U) \<in> P \<Longrightarrow> finite U) \<Longrightarrow> finite_decomp P"
  unfolding finite_decomp_def by blast

lemma finite_decompD:
  assumes "finite_decomp P"
  shows "finite P" and "\<And>t U. (t, U) \<in> P \<Longrightarrow> finite U"
  using assms unfolding finite_decomp_def by blast+

lemma finite_decomp_empty: "finite_decomp {}"
  by (simp add: finite_decomp_def)

lemma finite_decomp_Un: "finite_decomp P \<Longrightarrow> finite_decomp Q \<Longrightarrow> finite_decomp (P \<union> Q)"
  by (auto intro: finite_decompI dest: finite_decompD)

lemma finite_decomp_UN: "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> finite_decomp (f a)) \<Longrightarrow> finite_decomp (\<Union> (f ` A))"
  by (auto intro: finite_decompI dest: finite_decompD)

corollary finite_decomp_UN_prod:
  "finite P \<Longrightarrow> (\<And>t U. (t, U) \<in> P \<Longrightarrow> finite_decomp (f t U)) \<Longrightarrow> finite_decomp (\<Union>(t, U)\<in>P. f t U)"
  by (metis (mono_tags) case_prod_conv finite_decomp_UN prod.exhaust)

lemma cone_decompI:
  assumes "finite P" and "T = (\<Union>(t, U)\<in>P. cone t U)"
    and "\<And>t1 t2 U1 U2 s. (t1, U1) \<in> P \<Longrightarrow> (t2, U2) \<in> P \<Longrightarrow> s \<in> cone t1 U1 \<Longrightarrow> s \<in> cone t2 U2 \<Longrightarrow>
            (t1, U1) = (t2, U2)"
  shows "cone_decomp T P"
  unfolding cone_decomp_def using assms by blast

lemma cone_decompD:
  assumes "cone_decomp T P"
  shows "finite P" and "T = (\<Union>(t, U)\<in>P. cone t U)"
    and "\<And>t1 t2 U1 U2 s. (t1, U1) \<in> P \<Longrightarrow> (t2, U2) \<in> P \<Longrightarrow> s \<in> cone t1 U1 \<Longrightarrow> s \<in> cone t2 U2 \<Longrightarrow>
            (t1, U1) = (t2, U2)"
  using assms unfolding cone_decomp_def by blast+

lemma cone_decomp_indets:
  assumes "cone_decomp T P" and "T \<subseteq> .[X]" and "(t, U) \<in> P"
  shows "t \<in> .[X]" and "U \<subseteq> X"
proof -
  from assms(1) have "T = (\<Union>(t, U)\<in>P. cone t U)" by (rule cone_decompD)
  hence "cone t U \<subseteq> T" using assms(3) by blast
  hence "cone t U \<subseteq> .[X]" using assms(2) by (rule subset_trans)
  thus "t \<in> .[X]" and "U \<subseteq> X" by (rule cone_indets)+
qed

lemma cone_decomp_empty_iff: "cone_decomp {} P \<longleftrightarrow> (P = {})"
proof
  assume "cone_decomp {} P"
  hence "{} = (\<Union>(t, U)\<in>P. cone t U)" by (rule cone_decompD)
  hence 1: "\<And>t U. (t, U) \<in> P \<Longrightarrow> cone t U = {}" by blast
  {
    fix t U
    assume "(t, U) \<in> P"
    hence "cone t U = {}" by (rule 1)
    moreover have "t \<in> cone t U" by (fact tip_in_cone)
    ultimately have False by simp
  }
  thus "P = {}" by fastforce
qed (simp add: cone_decomp_def)

lemma cone_decomp_singleton: "cone_decomp (cone t U) {(t, U)}"
  by (simp add: cone_decomp_def)

lemma cone_decomp_UN:
  assumes "finite I" and "\<And>i1 i2 t. i1 \<in> I \<Longrightarrow> i2 \<in> I \<Longrightarrow> t \<in> T i1 \<Longrightarrow> t \<in> T i2 \<Longrightarrow> i1 = i2"
    and "\<And>i. i \<in> I \<Longrightarrow> cone_decomp ((T i)::('x::countable \<Rightarrow>\<^sub>0 nat) set) (P i)"
  shows "cone_decomp (\<Union> (T ` I)) (\<Union> (P ` I))"
proof -
  have T: "T i = (\<Union>(t, U)\<in>P i. cone t U)" if "i \<in> I" for i
    by (rule cone_decompD, rule assms(3), fact that)
  show ?thesis
  proof (rule cone_decompI)
    from assms(1) show "finite (\<Union> (P ` I))"
    proof (rule finite_UN_I)
      fix i
      assume "i \<in> I"
      hence "cone_decomp (T i) (P i)" by (rule assms(3))
      thus "finite (P i)" by (rule cone_decompD)
    qed
  next
    show "\<Union> (T ` I) = (\<Union>(t, U)\<in>\<Union> (P ` I). cone t U)" by (simp add: T)
  next
    fix t1 t2 :: "'x::countable \<Rightarrow>\<^sub>0 nat" and U1 U2 s
    assume s1: "s \<in> cone t1 U1" and s2: "s \<in> cone t2 U2"
    assume "(t1, U1) \<in> \<Union> (P ` I)"
    then obtain i1 where "i1 \<in> I" and "(t1, U1) \<in> P i1" ..
    hence "cone t1 U1 \<subseteq> T i1" by (fastforce simp: T)
    with s1 have "s \<in> T i1" ..
    assume "(t2, U2) \<in> \<Union> (P ` I)"
    then obtain i2 where "i2 \<in> I" and "(t2, U2) \<in> P i2" ..
    hence "cone t2 U2 \<subseteq> T i2" by (fastforce simp: T)
    with s2 have "s \<in> T i2" ..
    with \<open>i1 \<in> I\<close> \<open>i2 \<in> I\<close> \<open>s \<in> T i1\<close> have "i1 = i2" by (rule assms(2))
    from \<open>i2 \<in> I\<close> have "cone_decomp (T i2) (P i2)" by (rule assms(3))
    moreover from \<open>(t1, U1) \<in> P i1\<close> have "(t1, U1) \<in> P i2" by (simp only: \<open>i1 = i2\<close>)
    ultimately show "(t1, U1) = (t2, U2)" using \<open>(t2, U2) \<in> P i2\<close> s1 s2 by (rule cone_decompD)
  qed
qed

corollary cone_decomp_UN_prod:
  assumes "finite P"
    and "\<And>t1 t2 U1 U2 s. (t1, U1) \<in> P \<Longrightarrow> (t2, U2) \<in> P \<Longrightarrow> s \<in> f t1 U1 \<Longrightarrow> s \<in> f t2 U2 \<Longrightarrow> (t1, U1) = (t2, U2)"
    and "\<And>t U. (t, U) \<in> P \<Longrightarrow> cone_decomp (f t U) (g t U)"
  shows "cone_decomp (\<Union>(t, U)\<in>P. f t U) (\<Union>(t, U)\<in>P. g t U)"
  using assms by (metis (mono_tags) case_prod_conv cone_decomp_UN prod.exhaust)

corollary cone_decomp_Un:
  assumes "T \<inter> S = {}" and "cone_decomp T P" and "cone_decomp S Q"
  shows "cone_decomp (T \<union> S) (P \<union> Q)"
proof (cases "S = T")
  case True
  with assms(1) have "T = {}" by simp
  with assms(2, 3) True show ?thesis by (simp add: cone_decomp_empty_iff)
next
  case False
  let ?P = "\<lambda>x. if x = T then P else if x = S then Q else {}"
  have "cone_decomp (\<Union> (id ` {T, S})) (\<Union> (?P ` {T, S}))"
  proof (rule cone_decomp_UN)
    fix A B t
    assume "A \<in> {T, S}" and "B \<in> {T, S}" and "t \<in> id A" and "t \<in> id B"
    with assms(1) show "A = B" by auto
  next
    fix A
    assume "A \<in> {T, S}"
    with assms(2, 3) show "cone_decomp (id A) (?P A)" by auto
  qed simp
  with False show ?thesis by (simp split: if_split_asm)
qed

lemma cone_decomp_plus:
  assumes "cone_decomp T P"
  shows "cone_decomp ((+) s ` T) (apfst ((+) s) ` P)"
proof (rule cone_decompI)
  from assms have "finite P" by (rule cone_decompD)
  thus "finite (apfst ((+) s) ` P)" by (rule finite_imageI)
next
  from assms have "T = (\<Union>(t, U)\<in>P. cone t U)" by (rule cone_decompD)
  thus "(+) s ` T = (\<Union>(t, U)\<in>apfst ((+) s) ` P. cone t U)"
    by (simp add: image_UN image_plus_cone case_prod_beta')
next
  fix t1 t2 U1 U2 s'
  assume "(t1, U1) \<in> apfst ((+) s) ` P"
  then obtain t1' where "(t1', U1) \<in> P" and t1: "t1 = s + t1'" by fastforce
  assume "(t2, U2) \<in> apfst ((+) s) ` P"
  then obtain t2' where "(t2', U2) \<in> P" and t2: "t2 = s + t2'" by fastforce
  assume "s' \<in> cone t1 U1"
  also have "... = (+) s ` cone t1' U1" by (simp only: t1 image_plus_cone)
  finally obtain s1 where "s1 \<in> cone t1' U1" and "s' = s + s1" ..
  assume "s' \<in> cone t2 U2"
  also have "... = (+) s ` cone t2' U2" by (simp only: t2 image_plus_cone)
  finally obtain s2 where "s2 \<in> cone t2' U2" and "s' = s + s2" ..
  from this(2) have "s1 = s2" by (simp add: \<open>s' = s + s1\<close>)
  with \<open>s1 \<in> cone t1' U1\<close> have "s2 \<in> cone t1' U1" by simp
  with assms \<open>(t1', U1) \<in> P\<close> \<open>(t2', U2) \<in> P\<close> have "(t1', U1) = (t2', U2)" using \<open>s2 \<in> cone t2' U2\<close>
    by (rule cone_decompD)
  thus "(t1, U1) = (t2, U2)" by (simp add: t1 t2)
qed

lemma finite_cone_decompI:
  assumes "finite X" and "T \<subseteq> .[X]" and "cone_decomp T P"
  shows "finite_decomp P"
proof (rule finite_decompI)
  from assms(3) show "finite P" by (rule cone_decompD)
next
  fix t U
  assume "(t, U) \<in> P"
  with assms(3, 2) have "U \<subseteq> X" by (rule cone_decomp_indets)
  thus "finite U" using assms(1) by (rule finite_subset)
qed

lemma Hilbert_fun_cone_decomp:
  assumes "cone_decomp T P" and "finite_decomp P"
  shows "Hilbert_fun T z = (\<Sum>(t, U)\<in>P. Hilbert_fun (cone t U) z)"
proof -
  from assms(1) have "T = (\<Union>(t, U)\<in>P. cone t U)" by (rule cone_decompD)
  hence "{t \<in> T. deg_pm t = z} = (\<Union>p\<in>P. {v \<in> cone (fst p) (snd p). deg_pm v = z})" by fastforce
  hence "Hilbert_fun T z = card ..." by (simp only: Hilbert_fun_def)
  also have "... = (\<Sum>p\<in>P. card {v \<in> cone (fst p) (snd p). deg_pm v = z})"
  proof (rule card_UN_disjoint)
    from assms(1) show "finite P" by (rule cone_decompD)
  next
    {
      fix t U
      assume "(t, U) \<in> P"
      with assms(2) have "finite U" by (rule finite_decompD)
      hence "finite {v \<in> cone t U. deg_pm v = z}" by (rule finite_cone_deg)
    }
    thus "\<forall>p\<in>P. finite {v \<in> cone (fst p) (snd p). deg_pm v = z}" by fastforce
  next
    {
      fix t1 t2 U1 U2 s
      assume "(t1, U1) \<in> P" and "(t2, U2) \<in> P"
      assume "s \<in> {v \<in> cone t1 U1. deg_pm v = z} \<inter> {v \<in> cone t2 U2. deg_pm v = z}"
      hence "s \<in> cone t1 U1" and "s \<in> cone t2 U2" by simp_all
      with assms(1) \<open>(t1, U1) \<in> P\<close> \<open>(t2, U2) \<in> P\<close> have "(t1, U1) = (t2, U2)" by (rule cone_decompD)
    }
    thus "\<forall>p1\<in>P. \<forall>p2\<in>P. p1 \<noteq> p2 \<longrightarrow>
          {v \<in> cone (fst p1) (snd p1). deg_pm v = z} \<inter> {v \<in> cone (fst p2) (snd p2). deg_pm v = z} = {}"
      by fastforce
  qed
  also have "... = (\<Sum>(t, U)\<in>P. Hilbert_fun (cone t U) z)"
    by (simp add: case_prod_beta' Hilbert_fun_def)
  finally show ?thesis .
qed

definition pos_decomp :: "(('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set" ("(_\<^sub>+)" [1000] 999)
  where "pos_decomp P = {p \<in> P. snd p \<noteq> {}}"

definition standard_decomp :: "nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> bool"
  where "standard_decomp k P \<longleftrightarrow> (\<forall>(t, U)\<in>P\<^sub>+. k \<le> deg_pm t \<and>
                                      (\<forall>d. k \<le> d \<longrightarrow> d \<le> deg_pm t \<longrightarrow>
                                        (\<exists>(t', U')\<in>P. deg_pm t' = d \<and> card U \<le> card U')))"

lemma pos_decomp_empty [simp]: "{}\<^sub>+ = {}"
  by (simp add: pos_decomp_def)

lemma pos_decomp_Un: "(P \<union> Q)\<^sub>+ = P\<^sub>+ \<union> Q\<^sub>+"
  by (fastforce simp: pos_decomp_def)

lemma pos_decomp_UN: "(\<Union> A)\<^sub>+ = (\<Union> (pos_decomp ` A))"
  by (fastforce simp: pos_decomp_def)

lemma pos_decomp_image: "(apfst f ` P)\<^sub>+ = apfst f ` P\<^sub>+"
  by (auto simp: pos_decomp_def)

lemma standard_decompI:
  assumes "\<And>t U. (t, U) \<in> P\<^sub>+ \<Longrightarrow> k \<le> deg_pm t"
    and "\<And>t U d. (t, U) \<in> P\<^sub>+ \<Longrightarrow> k \<le> d \<Longrightarrow> d \<le> deg_pm t \<Longrightarrow>
          (\<exists>t' U'. (t', U') \<in> P \<and> deg_pm t' = d \<and> card U \<le> card U')"
  shows "standard_decomp k P"
  unfolding standard_decomp_def using assms by blast

lemma standard_decompD: "standard_decomp k P \<Longrightarrow> (t, U) \<in> P\<^sub>+ \<Longrightarrow> k \<le> deg_pm t"
  unfolding standard_decomp_def by blast

lemma standard_decompE:
  assumes "standard_decomp k P" and "(t, U) \<in> P\<^sub>+" and "k \<le> d" and "d \<le> deg_pm t"
  obtains t' U' where "(t', U') \<in> P" and "deg_pm t' = d" and "card U \<le> card U'"
  using assms unfolding standard_decomp_def by blast

lemma standard_decomp_empty: "P\<^sub>+ = {} \<Longrightarrow> standard_decomp k P"
  by (simp add: standard_decomp_def)

lemma standard_decomp_singleton: "standard_decomp (deg_pm t) {(t, U)}"
  by (simp add: standard_decomp_def pos_decomp_def)

lemma standard_decomp_UN:
  assumes "\<And>a. a \<in> A \<Longrightarrow> standard_decomp k (f a)"
  shows "standard_decomp k (\<Union> (f ` A))"
proof (rule standard_decompI)
  fix t U
  assume "(t, U) \<in> (\<Union> (f ` A))\<^sub>+"
  hence *: "(t, U) \<in> (\<Union> ((\<lambda>a. pos_decomp (f a)) ` A))" by (simp only: pos_decomp_UN image_image)
  thus "k \<le> deg_pm t"
  proof
    fix a
    assume "a \<in> A"
    hence "standard_decomp k (f a)" by (rule assms)
    moreover assume "(t, U) \<in> (f a)\<^sub>+"
    ultimately show ?thesis by (rule standard_decompD)
  qed

  fix d
  assume "k \<le> d" and "d \<le> deg_pm t"
  from * show "\<exists>t' U'. (t', U') \<in> \<Union> (f ` A) \<and> deg_pm t' = d \<and> card U \<le> card U'"
  proof
    fix a
    assume "a \<in> A"
    hence "standard_decomp k (f a)" by (rule assms)
    moreover assume "(t, U) \<in> (f a)\<^sub>+"
    ultimately obtain t' U' where "(t', U') \<in> f a" and "deg_pm t' = d" and "card U \<le> card U'"
      using \<open>k \<le> d\<close> \<open>d \<le> deg_pm t\<close> by (rule standard_decompE)
    thus ?thesis using \<open>a \<in> A\<close> by blast
  qed
qed

corollary standard_decomp_UN_prod:
  "(\<And>t U. (t, U) \<in> P \<Longrightarrow> standard_decomp k (g t U)) \<Longrightarrow> standard_decomp k (\<Union>(t, U)\<in>P. g t U)"
  by (metis (mono_tags) case_prod_conv standard_decomp_UN prod.exhaust)

corollary standard_decomp_Un:
  assumes "standard_decomp k P" and "standard_decomp k Q"
  shows "standard_decomp k (P \<union> Q)"
proof -
  have "standard_decomp k (\<Union> (id ` {P, Q}))" by (rule standard_decomp_UN) (auto simp: assms)
  thus ?thesis by simp
qed

lemma standard_decomp_plus:
  assumes "standard_decomp k P"
  shows "standard_decomp (k + deg_pm s) (apfst ((+) s) ` P)"
proof (rule standard_decompI)
  fix t U
  assume "(t, U) \<in> (apfst ((+) s) ` P)\<^sub>+"
  then obtain t0 where "(t0, U) \<in> P\<^sub>+" and t: "t = s + t0" by (fastforce simp: pos_decomp_image)
  from assms this(1) have "k \<le> deg_pm t0" by (rule standard_decompD)
  thus "k + deg_pm s \<le> deg_pm t" by (simp add: t deg_pm_plus)

  fix d
  assume "k + deg_pm s \<le> d" and "d \<le> deg_pm t"
  hence "k \<le> d - deg_pm s" and "d - deg_pm s \<le> deg_pm t0" by (simp_all add: t deg_pm_plus)
  with assms \<open>(t0, U) \<in> P\<^sub>+\<close> obtain t' U' where "(t', U') \<in> P" and "deg_pm t' = d - deg_pm s"
    and "card U \<le> card U'" by (rule standard_decompE)
  from this(1) have "(s + t', U') \<in> apfst ((+) s) ` P" by force
  moreover from \<open>k + deg_pm s \<le> d\<close> \<open>deg_pm t' = d - deg_pm s\<close> have "deg_pm (s + t') = d"
    by (simp add: deg_pm_plus)
  ultimately show "\<exists>t' U'. (t', U') \<in> apfst ((+) s) ` P \<and> deg_pm t' = d \<and> card U \<le> card U'"
    using \<open>card U \<le> card U'\<close> by fastforce
qed

lemma standard_decomp_nonempty_unique:
  assumes "finite_decomp P" and "standard_decomp k P" and "P\<^sub>+ \<noteq> {}"
  shows "k = Min ((deg_pm \<circ> fst) ` P\<^sub>+)"
proof -
  define m where "m = Min ((deg_pm \<circ> fst) ` P\<^sub>+)"
  from assms(1) have "finite P" by (rule finite_decompD)
  hence "finite (P\<^sub>+)" by (simp add: pos_decomp_def)
  hence "finite ((deg_pm \<circ> fst) ` P\<^sub>+)" by (rule finite_imageI)
  moreover from assms(3) have "(deg_pm \<circ> fst) ` P\<^sub>+ \<noteq> {}" by simp
  ultimately have "m \<in> (deg_pm \<circ> fst) ` P\<^sub>+" unfolding m_def by (rule Min_in)
  then obtain t U where "(t, U) \<in> P\<^sub>+" and m: "m = deg_pm t" by fastforce
  have m_min: "m \<le> deg_pm t'" if "(t', U') \<in> P\<^sub>+" for t' U'
  proof -
    from that have "(deg_pm \<circ> fst) (t', U') \<in> (deg_pm \<circ> fst) ` P\<^sub>+" by (rule imageI)
    with \<open>finite ((deg_pm \<circ> fst) ` P\<^sub>+)\<close> have "m \<le> (deg_pm \<circ> fst) (t', U')"
      unfolding m_def by (rule Min_le)
    thus ?thesis by simp
  qed
  show ?thesis
  proof (rule linorder_cases)
    assume "k < m"
    hence "k \<le> deg_pm t" by (simp add: m)
    with assms(2) \<open>(t, U) \<in> P\<^sub>+\<close> le_refl obtain t' U'
      where "(t', U') \<in> P" and "deg_pm t' = k" and "card U \<le> card U'" by (rule standard_decompE)
    from this(2) \<open>k < m\<close> have "\<not> m \<le> deg_pm t'" by simp
    with m_min have "(t', U') \<notin> P\<^sub>+" by blast
    with \<open>(t', U') \<in> P\<close> have "U' = {}" by (simp add: pos_decomp_def)
    with \<open>card U \<le> card U'\<close> have "U = {} \<or> infinite U" by (simp add: card_eq_0_iff)
    thus ?thesis
    proof
      assume "U = {}"
      with \<open>(t, U) \<in> P\<^sub>+\<close> show ?thesis by (simp add: pos_decomp_def)
    next
      assume "infinite U"
      moreover from assms(1) have "finite U"
      proof (rule finite_decompD)
        from \<open>(t, U) \<in> P\<^sub>+\<close> show "(t, U) \<in> P" by (simp add: pos_decomp_def)
      qed
      ultimately show ?thesis ..
    qed
  next
    assume "m < k"
    hence "\<not> k \<le> m" by simp
    moreover from assms(2) \<open>(t, U) \<in> P\<^sub>+\<close> have "k \<le> m" unfolding m by (rule standard_decompD)
    ultimately show ?thesis ..
  qed (simp only: m_def)
qed

lemma standard_decomp_SucE:
  assumes "finite U"
  obtains P where "finite_decomp P" and "cone_decomp (cone t U) P" and "standard_decomp (Suc (deg_pm t)) P"
  using assms
proof (induct U arbitrary: thesis rule: finite_induct)
  case empty
  have "finite_decomp {(t, {})}" by (simp add: finite_decomp_def)
  moreover note cone_decomp_singleton
  moreover have "standard_decomp (Suc (deg_pm t)) {(t, {})}"
    by (rule standard_decomp_empty) (simp add: pos_decomp_def)
  ultimately show ?case by (rule empty)
next
  case (insert x U)
  obtain P where 0: "finite_decomp P" and 1: "cone_decomp (cone t U) P"
    and 2: "standard_decomp (Suc (deg_pm t)) P" by (rule insert.hyps)
  define Q where "Q = {(Poly_Mapping.single x 1 + t, insert x U)}"
  show ?case
  proof (rule insert.prems)
    from insert.hyps(1) have "finite_decomp Q" by (simp add: Q_def finite_decomp_def)
    with 0 show "finite_decomp (P \<union> Q)" by (rule finite_decomp_Un)
  next
    note cone_insert
    also have "cone_decomp (cone t U \<union> cone (Poly_Mapping.single x 1 + t) (insert x U)) (P \<union> Q)"
    proof (rule cone_decomp_Un)
      from insert.hyps(2) show "cone t U \<inter> cone (monomial 1 x + t) (insert x U) = {}"
        by (rule cone_insert_disjoint)
    next
      show "cone_decomp (cone (monomial 1 x + t) (insert x U)) Q"
        by (simp add: Q_def cone_decomp_singleton)
    qed (fact 1)
    finally show "cone_decomp (cone t (insert x U)) (P \<union> Q)" .
  next
    from standard_decomp_singleton[of "Poly_Mapping.single x 1 + t" "insert x U"]
    have "standard_decomp (Suc (deg_pm t)) Q" by (simp add: deg_pm_plus Q_def deg_pm_single)
    with 2 show "standard_decomp (Suc (deg_pm t)) (P \<union> Q)" by (rule standard_decomp_Un)
  qed
qed

lemma standard_decomp_geE:
  assumes "finite_decomp P" and "cone_decomp (T::('x::countable \<Rightarrow>\<^sub>0 nat) set) P"
    and "standard_decomp k P" and "k \<le> d"
  obtains Q where "finite_decomp Q" and "cone_decomp T Q" and "standard_decomp d Q"
proof -
  have "\<exists>Q. finite_decomp Q \<and> cone_decomp T Q \<and> standard_decomp (k + i) Q" for i
  proof (induct i)
    case 0
    from assms(1, 2, 3) show ?case unfolding add_0_right by blast
  next
    case (Suc i)
    then obtain Q where 0: "finite_decomp Q" and 1: "cone_decomp T Q" and 2: "standard_decomp (k + i) Q"
      by blast
    define R where "R = {(t, U) \<in> Q. deg_pm t = k + i}"
    let ?S = "Q - R"

    have "R \<subseteq> Q" by (fastforce simp: R_def)
    hence "finite R"
    proof (rule finite_subset)
      from 0 show "finite Q" by (rule finite_decompD)
    qed
    have fin_U: "finite U" if "(t, U) \<in> R" for t U
    proof -
      from that \<open>R \<subseteq> Q\<close> have "(t, U) \<in> Q" ..
      with 0 show ?thesis by (rule finite_decompD)
    qed

    have "?S \<subseteq> Q" by blast
    hence "finite ?S"
    proof (rule finite_subset)
      from 0 show "finite Q" by (rule finite_decompD)
    qed

    define f where "f = (\<lambda>t U. SOME P'. finite_decomp P' \<and> cone_decomp (cone t U) P' \<and>
                                        standard_decomp (Suc (deg_pm (t::'x \<Rightarrow>\<^sub>0 _))) P')"
    have "finite_decomp (f t U) \<and> cone_decomp (cone t U) (f t U) \<and> standard_decomp (Suc (k + i)) (f t U)"
      if "(t, U) \<in> R" for t U
    proof -
      from that have eq: "deg_pm t = k + i" by (simp add: R_def)
      from that have "finite U" by (rule fin_U)
      then obtain P' where "finite_decomp P'" and "cone_decomp (cone t U) P'"
        and "standard_decomp (Suc (deg_pm t)) P'" by (rule standard_decomp_SucE)
      hence "finite_decomp P' \<and> cone_decomp (cone t U) P' \<and> standard_decomp (Suc (deg_pm t)) P'"
        by simp
      thus ?thesis unfolding f_def eq by (rule someI)
    qed
    hence f1: "\<And>t U. (t, U) \<in> R \<Longrightarrow> finite_decomp (f t U)"
      and f2: "\<And>t U. (t, U) \<in> R \<Longrightarrow> cone_decomp (cone t U) (f t U)"
      and f3: "\<And>t U. (t, U) \<in> R \<Longrightarrow> standard_decomp (Suc (k + i)) (f t U)" by blast+

    define R' where "R' = (\<Union>(t, U)\<in>R. f t U)"
    show ?case unfolding add_Suc_right
    proof (intro exI conjI)
      from \<open>finite ?S\<close> have "finite_decomp ?S"
      proof (rule finite_decompI)
        fix t U
        assume "(t, U) \<in> ?S"
        hence "(t, U) \<in> Q" using \<open>?S \<subseteq> Q\<close> ..
        with 0 show "finite U" by (rule finite_decompD)
      qed
      moreover have "finite_decomp R'"
        unfolding R'_def using \<open>finite R\<close> f1 by (rule finite_decomp_UN_prod)
      ultimately show "finite_decomp (?S \<union> R')" by (rule finite_decomp_Un)
    next
      have "(\<Union>(t, U)\<in>?S. cone t U) \<inter> (\<Union>(t, U)\<in>R. cone t U) = {}"
      proof
        {
          fix s
          assume "s \<in> (\<Union>(t, U)\<in>?S. cone t U)"
          then obtain t1 U1 where "(t1, U1) \<in> ?S" and s1: "s \<in> cone t1 U1" by blast
          from this(1) \<open>?S \<subseteq> Q\<close> have "(t1, U1) \<in> Q" ..
          assume "s \<in> (\<Union>(t, U)\<in>R. cone t U)"
          then obtain t2 U2 where "(t2, U2) \<in> R" and s2: "s \<in> cone t2 U2" by blast
          from this(1) \<open>R \<subseteq> Q\<close> have "(t2, U2) \<in> Q" ..
          with 1 \<open>(t1, U1) \<in> Q\<close> have "(t1, U1) = (t2, U2)" using s1 s2 by (rule cone_decompD)
          with \<open>(t1, U1) \<in> ?S\<close> \<open>(t2, U2) \<in> R\<close> have False by simp
        }
        thus "(\<Union>(t, U)\<in>?S. cone t U) \<inter> (\<Union>(t, U)\<in>R. cone t U) \<subseteq> {}" by blast
      qed (fact empty_subsetI)
      moreover from \<open>finite ?S\<close> refl have "cone_decomp (\<Union>(t, U)\<in>?S. cone t U) ?S"
      proof (rule cone_decompI)
        fix t1 t2 U1 U2 s
        assume "(t1, U1) \<in> ?S" and "(t2, U2) \<in> ?S"
        note 1
        moreover from \<open>(t1, U1) \<in> ?S\<close> \<open>?S \<subseteq> Q\<close> have "(t1, U1) \<in> Q" ..
        moreover from \<open>(t2, U2) \<in> ?S\<close> \<open>?S \<subseteq> Q\<close> have "(t2, U2) \<in> Q" ..
        moreover assume "s \<in> cone t1 U1" and "s \<in> cone t2 U2"
        ultimately show "(t1, U1) = (t2, U2)" by (rule cone_decompD)
      qed
      moreover have "cone_decomp (\<Union>(t, U)\<in>R. cone t U) R'" unfolding R'_def using \<open>finite R\<close> _ f2
      proof (rule cone_decomp_UN_prod)
        fix t1 t2 U1 U2 s
        assume "(t1, U1) \<in> R" and "(t2, U2) \<in> R"
        note 1
        moreover from \<open>(t1, U1) \<in> R\<close> \<open>R \<subseteq> Q\<close> have "(t1, U1) \<in> Q" ..
        moreover from \<open>(t2, U2) \<in> R\<close> \<open>R \<subseteq> Q\<close> have "(t2, U2) \<in> Q" ..
        moreover assume "s \<in> cone t1 U1" and "s \<in> cone t2 U2"
        ultimately show "(t1, U1) = (t2, U2)" by (rule cone_decompD)
      qed
      ultimately have "cone_decomp ((\<Union>(t, U)\<in>?S. cone t U) \<union> (\<Union>(t, U)\<in>R. cone t U)) (?S \<union> R')"
        by (rule cone_decomp_Un)
      with \<open>R \<subseteq> Q\<close> have "cone_decomp (\<Union>(t, U)\<in>Q. cone t U) (?S \<union> R')"
        by (simp only: UN_Un[symmetric] Un_Diff_cancel2 Un_absorb2)
      moreover from 1 have "T = (\<Union>(t, U)\<in>Q. cone t U)" by (rule cone_decompD)
      ultimately show "cone_decomp T (?S \<union> R')" by (simp only:)
    next
      have "standard_decomp (Suc (k + i)) ?S"
      proof (rule standard_decompI)
        fix t U
        assume "(t, U) \<in> ?S\<^sub>+"
        hence "(t, U) \<in> Q\<^sub>+" and "deg_pm t \<noteq> k + i" by (simp_all add: pos_decomp_def R_def)
        from 2 this(1) have "k + i \<le> deg_pm t" by (rule standard_decompD)
        with \<open>deg_pm t \<noteq> k + i\<close> show "Suc (k + i) \<le> deg_pm t" by simp
  
        fix d'
        assume "Suc (k + i) \<le> d'" and "d' \<le> deg_pm t"
        from this(1) have "k + i \<le> d'" and "d' \<noteq> k + i" by simp_all
        from 2 \<open>(t, U) \<in> Q\<^sub>+\<close> this(1) obtain t' U'
          where "(t', U') \<in> Q" and "deg_pm t' = d'" and "card U \<le> card U'"
          using \<open>d' \<le> deg_pm t\<close> by (rule standard_decompE)
        moreover from \<open>d' \<noteq> k + i\<close> this(2) have "(t', U') \<notin> R" by (simp add: R_def)
        ultimately show "\<exists>t' U'. (t', U') \<in> Q - R \<and> deg_pm t' = d' \<and> card U \<le> card U'" by blast
      qed
      moreover have "standard_decomp (Suc (k + i)) R'"
        unfolding R'_def using f3 by (rule standard_decomp_UN_prod)
      ultimately show "standard_decomp (Suc (k + i)) (?S \<union> R')" by (rule standard_decomp_Un)
    qed
  qed
  then obtain Q where 1: "finite_decomp Q" and 2: "cone_decomp T Q" and "standard_decomp (k + (d - k)) Q"
    by blast
  from this(3) assms(4) have "standard_decomp d Q" by simp
  with 1 2 show ?thesis ..
qed

lemma standard_decomp_MaxE:
  assumes "finite I" and "\<And>i1 i2 s. i1 \<in> I \<Longrightarrow> i2 \<in> I \<Longrightarrow> s \<in> T i1 \<Longrightarrow> s \<in> T i2 \<Longrightarrow> i1 = i2"
    and "\<And>i. i \<in> I \<Longrightarrow> finite_decomp (P i)"
    and "\<And>i. i \<in> I \<Longrightarrow> cone_decomp ((T i)::('x::countable \<Rightarrow>\<^sub>0 nat) set) (P i)"
    and "\<And>i. i \<in> I \<Longrightarrow> standard_decomp (k i) (P i)"
    and "Max (k ` I) \<le> d"
  obtains Q where "finite_decomp Q" and "cone_decomp (\<Union> (T ` I)) Q" and "standard_decomp d Q"
proof -
  define f where "f = (\<lambda>i. SOME Q. finite_decomp Q \<and> cone_decomp (T i) Q \<and> standard_decomp d Q)"
  have "finite_decomp (f i) \<and> cone_decomp (T i) (f i) \<and> standard_decomp d (f i)" if "i \<in> I" for i
  proof -
    from that have "finite_decomp (P i)" and "cone_decomp (T i) (P i)" and "standard_decomp (k i) (P i)"
      by (rule assms)+
    moreover have "k i \<le> d"
    proof (rule le_trans)
      from assms(1) have "finite (k ` I)" by (rule finite_imageI)
      moreover from that have "k i \<in> k ` I" by (rule imageI)
      ultimately show "k i \<le> Max (k ` I)" by (rule Max_ge)
    qed (fact assms(6))
    ultimately obtain Q where "finite_decomp Q" and "cone_decomp (T i) Q"
      and "standard_decomp d Q" by (rule standard_decomp_geE)
    hence "finite_decomp Q \<and> cone_decomp (T i) Q \<and> standard_decomp d Q" by simp
    thus ?thesis unfolding f_def by (rule someI)
  qed
  hence f1: "\<And>i. i \<in> I \<Longrightarrow> finite_decomp (f i)"
    and f2: "\<And>i. i \<in> I \<Longrightarrow> cone_decomp (T i) (f i)"
    and f3: "\<And>i. i \<in> I \<Longrightarrow> standard_decomp d (f i)" by blast+
  show ?thesis
  proof
    from assms(1) f1 show "finite_decomp (\<Union> (f ` I))" by (rule finite_decomp_UN)
  next
    from assms(1, 2) f2 show "cone_decomp (\<Union> (T ` I)) (\<Union> (f ` I))" by (rule cone_decomp_UN)
  next
    from f3 show "standard_decomp d (\<Union> (f ` I))" by (rule standard_decomp_UN)
  qed
qed

lemma standard_decomp_MaxE_prod:
  assumes "finite P"
    and "\<And>t1 t2 U1 U2 s. (t1, U1) \<in> P \<Longrightarrow> (t2, U2) \<in> P \<Longrightarrow> s \<in> f t1 U1 \<Longrightarrow> s \<in> f t2 U2 \<Longrightarrow> (t1, U1) = (t2, U2)"
    and "\<And>t U. (t, U) \<in> P \<Longrightarrow> finite_decomp (g t U)"
    and "\<And>t U. (t, U) \<in> P \<Longrightarrow> cone_decomp ((f t U)::('x::countable \<Rightarrow>\<^sub>0 nat) set) (g t U)"
    and "\<And>t U. (t, U) \<in> P \<Longrightarrow> standard_decomp (k t U) (g t U)"
    and "(MAX (t, U)\<in>P. k t U) \<le> d"
  obtains Q where "finite_decomp Q" and "cone_decomp (\<Union>(t, U)\<in>P. f t U) Q" and "standard_decomp d Q"
proof (rule standard_decomp_MaxE)
  from assms(1) show "finite P" .
  show "\<And>i1 i2 s. i1 \<in> P \<Longrightarrow> i2 \<in> P \<Longrightarrow> s \<in> case_prod f i1 \<Longrightarrow> s \<in> case_prod f i2 \<Longrightarrow> i1 = i2"
    using assms(2) by blast
  from assms(3) show "\<And>i. i \<in> P \<Longrightarrow> finite_decomp (case_prod g i)" by (simp add: split_beta)
  from assms(4) show "\<And>i. i \<in> P \<Longrightarrow> cone_decomp (case_prod f i) (case_prod g i)" by (simp add: split_beta)
  from assms(5) show "\<And>i. i \<in> P \<Longrightarrow> standard_decomp (case_prod k i) (case_prod g i)"
    by (simp add: split_beta)
  from assms(6) show "(MAX i\<in>P. case_prod k i) \<le> d" by blast
qed blast

subsection \<open>Ideal-like Sets of Power-Products\<close>

context
  fixes X :: "'x::countable set"
begin

definition ideal_like :: "('x::countable \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> bool"
  where "ideal_like T \<longleftrightarrow> T \<subseteq> .[X] \<and> (\<forall>s\<in>.[X]. \<forall>t\<in>T. s + t \<in> T)"

(* OBSOLETE? *)
definition aideal_like :: "('x::countable \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> bool"
  where "aideal_like T \<longleftrightarrow> (\<forall>s. \<forall>t\<in>T. s adds t \<longrightarrow> s \<in> T)"

lemma ideal_likeI: "T \<subseteq> .[X] \<Longrightarrow> (\<And>s t. s \<in> .[X] \<Longrightarrow> t \<in> T \<Longrightarrow> s + t \<in> T) \<Longrightarrow> ideal_like T"
  by (simp add: ideal_like_def)

lemma ideal_likeD:
  assumes "ideal_like T"
  shows "T \<subseteq> .[X]" and "\<And>t s. s \<in> .[X] \<Longrightarrow> t \<in> T \<Longrightarrow> s + t \<in> T"
  using assms by (simp_all add: ideal_like_def)

lemma aideal_likeI: "(\<And>t s. t \<in> T \<Longrightarrow> s adds t \<Longrightarrow> s \<in> T) \<Longrightarrow> aideal_like T"
  by (simp add: aideal_like_def)

lemma aideal_likeD: "aideal_like T \<Longrightarrow> t \<in> T \<Longrightarrow> s adds t \<Longrightarrow> s \<in> T"
  unfolding aideal_like_def by blast

lemma ideal_like_Diff:
  assumes "aideal_like T"
  shows "ideal_like (.[X] - T)"
proof (rule ideal_likeI)
  show ".[X] - T \<subseteq> .[X]" by blast
next
  fix s t
  assume "s \<in> .[X]"
  assume "t \<in> .[X] - T"
  hence "t \<in> .[X]" and "t \<notin> T" by simp_all
  from \<open>s \<in> .[X]\<close> this(1) have "s + t \<in> .[X]" by (rule PPs_closed_plus)
  moreover have "s + t \<notin> T"
  proof
    note assms
    moreover assume "s + t \<in> T"
    moreover from add.commute have "t adds s + t" by (rule addsI)
    ultimately have "t \<in> T" by (rule aideal_likeD)
    with \<open>t \<notin> T\<close> show False ..
  qed
  ultimately show "s + t \<in> .[X] - T" by simp
qed

lemma aideal_like_Diff:
  assumes "U \<subseteq> X" and "ideal_like T"
  shows "aideal_like (.[U] - T)"
proof (rule aideal_likeI)
  fix t s
  assume "t \<in> .[U] - T"
  hence "t \<in> .[U]" and "t \<notin> T" by simp_all
  note this(1)
  moreover assume "s adds t"
  ultimately have "s \<in> .[U]" by (rule PPs_closed_adds)
  moreover have "s \<notin> T"
  proof
    note assms(2)
    moreover have "t - s \<in> .[X]"
    proof
      from \<open>t \<in> .[U]\<close> show "t - s \<in> .[U]" by (rule PPs_closed_minus)
    next
      from assms(1) show ".[U] \<subseteq> .[X]" by (rule PPs_mono)
    qed
    moreover assume "s \<in> T"
    ultimately have "(t - s) + s \<in> T" by (rule ideal_likeD)
    with \<open>s adds t\<close> have "t \<in> T" by (simp add: adds_minus)
    with \<open>t \<notin> T\<close> show False ..
  qed
  ultimately show "s \<in> .[U] - T" by simp
qed

lemma cone_subset_ideal_like_iff:
  assumes "ideal_like T"
  shows "cone t U \<subseteq> T \<longleftrightarrow> (t \<in> T \<and> U \<subseteq> X)"
proof
  assume *: "cone t U \<subseteq> T"
  show "t \<in> T \<and> U \<subseteq> X"
  proof (intro conjI subsetI)
    from tip_in_cone * show "t \<in> T" ..
  next
    fix x
    assume "x \<in> U"
    hence "Poly_Mapping.single x 1 \<in> .[U]" by (rule PPs_closed_single)
    with refl have "Poly_Mapping.single x 1 + t \<in> cone t U" by (rule coneI)
    also note *
    also from assms have "T \<subseteq> .[X]" by (rule ideal_likeD)
    finally have "Poly_Mapping.single x 1 + t \<in> .[X]" .
    hence "Poly_Mapping.single x 1 + t - t \<in> .[X]" by (rule PPs_closed_minus)
    thus "x \<in> X" by (simp add: PPs_def)
  qed
next
  assume "t \<in> T \<and> U \<subseteq> X"
  hence "t \<in> T" and "U \<subseteq> X" by simp_all
  show "cone t U \<subseteq> T"
  proof
    fix s
    assume "s \<in> cone t U"
    also from \<open>U \<subseteq> X\<close> have "... \<subseteq> cone t X" by (rule cone_mono_2)
    finally obtain s' where "s' \<in> .[X]" and s: "s = s' + t" by (rule coneE)
    from assms this(1) \<open>t \<in> T\<close> show "s \<in> T" unfolding s by (rule ideal_likeD)
  qed
qed

(* OBSOLETE? *)
lemma ideal_like_generated:
  assumes "finite X" and "ideal_like T"
  obtains S where "finite S" and "S \<subseteq> T" and "T = (\<Union>s\<in>S. cone s X)"
proof -
  have refl: "reflp ((adds)::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> _)" by (simp add: reflp_def)
  define m where "m = Max (elem_index ` X)"
  from assms(2) have "T \<subseteq> .[X]" by (rule ideal_likeD)
  also have "... \<subseteq> {t. varnum t \<le> Suc m}" (is "_ \<subseteq> ?Y")
  proof
    fix t
    assume "t \<in> .[X]"
    from assms(1) have fin: "finite (elem_index ` X)" by (rule finite_imageI)
    {
      fix x
      assume "x \<in> keys t"
      moreover from \<open>t \<in> .[X]\<close> have "keys t \<subseteq> X" by (rule PPsD)
      ultimately have "x \<in> X" ..
      hence "elem_index x \<in> elem_index ` X" by (rule imageI)
      with fin have "elem_index x \<le> m" unfolding m_def by (rule Max_ge)
    }
    hence "varnum t \<le> Suc m" by (simp add: varnum_def)
    thus "t \<in> ?Y" by simp
  qed
  finally have "T \<subseteq> ?Y" .
  moreover from dickson_grading_varnum have "almost_full_on (adds) ?Y"
    by (rule dickson_gradingD2)
  ultimately have "almost_full_on (adds) T" by (rule almost_full_on_subset)
  with refl obtain S where "finite S" and "S \<subseteq> T" and 1: "\<And>t. t \<in> T \<Longrightarrow> (\<exists>s\<in>S. s adds t)"
    by (rule almost_full_on_finite_subsetE, blast)
  from this(1, 2) show ?thesis
  proof
    show "T = (\<Union>s\<in>S. cone s X)"
    proof (rule Set.set_eqI)
      fix t
      show "t \<in> T \<longleftrightarrow> t \<in> (\<Union>s\<in>S. cone s X)"
      proof
        assume "t \<in> T"
        hence "\<exists>s\<in>S. s adds t" by (rule 1)
        then obtain s where "s \<in> S" and "s adds t" ..
        have "t \<in> cone s X"
        proof (rule coneI)
          from \<open>s adds t\<close> show "t = (t - s) + s" by (simp only: adds_minus)
        next
          from \<open>t \<in> T\<close> \<open>T \<subseteq> .[X]\<close> have "t \<in> .[X]" ..
          thus "t - s \<in> .[X]" by (rule PPs_closed_minus)
        qed
        with \<open>s \<in> S\<close> show "t \<in> (\<Union>s\<in>S. cone s X)" ..
      next
        assume "t \<in> (\<Union>s\<in>S. cone s X)"
        then obtain s where "s \<in> S" and "t \<in> cone s X" ..
        from this(2) obtain s' where "s' \<in> .[X]" and t: "t = s' + s" by (rule coneE)
        note assms(2) this(1)
        moreover from \<open>s \<in> S\<close> \<open>S \<subseteq> T\<close> have "s \<in> T" ..
        ultimately show "t \<in> T" unfolding t by (rule ideal_likeD)
      qed
    qed
  qed
qed

lemma ideal_like_image_minus_iff:
  assumes "ideal_like I" and "t \<in> .[X]"
  shows "s \<in> (\<lambda>s. s - t) ` I \<longleftrightarrow> s + t \<in> I"
proof
  assume "s \<in> (\<lambda>s. s - t) ` I"
  then obtain s' where "s' \<in> I" and s: "s = s' - t" ..
  have "s' adds s + t"
  proof (rule adds_poly_mappingI)
    show "lookup s' \<le> lookup (s + t)" unfolding le_fun_def
    proof
      fix x
      from s have "lookup s x = lookup (s' - t) x" by simp
      thus "lookup s' x \<le> lookup (s + t) x" by (simp add: lookup_minus lookup_add)
    qed
  qed
  hence eq: "(s + t - s') + s' = s + t" by (rule adds_minus)
  from assms(1) have "I \<subseteq> .[X]" by (rule ideal_likeD)
  with \<open>s' \<in> I\<close> have "s' \<in> .[X]" ..
  hence "s \<in> .[X]" unfolding s by (rule PPs_closed_minus)
  hence "s + t \<in> .[X]" using assms(2) by (rule PPs_closed_plus)
  hence "s + t - s' \<in> .[X]" by (rule PPs_closed_minus)
  with assms(1) have "(s + t - s') + s' \<in> I" using \<open>s' \<in> I\<close> by (rule ideal_likeD)
  thus "s + t \<in> I" by (simp only: eq)
next
  assume "s + t \<in> I"
  hence "(s + t) - t \<in> (\<lambda>s. s - t) ` I" by (rule imageI)
  thus "s \<in> (\<lambda>s. s - t) ` I" by simp
qed

lemma ideal_like_cone_iff: "ideal_like (cone t U) \<longleftrightarrow> (t \<in> .[X] \<and> U = X)"
proof
  assume *: "ideal_like (cone t U)"
  hence **: "cone t U \<subseteq> .[X]" by (rule ideal_likeD)
  also have "\<dots> = cone 0 X" by simp
  finally have "U \<subseteq> X" by (rule cone_subsetD)
  moreover have "X \<subseteq> U"
  proof (rule cone_subsetD)
    have ".[X] \<subseteq> .[U]"
    proof
      fix s
      assume "s \<in> .[X]"
      with * have "s + t \<in> cone t U" using tip_in_cone by (rule ideal_likeD)
      then obtain s' where "s' \<in> .[U]" and "s + t = s' + t" by (rule coneE)
      from this(2) have "s = s'" by simp
      with \<open>s' \<in> .[U]\<close> show "s \<in> .[U]" by simp
    qed
    thus "cone 0 X \<subseteq> cone 0 U" by simp
  qed
  ultimately have "U = X" ..
  moreover from tip_in_cone ** have "t \<in> .[X]" ..
  ultimately show "t \<in> .[X] \<and> U = X" by simp
next
  assume "t \<in> .[X] \<and> U = X"
  hence "t \<in> .[X]" and "U = X" by simp_all
  show "ideal_like (cone t U)" unfolding \<open>U = X\<close>
  proof (rule ideal_likeI)
    have "cone t X = cone (t + 0) X" by simp
    also from \<open>t \<in> .[X]\<close> have "\<dots> \<subseteq> cone 0 X" by (rule cone_mono_1)
    thus "cone t X \<subseteq> .[X]" by simp
  next
    fix s s'
    assume "s \<in> .[X]"
    assume "s' \<in> cone t X"
    then obtain s'' where "s'' \<in> .[X]" and "s' = s'' + t" by (rule coneE)
    from this(2) have "s + s' = s + s'' + t" by (simp only: add.assoc)
    moreover from \<open>s \<in> .[X]\<close> \<open>s'' \<in> .[X]\<close> have "s + s'' \<in> .[X]" by (rule PPs_closed_plus)
    ultimately show "s + s' \<in> cone t X" by (rule coneI)
  qed
qed

corollary ideal_like_PPs_iff: "ideal_like .[U] \<longleftrightarrow> U = X"
proof -
  have "ideal_like .[U] = ideal_like (cone 0 U)" by simp
  also have "\<dots> = (0 \<in> .[X] \<and> U = X)" by (simp only: ideal_like_cone_iff)
  also have "\<dots> = (U = X)" by (simp add: zero_in_PPs)
  finally show ?thesis .
qed

lemma ideal_like_UN:
  assumes "\<And>a. a \<in> A \<Longrightarrow> ideal_like (I a)"
  shows "ideal_like (\<Union> (I ` A))"
proof (rule ideal_likeI)
  show "\<Union> (I ` A) \<subseteq> .[X]"
  proof
    fix t
    assume "t \<in> \<Union> (I ` A)"
    then obtain a where "a \<in> A" and "t \<in> I a" ..
    from this(1) have "ideal_like (I a)" by (rule assms)
    hence "I a \<subseteq> .[X]" by (rule ideal_likeD)
    with \<open>t \<in> I a\<close> show "t \<in> .[X]" ..
  qed
next
  fix s t
  assume "s \<in> .[X]"
  assume "t \<in> \<Union> (I ` A)"
  then obtain a where "a \<in> A" and "t \<in> I a" ..
  from this(1) have "ideal_like (I a)" by (rule assms)
  hence "s + t \<in> I a" using \<open>s \<in> .[X]\<close> \<open>t \<in> I a\<close> by (rule ideal_likeD)
  with \<open>a \<in> A\<close> show "s + t \<in> \<Union> (I ` A)" ..
qed

corollary ideal_like_Un:
  assumes "ideal_like I1" and "ideal_like I2"
  shows "ideal_like (I1 \<union> I2)"
proof -
  have "ideal_like (\<Union> (id ` {I1, I2}))" by (rule ideal_like_UN) (auto simp: assms)
  thus ?thesis by simp
qed

subsection \<open>Splitting w.r.t. Ideal-like Sets\<close>

definition splits_wrt :: "((('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<times> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set) \<Rightarrow>
                          ('x \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> bool"
  where "splits_wrt PQ T I \<longleftrightarrow> cone_decomp T (fst PQ \<union> snd PQ) \<and> ideal_like I \<and>
                                (\<forall>(t, U)\<in>fst PQ. cone t U \<subseteq> I) \<and> (\<forall>(t, U)\<in>snd PQ. U \<subseteq> X \<and> cone t U \<inter> I = {})"

lemma splits_wrtI:
  assumes "cone_decomp T (P \<union> Q)" and "ideal_like I"
    and "\<And>t U. (t, U) \<in> P \<Longrightarrow> U \<subseteq> X" and "\<And>t U. (t, U) \<in> P \<Longrightarrow> t \<in> I"
    and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X" and "\<And>t U s. (t, U) \<in> Q \<Longrightarrow> s \<in> cone t U \<Longrightarrow> s \<in> I \<Longrightarrow> False"
  shows "splits_wrt (P, Q) T I"
  unfolding splits_wrt_def fst_conv snd_conv
proof (intro conjI ballI)
  fix p
  assume "p \<in> P"
  moreover obtain t U where p: "p = (t, U)" using prod.exhaust by blast
  ultimately have "(t, U) \<in> P" by simp
  hence "U \<subseteq> X" and "t \<in> I" by (rule assms)+
  have "cone t U \<subseteq> I"
  proof
    fix s
    assume "s \<in> cone t U"
    then obtain s' where "s' \<in> .[U]" and s: "s = s' + t" by (rule coneE)
    from \<open>U \<subseteq> X\<close> have ".[U] \<subseteq> .[X]" by (rule PPs_mono)
    with \<open>s' \<in> .[U]\<close> have "s' \<in> .[X]" ..
    with assms(2) show "s \<in> I" unfolding s using \<open>t \<in> I\<close> by (rule ideal_likeD)
  qed
  thus "case p of (t, U) \<Rightarrow> cone t U \<subseteq> I" by (simp add: p)
next
  fix q
  assume "q \<in> Q"
  moreover obtain t U where q: "q = (t, U)" using prod.exhaust by blast
  ultimately have "(t, U) \<in> Q" by simp
  hence "U \<subseteq> X" and "\<And>s. s \<in> cone t U \<Longrightarrow> s \<in> I \<Longrightarrow> False" by (rule assms)+
  thus "case q of (t, U) \<Rightarrow> U \<subseteq> X \<and> cone t U \<inter> I = {}" by (fastforce simp: q)
qed (fact assms)+

lemma splits_wrtD:
  assumes "splits_wrt (P, Q) T I"
  shows "cone_decomp T (P \<union> Q)" and "ideal_like I" and "\<And>t U. (t, U) \<in> P \<Longrightarrow> cone t U \<subseteq> I"
    and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X" and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> cone t U \<inter> I = {}"
  using assms by (fastforce simp: splits_wrt_def)+

lemma splits_wrt_finite_decomp:
  assumes "finite X" and "splits_wrt (P, Q) T I"
  shows "finite_decomp P" and "finite_decomp Q" and "finite_decomp (P \<union> Q)"
proof -
  from assms(2) have "cone_decomp T (P \<union> Q)" by (rule splits_wrtD)
  hence "finite (P \<union> Q)" by (rule cone_decompD)
  hence "finite P" and "finite Q" by simp_all
  from this(1) show "finite_decomp P"
  proof (rule finite_decompI)
    fix t U
    assume "(t, U) \<in> P"
    with assms(2) have "cone t U \<subseteq> I" by (rule splits_wrtD)
    moreover from assms(2) have "ideal_like I" by (rule splits_wrtD)
    ultimately have "U \<subseteq> X" by (simp only: cone_subset_ideal_like_iff)
    thus "finite U" using assms(1) by (rule finite_subset)
  qed
  moreover from \<open>finite Q\<close> show "finite_decomp Q"
  proof (rule finite_decompI)
    fix t U
    assume "(t, U) \<in> Q"
    with assms(2) have "U \<subseteq> X" by (rule splits_wrtD)
    thus "finite U" using assms(1) by (rule finite_subset)
  qed
  ultimately show "finite_decomp (P \<union> Q)" by (rule finite_decomp_Un)
qed

lemma splits_wrt_cone_decomp_1:
  assumes "splits_wrt (P, Q) T I"
  shows "cone_decomp (T \<inter> I) P"
proof -
  from assms have *: "cone_decomp T (P \<union> Q)" by (rule splits_wrtD)
  show ?thesis
  proof (rule cone_decompI)
    from * have "finite (P \<union> Q)" by (rule cone_decompD)
    thus "finite P" by simp
  next
    have "cone t U \<inter> I = cone t U" if "(t, U) \<in> P" for t U
    proof -
      from assms that have "cone t U \<subseteq> I" by (rule splits_wrtD)
      thus ?thesis by (rule Int_absorb2)
    qed
    hence eq1: "(\<Union>(t, U)\<in>P. cone t U \<inter> I) = (\<Union>(t, U)\<in>P. cone t U)" by blast
    have "cone t U \<inter> I = {}" if "(t, U) \<in> Q" for t U using assms that by (rule splits_wrtD)
    hence eq2: "(\<Union>(t, U)\<in>Q. cone t U \<inter> I) = {}" by blast
    from * have "T = (\<Union>(t, U)\<in>P\<union>Q. cone t U)" by (rule cone_decompD)
    hence "T \<inter> I = (\<Union>(t, U)\<in>P. cone t U \<inter> I) \<union> (\<Union>(t, U)\<in>Q. cone t U \<inter> I)" by blast
    also have "... = (\<Union>(t, U)\<in>P. cone t U)" by (simp only: eq1 eq2 Un_empty_right)
    finally show "T \<inter> I = (\<Union>(t, U)\<in>P. cone t U)" .
  next
    fix t1 t2 :: "'x \<Rightarrow>\<^sub>0 nat" and U1 U2 s
    assume s1: "s \<in> cone t1 U1" and s2: "s \<in> cone t2 U2"
    assume "(t1, U1) \<in> P" and "(t2, U2) \<in> P"
    hence "(t1, U1) \<in> P \<union> Q" and "(t2, U2) \<in> P \<union> Q" by simp_all
    with * show "(t1, U1) = (t2, U2)" using s1 s2 by (rule cone_decompD)
  qed
qed

lemma splits_wrt_cone_decomp_2:
  assumes "splits_wrt (P, Q) T I"
  shows "cone_decomp (T - I) Q"
proof -
  from assms have *: "cone_decomp T (P \<union> Q)" by (rule splits_wrtD)
  show ?thesis
  proof (rule cone_decompI)
    from * have "finite (P \<union> Q)" by (rule cone_decompD)
    thus "finite Q" by simp
  next
    have "cone t U - I = {}" if "(t, U) \<in> P" for t U
    proof -
      from assms that have "cone t U \<subseteq> I" by (rule splits_wrtD)
      thus ?thesis by (simp only: Diff_eq_empty_iff)
    qed
    hence eq1: "(\<Union>(t, U)\<in>P. cone t U - I) = {}" by blast
    have "cone t U - I = cone t U" if "(t, U) \<in> Q" for t U
    proof -
      from assms that have "cone t U \<inter> I = {}" by (rule splits_wrtD)
      thus ?thesis by (rule Diff_triv)
    qed
    hence eq2: "(\<Union>(t, U)\<in>Q. cone t U - I) = (\<Union>(t, U)\<in>Q. cone t U)" by blast
    from * have "T = (\<Union>(t, U)\<in>P\<union>Q. cone t U)" by (rule cone_decompD)
    hence "T - I = (\<Union>(t, U)\<in>P. cone t U - I) \<union> (\<Union>(t, U)\<in>Q. cone t U - I)" by blast
    also have "... = (\<Union>(t, U)\<in>Q. cone t U)" by (simp only: eq1 eq2 Un_empty_left)
    finally show "T - I = (\<Union>(t, U)\<in>Q. cone t U)" .
  next
    fix t1 t2 :: "'x \<Rightarrow>\<^sub>0 nat" and U1 U2 s
    assume s1: "s \<in> cone t1 U1" and s2: "s \<in> cone t2 U2"
    assume "(t1, U1) \<in> Q" and "(t2, U2) \<in> Q"
    hence "(t1, U1) \<in> P \<union> Q" and "(t2, U2) \<in> P \<union> Q" by simp_all
    with * show "(t1, U1) = (t2, U2)" using s1 s2 by (rule cone_decompD)
  qed
qed

lemma lem_4_2_1:
  assumes "ideal_like I" and "U \<subseteq> X" and "t \<in> .[X]" and "(\<lambda>s. s - t) ` I = (\<Union>f\<in>F. cone f X)"
  shows "cone t U \<subseteq> I \<longleftrightarrow> 0 \<in> F"
proof -
  from assms(1, 2) have "cone t U \<subseteq> I \<longleftrightarrow> t \<in> I" by (simp add: cone_subset_ideal_like_iff)
  also from assms(1, 3) have "... \<longleftrightarrow> 0 \<in> (\<lambda>s. s - t) ` I" by (simp add: ideal_like_image_minus_iff)
  also have "... \<longleftrightarrow> 0 \<in> F" by (simp add: assms(4) zero_in_cone_iff)
  finally show ?thesis .
qed

lemma lem_4_2_2:
  assumes "ideal_like I" and "U \<subseteq> X" and "t \<in> .[X]" and "(\<lambda>s. s - t) ` I = (\<Union>f\<in>F. cone f X)"
  shows "cone t U \<inter> I = {} \<longleftrightarrow> F \<inter> .[U] = {}"
proof
  assume *: "cone t U \<inter> I = {}"
  {
    fix s
    assume "s \<in> F"
    hence "s \<in> (\<lambda>s. s - t) ` I" unfolding assms(4) using tip_in_cone ..
    with assms(1, 3) have "s + t \<in> I" by (simp add: ideal_like_image_minus_iff)
    assume "s \<in> .[U]"
    with refl have "s + t \<in> cone t U" by (rule coneI)
    with * have "s + t \<notin> I" by blast
    hence False using \<open>s + t \<in> I\<close> ..
  }
  thus "F \<inter> .[U] = {}" by blast
next
  assume *: "F \<inter> .[U] = {}"
  {
    fix s
    assume "s \<in> cone t U"
    then obtain s' where "s' \<in> .[U]" and s: "s = s' + t" by (rule coneE)
    assume "s \<in> I"
    with assms(1, 3) have "s' \<in> (\<lambda>s. s - t) ` I" by (simp add: s ideal_like_image_minus_iff)
    then obtain f where "f \<in> F" and "s' \<in> cone f X" unfolding assms(4) ..
    from this(2) obtain f' where s': "s' = f' + f" by (rule coneE)
    from \<open>s' \<in> .[U]\<close> have "s' - f' \<in> .[U]" by (rule PPs_closed_minus)
    hence "f \<in> .[U]" by (simp add: s')
    with \<open>f \<in> F\<close> * have False by blast
  }
  thus "cone t U \<inter> I = {}" by blast
qed
end (* theory *)
