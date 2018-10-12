section \<open>Cone Decompositions\<close>

theory Cone_Decomposition
  imports Poly_Fun General_Utils MPoly_PM
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

lemma finite_decomp_image: "finite_decomp P \<Longrightarrow> finite_decomp (apfst f ` P)"
  by (auto dest: finite_decompD intro!: finite_decompI)

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

lemma pos_decomp_subset: "P\<^sub>+ \<subseteq> P"
  unfolding pos_decomp_def by blast

lemma pos_decomp_Un: "(P \<union> Q)\<^sub>+ = P\<^sub>+ \<union> Q\<^sub>+"
  by (fastforce simp: pos_decomp_def)

lemma pos_decomp_UN: "(\<Union> A)\<^sub>+ = (\<Union> (pos_decomp ` A))"
  by (fastforce simp: pos_decomp_def)

lemma pos_decomp_image: "(apfst f ` P)\<^sub>+ = apfst f ` P\<^sub>+"
  by (auto simp: pos_decomp_def)

lemma card_Diff_pos_decomp: "card {(t, U) \<in> Q - Q\<^sub>+. P t} = card {t. (t, {}) \<in> Q \<and> P t}"
proof -
  have "{t. (t, {}) \<in> Q \<and> P t} = fst ` {(t, U) \<in> Q - Q\<^sub>+. P t}"
    by (auto simp: pos_decomp_def image_Collect)
  also have "card \<dots> = card {(t, U) \<in> Q - Q\<^sub>+. P t}"
    by (rule card_image, auto simp: pos_decomp_def intro: inj_onI)
  finally show ?thesis by (rule sym)
qed

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
  shows "k = Min (deg_pm ` fst ` P\<^sub>+)"
proof -
  define m where "m = Min (deg_pm ` fst ` P\<^sub>+)"
  from assms(1) have "finite P" by (rule finite_decompD)
  hence "finite (P\<^sub>+)" by (simp add: pos_decomp_def)
  hence "finite (deg_pm ` fst ` P\<^sub>+)" by (intro finite_imageI)
  moreover from assms(3) have "deg_pm ` fst ` P\<^sub>+ \<noteq> {}" by simp
  ultimately have "m \<in> deg_pm ` fst ` P\<^sub>+" unfolding m_def by (rule Min_in)
  then obtain t U where "(t, U) \<in> P\<^sub>+" and m: "m = deg_pm t" by fastforce
  have m_min: "m \<le> deg_pm t'" if "(t', U') \<in> P\<^sub>+" for t' U'
  proof -
    from that have "deg_pm (fst (t', U')) \<in> deg_pm ` fst ` P\<^sub>+" by (intro imageI)
    with \<open>finite (deg_pm ` fst ` P\<^sub>+)\<close> have "m \<le> deg_pm (fst (t', U'))"
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

corollary ideal_like_image_plus_minus_subset:
  assumes "ideal_like I" and "t \<in> .[X]"
  shows "(+) t ` (\<lambda>s. s - t) ` I \<subseteq> I"
proof
  fix v
  assume "v \<in> (+) t ` (\<lambda>s. s - t) ` I"
  then obtain s where "s \<in> (\<lambda>s. s - t) ` I" and v: "v = t + s" ..
  from assms this(1) have "s + t \<in> I" by (simp only: ideal_like_image_minus_iff)
  thus "v \<in> I" by (simp only: v add.commute)
qed

corollary ideal_like_image_plus_minus_superset:
  assumes "ideal_like I" and "t \<in> .[X]"
  shows "I \<inter> cone t X \<subseteq> (+) t ` (\<lambda>s. s - t) ` I"
proof
  fix v
  assume "v \<in> I \<inter> cone t X"
  hence "v \<in> I" and "v \<in> cone t X" by simp_all
  from this(2) obtain s where "s \<in> .[X]" and v: "v = s + t" by (rule coneE)
  from \<open>v \<in> I\<close> have "s + t \<in> I" by (simp only: v)
  with assms have "s \<in> (\<lambda>s. s - t) ` I" by (simp only: ideal_like_image_minus_iff)
  thus "v \<in> (+) t ` (\<lambda>s. s - t) ` I" by (rule rev_image_eqI) (simp only: v add.commute)
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

subsection \<open>Function \<open>split\<close>\<close>

definition max_subset :: "'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set"
  where "max_subset A P = (ARG_MAX card B. B \<subseteq> A \<and> P B)"

lemma max_subset:
  assumes "finite A" and "B \<subseteq> A" and "P B"
  shows "max_subset A P \<subseteq> A" (is ?thesis1)
    and "P (max_subset A P)" (is ?thesis2)
    and "card B \<le> card (max_subset A P)" (is ?thesis3)
proof -
  from assms(2, 3) have "B \<subseteq> A \<and> P B" by simp
  moreover have "\<forall>C. C \<subseteq> A \<and> P C \<longrightarrow> card C < Suc (card A)"
  proof (intro allI impI, elim conjE)
    fix C
    assume "C \<subseteq> A"
    with assms(1) have "card C \<le> card A" by (rule card_mono)
    thus "card C < Suc (card A)" by simp
  qed
  ultimately have "?thesis1 \<and> ?thesis2" and ?thesis3 unfolding max_subset_def
    by (rule arg_max_natI, rule arg_max_nat_le)
  thus ?thesis1 and ?thesis2 and ?thesis3 by simp_all
qed

function (domintros) split :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) set \<Rightarrow>
                                (((('x \<Rightarrow>\<^sub>0 nat) \<times> ('x set)) set) \<times> ((('x \<Rightarrow>\<^sub>0 nat) \<times> ('x set)) set))"
  where
    "split t U F =
      (if 0 \<in> F then
        ({(t, U)}, {})
      else if F \<inter> .[U] = {} then
        ({}, {(t, U)})
      else
        let x = SOME x'. x' \<in> U - (max_subset U (\<lambda>V. F \<inter> .[V] = {}));
            (P0, Q0) = split t (U - {x}) F;
            (P1, Q1) = split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) in
          (P0 \<union> P1, Q0 \<union> Q1))"
  by auto

text \<open>Function @{const split} is not executable, because this is not necessary.
  With some effort, it could be made executable, though.\<close>

lemma split_domI':
  assumes "finite X" and "fst (snd args) \<subseteq> X" and "finite (snd (snd args))"
  shows "split_dom args"
proof -
  let ?m = "\<lambda>args'. card (fst (snd args')) + sum deg_pm (snd (snd args'))"
  from wf_measure[of ?m] assms(2, 3) show ?thesis
  proof (induct args)
    case (less args)
    obtain t U F where args: "args = (t, U, F)" using prod.exhaust by metis
    from less.prems have "U \<subseteq> X" and "finite F" by (simp_all only: args fst_conv snd_conv)
    from this(1) assms(1) have "finite U" by (rule finite_subset)
    have IH: "split_dom (t', U', F')"
      if "U' \<subseteq> X" and "finite F'" and "card U' + sum deg_pm F' < card U + sum deg_pm F"
      for t' U' F'
      using less.hyps that by (simp add: args)

    define S where "S = max_subset U (\<lambda>V. F \<inter> .[V] = {})"
    define x where "x = (SOME x'. x' \<in> U \<and> x' \<notin> S)"
    show ?case unfolding args
    proof (rule split.domintros, simp_all only: x_def[symmetric] S_def[symmetric])
      fix f
      assume "0 \<notin> F" and "f \<in> F" and "f \<in> .[U]"
      from this(1) have "F \<inter> .[{}] = {}" by simp
      with \<open>finite U\<close> empty_subsetI have "S \<subseteq> U" and "F \<inter> .[S] = {}"
        unfolding S_def by (rule max_subset)+
      have "x \<in> U \<and> x \<notin> S" unfolding x_def
      proof (rule someI_ex)
        from \<open>f \<in> F\<close> \<open>f \<in> .[U]\<close> \<open>F \<inter> .[S] = {}\<close> have "S \<noteq> U" by blast
        with \<open>S \<subseteq> U\<close> show "\<exists>y. y \<in> U \<and> y \<notin> S" by blast
      qed
      hence "x \<in> U" and "x \<notin> S" by simp_all
      {
        assume "\<not> split_dom (t, U - {x}, F)"
        moreover from _ \<open>finite F\<close> have "split_dom (t, U - {x}, F)"
        proof (rule IH)
          from \<open>U \<subseteq> X\<close> show "U - {x} \<subseteq> X" by blast
        next
          from \<open>finite U\<close> \<open>x \<in> U\<close> have "card (U - {x}) < card U" by (rule card_Diff1_less)
          thus "card (U - {x}) + sum deg_pm F < card U + sum deg_pm F" by simp
        qed
        ultimately show False ..
      }
      {
        let ?args = "(Poly_Mapping.single x (Suc 0) + t, U, (\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F)"
        assume "\<not> split_dom ?args"
        moreover from \<open>U \<subseteq> X\<close> have "split_dom ?args"
        proof (rule IH)
          from \<open>finite F\<close> show "finite ((\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F)"
            by (rule finite_imageI)
        next
          have "sum deg_pm ((\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F) \<le>
                sum (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) F"
            using \<open>finite F\<close> by (rule sum_image_le) simp
          also from \<open>finite F\<close> have "\<dots> < sum deg_pm F"
          proof (rule sum_strict_mono_ex1)
            show "\<forall>f\<in>F. (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) f \<le> deg_pm f"
              by (simp add: deg_pm_minus_le)
          next
            show "\<exists>f\<in>F. (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) f < deg_pm f"
            proof (rule ccontr)
              assume *: "\<not> (\<exists>f\<in>F. (deg_pm \<circ> (\<lambda>f. f - Poly_Mapping.single x (Suc 0))) f < deg_pm f)"
              note \<open>finite U\<close>
              moreover from \<open>x \<in> U\<close> \<open>S \<subseteq> U\<close> have "insert x S \<subseteq> U" by (rule insert_subsetI)
              moreover have "F \<inter> .[insert x S] = {}"
              proof -
                {
                  fix s
                  assume "s \<in> F"
                  with * have "\<not> deg_pm (s - Poly_Mapping.single x (Suc 0)) < deg_pm s" by simp
                  with deg_pm_minus_le[of s "Poly_Mapping.single x (Suc 0)"]
                  have "deg_pm (s - Poly_Mapping.single x (Suc 0)) = deg_pm s" by simp
                  hence "keys s \<inter> keys (Poly_Mapping.single x (Suc 0)) = {}"
                    by (simp only: deg_pm_minus_id_iff)
                  hence "x \<notin> keys s" by simp
                  moreover assume "s \<in> .[insert x S]"
                  ultimately have "s \<in> .[S]"
                  by (fastforce simp add: PPs_def simp del: not_in_keys_iff_lookup_eq_zero)
                  with \<open>s \<in> F\<close> \<open>F \<inter> .[S] = {}\<close> have False by blast
                }
                thus ?thesis by blast
              qed
              ultimately have "card (insert x S) \<le> card S" unfolding S_def by (rule max_subset)
              moreover from \<open>S \<subseteq> U\<close> \<open>finite U\<close> have "finite S" by (rule finite_subset)
              ultimately show False using \<open>x \<notin> S\<close> by simp
            qed
          qed
          finally show "card U + sum deg_pm ((\<lambda>f. f - monomial (Suc 0) x) ` F) < card U + sum deg_pm F"
            by simp
        qed
        ultimately show False ..
      }
    qed
  qed
qed

corollary split_domI: "finite X \<Longrightarrow> U \<subseteq> X \<Longrightarrow> finite F \<Longrightarrow> split_dom (t, U, F)"
  using split_domI'[of "(t, U, F)"] by simp

lemma split_empty:
  assumes "finite X" and "U \<subseteq> X"
  shows "split t U {} = ({}, {(t, U)})"
proof -
  have "finite {}" ..
  with assms have "split_dom (t, U, {})" by (rule split_domI)
  thus ?thesis by (simp add: split.psimps)
qed

lemma split_induct [consumes 3, case_names base1 base2 step]:
  fixes P :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow> _"
  assumes "finite X" and "U \<subseteq> X" and "finite F"
  assumes "\<And>t U F. U \<subseteq> X \<Longrightarrow> finite F \<Longrightarrow> 0 \<in> F \<Longrightarrow> P t U F ({(t, U)}, {})"
  assumes "\<And>t U F. U \<subseteq> X \<Longrightarrow> finite F \<Longrightarrow> 0 \<notin> F \<Longrightarrow> F \<inter> .[U] = {} \<Longrightarrow> P t U F ({}, {(t, U)})"
  assumes "\<And>t U F S x P0 P1 Q0 Q1. U \<subseteq> X \<Longrightarrow> finite F \<Longrightarrow> 0 \<notin> F \<Longrightarrow> F \<inter> .[U] \<noteq> {} \<Longrightarrow> S \<subseteq> U \<Longrightarrow>
              F \<inter> .[S] = {} \<Longrightarrow> (\<And>S'. S' \<subseteq> U \<Longrightarrow> F \<inter> .[S'] = {} \<Longrightarrow> card S' \<le> card S) \<Longrightarrow>
              x \<in> U \<Longrightarrow> x \<notin> S \<Longrightarrow> S = max_subset U (\<lambda>V. F \<inter> .[V] = {}) \<Longrightarrow> x = (SOME x'. x' \<in> U - S) \<Longrightarrow>
              (P0, Q0) = split t (U - {x}) F \<Longrightarrow>
              (P1, Q1) = split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) \<Longrightarrow>
              split t U F = (P0 \<union> P1, Q0 \<union> Q1) \<Longrightarrow>
              P t (U - {x}) F (P0, Q0) \<Longrightarrow>
              P (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) (P1, Q1) \<Longrightarrow>
              P t U F (P0 \<union> P1, Q0 \<union> Q1)"
  shows "P t U F (split t U F)"
proof -
  from assms(1-3) have "split_dom (t, U, F)" by (rule split_domI)
  thus ?thesis using assms(2,3)
  proof (induct t U F rule: split.pinduct)
    case step: (1 t U F)
    from step(4) assms(1) have "finite U" by (rule finite_subset)
    define S where "S = max_subset U (\<lambda>V. F \<inter> .[V] = {})"
    define x where "x = (SOME x'. x' \<in> U \<and> x' \<notin> S)"
    show ?case
    proof (simp add: split.psimps[OF step(1)] S_def[symmetric] x_def[symmetric] split: prod.split, intro allI conjI impI)
      assume "0 \<in> F"
      with step(4, 5) show "P t U F ({(t, U)}, {})" by (rule assms(4))
      thus "P t U F ({(t, U)}, {})" .
    next
      assume "0 \<notin> F" and "F \<inter> .[U] = {}"
      with step(4, 5) show "P t U F ({}, {(t, U)})" by (rule assms(5))
    next
      fix P0 Q0 P1 Q1
      assume "split (Poly_Mapping.single x (Suc 0) + t) U ((\<lambda>f. f - Poly_Mapping.single x (Suc 0)) ` F) = (P1, Q1)"
      hence PQ1[symmetric]: "split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) = (P1, Q1)"
        by simp
      assume PQ0[symmetric]: "split t (U - {x}) F = (P0, Q0)"
      assume "F \<inter> .[U] \<noteq> {}" and "0 \<notin> F"
      from this(2) have "F \<inter> .[{}] = {}" by simp
      with \<open>finite U\<close> empty_subsetI have "S \<subseteq> U" and "F \<inter> .[S] = {}"
        unfolding S_def by (rule max_subset)+
      have S_max: "card S' \<le> card S" if "S' \<subseteq> U" and "F \<inter> .[S'] = {}" for S'
        using \<open>finite U\<close> that unfolding S_def by (rule max_subset)
      have "x \<in> U \<and> x \<notin> S" unfolding x_def
      proof (rule someI_ex)
        from \<open>F \<inter> .[U] \<noteq> {}\<close> \<open>F \<inter> .[S] = {}\<close> have "S \<noteq> U" by blast
        with \<open>S \<subseteq> U\<close> show "\<exists>y. y \<in> U \<and> y \<notin> S" by blast
      qed
      hence "x \<in> U" and "x \<notin> S" by simp_all
      from step(4, 5) \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close> \<open>S \<subseteq> U\<close> \<open>F \<inter> .[S] = {}\<close> S_max \<open>x \<in> U\<close> \<open>x \<notin> S\<close> S_def _ PQ0 PQ1
      show "P t U F (P0 \<union> P1, Q0 \<union> Q1)"
      proof (rule assms(6))
        show "P t (U - {x}) F (P0, Q0)"
          unfolding PQ0 using \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close> _ _ step(5)
        proof (rule step(2))
          from \<open>U \<subseteq> X\<close> show "U - {x} \<subseteq> X" by fastforce
        qed (simp add: x_def S_def)
      next
        show "P (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) (P1, Q1)"
          unfolding PQ1 using \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close> _ refl PQ0 \<open>U \<subseteq> X\<close>
        proof (rule step(3))
          from \<open>finite F\<close> show "finite ((\<lambda>f. f - Poly_Mapping.single x 1) ` F)" by (rule finite_imageI)
        qed (simp add: x_def S_def)
      next
        show "split t U F = (P0 \<union> P1, Q0 \<union> Q1)" using \<open>0 \<notin> F\<close> \<open>F \<inter> .[U] \<noteq> {}\<close>
          by (simp add: split.psimps[OF step(1)] Let_def flip: S_def x_def PQ0 PQ1 del: One_nat_def)
      qed (assumption+, simp add: x_def S_def)
    qed
  qed
qed

lemma finite_decomp_split:
  assumes "finite X" and "U \<subseteq> X" and "finite F"
  shows "finite_decomp (fst (split t U F))" and "finite_decomp (snd (split t U F))"
proof -
  from assms have "finite_decomp (fst (split t U F)) \<and> finite_decomp (snd (split t U F))"
  proof (induct t U F rule: split_induct)
    case (base1 t U F)
    from base1(1) assms(1) have "finite U" by (rule finite_subset)
    thus ?case by (simp add: finite_decomp_def)
  next
    case (base2 t U F)
    from base2(1) assms(1) have "finite U" by (rule finite_subset)
    thus ?case by (simp add: finite_decomp_def)
  next
    case (step t U F S x P0 P1 Q0 Q1)
    from step.hyps(15, 16) show ?case by (simp add: finite_decomp_Un)
  qed
  thus "finite_decomp (fst (split t U F))" and "finite_decomp (snd (split t U F))" by simp_all
qed

lemma split_splits_wrt:
  assumes "finite X" and "U \<subseteq> X" and "finite F" and "t \<in> .[X]"
    and "(\<lambda>s. s - t) ` I = (\<Union>f\<in>F. cone f X)" and "ideal_like I"
  shows "splits_wrt (split t U F) (cone t U) I"
  using assms(1-5)
proof (induct t U F rule: split_induct)
  case (base1 t U F)
  from base1(3) assms(6) \<open>U \<subseteq> X\<close> \<open>t \<in> .[X]\<close> have "cone t U \<subseteq> I"
    by (simp only: lem_4_2_1 base1(5))
  show ?case
  proof (rule splits_wrtI)
    fix t0 U0
    assume "(t0, U0) \<in> {(t, U)}"
    hence "t0 = t" by simp
    also have "... \<in> cone t U" by (fact tip_in_cone)
    also have "... \<subseteq> I" by fact
    finally show "t0 \<in> I" .
  qed (simp_all add: assms(6) cone_decomp_singleton \<open>U \<subseteq> X\<close>)
next
  case (base2 t U F)
  from base2(4) assms(6) \<open>U \<subseteq> X\<close> \<open>t \<in> .[X]\<close> have "cone t U \<inter> I = {}"
    by (simp only: lem_4_2_2 base2(6))
  show ?case
  proof (rule splits_wrtI)
    fix t0 U0 s
    assume "(t0, U0) \<in> {(t, U)}" and "s \<in> cone t0 U0"
    hence "s \<in> cone t U" by simp
    moreover assume "s \<in> I"
    ultimately have "s \<in> cone t U \<inter> I" by (rule IntI)
    also have "... = {}" by fact
    finally show False by simp
  qed (simp_all add: assms(6) cone_decomp_singleton \<open>U \<subseteq> X\<close>)
next
  case (step t U F S x P0 P1 Q0 Q1)
  from step.hyps(8) have U: "U = insert x (U - {x})" by blast
  also have "cone t ... = cone t (U - {x}) \<union> cone (Poly_Mapping.single x 1 + t) (insert x (U - {x}))"
    by (fact cone_insert)
  finally have eq: "cone t U = cone t (U - {x}) \<union> cone (Poly_Mapping.single x 1 + t) U" by simp

  from step.prems have 0: "splits_wrt (P0, Q0) (cone t ( U - {x})) I" by (rule step.hyps)
  have 1: "splits_wrt (P1, Q1) (cone (Poly_Mapping.single x 1 + t) U) I"
  proof (rule step.hyps)
    from step.hyps(8, 1) have "x \<in> X" ..
    hence "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
    thus "Poly_Mapping.single x 1 + t \<in> .[X]" using step.prems(1) by (rule PPs_closed_plus)
  next
    have "(\<lambda>s. s - (Poly_Mapping.single x 1 + t)) ` I = (\<lambda>s. s - Poly_Mapping.single x 1) ` (\<lambda>s. s - t) ` I"
      by (simp only: diff_diff_eq add.commute image_image)
    also have "\<dots> = (\<Union>f\<in>F. (\<lambda>s. s - Poly_Mapping.single x 1) ` cone f X)"
      by (simp only: step.prems(2) image_UN)
    also have "\<dots> = (\<Union>f\<in>(\<lambda>f. f - Poly_Mapping.single x 1) ` F. cone f X)"
      by (simp add: image_minus_cone)
    finally show "(\<lambda>s. s - (Poly_Mapping.single x 1 + t)) ` I =
                  (\<Union>f\<in>(\<lambda>f. f - Poly_Mapping.single x 1) ` F. cone f X)" .
  qed

  show ?case
  proof (rule splits_wrtI)
    have "cone t (U - {x}) \<inter> cone (Poly_Mapping.single x 1 + t) (insert x (U - {x})) = {}"
      by (rule cone_insert_disjoint) simp
    hence "cone t (U - {x}) \<inter> cone (Poly_Mapping.single x 1 + t) U = {}"
      by (simp only: U[symmetric])
    moreover from 0 have "cone_decomp (cone t (U - {x})) (P0 \<union> Q0)" by (rule splits_wrtD)
    moreover from 1 have "cone_decomp (cone (Poly_Mapping.single x 1 + t) U) (P1 \<union> Q1)"
      by (rule splits_wrtD)
    ultimately have "cone_decomp (cone t U) (P0 \<union> Q0 \<union> (P1 \<union> Q1))"
      unfolding eq by (rule cone_decomp_Un)
    thus "cone_decomp (cone t U) (P0 \<union> P1 \<union> (Q0 \<union> Q1))" by (simp only: ac_simps)
  next
    fix t0 U0
    assume "(t0, U0) \<in> P0 \<union> P1"
    hence "cone t0 U0 \<subseteq> I"
    proof
      assume "(t0, U0) \<in> P0"
      with 0 show ?thesis by (rule splits_wrtD)
    next
      assume "(t0, U0) \<in> P1"
      with 1 show ?thesis by (rule splits_wrtD)
    qed
    with assms(6) show "U0 \<subseteq> X" and "t0 \<in> I" by (simp_all only: cone_subset_ideal_like_iff)
  next
    fix t0 U0
    assume "(t0, U0) \<in> Q0 \<union> Q1"
    thus "U0 \<subseteq> X"
    proof
      assume "(t0, U0) \<in> Q0"
      with 0 show ?thesis by (rule splits_wrtD)
    next
      assume "(t0, U0) \<in> Q1"
      with 1 show ?thesis by (rule splits_wrtD)
    qed
    from \<open>(t0, U0) \<in> Q0 \<union> Q1\<close> have "cone t0 U0 \<inter> I = {}"
    proof
      assume "(t0, U0) \<in> Q0"
      with 0 show ?thesis by (rule splits_wrtD)
    next
      assume "(t0, U0) \<in> Q1"
      with 1 show ?thesis by (rule splits_wrtD)
    qed
    thus "\<And>s. s \<in> cone t0 U0 \<Longrightarrow> s \<in> I \<Longrightarrow> False" by blast
  qed (fact assms(6))
qed

lemma lem_4_5:
  assumes "finite X" and "U \<subseteq> X" and "finite F" and "t \<in> .[X]"
    and "(\<lambda>s. s - t) ` I = (\<Union>f\<in>F. cone f X)" and "ideal_like I"
  shows "cone t V \<subseteq> cone t U - I \<longleftrightarrow> V \<subseteq> U \<and> F \<inter> .[V] = {}"
proof
  assume "cone t V \<subseteq> cone t U - I"
  hence "cone t V \<subseteq> cone t U" and *: "cone t V \<inter> I = {}" by blast+
  from this(1) have "V \<subseteq> U" by (simp only: cone_subsetD)
  moreover have "F \<inter> .[V] = {}"
  proof
    show "F \<inter> .[V] \<subseteq> {}"
    proof
      fix f
      assume "f \<in> F \<inter> .[V]"
      hence "f \<in> F" and "f \<in> .[V]" by simp_all
      from refl this(2) have "f + t \<in> cone t V" by (rule coneI)
      with * have "f + t \<notin> I" by blast
      with assms(6, 4) have "f \<notin> (\<Union>f\<in>F. cone f X)"
        by (simp add: ideal_like_image_minus_iff assms(5)[symmetric])
      moreover from \<open>f \<in> F\<close> tip_in_cone have "f \<in> (\<Union>f\<in>F. cone f X)" by (rule UN_I)
      ultimately show "f \<in> {}" ..
    qed
  qed (fact empty_subsetI)
  ultimately show "V \<subseteq> U \<and> F \<inter> .[V] = {}" ..
next
  assume "V \<subseteq> U \<and> F \<inter> .[V] = {}"
  hence "V \<subseteq> U" and *: "F \<inter> .[V] = {}" by simp_all
  from this(1) have "cone t V \<subseteq> cone t U" by (rule cone_mono_2)
  moreover have "cone t V \<inter> I \<subseteq> {}"
  proof
    fix s
    assume "s \<in> cone t V \<inter> I"
    hence "s \<in> cone t V" and "s \<in> I" by simp_all
    from this(1) obtain v where "v \<in> .[V]" and s: "s = v + t" by (rule coneE)
    from \<open>s \<in> I\<close> have "s - t \<in> (\<lambda>s. s - t) ` I" by (rule imageI)
    also have "... = (\<Union>f\<in>F. cone f X)" by (fact assms(5))
    finally have "v \<in> (\<Union>f\<in>F. cone f X)" by (simp add: s)
    then obtain f where "f \<in> F" and "v \<in> cone f X" ..
    from this(2) obtain s' where "v = s' + f" by (rule coneE)
    with \<open>v \<in> .[V]\<close> have "s' + f \<in> .[V]" by (simp only:)
    hence "s' + f - s' \<in> .[V]" by (rule PPs_closed_minus)
    hence "f \<in> .[V]" by simp
    with \<open>f \<in> F\<close> * show "s \<in> {}" by blast
  qed
  ultimately show "cone t V \<subseteq> cone t U - I" by blast
qed

lemma lem_4_6:
  assumes "finite X" and "U \<subseteq> X" and "finite F" and "t \<in> .[X]"
    and "(\<lambda>s. s - t) ` I = (\<Union>f\<in>F. cone f X)" and "ideal_like I"
  assumes "cone t' V \<subseteq> cone t U - I"
  obtains V' where "(t, V') \<in> snd (split t U F)" and "card V \<le> card V'"
proof -
  assume *: "\<And>V'. (t, V') \<in> snd (split t U F) \<Longrightarrow> card V \<le> card V' \<Longrightarrow> thesis"
  from assms(7) have "cone t' V \<subseteq> cone t U" and "cone t' V \<inter> I = {}" by blast+
  from this(1) have "V \<subseteq> U" by (rule cone_subsetD)
  hence "cone t V \<subseteq> cone t U" by (rule cone_mono_2)
  moreover have "cone t V \<inter> I \<subseteq> {}"
  proof
    fix s
    assume "s \<in> cone t V \<inter> I"
    hence "s \<in> cone t V" and "s \<in> I" by simp_all
    from this(1) obtain s0 where "s0 \<in> .[V]" and s: "s = s0 + t" by (rule coneE)
    from tip_in_cone \<open>cone t' V \<subseteq> cone t U\<close> have "t' \<in> cone t U" ..
    then obtain s' where "s' \<in> .[U]" and t': "t' = s' + t" by (rule coneE)
    note this(1)
    also from assms(2) have ".[U] \<subseteq> .[X]" by (rule PPs_mono)
    finally have "s' \<in> .[X]" .
    have "s' + s = s0 + t'" by (simp add: s t' ac_simps)
    also from refl \<open>s0 \<in> .[V]\<close> have "\<dots> \<in> cone t' V" by (rule coneI)
    finally have "s' + s \<in> cone t' V" .
    moreover from assms(6) \<open>s' \<in> .[X]\<close> \<open>s \<in> I\<close> have "s' + s \<in> I" by (rule ideal_likeD)
    ultimately show "s \<in> {}" using \<open>cone t' V \<inter> I = {}\<close> by blast
  qed
  ultimately have "cone t V \<subseteq> cone t U - I" by blast
  with assms have "V \<subseteq> U" and "F \<inter> .[V] = {}" by (simp_all add: lem_4_5)
  with assms(1, 2, 3) show ?thesis using *
  proof (induct t U F arbitrary: V thesis rule: split_induct)
    case (base1 t U F)
    from base1.hyps(3) have "0 \<in> F \<inter> .[V]" using zero_in_PPs by (rule IntI)
    thus ?case by (simp add: base1.prems(2))
  next
    case (base2 t U F)
    show ?case
    proof (rule base2.prems)
      show "(t, U) \<in> snd ({}, {(t, U)})" by simp
    next
      from base2.hyps(1) assms(1) have "finite U" by (rule finite_subset)
      thus "card V \<le> card U" using base2.prems(1) by (rule card_mono)
    qed
  next
    case (step t U F S x P0 P1 Q0 Q1)
    from step.prems(1, 2) have 0: "card V \<le> card S" by (rule step.hyps)
    from step.hyps(5, 9) have "S \<subseteq> U - {x}" by blast
    then obtain V' where 1: "(t, V') \<in> snd (P0, Q0)" and 2: "card S \<le> card V'"
      using step.hyps(6) by (rule step.hyps)
    show ?case
    proof (rule step.prems)
      from 1 show "(t, V') \<in> snd (P0 \<union> P1, Q0 \<union> Q1)" by simp
    next
      from 0 2 show "card V \<le> card V'" by (rule le_trans)
    qed
  qed
qed

definition reduced_basis :: "('x \<Rightarrow>\<^sub>0 nat) set \<Rightarrow> bool"
  where "reduced_basis T \<longleftrightarrow> (\<forall>s\<in>T. \<forall>t\<in>T. s adds t \<longrightarrow> s = t)"

lemma reduced_basisI: "(\<And>s t. s \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> s adds t \<Longrightarrow> s = t) \<Longrightarrow> reduced_basis T"
  by (simp add: reduced_basis_def)

lemma reduced_basisD: "reduced_basis T \<Longrightarrow> s \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> s adds t \<Longrightarrow> s = t"
  by (simp add: reduced_basis_def)

lemma lem_4_7:
  assumes "finite X" and "I = (\<Union>f\<in>F. cone f X)" and "reduced_basis F" and "f \<in> F"
    and "cone_decomp I P"
  obtains U where "(f, U) \<in> P"
proof -
  from assms(4) tip_in_cone have "f \<in> (\<Union>f\<in>F. cone f X)" ..
  also from assms(5) have "\<dots> = (\<Union>(t, U)\<in>P. cone t U)" unfolding assms(2) by (rule cone_decompD)
  finally obtain t U where "(t, U) \<in> P" and "f \<in> cone t U" by blast
  from this(2) obtain s where "f = s + t" by (rule coneE)
  hence "t adds f" by simp
  from \<open>(t, U) \<in> P\<close> tip_in_cone have "t \<in> (\<Union>(t, U)\<in>P. cone t U)" by blast
  also have "\<dots> = (\<Union>f\<in>F. cone f X)"
    unfolding assms(2)[symmetric] by (rule sym, rule cone_decompD, fact)
  finally obtain f' where "f' \<in> F" and "t \<in> cone f' X" ..
  from this(2) obtain s' where "t = s' + f'" by (rule coneE)
  hence "f' adds t" by simp
  hence "f' adds f" using \<open>t adds f\<close> by (rule adds_trans)
  with assms(3) \<open>f' \<in> F\<close> assms(4) have "f' = f" by (rule reduced_basisD)
  with \<open>f' adds t\<close> have "f adds t" by simp
  with \<open>t adds f\<close> have "t = f" by (rule adds_antisym)
  with \<open>(t, U) \<in> P\<close> have "(f, U) \<in> P" by simp
  thus ?thesis ..
qed

lemma snd_splitI:
  assumes "finite X" and "U \<subseteq> X" and "finite F" and "0 \<notin> F"
  obtains V where "V \<subseteq> U" and "(t, V) \<in> snd (split t U F)"
  using assms
proof (induct t U F arbitrary: thesis rule: split_induct)
  case (base1 t U F)
  from base1.prems(2) base1.hyps(3) show ?case ..
next
  case (base2 t U F)
  from subset_refl show ?case by (rule base2.prems) simp
next
  case (step t U F S x P0 P1 Q0 Q1)
  from step.hyps(3) obtain V where 1: "V \<subseteq> U - {x}" and 2: "(t, V) \<in> snd (P0, Q0)"
    using step.hyps(15) by blast
  show ?case
  proof (rule step.prems)
    from 1 show "V \<subseteq> U" by blast
  next
    from 2 show "(t, V) \<in> snd (P0 \<union> P1, Q0 \<union> Q1)" by fastforce
  qed
qed

lemma fst_splitE:
  assumes "finite X" and "U \<subseteq> X" and "finite F" and "0 \<notin> F" and "(s, V) \<in> fst (split t U F)"
  obtains t' x where "t' \<in> .[X]" and "x \<in> X" and "V \<subseteq> U" and "0 \<notin> (\<lambda>s. s - t') ` F"
    and "s = t' + t + Poly_Mapping.single x 1"
    and "(s, V) \<in> fst (split (t' + t) V ((\<lambda>s. s - t') ` F))"
    and "snd (split (t' + t) V ((\<lambda>s. s - t') ` F)) \<subseteq> snd (split t U F)"
  using assms
proof (induct t U F arbitrary: thesis rule: split_induct)
  case (base1 t U F)
  from base1.prems(2) base1.hyps(3) show ?case ..
next
  case (base2 t U F)
  from base2.prems(3) show ?case by simp
next
  case (step t U F S x P0 P1 Q0 Q1)
  from step.prems(3) have "(s, V) \<in> P0 \<union> P1" by (simp only: fst_conv)
  thus ?case
  proof
    assume "(s, V) \<in> P0"
    hence "(s, V) \<in> fst (P0, Q0)" by (simp only: fst_conv)
    with step.hyps(3) obtain t' x' where "t' \<in> .[X]" and "x' \<in> X" and "V \<subseteq> U - {x}" and "0 \<notin> (\<lambda>s. s - t') ` F"
      and "s = t' + t + Poly_Mapping.single x' 1"
      and "(s, V) \<in> fst (split (t' + t) V ((\<lambda>s. s - t') ` F))"
      and "snd (split (t' + t) V ((\<lambda>s. s - t') ` F)) \<subseteq> snd (P0, Q0)"
      using step.hyps(15) by blast
    note this(7)
    also have "snd (P0, Q0) \<subseteq> snd (P0 \<union> P1, Q0 \<union> Q1)" by simp
    finally have "snd (split (t' + t) V ((\<lambda>s. s - t') ` F)) \<subseteq> snd (P0 \<union> P1, Q0 \<union> Q1)" .
    from \<open>V \<subseteq> U - {x}\<close> have "V \<subseteq> U" by blast
    show ?thesis by (rule step.prems) fact+
  next
    assume "(s, V) \<in> P1"
    show ?thesis
    proof (cases "0 \<in> (\<lambda>f. f - Poly_Mapping.single x 1) ` F")
      case True
      from step.hyps(2) have fin: "finite ((\<lambda>f. f - Poly_Mapping.single x 1) ` F)"
        by (rule finite_imageI)
      have "split (Poly_Mapping.single x 1 + t) U ((\<lambda>f. f - Poly_Mapping.single x 1) ` F) =
              ({(Poly_Mapping.single x 1 + t, U)}, {})"
        by (simp only: split.psimps[OF split_domI, OF assms(1) step.hyps(1) fin] True if_True)
      hence "P1 = {(Poly_Mapping.single x 1 + t, U)}"
        by (simp only: step.hyps(13)[symmetric] prod.inject)
      with \<open>(s, V) \<in> P1\<close> have s: "s = Poly_Mapping.single x 1 + t" and "V = U" by simp_all
      show ?thesis
      proof (rule step.prems)
        show "0 \<in> .[X]" by (fact zero_in_PPs)
      next
        from step.hyps(8, 1) show "x \<in> X" ..
      next
        show "V \<subseteq> U" by (simp add: \<open>V = U\<close>)
      next
        from step.hyps(3) show "0 \<notin> (\<lambda>s. s - 0) ` F" by simp
      next
        show "s = 0 + t + Poly_Mapping.single x 1" by (simp add: s add.commute)
      next
        from \<open>(s, V) \<in> P1\<close> show "(s, V) \<in> fst (split (0 + t) V ((\<lambda>s. s - 0) ` F))"
          by (simp add: step.hyps(14) \<open>V = U\<close>)
      next
        show "snd (split (0 + t) V ((\<lambda>s. s - 0) ` F)) \<subseteq> snd (P0 \<union> P1, Q0 \<union> Q1)"
          by (simp add: step.hyps(14) \<open>V = U\<close>)
      qed
    next
      case False
      moreover from \<open>(s, V) \<in> P1\<close> have "(s, V) \<in> fst (P1, Q1)" by (simp only: fst_conv)
      ultimately obtain t' x' where "t' \<in> .[X]" and "x' \<in> X" and "V \<subseteq> U"
        and 1: "0 \<notin> (\<lambda>s. s - t') ` (\<lambda>f. f - Poly_Mapping.single x 1) ` F"
        and s: "s = t' + (Poly_Mapping.single x 1 + t) + Poly_Mapping.single x' 1"
        and 2: "(s, V) \<in> fst (split (t' + (Poly_Mapping.single x 1 + t)) V ((\<lambda>s. s - t') ` (\<lambda>f. f - Poly_Mapping.single x 1) ` F))"
        and 3: "snd (split (t' + (Poly_Mapping.single x 1 + t)) V ((\<lambda>s. s - t') ` (\<lambda>f. f - monomial 1 x) ` F)) \<subseteq> snd (P1, Q1)"
        using step.hyps(16) by blast
      have eq: "(\<lambda>s. s - t') ` (\<lambda>f. f - Poly_Mapping.single x 1) ` F =
                (\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` F"
        by (simp add: image_image add.commute diff_diff_eq)
      show ?thesis
      proof (rule step.prems)
        from step.hyps(8, 1) have "x \<in> X" ..
        hence "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
        with \<open>t' \<in> .[X]\<close> show "t' + Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_plus)
      next
        from 1 show "0 \<notin> (\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` F"
          by (simp only: eq not_False_eq_True)
      next
        show "s = t' + Poly_Mapping.single x 1 + t + Poly_Mapping.single x' 1" by (simp only: s ac_simps)
      next
        show "(s, V) \<in> fst (split (t' + Poly_Mapping.single x 1 + t) V ((\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` F))"
          using 2 by (simp only: eq add.assoc)
      next
        have "snd (split (t' + Poly_Mapping.single x 1 + t) V ((\<lambda>s. s - (t' + Poly_Mapping.single x 1)) ` F)) \<subseteq>
              snd (P1, Q1)" (is "?x \<subseteq> _") using 3 by (simp only: eq add.assoc)
        also have "\<dots> \<subseteq> snd (P0 \<union> P1, Q0 \<union> Q1)" by simp
        finally show "?x \<subseteq> snd (P0 \<union> P1, Q0 \<union> Q1)" .
      qed fact+
    qed
  qed
qed

lemma lem_4_8:
  assumes "finite X" and "finite F" and "reduced_basis R" and "(\<Union>r\<in>R. cone r X) = (\<Union>f\<in>F. cone f X)"
    and "F \<subseteq> .[X]" and "0 \<notin> F" and "r \<in> R"
  obtains t U where "U \<subseteq> X" and "(t, U) \<in> snd (split 0 X F)" and "deg_pm r = Suc (deg_pm t)"
proof -
  have 1: "f \<in> .[X]" if "f \<in> F" for f using that assms(5) ..
  note assms(1) subset_refl assms(2) zero_in_PPs
  moreover have "(\<lambda>s. s - 0) ` (\<Union>f\<in>F. cone f X) = (\<Union>f\<in>F. cone f X)" by simp
  moreover have "ideal_like (\<Union>f\<in>F. cone f X)" by (rule ideal_like_UN, simp add: ideal_like_cone_iff 1)
  ultimately have "splits_wrt (split 0 X F) (cone 0 X) (\<Union>f\<in>F. cone f X)" by (rule split_splits_wrt)
  hence "splits_wrt (fst (split 0 X F), snd (split 0 X F)) .[X] (\<Union>f\<in>F. cone f X)" by simp
  hence "cone_decomp (.[X] \<inter> (\<Union>f\<in>F. cone f X)) (fst (split 0 X F))" by (rule splits_wrt_cone_decomp_1)
  hence "cone_decomp (\<Union>f\<in>F. cone f X) (fst (split 0 X F))"
    by (simp add: PPs_Int_cone 1 flip: UN_simps(5))
  with assms(1) assms(4)[symmetric] assms(3, 7) obtain U where "(r, U) \<in> fst (split 0 X F)"
    by (rule lem_4_7)
  with assms(1) subset_refl assms(2, 6) obtain t' x where "t' \<in> .[X]" and "x \<in> X" and "U \<subseteq> X"
    and "0 \<notin> (\<lambda>s. s - t') ` F" and r: "r = t' + 0 + Poly_Mapping.single x 1"
    and "(r, U) \<in> fst (split (t' + 0) U ((\<lambda>s. s - t') ` F))"
    and "snd (split (t' + 0) U ((\<lambda>s. s - t') ` F)) \<subseteq> snd (split 0 X F)"
    by (rule fst_splitE)
  let ?F = "(\<lambda>s. s - t') ` F"
  from assms(2) have "finite ?F" by (rule finite_imageI)
  with assms(1) \<open>U \<subseteq> X\<close> obtain V where "V \<subseteq> U" and "(t' + 0, V) \<in> snd (split (t' + 0) U ?F)"
    using \<open>0 \<notin> ?F\<close> by (rule snd_splitI)
  note this(2)
  also have "\<dots> \<subseteq> snd (split 0 X F)" by fact
  finally have "(t', V) \<in> snd (split 0 X F)" by simp
  have "deg_pm r = Suc (deg_pm t')" by (simp add: r deg_pm_plus deg_pm_single)
  from \<open>V \<subseteq> U\<close> \<open>U \<subseteq> X\<close> have "V \<subseteq> X" by (rule subset_trans)
  show ?thesis by rule fact+
qed

corollary cor_4_9:
  assumes "finite X" and "finite F" and "reduced_basis R" and "(\<Union>r\<in>R. cone r X) = (\<Union>f\<in>F. cone f X)"
    and "F \<subseteq> .[X]" and "r \<in> R"
  shows "deg_pm r \<le> Suc (Max (deg_pm ` fst ` snd (split 0 X F)))"
proof (cases "0 \<in> F")
  case True
  hence "0 \<in> (\<Union>r\<in>R. cone r X)" unfolding assms(4) using tip_in_cone ..
  then obtain r' where "r' \<in> R" and "0 \<in> cone r' X" ..
  from this(2) have "r' = 0" by (simp only: zero_in_cone_iff)
  hence "r' adds r" by simp
  with assms(3) \<open>r' \<in> R\<close> assms(6) have "r' = r" by (rule reduced_basisD)
  hence "r = 0" by (simp only: \<open>r' = 0\<close>)
  thus ?thesis by simp
next
  case False
  from assms(1) subset_refl assms(2) have "finite_decomp (snd (split 0 X F))"
    by (rule finite_decomp_split)
  hence "finite (snd (split 0 X F))" by (rule finite_decompD)
  hence fin: "finite (deg_pm ` fst ` snd (split 0 X F))" by (intro finite_imageI)
  obtain t U where "(t, U) \<in> snd (split 0 X F)" and r: "deg_pm r = Suc (deg_pm t)"
    using assms(1-5) False assms(6) by (rule lem_4_8)
  from this(1) have "deg_pm (fst (t, U)) \<in> deg_pm ` fst ` snd (split 0 X F)" by (intro imageI)
  hence "deg_pm t \<in> deg_pm ` fst ` snd (split 0 X F)" by (simp only: fst_conv)
  with fin have "deg_pm t \<le> Max (deg_pm ` fst ` snd (split 0 X F))"
    by (rule Max_ge)
  thus "deg_pm r \<le> Suc (Max (deg_pm ` fst ` snd (split 0 X F)))" by (simp add: r)
qed

lemma standard_decomp_snd_split:
  assumes "finite X" and "U \<subseteq> X" and "finite F" and "t \<in> .[X]"
    and "(\<lambda>s. s - t) ` I = (\<Union>f\<in>F. cone f X)" and "ideal_like I"
  shows "standard_decomp (deg_pm t) (snd (split t U F))"
  using assms(1-5)
proof (induct t U F rule: split_induct)
  case (base1 t U F)
  show ?case by (simp add: standard_decomp_empty)
next
  case (base2 t U F)
  show ?case by (simp add: standard_decomp_singleton)
next
  case (step t U F S x P0 P1 Q0 Q1)
  from step.hyps(15) step.prems have Q0: "standard_decomp (deg_pm t) Q0" by (simp only: snd_conv)
  have "(\<lambda>s. s - (Poly_Mapping.single x 1 + t)) ` I = (\<lambda>s. s - Poly_Mapping.single x 1) ` (\<lambda>s. s - t) ` I"
    by (simp add: image_image diff_diff_eq add.commute)
  also have "\<dots> = (\<lambda>s. s - Poly_Mapping.single x 1) ` (\<Union>f\<in>F. cone f X)" by (simp only: step.prems)
  also have "\<dots> = (\<Union>f\<in>(\<lambda>f. f - Poly_Mapping.single x 1) ` F. cone f X)"
    by (simp add: image_UN image_minus_cone)
  finally have "(\<lambda>s. s - (Poly_Mapping.single x 1 + t)) ` I =
                (\<Union>f\<in>(\<lambda>f. f - Poly_Mapping.single x 1) ` F. cone f X)" .
  moreover from _ step.prems(1) have "Poly_Mapping.single x 1 + t \<in> .[X]"
  proof (rule PPs_closed_plus)
    from step.hyps(8, 1) have "x \<in> X" ..
    thus "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
  qed
  ultimately have Q1: "standard_decomp (Suc (deg_pm t)) Q1" using step.hyps(16)
    by (simp add: deg_pm_plus deg_pm_single)
  show ?case unfolding snd_conv
  proof (rule standard_decompI)
    fix s V
    assume "(s, V) \<in> (Q0 \<union> Q1)\<^sub>+"
    hence *: "(s, V) \<in> Q0\<^sub>+ \<union> Q1\<^sub>+" by (simp only: pos_decomp_Un)
    thus "deg_pm t \<le> deg_pm s"
    proof
      assume "(s, V) \<in> Q0\<^sub>+"
      with Q0 show ?thesis by (rule standard_decompD)
    next
      assume "(s, V) \<in> Q1\<^sub>+"
      with Q1 have "Suc (deg_pm t) \<le> deg_pm s" by (rule standard_decompD)
      thus ?thesis by simp
    qed

    fix d
    assume d1: "deg_pm t \<le> d" and d2: "d \<le> deg_pm s"
    from * show "\<exists>t' U'. (t', U') \<in> Q0 \<union> Q1 \<and> deg_pm t' = d \<and> card V \<le> card U'"
    proof
      assume "(s, V) \<in> Q0\<^sub>+"
      with Q0 obtain t' U' where "(t', U') \<in> Q0" and "deg_pm t' = d" and "card V \<le> card U'"
        using d1 d2 by (rule standard_decompE)
      moreover from this(1) have "(t', U') \<in> Q0 \<union> Q1" by simp
      ultimately show ?thesis by blast
    next
      assume "(s, V) \<in> Q1\<^sub>+"
      hence "(s, V) \<in> Q1" by (simp add: pos_decomp_def)
      hence sub: "cone s V \<subseteq> (\<Union>(t', U')\<in>Q1. cone t' U')" by blast
      from d1 have "deg_pm t = d \<or> Suc (deg_pm t) \<le> d" by auto
      thus ?thesis
      proof
        assume "deg_pm t = d"
        have "splits_wrt (split t U F) (cone t U) I"
          using assms(1) step.hyps(1, 2) step.prems(1, 2) assms(6) by (rule split_splits_wrt)
        hence "splits_wrt (P0 \<union> P1, Q0 \<union> Q1) (cone t U) I" by (simp only: step.hyps(14))
        hence "cone_decomp (cone t U - I) (Q0 \<union> Q1)" by (rule splits_wrt_cone_decomp_2)
        hence "cone t U - I = (\<Union>(t', U')\<in>Q0 \<union> Q1. cone t' U')" by (rule cone_decompD)
        hence "(\<Union>(t', U')\<in>Q1. cone t' U') \<subseteq> cone t U - I" by simp
        with sub have "cone s V \<subseteq> cone t U - I" by (rule subset_trans)
        with assms(1) step.hyps(1, 2) step.prems(1, 2) assms(6)
        obtain U' where "(t, U') \<in> snd (split t U F)" and "card V \<le> card U'"
          by (rule lem_4_6)
        from this(1) have "(t, U') \<in> Q0 \<union> Q1" by (simp add: step.hyps(14))
        thus ?thesis using \<open>deg_pm t = d\<close> \<open>card V \<le> card U'\<close> by blast
      next
        assume "Suc (deg_pm t) \<le> d"
        with Q1 \<open>(s, V) \<in> Q1\<^sub>+\<close> obtain t' U' where "(t', U') \<in> Q1" and "deg_pm t' = d"
          and "card V \<le> card U'"
          using d2 by (rule standard_decompE)
        moreover from this(1) have "(t', U') \<in> Q0 \<union> Q1" by simp
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed

theorem standard_cone_decomp_snd_split:
  assumes "finite X" and "finite F" and "F \<subseteq> .[X]" and "I = (\<Union>f\<in>F. cone f X)"
  shows "standard_decomp 0 (snd (split 0 X F))" (is ?thesis1)
    and "cone_decomp (.[X] - I) (snd (split 0 X F))" (is ?thesis2)
proof -
  note assms(1) subset_refl assms(2) zero_in_PPs
  moreover have "(\<lambda>s. s - 0) ` I = (\<Union>f\<in>F. cone f X)" by (simp add: assms(4))
  moreover have "ideal_like I" unfolding assms(4)
  proof (rule ideal_like_UN)
    fix f
    assume "f \<in> F"
    hence "f \<in> .[X]" using assms(3) ..
    thus "ideal_like (cone f X)" by (simp only: ideal_like_cone_iff)
  qed
  ultimately have 1: "standard_decomp (deg_pm (0::'x \<Rightarrow>\<^sub>0 nat)) (snd (split 0 X F))"
    and 2: "splits_wrt (split 0 X F) (cone 0 X) I"
    by (rule standard_decomp_snd_split, rule split_splits_wrt)
  from 1 show ?thesis1 by simp

  from 2 have "splits_wrt (fst (split 0 X F), snd (split 0 X F)) .[X] I" by simp
  thus ?thesis2 by (rule splits_wrt_cone_decomp_2)
qed

subsection \<open>Exact Cone Decompositions\<close>

definition exact_decomp :: "nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> bool"
  where "exact_decomp m P \<longleftrightarrow> (\<forall>(t, U)\<in>P. t \<in> .[X] \<and> U \<subseteq> X) \<and>
                              (\<forall>(t, U)\<in>P. \<forall>(t', U')\<in>P. deg_pm t = deg_pm t' \<longrightarrow>
                                          m < card U \<longrightarrow> m < card U' \<longrightarrow> (t, U) = (t', U'))"

lemma exact_decompI:
  "(\<And>t U. (t, U) \<in> P \<Longrightarrow> t \<in> .[X]) \<Longrightarrow> (\<And>t U. (t, U) \<in> P \<Longrightarrow> U \<subseteq> X) \<Longrightarrow>
    (\<And>t t' U U'. (t, U) \<in> P \<Longrightarrow> (t', U') \<in> P \<Longrightarrow> deg_pm t = deg_pm t' \<Longrightarrow>
            m < card U \<Longrightarrow> m < card U' \<Longrightarrow> (t, U) = (t', U')) \<Longrightarrow>
    exact_decomp m P"
  unfolding exact_decomp_def by fastforce

lemma exact_decompD:
  assumes "exact_decomp m P" and "(t, U) \<in> P"
  shows "t \<in> .[X]" and "U \<subseteq> X"
    and "(t', U') \<in> P \<Longrightarrow> deg_pm t = deg_pm t' \<Longrightarrow> m < card U \<Longrightarrow> m < card U' \<Longrightarrow> (t, U) = (t', U')"
  using assms unfolding exact_decomp_def by fastforce+

lemma exact_decompI_zero:
  assumes "\<And>t U. (t, U) \<in> P \<Longrightarrow> t \<in> .[X]" and "\<And>t U. (t, U) \<in> P \<Longrightarrow> U \<subseteq> X"
    and "\<And>t t' U U'. (t, U) \<in> P\<^sub>+ \<Longrightarrow> (t', U') \<in> P\<^sub>+ \<Longrightarrow> deg_pm t = deg_pm t' \<Longrightarrow> (t, U) = (t', U')"
  shows "exact_decomp 0 P"
  using assms(1, 2)
proof (rule exact_decompI)
  fix t t' and U U' :: "'x set"
  assume "0 < card U"
  hence "U \<noteq> {}" by auto
  moreover assume "(t, U) \<in> P"
  ultimately have "(t, U) \<in> P\<^sub>+" by (simp add: pos_decomp_def)
  assume "0 < card U'"
  hence "U' \<noteq> {}" by auto
  moreover assume "(t', U') \<in> P"
  ultimately have "(t', U') \<in> P\<^sub>+" by (simp add: pos_decomp_def)
  assume "deg_pm t = deg_pm t'"
  with \<open>(t, U) \<in> P\<^sub>+\<close> \<open>(t', U') \<in> P\<^sub>+\<close> show "(t, U) = (t', U')" by (rule assms(3))
qed

lemma exact_decompD_zero:
  assumes "finite X" and "exact_decomp 0 P" and "(t, U) \<in> P\<^sub>+" and "(t', U') \<in> P\<^sub>+"
    and "deg_pm t = deg_pm t'"
  shows "(t, U) = (t', U')"
proof -
  from assms(3) have "(t, U) \<in> P" and "U \<noteq> {}" by (simp_all add: pos_decomp_def)
  from assms(2) this(1) have "U \<subseteq> X" by (rule exact_decompD)
  hence "finite U" using assms(1) by (rule finite_subset)
  with \<open>U \<noteq> {}\<close> have "0 < card U" by (simp add: card_gt_0_iff)
  from assms(4) have "(t', U') \<in> P" and "U' \<noteq> {}" by (simp_all add: pos_decomp_def)
  from assms(2) this(1) have "U' \<subseteq> X" by (rule exact_decompD)
  hence "finite U'" using assms(1) by (rule finite_subset)
  with \<open>U' \<noteq> {}\<close> have "0 < card U'" by (simp add: card_gt_0_iff)
  show ?thesis by (rule exact_decompD) fact+
qed

lemma exact_decomp_imp_finite_decomp:
  assumes "finite X" and "exact_decomp m P" and "finite P"
  shows "finite_decomp P"
  using assms(3)
proof (rule finite_decompI)
  fix t U
  assume "(t, U) \<in> P"
  with assms(2) have "U \<subseteq> X" by (rule exact_decompD)
  thus "finite U" using assms(1) by (rule finite_subset)
qed

lemma exact_decomp_card_X:
  assumes "finite X" and "\<And>t U. (t, U) \<in> P \<Longrightarrow> t \<in> .[X]" and "\<And>t U. (t, U) \<in> P \<Longrightarrow> U \<subseteq> X"
    and "card X \<le> m"
  shows "exact_decomp m P"
  using assms(2, 3)
proof (rule exact_decompI)
  fix t1 t2 U1 U2
  assume "(t1, U1) \<in> P"
  hence "U1 \<subseteq> X" by (rule assms(3))
  with assms(1) have "card U1 \<le> card X" by (rule card_mono)
  also have "\<dots> \<le> m" by (fact assms(4))
  also assume "m < card U1"
  finally show "(t1, U1) = (t2, U2)" by simp
qed

qualified definition \<a> :: "(('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> nat"
  where "\<a> P = (LEAST k. standard_decomp k P)"

qualified definition \<b> :: "(('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> nat \<Rightarrow> nat"
  where "\<b> P i = (LEAST d. \<a> P \<le> d \<and> (\<forall>(t, U)\<in>P. i \<le> card U \<longrightarrow> deg_pm t < d))"

lemma \<a>: "standard_decomp k P \<Longrightarrow> standard_decomp (\<a> P) P"
  unfolding \<a>_def by (rule LeastI)

lemma \<a>_empty:
  assumes "P\<^sub>+ = {}"
  shows "\<a> P = 0"
proof -
  from assms have "standard_decomp 0 P" by (rule standard_decomp_empty)
  thus ?thesis unfolding \<a>_def by (rule Least_eq_0)
qed

lemma \<a>_nonempty:
  assumes "finite_decomp P" and "standard_decomp k P" and "P\<^sub>+ \<noteq> {}"
  shows "\<a> P = Min (deg_pm ` fst ` P\<^sub>+)"
  using assms(1) _ assms(3)
proof (rule standard_decomp_nonempty_unique)
  from assms(2) show "standard_decomp (\<a> P) P" by (rule \<a>)
qed

lemma \<a>_nonempty_unique:
  assumes "finite_decomp P" and "standard_decomp k P" and "P\<^sub>+ \<noteq> {}"
  shows "\<a> P = k"
proof -
  from assms have "\<a> P = Min (deg_pm ` fst ` P\<^sub>+)" by (rule \<a>_nonempty)
  moreover from assms have "k = Min (deg_pm ` fst ` P\<^sub>+)" by (rule standard_decomp_nonempty_unique)
  ultimately show ?thesis by simp
qed

lemma \<b>:
  assumes "finite P"
  shows "\<a> P \<le> \<b> P i" and "(t, U) \<in> P \<Longrightarrow> i \<le> card U \<Longrightarrow> deg_pm t < \<b> P i"
proof -
  let ?A = "deg_pm ` fst ` P"
  define A where "A = insert (\<a> P) ?A"
  define m where "m = Suc (Max A)"
  from assms have "finite ?A" by (intro finite_imageI)
  hence "finite A" by (simp add: A_def)
  have "\<a> P \<le> \<b> P i \<and> (\<forall>(t', U')\<in>P. i \<le> card U' \<longrightarrow> deg_pm t' < \<b> P i)" unfolding \<b>_def
  proof (rule LeastI)
    have "\<a> P \<in> A" by (simp add: A_def)
    with \<open>finite A\<close> have "\<a> P \<le> Max A" by (rule Max_ge)
    hence "\<a> P \<le> m" by (simp add: m_def)
    moreover {
      fix t U
      assume "(t, U) \<in> P"
      hence "deg_pm (fst (t, U)) \<in> ?A" by (intro imageI)
      hence "deg_pm t \<in> A" by (simp add: A_def)
      with \<open>finite A\<close> have "deg_pm t \<le> Max A" by (rule Max_ge)
      hence "deg_pm t < m" by (simp add: m_def)
    }
    ultimately show "\<a> P \<le> m \<and> (\<forall>(t, U)\<in>P. i \<le> card U \<longrightarrow> deg_pm t < m)" by blast
  qed
  thus "\<a> P \<le> \<b> P i" and "(t, U) \<in> P \<Longrightarrow> i \<le> card U \<Longrightarrow> deg_pm t < \<b> P i" by blast+
qed

lemma \<b>_le: "\<a> P \<le> d \<Longrightarrow> (\<And>t' U'. (t', U') \<in> P \<Longrightarrow> i \<le> card U' \<Longrightarrow> deg_pm t' < d) \<Longrightarrow> \<b> P i \<le> d"
  unfolding \<b>_def by (intro Least_le) blast

lemma \<b>_decreasing:
  assumes "finite P" and "i \<le> j"
  shows "\<b> P j \<le> \<b> P i"
proof (rule \<b>_le)
  from assms(1) show "\<a> P \<le> \<b> P i" by (rule \<b>)
next
  fix t U
  assume "(t, U) \<in> P"
  assume "j \<le> card U"
  with assms(2) have "i \<le> card U" by (rule le_trans)
  with assms(1) \<open>(t, U) \<in> P\<close> show "deg_pm t < \<b> P i" by (rule \<b>)
qed

lemma \<b>_empty:
  assumes "P\<^sub>+ = {}" and "Suc 0 \<le> i"
  shows "\<b> P i = 0"
  unfolding \<b>_def
proof (rule Least_eq_0)
  from assms(1) have "\<a> P = 0" by (rule \<a>_empty)
  moreover {
    fix t and U::"'x set"
    note assms(2)
    also assume "i \<le> card U"
    finally have "U \<noteq> {}" by auto
    moreover assume "(t, U) \<in> P"
    ultimately have "(t, U) \<in> P\<^sub>+" by (simp add: pos_decomp_def)
    hence False by (simp add: assms)
  }
  ultimately show "\<a> P \<le> 0 \<and> (\<forall>(t, U)\<in>P. i \<le> card U \<longrightarrow> deg_pm t < 0)" by blast
qed

lemma \<b>_zero:
  assumes "finite P" and "P \<noteq> {}"
  shows "Suc (Max (deg_pm ` fst ` P)) \<le> \<b> P 0"
proof -
  from assms(1) have "finite (deg_pm ` fst ` P)" by (intro finite_imageI)
  moreover from assms(2) have "deg_pm ` fst ` P \<noteq> {}" by simp
  moreover have "\<forall>a\<in>deg_pm ` fst ` P. a < \<b> P 0"
  proof
    fix d
    assume "d \<in> deg_pm ` fst ` P"
    then obtain p where "p \<in> P" and "d = deg_pm (fst p)" by blast
    moreover obtain t U where "p = (t, U)" using prod.exhaust by blast
    ultimately have "(t, U) \<in> P" and d: "d = deg_pm t" by simp_all
    from assms(1) this(1) le0 show "d < \<b> P 0" unfolding d by (rule \<b>)
  qed
  ultimately have "Max (deg_pm ` fst ` P) < \<b> P 0" by simp
  thus ?thesis by simp
qed

corollary \<b>_zero_gr:
  assumes "finite P" and "(t, U) \<in> P"
  shows "deg_pm t < \<b> P 0"
proof -
  have "deg_pm t \<le> Max (deg_pm ` fst ` P)"
  proof (rule Max_ge)
    from assms(1) show "finite (deg_pm ` fst ` P)" by (intro finite_imageI)
  next
    from assms(2) have "deg_pm (fst (t, U)) \<in> deg_pm ` fst ` P" by (intro imageI)
    thus "deg_pm t \<in> deg_pm ` fst ` P" by simp
  qed
  also have "\<dots> < Suc \<dots>" by simp
  also from assms(1) have "\<dots> \<le> \<b> P 0"
  proof (rule \<b>_zero)
    from assms(2) show "P \<noteq> {}" by blast
  qed
  finally show ?thesis .
qed

lemma \<b>_one:
  assumes "finite_decomp P" and "standard_decomp k P"
  shows "\<b> P (Suc 0) = (if P\<^sub>+ = {} then 0 else Suc (Max (deg_pm ` fst ` P\<^sub>+)))"
proof (cases "P\<^sub>+ = {}")
  case True
  hence "\<b> P (Suc 0) = 0" using le_refl by (rule \<b>_empty)
  with True show ?thesis by simp
next
  case False
  with assms have aP: "\<a> P = Min (deg_pm ` fst ` P\<^sub>+)" (is "_ = Min ?A") by (rule \<a>_nonempty)
  note pos_decomp_subset
  moreover from assms(1) have "finite P" by (rule finite_decompD)
  ultimately have "finite (P\<^sub>+)" by (rule finite_subset)
  hence "finite ?A" by (intro finite_imageI)
  from False have "?A \<noteq> {}" by simp
  have "\<b> P (Suc 0) = Suc (Max ?A)" unfolding \<b>_def
  proof (rule Least_equality)
    from \<open>finite ?A\<close> \<open>?A \<noteq> {}\<close> have "\<a> P \<in> ?A" unfolding aP by (rule Min_in)
    with \<open>finite ?A\<close> have "\<a> P \<le> Max ?A" by (rule Max_ge)
    hence "\<a> P \<le> Suc (Max ?A)" by simp
    moreover {
      fix t U
      assume "(t, U) \<in> P"
      with assms(1) have "finite U" by (rule finite_decompD)
      moreover assume "Suc 0 \<le> card U"
      ultimately have "U \<noteq> {}" by auto
      with \<open>(t, U) \<in> P\<close> have "(t, U) \<in> P\<^sub>+" by (simp add: pos_decomp_def)
      hence "deg_pm (fst (t, U)) \<in> ?A" by (intro imageI)
      hence "deg_pm t \<in> ?A" by (simp only: fst_conv)
      with \<open>finite ?A\<close> have "deg_pm t \<le> Max ?A" by (rule Max_ge)
      hence "deg_pm t < Suc (Max ?A)" by simp
    }
    ultimately show "\<a> P \<le> Suc (Max ?A) \<and> (\<forall>(t, U)\<in>P. Suc 0 \<le> card U \<longrightarrow> deg_pm t < Suc (Max ?A))"
      by blast
  next
    fix d
    assume "\<a> P \<le> d \<and> (\<forall>(t, U)\<in>P. Suc 0 \<le> card U \<longrightarrow> deg_pm t < d)"
    hence rl: "deg_pm t < d" if "(t, U) \<in> P" and "0 < card U" for t U using that by auto
    have "Max ?A < d" unfolding Max_less_iff[OF \<open>finite ?A\<close> \<open>?A \<noteq> {}\<close>]
    proof
      fix d0
      assume "d0 \<in> deg_pm ` fst ` P\<^sub>+"
      then obtain t U where "(t, U) \<in> P\<^sub>+" and d0: "d0 = deg_pm t" by auto
      from this(1) have "(t, U) \<in> P" and "U \<noteq> {}" by (simp_all add: pos_decomp_def)
      from assms(1) this(1) have "finite U" by (rule finite_decompD)
      with \<open>U \<noteq> {}\<close> have "0 < card U" by (simp add: card_gt_0_iff)
      with \<open>(t, U) \<in> P\<close> show "d0 < d" unfolding d0 by (rule rl)
    qed
    thus "Suc (Max ?A) \<le> d" by simp
  qed
  with False show ?thesis by simp
qed

corollary \<b>_one_gr:
  assumes "finite_decomp P" and "standard_decomp k P" and "(t, U) \<in> P\<^sub>+"
  shows "deg_pm t < \<b> P (Suc 0)"
proof -
  from assms(3) have "P\<^sub>+ \<noteq> {}" by blast
  with assms(1, 2) have eq: "\<b> P (Suc 0) = Suc (Max (deg_pm ` fst ` P\<^sub>+))" by (simp add: \<b>_one)
  have "deg_pm t \<le> Max (deg_pm ` fst ` P\<^sub>+)"
  proof (rule Max_ge)
    from assms(1) have "finite P" by (rule finite_decompD)
    with pos_decomp_subset have "finite (P\<^sub>+)" by (rule finite_subset)
    thus "finite (deg_pm ` fst ` P\<^sub>+)" by (intro finite_imageI)
  next
    from assms(3) have "deg_pm (fst (t, U)) \<in> deg_pm ` fst ` P\<^sub>+" by (intro imageI)
    thus "deg_pm t \<in> deg_pm ` fst ` P\<^sub>+" by simp
  qed
  also have "\<dots> < \<b> P (Suc 0)" by (simp add: eq)
  finally show ?thesis .
qed

lemma \<b>_card_X:
  assumes "finite X" and "exact_decomp m P" and "Suc (card X) \<le> i"
  shows "\<b> P i = \<a> P"
  unfolding \<b>_def
proof (rule Least_equality)
  {
    fix t U
    assume "(t, U) \<in> P"
    with assms(2) have "U \<subseteq> X" by (rule exact_decompD)
    note assms(3)
    also assume "i \<le> card U"
    finally have "card X < card U" by simp
    with assms(1) have "\<not> U \<subseteq> X" by (auto dest: card_mono leD)
    hence False using \<open>U \<subseteq> X\<close> ..
  }
  thus "\<a> P \<le> \<a> P \<and> (\<forall>(t, U)\<in>P. i \<le> card U \<longrightarrow> deg_pm t < \<a> P)" by blast
qed simp

lemma lem_6_1_1:
  assumes "finite P" and "standard_decomp k P" and "exact_decomp m P" and "Suc 0 \<le> i"
    and "i \<le> card X" and "\<b> P (Suc i) \<le> d" and "d < \<b> P i"
  obtains t U where "(t, U) \<in> P\<^sub>+" and "deg_pm t = d" and "card U = i"
proof -
  have "P\<^sub>+ \<noteq> {}"
  proof
    assume "P\<^sub>+ = {}"
    hence "\<b> P i = 0" using assms(4) by (rule \<b>_empty)
    with assms(7) show False by simp
  qed
  from assms(4, 5) have "Suc 0 \<le> card X" by (rule le_trans)
  hence "finite X" by (simp add: card_ge_0_finite)
  hence eq1: "\<b> P (Suc (card X)) = \<a> P" using assms(3) le_refl by (rule \<b>_card_X)
  from assms(2) have std: "standard_decomp (\<b> P (Suc (card X))) P" unfolding eq1 by (rule \<a>)
  from assms(5) have "Suc i \<le> Suc (card X)" ..
  with assms(1) have "\<b> P (Suc (card X)) \<le> \<b> P (Suc i)" by (rule \<b>_decreasing)
  hence "\<a> P \<le> \<b> P (Suc i)" by (simp only: eq1)
  have "\<exists>t U. (t, U) \<in> P \<and> i \<le> card U \<and> \<b> P i \<le> Suc (deg_pm t)"
  proof (rule ccontr)
    assume *: "\<nexists>t U. (t, U) \<in> P \<and> i \<le> card U \<and> \<b> P i \<le> Suc (deg_pm t)"
    note \<open>\<a> P \<le> \<b> P (Suc i)\<close>
    also from assms(6, 7) have "\<b> P (Suc i) < \<b> P i" by (rule le_less_trans)
    finally have "\<a> P < \<b> P i" .
    hence "\<a> P \<le> \<b> P i - 1" by simp
    hence "\<b> P i \<le> \<b> P i - 1"
    proof (rule \<b>_le)
      fix t U
      assume "(t, U) \<in> P" and "i \<le> card U"
      show "deg_pm t < \<b> P i - 1"
      proof (rule ccontr)
        assume "\<not> deg_pm t < \<b> P i - 1"
        hence "\<b> P i \<le> Suc (deg_pm t)" by simp
        with * \<open>(t, U) \<in> P\<close> \<open>i \<le> card U\<close> show False by auto
      qed
    qed
    thus False using \<open>\<a> P < \<b> P i\<close> by linarith
  qed
  then obtain t U where "(t, U) \<in> P" and "i \<le> card U" and "\<b> P i \<le> Suc (deg_pm t)" by blast
  from assms(4) this(2) have "U \<noteq> {}" by auto
  with \<open>(t, U) \<in> P\<close> have "(t, U) \<in> P\<^sub>+" by (simp add: pos_decomp_def)
  note std this
  moreover have "\<b> P (Suc (card X)) \<le> d" unfolding eq1 using \<open>\<a> P \<le> \<b> P (Suc i)\<close> assms(6)
    by (rule le_trans)
  moreover have "d \<le> deg_pm t"
  proof -
    from assms(7) \<open>\<b> P i \<le> Suc (deg_pm t)\<close> have "d < Suc (deg_pm t)" by (rule less_le_trans)
    thus ?thesis by simp
  qed
  ultimately obtain t' U' where "(t', U') \<in> P" and d: "deg_pm t' = d" and "card U \<le> card U'"
    by (rule standard_decompE)
  from \<open>i \<le> card U\<close> this(3) have "i \<le> card U'" by (rule le_trans)
  with assms(4) have "U' \<noteq> {}" by auto
  with \<open>(t', U') \<in> P\<close> have "(t', U') \<in> P\<^sub>+" by (simp add: pos_decomp_def)
  moreover note \<open>deg_pm t' = d\<close>
  moreover have "card U' = i"
  proof (rule ccontr)
    assume "card U' \<noteq> i"
    with \<open>i \<le> card U'\<close> have "Suc i \<le> card U'" by simp
    with assms(1) \<open>(t', U') \<in> P\<close> have "deg_pm t' < \<b> P (Suc i)" by (rule \<b>)
    with assms(6) show False by (simp add: d)
  qed
  ultimately show ?thesis ..
qed

lemma lem_6_1_2:
  assumes "exact_decomp 0 P" and "Suc 0 \<le> i" and "i \<le> card X"
  assumes "(t1, U1) \<in> P\<^sub>+" and "(t2, U2) \<in> P\<^sub>+" and "deg_pm t1 = deg_pm t2"
  shows "(t1, U1) = (t2, U2)"
  using _ assms(1, 4, 5, 6)
proof (rule exact_decompD_zero)
  from assms(2, 3) have "Suc 0 \<le> card X" by (rule le_trans)
  thus "finite X" by (simp add: card_ge_0_finite)
qed

corollary lem_6_1_3:
  assumes "finite P" and "standard_decomp k P" and "exact_decomp 0 P" and "Suc 0 \<le> i"
    and "i \<le> card X" and "\<b> P (Suc i) \<le> d" and "d < \<b> P i"
  obtains t U where "{(t', U') \<in> P\<^sub>+. deg_pm t' = d} = {(t, U)}" and "card U = i"
proof -
  from assms obtain t U where "(t, U) \<in> P\<^sub>+" and "deg_pm t = d" and "card U = i"
    by (rule lem_6_1_1)
  hence "{(t, U)} \<subseteq> {(t', U') \<in> P\<^sub>+. deg_pm t' = d}" (is "_ \<subseteq> ?A") by simp
  moreover have "?A \<subseteq> {(t, U)}"
  proof
    fix x
    assume "x \<in> ?A"
    then obtain t' U' where "(t', U') \<in> P\<^sub>+" and "deg_pm t' = d" and x: "x = (t', U')"
      by blast
    note assms(3, 4, 5) \<open>(t, U) \<in> P\<^sub>+\<close> this(1)
    moreover have "deg_pm t = deg_pm t'" by (simp only: \<open>deg_pm t = d\<close> \<open>deg_pm t' = d\<close>)
    ultimately have "(t, U) = (t', U')" by (rule lem_6_1_2)
    thus "x \<in> {(t, U)}" by (simp add: x)
  qed
  ultimately have "{(t, U)} = ?A" ..
  hence "?A = {(t, U)}" by (rule sym)
  thus ?thesis using \<open>card U = i\<close> ..
qed

corollary lem_6_1_3':
  assumes "finite P" and "standard_decomp k P" and "exact_decomp 0 P" and "Suc 0 \<le> i"
    and "i \<le> card X" and "\<b> P (Suc i) \<le> d" and "d < \<b> P i"
  shows "card {(t', U') \<in> P\<^sub>+. deg_pm t' = d} = 1" (is "card ?A = _")
    and "{(t', U') \<in> P\<^sub>+. deg_pm t' = d \<and> card U' = i} = {(t', U') \<in> P\<^sub>+. deg_pm t' = d}" (is "?B = _")
    and "card {(t', U') \<in> P\<^sub>+. deg_pm t' = d \<and> card U' = i} = 1"
proof -
  from assms obtain t U where "?A = {(t, U)}" and "card U = i" by (rule lem_6_1_3)
  from this(1) show "card ?A = 1" by simp
  moreover show "?B = ?A"
  proof
    have "(t, U) \<in> ?A" by (simp add: \<open>?A = {(t, U)}\<close>)
    have "?A = {(t, U)}" by fact
    also from \<open>(t, U) \<in> ?A\<close> \<open>card U = i\<close> have "\<dots> \<subseteq> ?B" by simp
    finally show "?A \<subseteq> ?B" .
  qed blast
  ultimately show "card ?B = 1" by simp 
qed

corollary lem_6_1_4:
  assumes "finite X" and "finite P" and "standard_decomp k P" and "exact_decomp 0 P" and "Suc 0 \<le> i"
    and "i \<le> card X" and "(t, U) \<in> P\<^sub>+" and "card U = i"
  shows "\<b> P (Suc i) \<le> deg_pm t"
proof (rule ccontr)
  define j where "j = (LEAST j'. \<b> P j' \<le> deg_pm t)"
  assume "\<not> \<b> P (Suc i) \<le> deg_pm t"
  hence "deg_pm t < \<b> P (Suc i)" by simp
  from assms(1, 4) le_refl have "\<b> P (Suc (card X)) = \<a> P" by (rule \<b>_card_X)
  also from _ assms(7) have "\<dots> \<le> deg_pm t"
  proof (rule standard_decompD)
    from assms(3) show "standard_decomp (\<a> P) P" by (rule \<a>)
  qed
  finally have "\<b> P (Suc (card X)) \<le> deg_pm t" .
  hence 1: "\<b> P j \<le> deg_pm t" unfolding j_def by (rule LeastI)
  have "Suc i < j"
  proof (rule ccontr)
    assume "\<not> Suc i < j"
    hence "j \<le> Suc i" by simp
    with assms(2) have "\<b> P (Suc i) \<le> \<b> P j" by (rule \<b>_decreasing)
    also have "\<dots> \<le> deg_pm t" by fact
    finally show False using \<open>deg_pm t < \<b> P (Suc i)\<close> by simp
  qed
  hence eq: "Suc (j - 1) = j" by simp
  note assms(2-4)
  moreover from assms(5) have "Suc 0 \<le> j - 1"
  proof (rule le_trans)
    from \<open>Suc i < j\<close> show "i \<le> j - 1" by simp
  qed
  moreover have "j - 1 \<le> card X"
  proof -
    have "j \<le> Suc (card X)" unfolding j_def by (rule Least_le) fact
    thus ?thesis by simp
  qed
  moreover from 1 have "\<b> P (Suc (j - 1)) \<le> deg_pm t" by (simp only: eq)
  moreover have "deg_pm t < \<b> P (j - 1)"
  proof (rule ccontr)
    assume "\<not> deg_pm t < \<b> P (j - 1)"
    hence "\<b> P (j - 1) \<le> deg_pm t" by simp
    hence "j \<le> j - 1" unfolding j_def by (rule Least_le)
    also have "\<dots> < Suc (j - 1)" by simp
    finally show False by (simp only: eq)
  qed
  ultimately obtain t0 U0 where eq1: "{(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = deg_pm t} = {(t0, U0)}"
    and "card U0 = j - 1" by (rule lem_6_1_3)
  from assms(7) have "(t, U) \<in> {(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = deg_pm t}" by simp
  hence "(t, U) \<in> {(t0, U0)}" by (simp only: eq1)
  hence "U = U0" by simp
  hence "card U = j - 1" by (simp only: \<open>card U0 = j - 1\<close>)
  hence "i = j - 1" by (simp only: assms(8))
  hence "Suc i = j" by (simp only: eq)
  with \<open>Suc i < j\<close> show False by simp
qed

lemma lem_6_2_1:
  assumes "standard_decomp k P" and "(t1, U1) \<in> P" and "(t2, U2) \<in> P" and "deg_pm t1 = deg_pm t2"
    and "card U2 \<le> card U1" and "(t1, U1) \<noteq> (t2, U2)" and "x \<in> U2"
  shows "standard_decomp k (insert (Poly_Mapping.single x 1 + t2, U2) (insert (t2, U2 - {x}) (P - {(t2, U2)})))"
    (is "standard_decomp _ (insert ?p1 (insert ?p2 ?Q))")
proof (rule standard_decompI)
  fix t U
  assume "(t, U) \<in> (insert ?p1 (insert ?p2 ?Q))\<^sub>+"
  hence disj: "(t, U) = ?p1 \<or> ((t, U) = ?p2 \<and> U2 - {x} \<noteq> {}) \<or> (t, U) \<in> P\<^sub>+"
    by (auto simp: pos_decomp_def)
  from assms(7) have "U2 \<noteq> {}" by blast
  with assms(3) have "(t2, U2) \<in> P\<^sub>+" by (simp add: pos_decomp_def)
  with assms(1) have k_le: "k \<le> deg_pm t2" by (rule standard_decompD)

  from disj show "k \<le> deg_pm t"
  proof (elim disjE)
    assume "(t, U) = ?p1"
    hence t: "t = Poly_Mapping.single x 1 + t2" by simp
    note k_le
    also have "deg_pm t2 \<le> deg_pm t" by (simp add: t deg_pm_plus)
    finally show ?thesis .
  next
    assume "(t, U) = ?p2 \<and> U2 - {x} \<noteq> {}"
    with k_le show ?thesis by simp
  next
    assume "(t, U) \<in> P\<^sub>+"
    with assms(1) show ?thesis by (rule standard_decompD)
  qed

  fix d
  assume "k \<le> d" and "d \<le> deg_pm t"
  from disj obtain t' U' where 1: "(t', U') \<in> insert ?p1 P" and "deg_pm t' = d"
    and "card U \<le> card U'"
  proof (elim disjE)
    assume "(t, U) = ?p1"
    hence t: "t = Poly_Mapping.single x 1 + t2" and "U = U2" by simp_all
    from \<open>d \<le> deg_pm t\<close> have "d \<le> deg_pm t2 \<or> deg_pm t = d"
      by (auto simp: t deg_pm_plus deg_pm_single)
    thus ?thesis
    proof
      assume "d \<le> deg_pm t2"
      with assms(1) \<open>(t2, U2) \<in> P\<^sub>+\<close> \<open>k \<le> d\<close> obtain t' U'
        where "(t', U') \<in> P" and "deg_pm t' = d" and "card U2 \<le> card U'" by (rule standard_decompE)
      from this(1) have "(t', U') \<in> insert ?p1 P" by simp
      moreover note \<open>deg_pm t' = d\<close>
      moreover from \<open>card U2 \<le> card U'\<close> have "card U \<le> card U'" by (simp only: \<open>U = U2\<close>)
      ultimately show ?thesis ..
    next
      have "(t, U) \<in> insert ?p1 P" by (simp add: \<open>(t, U) = ?p1\<close>)
      moreover assume "deg_pm t = d"
      ultimately show ?thesis using le_refl ..
    qed
  next
    assume "(t, U) = ?p2 \<and> U2 - {x} \<noteq> {}"
    hence "t = t2" and U: "U = U2 - {x}" by simp_all
    from \<open>d \<le> deg_pm t\<close> this(1) have "d \<le> deg_pm t2" by simp
    with assms(1) \<open>(t2, U2) \<in> P\<^sub>+\<close> \<open>k \<le> d\<close> obtain t' U'
      where "(t', U') \<in> P" and "deg_pm t' = d" and "card U2 \<le> card U'" by (rule standard_decompE)
    from this(1) have "(t', U') \<in> insert ?p1 P" by simp
    moreover note \<open>deg_pm t' = d\<close>
    moreover from _ \<open>card U2 \<le> card U'\<close> have "card U \<le> card U'" unfolding U
      by (rule le_trans) (metis Diff_empty card_Diff1_le card_infinite finite_Diff_insert order_refl)
    ultimately show ?thesis ..
  next
    assume "(t, U) \<in> P\<^sub>+"
    from assms(1) this \<open>k \<le> d\<close> \<open>d \<le> deg_pm t\<close> obtain t' U'
      where "(t', U') \<in> P" and "deg_pm t' = d" and "card U \<le> card U'" by (rule standard_decompE)
    from this(1) have "(t', U') \<in> insert ?p1 P" by simp
    thus ?thesis using \<open>deg_pm t' = d\<close> \<open>card U \<le> card U'\<close> ..
  qed
  show "\<exists>t' U'. (t', U') \<in> insert ?p1 (insert ?p2 ?Q) \<and> deg_pm t' = d \<and> card U \<le> card U'"
  proof (cases "(t', U') = (t2, U2)")
    case True
    hence "t' = t2" and "U' = U2" by simp_all
    from assms(2, 6) have "(t1, U1) \<in> insert ?p1 (insert ?p2 ?Q)" by simp
    moreover from \<open>deg_pm t' = d\<close> have "deg_pm t1 = d" by (simp only: \<open>t' = t2\<close> assms(4))
    moreover from \<open>card U \<le> card U'\<close> assms(5) have "card U \<le> card U1" by (simp add: \<open>U' = U2\<close>)
    ultimately show ?thesis by blast
  next
    case False
    with 1 have "(t', U') \<in> insert ?p1 (insert ?p2 ?Q)" by blast
    thus ?thesis using \<open>deg_pm t' = d\<close> \<open>card U \<le> card U'\<close> by blast
  qed
qed

lemma lem_6_2_2:
  assumes "cone_decomp T P" and "(t, U) \<in> P" and "x \<in> U"
  shows "cone_decomp T (insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (P - {(t, U)})))"
    (is "cone_decomp _ (insert ?p1 (insert ?p2 ?Q))")
proof (rule cone_decompI)
  from assms(1) have "finite P" by (rule cone_decompD)
  thus "finite (insert ?p1 (insert ?p2 ?Q))" by simp
next
  from assms(3) have eq0: "insert x (U - {x}) = U" by blast
  hence "cone t U = cone t (insert x (U - {x}))" by simp
  also have "\<dots> = cone t (U - {x}) \<union> cone (Poly_Mapping.single x 1 + t) (insert x (U - {x}))"
    by (fact cone_insert)
  finally have eq1: "cone t U = cone t (U - {x}) \<union> cone (Poly_Mapping.single x 1 + t) U"
    by (simp only: eq0)
  from assms(2) have eq2: "insert (t, U) ?Q = P" by blast
  from assms(1) have "T = (\<Union>(t, U)\<in>P. cone t U)" by (rule cone_decompD)
  also have "\<dots> = (\<Union>(t, U)\<in>insert (t, U) ?Q. cone t U)" by (simp only: eq2)
  also have "\<dots> = cone t (U - {x}) \<union> cone (Poly_Mapping.single x 1 + t) U \<union> (\<Union>(t, U)\<in>?Q. cone t U)"
    by (simp only: UN_insert eq1 prod.case)
  also have "\<dots> = (\<Union>(t, U)\<in>(insert ?p1 (insert ?p2 ?Q)). cone t U)" by (simp add: ac_simps)
  finally show "T = (\<Union>(t, U)\<in>(insert ?p1 (insert ?p2 ?Q)). cone t U)" .
next
  fix t1 t2 U1 U2 s
  assume t1: "(t1, U1) \<in> insert ?p1 (insert ?p2 ?Q)" and t2: "(t2, U2) \<in> insert ?p1 (insert ?p2 ?Q)"
  assume s1: "s \<in> cone t1 U1" and s2: "s \<in> cone t2 U2"
  from assms(3) have eq0: "insert x (U - {x}) = U" by blast
  have "x \<notin> U - {x}" by simp
  hence "cone t (U - {x}) \<inter> cone (Poly_Mapping.single x 1 + t) (insert x (U - {x})) = {}"
    by (rule cone_insert_disjoint)
  hence "cone t (U - {x}) \<inter> cone (Poly_Mapping.single x 1 + t) U = {}"
    by (simp only: eq0)
  moreover have "cone t (U - {x}) \<inter> cone t' U' = {}" if "(t', U') \<in> ?Q" for t' U'
  proof -
    from that have "(t', U') \<in> P" and "(t', U') \<noteq> (t, U)" by simp_all
    {
      fix s'
      assume "s' \<in> cone t' U'"
      assume "s' \<in> cone t (U - {x})"
      also from Diff_subset have "\<dots> \<subseteq> cone t U" by (rule cone_mono_2)
      finally have "s' \<in> cone t U" .
      with assms(1) \<open>(t', U') \<in> P\<close> assms(2) \<open>s' \<in> cone t' U'\<close> have "(t', U') = (t, U)"
        by (rule cone_decompD)
      with \<open>(t', U') \<noteq> (t, U)\<close> have False ..
    }
    thus ?thesis by blast
  qed
  moreover have "cone (Poly_Mapping.single x 1 + t) U \<inter> cone t' U' = {}" if "(t', U') \<in> ?Q" for t' U'
  proof -
    from that have "(t', U') \<in> P" and "(t', U') \<noteq> (t, U)" by simp_all
    {
      fix s'
      assume "s' \<in> cone t' U'"
      assume "s' \<in> cone (Poly_Mapping.single x 1 + t) U"
      also have "\<dots> \<subseteq> cone t U" by (rule cone_mono_1, rule PPs_closed_single, fact)
      finally have "s' \<in> cone t U" .
      with assms(1) \<open>(t', U') \<in> P\<close> assms(2) \<open>s' \<in> cone t' U'\<close> have "(t', U') = (t, U)"
        by (rule cone_decompD)
      with \<open>(t', U') \<noteq> (t, U)\<close> have False ..
    }
    thus ?thesis by blast
  qed
  moreover from assms(1) _ _ s1 s2 have "(t1, U1) = (t2, U2)" if "(t1, U1) \<in> ?Q" and "(t2, U2) \<in> ?Q"
  proof (rule cone_decompD)
    from that(1) show "(t1, U1) \<in> P" by simp
  next
    from that(2) show "(t2, U2) \<in> P" by simp
  qed
  ultimately show "(t1, U1) = (t2, U2)" using t1 t2 s1 s2
    by (smt insertE insert_disjoint(1) mk_disjoint_insert prod.sel)
qed

subsection \<open>Functions \<open>shift\<close> and \<open>exact\<close>\<close>

context
  fixes k m :: nat
begin

context
  fixes d :: nat
begin

definition shift2_inv :: "(('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> bool" where
  "shift2_inv Q \<longleftrightarrow> finite Q \<and> standard_decomp k Q \<and> exact_decomp (Suc m) Q \<and>
                         (\<forall>d0<d. card {q \<in> Q. deg_pm (fst q) = d0 \<and> m < card (snd q)} \<le> 1)"

fun shift1_inv :: "((('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<times> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set) \<Rightarrow> bool" where
  "shift1_inv (Q, B) \<longleftrightarrow> B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)} \<and> shift2_inv Q"

lemma shift2_invI:
  "finite Q \<Longrightarrow> standard_decomp k Q \<Longrightarrow> exact_decomp (Suc m) Q \<Longrightarrow>
    (\<And>d0. d0 < d \<Longrightarrow> card {q \<in> Q. deg_pm (fst q) = d0 \<and> m < card (snd q)} \<le> 1) \<Longrightarrow>
    shift2_inv Q"
  by (simp add: shift2_inv_def)

lemma shift2_invD:
  assumes "shift2_inv Q"
  shows "finite Q" and "standard_decomp k Q" and "exact_decomp (Suc m) Q"
    and "d0 < d \<Longrightarrow> card {q \<in> Q. deg_pm (fst q) = d0 \<and> m < card (snd q)} \<le> 1"
  using assms by (simp_all add: shift2_inv_def)

lemma shift1_invI:
  "B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)} \<Longrightarrow> shift2_inv Q \<Longrightarrow> shift1_inv (Q, B)"
  by simp

lemma shift1_invD:
  assumes "shift1_inv (Q, B)"
  shows "B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}" and "shift2_inv Q"
  using assms by simp_all

declare shift1_inv.simps[simp del]

lemma shift1_inv_finite_snd:
  assumes "shift1_inv (Q, B)"
  shows "finite B"
proof (rule finite_subset)
  from assms have "B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}" by (rule shift1_invD)
  also have "\<dots> \<subseteq> Q" by blast
  finally show "B \<subseteq> Q" .
next
  from assms have "shift2_inv Q" by (rule shift1_invD)
  thus "finite Q" by (rule shift2_invD)
qed

lemma shift1_inv_some_snd:
  assumes "shift1_inv (Q, B)" and "1 < card B" and "(t, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)"
  shows "(t, U) \<in> B" and "(t, U) \<in> Q" and "deg_pm t = d" and "card U = Suc m"
proof -
  define A where "A = {q \<in> B. card (snd q) = Suc m}"
  define Y where "Y = {q \<in> Q. deg_pm (fst q) = d \<and> Suc m < card (snd q)}"
  from assms(1) have B: "B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}" and inv2: "shift2_inv Q"
    by (rule shift1_invD)+
  have B': "B = A \<union> Y" by (auto simp: B A_def Y_def)
  have "finite A"
  proof (rule finite_subset)
    show "A \<subseteq> B" unfolding A_def by blast
  next
    from assms(1) show "finite B" by (rule shift1_inv_finite_snd)
  qed
  moreover have "finite Y"
  proof (rule finite_subset)
    show "Y \<subseteq> Q" unfolding Y_def by blast
  next
    from inv2 show "finite Q" by (rule shift2_invD)
  qed
  moreover have "A \<inter> Y = {}" by (auto simp: A_def Y_def)
  ultimately have "card (A \<union> Y) = card A + card Y" by (rule card_Un_disjoint)
  with assms(2) have "1 < card A + card Y" by (simp only: B')
  moreover have "card Y \<le> 1"
  proof (rule card_le_1I)
    fix q1 q2 :: "('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set"
    obtain t1 U1 where q1: "q1 = (t1, U1)" using prod.exhaust by blast
    obtain t2 U2 where q2: "q2 = (t2, U2)" using prod.exhaust by blast
    assume "q1 \<in> Y"
    hence "(t1, U1) \<in> Q" and "deg_pm t1 = d" and "Suc m < card U1" by (simp_all add: q1 Y_def)
    assume "q2 \<in> Y"
    hence "(t2, U2) \<in> Q" and "deg_pm t2 = d" and "Suc m < card U2" by (simp_all add: q2 Y_def)
    from this(2) have "deg_pm t1 = deg_pm t2" by (simp only: \<open>deg_pm t1 = d\<close>)
    from inv2 have "exact_decomp (Suc m) Q" by (rule shift2_invD)
    thus "q1 = q2" unfolding q1 q2 by (rule exact_decompD) fact+
  qed
  ultimately have "0 < card A" by simp
  hence "A \<noteq> {}" by auto
  then obtain a where "a \<in> A" by blast
  have "(t, U) \<in> B \<and> card (snd (t, U)) = Suc m" unfolding assms(3)
  proof (rule someI)
    from \<open>a \<in> A\<close> show "a \<in> B \<and> card (snd a) = Suc m" by (simp add: A_def)
  qed
  thus "(t, U) \<in> B" and "card U = Suc m" by simp_all
  from this(1) show "(t, U) \<in> Q" and "deg_pm t = d" by (simp_all add: B)
qed

lemma shift1_inv_preserved:
  assumes "shift1_inv (Q, B)" and "1 < card B" and "(t, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)"
    and "x = (SOME y. y \<in> U)"
  shows "shift1_inv (insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (Q - {(t, U)})), B - {(t, U)})"
      (is "shift1_inv (insert ?p1 (insert ?p2 ?Q), ?B)")
proof -
  from assms(1, 2, 3) have "(t, U) \<in> B" and "(t, U) \<in> Q" and deg_t: "deg_pm t = d"
    and card_U: "card U = Suc m" by (rule shift1_inv_some_snd)+
  from card_U have "U \<noteq> {}" by auto
  then obtain y where "y \<in> U" by blast
  hence "x \<in> U" unfolding assms(4) by (rule someI)
  with card_U have card_Ux: "card (U - {x}) = m"
    by (metis card_Diff_singleton card_infinite diff_Suc_1 nat.simps(3))
  from assms(1) have B: "B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}" and inv2: "shift2_inv Q"
    by (rule shift1_invD)+
  from inv2 have "finite Q" by (rule shift2_invD)
  show ?thesis
  proof (intro shift1_invI shift2_invI)
    show "?B = {q \<in> insert ?p1 (insert ?p2 ?Q). deg_pm (fst q) = d \<and> m < card (snd q)}" (is "_ = ?C")
    proof (rule Set.set_eqI)
      fix b
      show "b \<in> ?B \<longleftrightarrow> b \<in> ?C"
      proof
        assume "b \<in> ?C"
        hence "b \<in> insert ?p1 (insert ?p2 ?Q)" and b1: "deg_pm (fst b) = d" and b2: "m < card (snd b)"
          by simp_all
        from this(1) show "b \<in> ?B"
        proof (elim insertE)
          assume "b = ?p1"
          hence "deg_pm (fst b) = Suc d" by (simp add: deg_pm_plus deg_pm_single deg_t)
          thus ?thesis by (simp add: b1)
        next
          assume "b = ?p2"
          hence "card (snd b) = m" by (simp add: card_Ux)
          with b2 show ?thesis by simp
        next
          assume "b \<in> ?Q"
          with b1 b2 show ?thesis by (auto simp: B)
        qed
      qed (auto simp: B)
    qed
  next
    from inv2 have "finite Q" by (rule shift2_invD)
    thus "finite (insert ?p1 (insert ?p2 ?Q))" by simp
  next
    from inv2 have std: "standard_decomp k Q" by (rule shift2_invD)
    have "?B \<noteq> {}"
    proof
      assume "?B = {}"
      hence "B \<subseteq> {(t, U)}" by simp
      with _ have "card B \<le> card {(t, U)}" by (rule card_mono) simp
      with assms(2) show False by simp
    qed
    then obtain t' U' where "(t', U') \<in> B" and "(t', U') \<noteq> (t, U)" by auto
    from this(1) have "(t', U') \<in> Q" and "deg_pm t' = d" and "Suc m \<le> card U'" by (simp_all add: B)
    note std this(1) \<open>(t, U) \<in> Q\<close>
    moreover from \<open>deg_pm t' = d\<close> have "deg_pm t' = deg_pm t" by (simp only: deg_t)
    moreover from \<open>Suc m \<le> card U'\<close> have "card U \<le> card U'" by (simp only: card_U)
    ultimately show "standard_decomp k (insert ?p1 (insert ?p2 ?Q))" by (rule lem_6_2_1) fact+
  next
    from inv2 have exct: "exact_decomp (Suc m) Q" by (rule shift2_invD)
    show "exact_decomp (Suc m) (insert ?p1 (insert ?p2 ?Q))"
    proof (rule exact_decompI)
      fix t' U'
      assume *: "(t', U') \<in> insert ?p1 (insert ?p2 ?Q)"
      thus "t' \<in> .[X]"
      proof (elim insertE)
        assume "(t', U') = ?p1"
        hence t': "t' = Poly_Mapping.single x 1 + t" by simp
        from exct \<open>(t, U) \<in> Q\<close> have "U \<subseteq> X" by (rule exact_decompD)
        with \<open>x \<in> U\<close> have "x \<in> X" ..
        hence "Poly_Mapping.single x 1 \<in> .[X]" by (rule PPs_closed_single)
        moreover from exct \<open>(t, U) \<in> Q\<close> have "t \<in> .[X]" by (rule exact_decompD)
        ultimately show ?thesis unfolding t' by (rule PPs_closed_plus)
      next
        assume "(t', U') = ?p2"
        hence "t' = t" by simp
        also from exct \<open>(t, U) \<in> Q\<close> have "\<dots> \<in> .[X]" by (rule exact_decompD)
        finally show ?thesis .
      next
        assume "(t', U') \<in> ?Q"
        hence "(t', U') \<in> Q" by simp
        with exct show ?thesis by (rule exact_decompD)
      qed

      from * show "U' \<subseteq> X"
      proof (elim insertE)
        assume "(t', U') = ?p1"
        hence "U' = U" by simp
        also from exct \<open>(t, U) \<in> Q\<close> have "\<dots> \<subseteq> X" by (rule exact_decompD)
        finally show ?thesis .
      next
        assume "(t', U') = ?p2"
        hence "U' = U - {x}" by simp
        also have "\<dots> \<subseteq> U" by blast
        also from exct \<open>(t, U) \<in> Q\<close> have "\<dots> \<subseteq> X" by (rule exact_decompD)
        finally show ?thesis .
      next
        assume "(t', U') \<in> ?Q"
        hence "(t', U') \<in> Q" by simp
        with exct show ?thesis by (rule exact_decompD)
      qed
    next
      fix t1 t2 U1 U2
      assume "(t1, U1) \<in> insert ?p1 (insert ?p2 ?Q)" and "Suc m < card U1"
      hence "(t1, U1) \<in> Q" using card_U card_Ux by auto
      assume "(t2, U2) \<in> insert ?p1 (insert ?p2 ?Q)" and "Suc m < card U2"
      hence "(t2, U2) \<in> Q" using card_U card_Ux by auto
      assume "deg_pm t1 = deg_pm t2"
      from exct show "(t1, U1) = (t2, U2)" by (rule exact_decompD) fact+
    qed
  next
    fix d0
    assume "d0 < d"
    from _ \<open>finite Q\<close> have "finite {q \<in> Q. deg_pm (fst q) = d0 \<and> m < card (snd q)}" (is "finite ?A")
      by (rule finite_subset) blast
    moreover have "{q \<in> insert ?p1 (insert ?p2 ?Q). deg_pm (fst q) = d0 \<and> m < card (snd q)} \<subseteq> ?A"
      (is "?C \<subseteq> _")
    proof
      fix q
      assume "q \<in> ?C"
      hence "q = ?p1 \<or> q = ?p2 \<or> q \<in> ?Q" and 1: "deg_pm (fst q) = d0" and 2: "m < card (snd q)"
        by simp_all
      from this(1) show "q \<in> ?A"
      proof (elim disjE)
        assume "q = ?p1"
        hence "d \<le> deg_pm (fst q)" by (simp add: deg_pm_plus deg_t)
        with \<open>d0 < d\<close> show ?thesis by (simp only: 1)
      next
        assume "q = ?p2"
        hence "d \<le> deg_pm (fst q)" by (simp add: deg_pm_plus deg_t)
        with \<open>d0 < d\<close> show ?thesis by (simp only: 1)
      next
        assume "q \<in> ?Q"
        with 1 2 show ?thesis by simp
      qed
    qed
    ultimately have "card ?C \<le> card ?A" by (rule card_mono)
    also from inv2 \<open>d0 < d\<close> have "\<dots> \<le> 1" by (rule shift2_invD)
    finally show "card ?C \<le> 1" .
  qed
qed

function (domintros) shift1 :: "((('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<times> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set) \<Rightarrow>
                                ((('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<times> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set)" where
  "shift1 (Q, B) =
      (if 1 < card B then
        let (t, U) = SOME b. b \<in> B \<and> card (snd b) = Suc m; x = SOME y. y \<in> U in
          shift1 (insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (Q - {(t, U)})), B - {(t, U)})
      else (Q, B))"
  by auto

lemma shift1_domI:
  assumes "shift1_inv args"
  shows "shift1_dom args"
proof -
  from wf_measure[of "card \<circ> snd"] show ?thesis using assms
  proof (induct)
    case (less args)
    obtain Q B where args: "args = (Q, B)" using prod.exhaust by blast
    have IH: "shift1_dom (Q0, B0)" if "card B0 < card B" and "shift1_inv (Q0, B0)" for Q0 B0
      using _ that(2)
    proof (rule less)
      from that(1) show "((Q0, B0), args) \<in> measure (card \<circ> snd)" by (simp add: args)
    qed
    from less(2) have inv: "shift1_inv (Q, B)" by (simp only: args)
    show ?case unfolding args
    proof (rule shift1.domintros)
      fix t U
      assume tU: "(t, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)"
      define x where "x = (SOME y. y \<in> U)"
      assume "Suc 0 < card B"
      hence "1 < card B" by simp
      have "shift1_dom
              (insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (Q - {(t, U)})),
              B - {(t, U)})" (is "shift1_dom (insert ?p1 (insert ?p2 ?Q), ?B)")
      proof (rule IH)
        from inv have "finite B" by (rule shift1_inv_finite_snd)
        moreover from inv \<open>1 < card B\<close> tU have "(t, U) \<in> B" by (rule shift1_inv_some_snd)
        ultimately show "card ?B < card B" by (rule card_Diff1_less)
      next
        from inv \<open>1 < card B\<close> tU x_def show "shift1_inv (insert ?p1 (insert ?p2 ?Q), ?B)"
          by (rule shift1_inv_preserved)
      qed
      thus "shift1_dom (insert (Poly_Mapping.single x (Suc 0) + t, U)
                          (insert (t, U - {x}) (Q - {SOME b. b \<in> B \<and> card (snd b) = Suc m})),
                    B - {SOME b. b \<in> B \<and> card (snd b) = Suc m})" by (simp add: tU)
    qed
  qed
qed

lemma shift1_induct [consumes 1, case_names base step]:
  assumes "shift1_inv args"
  assumes "\<And>Q B. shift1_inv (Q, B) \<Longrightarrow> card B \<le> 1 \<Longrightarrow> P (Q, B) (Q, B)"
  assumes "\<And>Q B t U x. shift1_inv (Q, B) \<Longrightarrow> 1 < card B \<Longrightarrow>
            (t, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m) \<Longrightarrow> x = (SOME y. y \<in> U) \<Longrightarrow>
            finite U \<Longrightarrow> x \<in> U \<Longrightarrow> card (U - {x}) = m \<Longrightarrow>
            P (insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (Q - {(t, U)})), B - {(t, U)})
                (shift1 (insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (Q - {(t, U)})), B - {(t, U)})) \<Longrightarrow>
            P (Q, B) (shift1 (insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (Q - {(t, U)})), B - {(t, U)}))"
  shows "P args (shift1 args)"
proof -
  from assms(1) have "shift1_dom args" by (rule shift1_domI)
  thus ?thesis using assms(1)
  proof (induct args rule: shift1.pinduct)
    case step: (1 Q B)
    obtain t U where tU: "(t, U) = (SOME b. b \<in> B \<and> card (snd b) = Suc m)" by (smt prod.exhaust)
    define x where "x = (SOME y. y \<in> U)"
    show ?case
    proof (simp add: shift1.psimps[OF step.hyps(1)] tU[symmetric] x_def[symmetric] del: One_nat_def,
          intro conjI impI)
      let ?args = "(insert (Poly_Mapping.single x 1 + t, U) (insert (t, U - {x}) (Q - {(t, U)})), B - {(t, U)})"
      assume "1 < card B"
      with step.prems have card_U: "card U = Suc m" using tU by (rule shift1_inv_some_snd)
      from card_U have "finite U" using card_infinite by fastforce
      from card_U have "U \<noteq> {}" by auto
      then obtain y where "y \<in> U" by blast
      hence "x \<in> U" unfolding x_def by (rule someI)
      with step.prems \<open>1 < card B\<close> tU x_def \<open>finite U\<close> show "P (Q, B) (shift1 ?args)"
      proof (rule assms(3))
        from \<open>finite U\<close> \<open>x \<in> U\<close> show "card (U - {x}) = m" by (simp add: card_U)
      next
        from \<open>1 < card B\<close> refl tU x_def show "P ?args (shift1 ?args)"
        proof (rule step.hyps)
          from step.prems \<open>1 < card B\<close> tU x_def show "shift1_inv ?args" by (rule shift1_inv_preserved)
        qed
      qed
    next
      assume "\<not> 1 < card B"
      hence "card B \<le> 1" by simp
      with step.prems show "P (Q, B) (Q, B)" by (rule assms(2))
    qed
  qed
qed

lemma shift1_1:
  assumes "shift1_inv args" and "d0 \<le> d"
  shows "card {q \<in> fst (shift1 args). deg_pm (fst q) = d0 \<and> m < card (snd q)} \<le> 1"
  using assms(1)
proof (induct args rule: shift1_induct)
  case (base Q B)
  from assms(2) have "d0 < d \<or> d0 = d" by auto
  thus ?case
  proof
    from base(1) have "shift2_inv Q" by (rule shift1_invD)
    moreover assume "d0 < d"
    ultimately show ?thesis unfolding fst_conv by (rule shift2_invD)
  next
    assume "d0 = d"
    from base(1) have "B = {q \<in> fst (Q, B). deg_pm (fst q) = d0 \<and> m < card (snd q)}"
      unfolding fst_conv \<open>d0 = d\<close> by (rule shift1_invD)
    with base(2) show ?thesis by simp
  qed
qed

lemma shift1_2:
  "shift1_inv args \<Longrightarrow> card {q \<in> fst (shift1 args). m < card (snd q)} \<le> card {q \<in> fst args. m < card (snd q)}"
proof (induct args rule: shift1_induct)
  case (base Q B)
  show ?case ..
next
  case (step Q B t U x)
  let ?p1 = "(Poly_Mapping.single x 1 + t, U)"
  let ?A = "{q \<in> Q. m < card (snd q)}"
  from step(1-3) have card_U: "card U = Suc m" and "(t, U) \<in> Q" by (rule shift1_inv_some_snd)+
  from step(1) have "shift2_inv Q" by (rule shift1_invD)
  hence "finite Q" by (rule shift2_invD)
  with _ have fin1: "finite ?A" by (rule finite_subset) blast
  hence fin2: "finite (insert ?p1 ?A)" by simp
  from \<open>(t, U) \<in> Q\<close> have tU_in: "(t, U) \<in> insert ?p1 ?A" by (simp add: card_U)
  have "?p1 \<noteq> (t, U)" by rule (simp add: monomial_0_iff)
  let ?Q = "insert ?p1 (insert (t, U - {x}) (Q - {(t, U)}))"
  have "{q \<in> fst (?Q, B - {(t, U)}). m < card (snd q)} = (insert ?p1 ?A) - {(t, U)}"
    using step(7) card_U \<open>?p1 \<noteq> (t, U)\<close> by force
  also from fin2 tU_in have "card \<dots> = card (insert ?p1 ?A) - 1" by (simp add: card_Diff_singleton_if)
  thm card_Diff_singleton_if
  also from fin1 have "\<dots> \<le> Suc (card ?A) - 1" by (simp add: card_insert_if)
  also have "\<dots> = card {q \<in> fst (Q, B). m < card (snd q)}" by simp
  finally have "card {q \<in> fst (?Q, B - {(t, U)}). m < card (snd q)} \<le> card {q \<in> fst (Q, B). m < card (snd q)}" .
  with step(8) show ?case by (rule le_trans)
qed

lemma shift1_3: "shift1_inv args \<Longrightarrow> cone_decomp T (fst args) \<Longrightarrow> cone_decomp T (fst (shift1 args))"
proof (induct args rule: shift1_induct)
  case (base Q B)
  from base(3) show ?case .
next
  case (step Q B t U x)
  from step.prems have "cone_decomp T Q" by (simp only: fst_conv)
  moreover from step.hyps(1-3) have "(t, U) \<in> Q" by (rule shift1_inv_some_snd)
  ultimately have "cone_decomp T (fst (insert (Poly_Mapping.single x 1 + t, U)
                      (insert (t, U - {x}) (Q - {(t, U)})), B - {(t, U)}))"
    unfolding fst_conv using step.hyps(6) by (rule lem_6_2_2)
  thus ?case by (rule step.hyps(8))
qed

lemma shift1_4:
  "shift1_inv args \<Longrightarrow> Max (deg_pm ` fst ` fst args) \<le> Max (deg_pm ` fst ` fst (shift1 args))"
proof (induct args rule: shift1_induct)
  case (base Q B)
  show ?case ..
next
  case (step Q B t U x)
  let ?p1 = "(Poly_Mapping.single x 1 + t, U)"
  let ?Q = "insert ?p1 (insert (t, U - {x}) (Q - {(t, U)}))"
  from step(1) have "B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}" and inv2: "shift2_inv Q"
    by (rule shift1_invD)+
  from this(1) have "B \<subseteq> Q" by auto
  with step(2) have "Q \<noteq> {}" by auto
  from inv2 have "finite Q" by (rule shift2_invD)
  hence "finite ?Q" by simp
  hence fin: "finite (deg_pm ` fst ` ?Q)" by (intro finite_imageI)
  have "Max (deg_pm ` fst ` fst (Q, B)) \<le> Max (deg_pm ` fst ` fst (?Q, B - {(t, U)}))"
    unfolding fst_conv
  proof (rule Max.boundedI)
    from \<open>finite Q\<close> show "finite (deg_pm ` fst ` Q)" by (intro finite_imageI)
  next
    from \<open>Q \<noteq> {}\<close> show "deg_pm ` fst ` Q \<noteq> {}" by simp
  next
    fix a
    assume "a \<in> deg_pm ` fst ` Q"
    then obtain q where "q \<in> Q" and a: "a = deg_pm (fst q)" by blast
    show "a \<le> Max (deg_pm ` fst ` ?Q)"
    proof (cases "q = (t, U)")
      case True
      hence "a \<le> deg_pm (fst ?p1)" by (simp add: a deg_pm_plus)
      also from fin have "\<dots> \<le> Max (deg_pm ` fst ` ?Q)"
      proof (rule Max_ge)
        have "?p1 \<in> ?Q" by simp
        thus "deg_pm (fst ?p1) \<in> deg_pm ` fst ` ?Q" by (intro imageI)
      qed
      finally show ?thesis .
    next
      case False
      with \<open>q \<in> Q\<close> have "q \<in> ?Q" by simp
      hence "a \<in> deg_pm ` fst ` ?Q" unfolding a by (intro imageI)
      with fin show ?thesis by (rule Max_ge)
    qed
  qed
  thus ?case using step(8) by (rule le_trans)
qed

lemma shift1_5: "shift1_inv args \<Longrightarrow> fst (shift1 args) = {} \<longleftrightarrow> fst args = {}"
proof (induct args rule: shift1_induct)
  case (base Q B)
  show ?case ..
next
  case (step Q B t U x)
  let ?p1 = "(Poly_Mapping.single x 1 + t, U)"
  let ?Q = "insert ?p1 (insert (t, U - {x}) (Q - {(t, U)}))"
  from step(1) have "B = {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}" and inv2: "shift2_inv Q"
    by (rule shift1_invD)+
  from this(1) have "B \<subseteq> Q" by auto
  with step(2) have "Q \<noteq> {}" by auto
  thm step.hyps
  moreover have "fst (local.shift1 (?Q, B - {(t, U)})) \<noteq> {}"
    by (simp add: step.hyps(8) del: One_nat_def)
  ultimately show ?case by simp
qed

end

lemma shift2_inv_preserved:
  assumes "shift2_inv d Q"
  shows "shift2_inv (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})))"
proof -
  define args where "args = (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})"
  from refl assms have inv1: "shift1_inv d args" unfolding args_def
    by (rule shift1_invI)
  hence "shift1_inv d (shift1 args)" by (induct args rule: shift1_induct)
  hence "shift1_inv d (fst (shift1 args), snd (shift1 args))" by simp
  hence "shift2_inv d (fst (shift1 args))" by (rule shift1_invD)
  hence "finite (fst (shift1 args))" and "standard_decomp k (fst (shift1 args))"
    and "exact_decomp (Suc m) (fst (shift1 args))" by (rule shift2_invD)+
  thus "shift2_inv (Suc d) (fst (shift1 args))"
  proof (rule shift2_invI)
    fix d0
    assume "d0 < Suc d"
    hence "d0 \<le> d" by simp
    with inv1 show "card {q \<in> fst (shift1 args). deg_pm (fst q) = d0 \<and> m < card (snd q)} \<le> 1"
      by (rule shift1_1)
  qed
qed

function shift2 :: "nat \<Rightarrow> nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set" where
  "shift2 c d Q =
      (if c \<le> d then Q
      else shift2 c (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}))))"
  by auto
termination proof
  show "wf (measure (\<lambda>(c, d, _). c - d))" by (fact wf_measure)
qed simp

lemma shift2_1: "shift2_inv d Q \<Longrightarrow> shift2_inv c (shift2 c d Q)"
proof (induct c d Q rule: shift2.induct)
  case IH: (1 c d Q)
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro conjI impI)
    assume "c \<le> d"
    show "shift2_inv c Q"
    proof (rule shift2_invI)
      from IH(2) show "finite Q" and "standard_decomp k Q" and "exact_decomp (Suc m) Q"
        by (rule shift2_invD)+
    next
      fix d0
      assume "d0 < c"
      hence "d0 < d" using \<open>c \<le> d\<close> by (rule less_le_trans)
      with IH(2) show "card {q \<in> Q. deg_pm (fst q) = d0 \<and> m < card (snd q)} \<le> 1" by (rule shift2_invD)
    qed
  next
    assume "\<not> c \<le> d"
    thus "shift2_inv c (shift2 c (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}))))"
    proof (rule IH)
      from IH(2) show "shift2_inv (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})))"
        by (rule shift2_inv_preserved)
    qed
  qed
qed

lemma shift2_2:
  "shift2_inv d Q \<Longrightarrow> card {q \<in> shift2 c d Q. m < card (snd q)} \<le> card {q \<in> Q. m < card (snd q)}"
proof (induct c d Q rule: shift2.induct)
  case IH: (1 c d Q)
  let ?A = "{q \<in> shift2 c (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}))). m < card (snd q)}"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    hence "card ?A \<le> card {q \<in> fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})). m < card (snd q)}"
    proof (rule IH)
      from IH(2) show "shift2_inv (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})))"
        by (rule shift2_inv_preserved)
    qed
    also from refl IH(2) have "\<dots> \<le> card {q \<in> fst (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}). m < card (snd q)}"
      by (intro shift1_2 shift1_invI)
    finally show "card ?A \<le> card {q \<in> Q. m < card (snd q)}" by (simp only: fst_conv)
  qed
qed

lemma shift2_3: "shift2_inv d Q \<Longrightarrow> cone_decomp T Q \<Longrightarrow> cone_decomp T (shift2 c d Q)"
proof (induct c d Q rule: shift2.induct)
  case IH: (1 c d Q)
  from IH(2) have inv2: "shift2_inv (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})))"
    by (rule shift2_inv_preserved)
  show ?case
  proof (subst shift2.simps, simp add: IH.prems del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    moreover note inv2
    moreover have "cone_decomp T (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})))"
    proof (rule shift1_3)
      from refl IH(2) show "shift1_inv d (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})"
        by (rule shift1_invI)
    qed (simp add: IH.prems)
    ultimately show "cone_decomp T (shift2 c (Suc d) (fst (shift1 (Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)}))))"
      by (rule IH)
  qed
qed

lemma shift2_4:
  "shift2_inv d Q \<Longrightarrow> Max (deg_pm ` fst ` Q) \<le> Max (deg_pm ` fst ` shift2 c d Q)"
proof (induct c d Q rule: shift2.induct)
  case IH: (1 c d Q)
  let ?args = "(Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    from refl IH(2) have "Max (deg_pm ` fst ` fst ?args) \<le> Max (deg_pm ` fst ` fst (shift1 ?args))"
      by (intro shift1_4 shift1_invI)
    also from \<open>\<not> c \<le> d\<close> have "\<dots> \<le> Max (deg_pm ` fst ` shift2 c (Suc d) (fst (shift1 ?args)))"
    proof (rule IH)
      from IH(2) show "shift2_inv (Suc d) (fst (shift1 ?args))"
        by (rule shift2_inv_preserved)
    qed
    finally show "Max (deg_pm ` fst ` Q) \<le> Max (deg_pm ` fst ` shift2 c (Suc d) (fst (shift1 ?args)))"
      by (simp only: fst_conv)
  qed
qed

lemma shift2_5:
  "shift2_inv d Q \<Longrightarrow> shift2 c d Q = {} \<longleftrightarrow> Q = {}"
proof (induct c d Q rule: shift2.induct)
  case IH: (1 c d Q)
  let ?args = "(Q, {q \<in> Q. deg_pm (fst q) = d \<and> m < card (snd q)})"
  show ?case
  proof (subst shift2.simps, simp del: shift2.simps, intro impI)
    assume "\<not> c \<le> d"
    hence "shift2 c (Suc d) (fst (shift1 ?args)) = {} \<longleftrightarrow> fst (shift1 ?args) = {}"
    proof (rule IH)
      from IH(2) show "shift2_inv (Suc d) (fst (shift1 ?args))"
        by (rule shift2_inv_preserved)
    qed
    also from refl IH(2) have "\<dots> \<longleftrightarrow> fst ?args = {}" by (intro shift1_5 shift1_invI)
    finally show "shift2 c (Suc d) (fst (shift1 ?args)) = {} \<longleftrightarrow> Q = {}" by (simp only: fst_conv)
  qed
qed

definition shift :: "(('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set"
  where "shift Q = shift2 (k + card {q \<in> Q. m < card (snd q)}) k Q"

lemma shift2_inv_init:
  assumes "finite Q" and "standard_decomp k Q" and "exact_decomp (Suc m) Q"
  shows "shift2_inv k Q"
  using assms
proof (rule shift2_invI)
  fix d0
  assume "d0 < k"
  have "{q \<in> Q. deg_pm (fst q) = d0 \<and> m < card (snd q)} = {}"
  proof -
    {
      fix q
      assume "q \<in> Q"
      obtain t U where q: "q = (t, U)" using prod.exhaust by blast
      assume "deg_pm (fst q) = d0" and "m < card (snd q)"
      hence "deg_pm t < k" and "m < card U" using \<open>d0 < k\<close> by (simp_all add: q)
      from this(2) have "U \<noteq> {}" by auto
      with \<open>q \<in> Q\<close> have "(t, U) \<in> Q\<^sub>+" by (simp add: q pos_decomp_def)
      with assms(2) have "k \<le> deg_pm t" by (rule standard_decompD)
      with \<open>deg_pm t < k\<close> have False by simp
    }
    thus ?thesis by blast
  qed
  thus "card {q \<in> Q. deg_pm (fst q) = d0 \<and> m < card (snd q)} \<le> 1" by (simp only: card_empty)
qed

lemma shift:
  assumes "finite Q" and "standard_decomp k Q" and "exact_decomp (Suc m) Q"
  shows "finite (shift Q)" and "standard_decomp k (shift Q)" and "exact_decomp m (shift Q)"
proof -
  define c where "c = card {q \<in> Q. m < card (snd q)}"
  define A where "A = {q \<in> shift Q. m < card (snd q)}"
  from assms have "shift2_inv k Q" by (rule shift2_inv_init)
  hence inv2: "shift2_inv (k + c) (shift Q)" and "card A \<le> c"
    unfolding shift_def c_def A_def by (rule shift2_1, rule shift2_2)
  from inv2 have fin: "finite (shift Q)" and std: "standard_decomp k (shift Q)"
    and exct: "exact_decomp (Suc m) (shift Q)"
    by (rule shift2_invD)+
  show "finite (shift Q)" and "standard_decomp k (shift Q)" by fact+
  from _ this(1) have "finite A" unfolding A_def by (rule finite_subset) blast

  show "exact_decomp m (shift Q)"
  proof (rule exact_decompI)
    fix t U
    assume "(t, U) \<in> shift Q"
    with exct show "t \<in> .[X]" and "U \<subseteq> X" by (rule exact_decompD)+
  next
    fix t1 t2 U1 U2
    assume 1: "(t1, U1) \<in> shift Q" and 2: "(t2, U2) \<in> shift Q"
    assume 3: "deg_pm t1 = deg_pm t2" and 4: "m < card U1" and 5: "m < card U2"
    from 5 have "U2 \<noteq> {}" by auto
    with 2 have "(t2, U2) \<in> (shift Q)\<^sub>+" by (simp add: pos_decomp_def)
    let ?C = "{q \<in> shift Q. deg_pm (fst q) = deg_pm t2 \<and> m < card (snd q)}"
    define B where "B = {q \<in> A. k \<le> deg_pm (fst q) \<and> deg_pm (fst q) \<le> deg_pm t2}"
    have "Suc (deg_pm t2) - k \<le> card B"
    proof -
      have "B = (\<Union>d0\<in>{k..deg_pm t2}. {q \<in> A. deg_pm (fst q) = d0})" by (auto simp: B_def)
      also have "card \<dots> = (\<Sum>d0=k..deg_pm t2. card {q \<in> A. deg_pm (fst q) = d0})"
      proof (intro card_UN_disjoint ballI impI)
        fix d0
        from _ \<open>finite A\<close> show "finite {q \<in> A. deg_pm (fst q) = d0}" by (rule finite_subset) blast
      next
        fix d0 d1 :: nat
        assume "d0 \<noteq> d1"
        thus "{q \<in> A. deg_pm (fst q) = d0} \<inter> {q \<in> A. deg_pm (fst q) = d1} = {}" by blast
      qed (fact finite_atLeastAtMost)
      also have "\<dots> \<ge> (\<Sum>d0=k..deg_pm t2. 1)"
      proof (rule sum_mono)
        fix d0
        assume "d0 \<in> {k..deg_pm t2}"
        hence "k \<le> d0" and "d0 \<le> deg_pm t2" by simp_all
        with std \<open>(t2, U2) \<in> (shift Q)\<^sub>+\<close> obtain t' U' where "(t', U') \<in> shift Q" and "deg_pm t' = d0"
          and "card U2 \<le> card U'" by (rule standard_decompE)
        from 5 this(3) have "m < card U'" by (rule less_le_trans)
        with \<open>(t', U') \<in> shift Q\<close> have "(t', U') \<in> {q \<in> A. deg_pm (fst q) = d0}"
          by (simp add: A_def \<open>deg_pm t' = d0\<close>)
        hence "{q \<in> A. deg_pm (fst q) = d0} \<noteq> {}" by blast
        moreover from _ \<open>finite A\<close> have "finite {q \<in> A. deg_pm (fst q) = d0}"
          by (rule finite_subset) blast
        ultimately show "1 \<le> card {q \<in> A. deg_pm (fst q) = d0}"
          by (simp add: card_gt_0_iff Suc_le_eq)
      qed
      also have "(\<Sum>d0=k..deg_pm t2. 1) = Suc (deg_pm t2) - k" by auto
      finally show ?thesis .
    qed
    also from \<open>finite A\<close> _ have "\<dots> \<le> card A" by (rule card_mono) (auto simp: B_def)
    also have "\<dots> \<le> c" by fact
    finally have "deg_pm t2 < k + c" by simp
    with inv2 have "card ?C \<le> 1" by (rule shift2_invD)
    from _ fin have "finite ?C" by (rule finite_subset) blast
    moreover note \<open>card ?C \<le> 1\<close>
    moreover from 1 3 4 have "(t1, U1) \<in> ?C" by simp
    moreover from 2 5 have "(t2, U2) \<in> ?C" by simp
    ultimately show "(t1, U1) = (t2, U2)" by (rule card_le_1D)
  qed
qed

lemma cone_decomp_shift:
  assumes "standard_decomp k Q" and "exact_decomp (Suc m) Q" and "cone_decomp T Q"
  shows "cone_decomp T (shift Q)"
proof -
  from assms(3) have "finite Q" by (rule cone_decompD)
  hence "shift2_inv k Q" using assms(1, 2) by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def using assms(3) by (rule shift2_3)
qed

lemma Max_shift_ge:
  assumes "finite Q" and "standard_decomp k Q" and "exact_decomp (Suc m) Q"
  shows "Max (deg_pm ` fst ` Q) \<le> Max (deg_pm ` fst ` shift Q)"
proof -
  from assms(1-3) have "shift2_inv k Q" by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def by (rule shift2_4)
qed

lemma shift_empty_iff:
  assumes "finite Q" and "standard_decomp k Q" and "exact_decomp (Suc m) Q"
  shows "shift Q = {} \<longleftrightarrow> Q = {}"
proof -
  from assms(1-3) have "shift2_inv k Q" by (rule shift2_inv_init)
  thus ?thesis unfolding shift_def by (rule shift2_5)
qed

end

primrec exact_aux :: "nat \<Rightarrow> nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set" where
  "exact_aux k 0 Q = Q" |
  "exact_aux k (Suc m) Q = exact_aux k m (shift k m Q)"

lemma exact_aux:
  assumes "finite Q" and "standard_decomp k Q" and "exact_decomp m Q"
  shows "finite (exact_aux k m Q)" (is ?thesis1)
    and "standard_decomp k (exact_aux k m Q)" (is ?thesis2)
    and "exact_decomp 0 (exact_aux k m Q)" (is ?thesis3)
proof -
  from assms have "?thesis1 \<and> ?thesis2 \<and> ?thesis3"
  proof (induct m arbitrary: Q)
    case 0
    thus ?case by simp
  next
    case (Suc m)
    let ?Q = "shift k m Q"
    have "finite (exact_aux k m ?Q) \<and> standard_decomp k (exact_aux k m ?Q) \<and> exact_decomp 0 (exact_aux k m ?Q)"
    proof (rule Suc)
      from Suc.prems show "finite ?Q" and "standard_decomp k ?Q" and "exact_decomp m ?Q"
        by (rule shift)+
    qed
    thus ?case by simp
  qed
  thus ?thesis1 and ?thesis2 and ?thesis3 by simp_all
qed

lemma cone_decomp_exact_aux:
  assumes "standard_decomp k Q" and "exact_decomp m Q" and "cone_decomp T Q"
  shows "cone_decomp T (exact_aux k m Q)"
  using assms
proof (induct m arbitrary: Q)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?Q = "shift k m Q"
  have "cone_decomp T (exact_aux k m ?Q)"
  proof (rule Suc)
    from Suc.prems(3) have "finite Q" by (rule cone_decompD)
    thus "standard_decomp k ?Q" and "exact_decomp m ?Q" using Suc.prems(1, 2)
      by (rule shift)+
  next
    from Suc.prems show "cone_decomp T ?Q" by (rule cone_decomp_shift)
  qed
  thus ?case by simp
qed

lemma Max_exact_aux_ge:
  assumes "finite Q" and "standard_decomp k Q" and "exact_decomp m Q"
  shows "Max (deg_pm ` fst ` Q) \<le> Max (deg_pm ` fst ` exact_aux k m Q)"
  using assms
proof (induct m arbitrary: Q)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?Q = "shift k m Q"
  from Suc.prems have "Max (deg_pm ` fst ` Q) \<le> Max (deg_pm ` fst ` ?Q)" by (rule Max_shift_ge)
  also have "\<dots> \<le> Max (deg_pm ` fst ` exact_aux k m ?Q)"
  proof (rule Suc)
    from Suc.prems show "finite ?Q" and "standard_decomp k ?Q" and "exact_decomp m ?Q"
      by (rule shift)+
  qed
  finally show ?case by simp
qed

lemma exact_aux_empty_iff:
  assumes "finite Q" and "standard_decomp k Q" and "exact_decomp m Q"
  shows "exact_aux k m Q = {} \<longleftrightarrow> Q = {}"
  using assms
proof (induct m arbitrary: Q)
  case 0
  thus ?case by simp
next
  case (Suc m)
  let ?Q = "shift k m Q"
  have "exact_aux k m ?Q = {} \<longleftrightarrow> ?Q = {}"
  proof (rule Suc)
    from Suc.prems show "finite ?Q" and "standard_decomp k ?Q" and "exact_decomp m ?Q"
      by (rule shift)+
  qed
  also from Suc.prems have "\<dots> \<longleftrightarrow> Q = {}" by (rule shift_empty_iff)
  finally show ?case by simp
qed

definition exact :: "nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<times> 'x set) set"
  where "exact k Q = exact_aux k (card X) Q"

lemma exact:
  assumes "finite X" and "finite Q" and "standard_decomp k Q" and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> t \<in> .[X]"
    and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X"
  shows "finite (exact k Q)" (is ?thesis1)
    and "standard_decomp k (exact k Q)" (is ?thesis2)
    and "exact_decomp 0 (exact k Q)" (is ?thesis3)
proof -
  from assms(1, 4, 5) le_refl have "exact_decomp (card X) Q" by (rule exact_decomp_card_X)
  with assms(2, 3) show ?thesis1 and ?thesis2 and ?thesis3 unfolding exact_def by (rule exact_aux)+
qed

lemma cone_decomp_exact:
  assumes "finite X" and "standard_decomp k Q" and "cone_decomp T Q"
    and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> t \<in> .[X]" and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X"
  shows "cone_decomp T (exact k Q)"
proof -
  from assms(1, 4, 5) le_refl have "exact_decomp (card X) Q" by (rule exact_decomp_card_X)
  with assms(2) show ?thesis unfolding exact_def using assms(3) by (rule cone_decomp_exact_aux)
qed

lemma Max_exact_ge:
  assumes "finite X" and "finite Q" and "standard_decomp k Q" and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> t \<in> .[X]"
    and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X"
  shows "Max (deg_pm ` fst ` Q) \<le> Max (deg_pm ` fst ` exact k Q)"
proof -
  from assms(1, 4, 5) le_refl have "exact_decomp (card X) Q" by (rule exact_decomp_card_X)
  with assms(2, 3) show ?thesis unfolding exact_def by (rule Max_exact_aux_ge)
qed

lemma exact_empty_iff:
  assumes "finite X" and "finite Q" and "standard_decomp k Q" and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> t \<in> .[X]"
    and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X"
  shows "exact k Q = {} \<longleftrightarrow> Q = {}"
proof -
  from assms(1, 4, 5) le_refl have "exact_decomp (card X) Q" by (rule exact_decomp_card_X)
  with assms(2, 3) show ?thesis unfolding exact_def by (rule exact_aux_empty_iff)
qed

corollary \<b>_zero_exact:
  assumes "finite X" and "finite Q" and "standard_decomp k Q" and "Q \<noteq> {}"
    and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> t \<in> .[X]" and "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X"
  shows "Suc (Max (deg_pm ` fst ` Q)) \<le> \<b> (exact k Q) 0"
proof -
  from assms(1, 2, 3, 5, 6) have "Max (deg_pm ` fst ` Q) \<le> Max (deg_pm ` fst ` exact k Q)"
    by (rule Max_exact_ge)
  also have "Suc \<dots> \<le> \<b> (exact k Q) 0"
  proof (rule \<b>_zero)
    from assms(1, 2, 3, 5, 6) show "finite (exact k Q)" by (rule exact)
  next
    from assms show "exact k Q \<noteq> {}" by (simp add: exact_empty_iff)
  qed
  finally show ?thesis by simp
qed

lemma ideal_compl_exact_decompE:
  assumes "finite X" and "finite F" and "F \<subseteq> .[X]" and "reduced_basis F" and "I = (\<Union>g\<in>F. cone g X)"
  obtains Q where "standard_decomp 0 Q" and "cone_decomp (.[X] - I) Q" and "exact_decomp 0 Q"
    and "\<And>f. f \<in> F \<Longrightarrow> deg_pm f \<le> \<b> Q 0"
proof -
  define Q where "Q = snd (split 0 X F)"
  from assms(1, 2, 3, 5) have std: "standard_decomp 0 Q" and cn: "cone_decomp (.[X] - I) Q"
    unfolding Q_def by (rule standard_cone_decomp_snd_split)+
  from cn have fin: "finite Q" by (rule cone_decompD)
  have ".[X] - I \<subseteq> .[X]" by blast
  moreover from cn have eq: ".[X] - I = (\<Union>(t, U)\<in>Q. cone t U)" by (rule cone_decompD)
  ultimately have "cone t U \<subseteq> .[X]" if "(t, U) \<in> Q" for t U using that by blast
  hence 1: "\<And>t U. (t, U) \<in> Q \<Longrightarrow> t \<in> .[X]" and 2: "\<And>t U. (t, U) \<in> Q \<Longrightarrow> U \<subseteq> X"
    by (auto dest: cone_indets)
  let ?Q = "exact 0 Q"
  from assms(1) fin std 1 2 have "standard_decomp 0 ?Q" by (rule exact)
  moreover from assms(1) std cn 1 2 have "cone_decomp (.[X] - I) ?Q" by (rule cone_decomp_exact)
  moreover from assms(1) fin std 1 2 have "exact_decomp 0 ?Q" by (rule exact)
  moreover have "deg_pm f \<le> \<b> ?Q 0" if "f \<in> F" for f
  proof (cases "Q = {}")
    case True
    hence ".[X] - I = {}" by (simp add: eq)
    hence ".[X] \<subseteq> I" by blast
    with zero_in_PPs have "0 \<in> I" ..
    then obtain g where "g \<in> F" and "0 \<in> cone g X" unfolding assms(5) ..
    from this(2) have "g = 0" by (simp only: zero_in_cone_iff)
    with \<open>g \<in> F\<close> have "0 \<in> F" by simp
    with assms(4) have "0 = f" using that zero_adds by (rule reduced_basisD)
    thus ?thesis by simp
  next
    case False
    from assms(1, 2, 4) refl assms(3) have "deg_pm f \<le> Suc (Max (deg_pm ` fst ` Q))"
      unfolding Q_def using that by (rule cor_4_9)
    also from assms(1) fin std False 1 2 have "\<dots> \<le> \<b> ?Q 0" by (rule \<b>_zero_exact)
    finally show ?thesis .
  qed
  ultimately show ?thesis ..
qed

subsection \<open>Hilbert Polynomial\<close>

definition Hilbert_poly :: "(nat \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> int"
  where "Hilbert_poly b d =
                (let n = card X in
                  ((d - b (Suc n) + n) gchoose n) - 1 - (\<Sum>i=1..n. (d - b i + i - 1) gchoose i))"

definition Hilbert_poly_real :: "(nat \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> real"
  where "Hilbert_poly_real b z =
                (let n = card X in
                  ((z - b (Suc n) + n) gchoose n) - 1 - (\<Sum>i=1..n. (z - b i + i - 1) gchoose i))"

lemma real_Hilbert_poly: "of_int (Hilbert_poly b d) = Hilbert_poly_real b (real d)"
  by (simp add: Hilbert_poly_def Hilbert_poly_real_def Let_def of_int_gbinomial)

lemma Hilbert_fun_eq_Hilbert_poly_plus_card:
  assumes "finite X" and "cone_decomp T P" and "standard_decomp k P" and "exact_decomp 0 P"
    and "\<b> P (Suc 0) \<le> d"
  shows "int (Hilbert_fun T d) = card {t. (t, {}) \<in> P \<and> deg_pm t = d} + Hilbert_poly (\<b> P) d"
proof (cases "X = {}")
  case True
  have H: "Hilbert_poly b z = 0" for b z by (simp add: Hilbert_poly_def Let_def) (simp add: True)
  from assms(2) have T: "T = (\<Union>(t, U)\<in>P. cone t U)" by (rule cone_decompD)
  have "P \<subseteq> {(0, {})}"
  proof
    fix p
    assume "p \<in> P"
    moreover obtain t U where p: "p = (t, U)" using prod.exhaust by blast
    ultimately have "(t, U) \<in> P" by simp
    with assms(4) have "t \<in> .[X]" and "U \<subseteq> X" by (rule exact_decompD)+
    thus "p \<in> {(0, {})}" by (simp add: True p)
  qed
  hence "P = {} \<or> P = {(0, {})}" by blast
  thus ?thesis
  proof
    assume "P = {}"
    moreover from this have "T = {}" by (simp add: T)
    ultimately show ?thesis by (simp add: Hilbert_fun_def H)
  next
    assume P: "P = {(0, {})}"
    hence Pp: "{(0, {})}\<^sub>+ = {}" and T: "T = {0}" by (simp_all add: pos_decomp_def T)
    show ?thesis
    proof (cases "d = 0")
      case True
      thus ?thesis using card_Suc_eq by (fastforce simp: P Pp T Hilbert_fun_def H)
    next
      case False
      thus ?thesis by (simp add: P Pp T Hilbert_fun_def H)
    qed
  qed
next
  case False
  moreover define n where "n = card X"
  ultimately have "0 < n" using assms(1) by (simp add: card_gt_0_iff)
  hence "1 \<le> n" and "Suc 0 \<le> n" by simp_all
  from assms(2) have "finite P" by (rule cone_decompD)
  with assms(1, 4) have "finite_decomp P" by (rule exact_decomp_imp_finite_decomp)
  from pos_decomp_subset have eq0: "(P - P\<^sub>+) \<union> P\<^sub>+ = P" by blast
  from pos_decomp_subset \<open>finite P\<close> have fin1: "finite (P\<^sub>+)" by (rule finite_subset)
  have "P - P\<^sub>+ \<subseteq> P" by blast
  hence fin2: "finite (P - P\<^sub>+)" using \<open>finite P\<close> by (rule finite_subset)

  have "(\<Sum>(t, U)\<in>P - P\<^sub>+. Hilbert_fun (cone t U) d) = (\<Sum>(t, U)\<in>P - P\<^sub>+. if deg_pm t = d then 1 else 0)"
    using refl
  proof (rule sum.cong)
    fix x
    assume "x \<in> P - P\<^sub>+"
    moreover obtain t U where x: "x = (t, U)" using prod.exhaust by blast
    ultimately have "U = {}" by (simp add: pos_decomp_def)
    hence "{s \<in> cone t U. deg_pm s = d} = (if deg_pm t = d then {t} else {})" by (auto simp: Hilbert_fun_def)
    also have "card \<dots> = (if deg_pm t = d then 1 else 0)" by simp
    finally have "Hilbert_fun (cone t U) d = (if deg_pm t = d then 1 else 0)" by (simp only: Hilbert_fun_def)
    thus "(case x of (t, U) \<Rightarrow> Hilbert_fun (cone t U) d) = (case x of (t, U) \<Rightarrow> if deg_pm t = d then 1 else 0)"
      by (simp add: x)
  qed
  also from fin2 have "\<dots> = (\<Sum>(t, U)\<in>{(t', U') \<in> P - P\<^sub>+. deg_pm t' = d}. 1)"
    by (rule sum.mono_neutral_cong_right) (auto split: if_splits)
  also have "\<dots> = card {(t, U) \<in> P - P\<^sub>+. deg_pm t = d}" by auto
  also have "\<dots> = card {t. (t, {}) \<in> P \<and> deg_pm t = d}" by (fact card_Diff_pos_decomp)
  finally have eq1: "(\<Sum>(t, U)\<in>P - P\<^sub>+. Hilbert_fun (cone t U) d) = card {t. (t, {}) \<in> P \<and> deg_pm t = d}" .

  let ?f = "\<lambda>a b. (int d) - a + b gchoose b"
  have "int (\<Sum>(t, U)\<in>P\<^sub>+. Hilbert_fun (cone t U) d) = (\<Sum>(t, U)\<in>P\<^sub>+. int (Hilbert_fun (cone t U) d))"
    by (simp add: int_sum prod.case_distrib)
  also have "\<dots> = (\<Sum>(t, U)\<in>(\<Union>i\<in>{1..n}. {(t, U) \<in> P\<^sub>+. card U = i}). ?f (deg_pm t) (card U - 1))"
  proof (rule sum.cong)
    show "P\<^sub>+ = (\<Union>i\<in>{1..n}. {(t, U). (t, U) \<in> P\<^sub>+ \<and> card U = i})"
    proof (rule Set.set_eqI, rule)
      fix x
      assume "x \<in> P\<^sub>+"
      moreover obtain t U where x: "x = (t, U)" using prod.exhaust by blast
      ultimately have "(t, U) \<in> P\<^sub>+" by simp
      hence "(t, U) \<in> P" and "U \<noteq> {}" by (simp_all add: pos_decomp_def)
      from assms(4) this(1) have "U \<subseteq> X" by (rule exact_decompD)
      hence "finite U" using assms(1) by (rule finite_subset)
      with \<open>U \<noteq> {}\<close> have "0 < card U" by (simp add: card_gt_0_iff)
      moreover from assms(1) \<open>U \<subseteq> X\<close> have "card U \<le> n" unfolding n_def by (rule card_mono)
      ultimately have "card U \<in> {1..n}" by simp
      moreover from \<open>(t, U) \<in> P\<^sub>+\<close> have "(t, U) \<in> {(t', U'). (t', U') \<in> P\<^sub>+ \<and> card U' = card U}"
        by simp
      ultimately show "x \<in> (\<Union>i\<in>{1..n}. {(t, U). (t, U) \<in> P\<^sub>+ \<and> card U = i})" by (simp add: x)
    qed blast
  next
    fix x
    assume "x \<in> (\<Union>i\<in>{1..n}. {(t, U). (t, U) \<in> P\<^sub>+ \<and> card U = i})"
    then obtain j where "j \<in> {1..n}" and "x \<in> {(t, U). (t, U) \<in> P\<^sub>+ \<and> card U = j}" ..
    from this(2) obtain t U where "(t, U) \<in> P\<^sub>+" and "card U = j" and x: "x = (t, U)" by blast
    from \<open>finite_decomp P\<close> assms(3) this(1) have "deg_pm t < \<b> P (Suc 0)" by (rule \<b>_one_gr)
    also have "\<dots> \<le> d" by fact
    finally have "deg_pm t < d" .
    hence int1: "int (d - deg_pm t) = int d - int (deg_pm t)" by simp
    from \<open>card U = j\<close> \<open>j \<in> {1..n}\<close> have "0 < card U" by simp
    hence int2: "int (card U - Suc 0) = int (card U) - 1" by simp
    from \<open>0 < card U\<close> card_ge_0_finite have "finite U" and "U \<noteq> {}" by auto
    hence "Hilbert_fun (cone t U) d = (if deg_pm t \<le> d then (d - deg_pm t + (card U - 1)) choose (card U - 1) else 0)"
      by (rule Hilbert_fun_cone)
    also from \<open>deg_pm t < d\<close> have "\<dots> = (d - deg_pm t + (card U - 1)) choose (card U - 1)" by simp
    finally
    have "int (Hilbert_fun (cone t U) d) = (int d - int (deg_pm t) + (int (card U - 1))) gchoose (card U - 1)"
      by (simp add: int_binomial int1 int2)
    thus "(case x of (t, U) \<Rightarrow> int (Hilbert_fun (cone t U) d)) =
          (case x of (t, U) \<Rightarrow> int d - int (deg_pm t) + (int (card U - 1)) gchoose (card U - 1))"
      by (simp add: x)
  qed
  also have "\<dots> = (\<Sum>j=1..n. \<Sum>(t, U)\<in>{(t', U') \<in> P\<^sub>+. card U' = j}. ?f (deg_pm t) (card U - 1))"
  proof (intro sum.UNION_disjoint ballI)
    fix j
    have "{(t, U). (t, U) \<in> P\<^sub>+ \<and> card U = j} \<subseteq> P\<^sub>+" by blast
    thus "finite {(t, U). (t, U) \<in> P\<^sub>+ \<and> card U = j}" using fin1 by (rule finite_subset)
  qed blast+
  also from refl have "\<dots> = (\<Sum>j=1..n. ?f (\<b> P (Suc j)) j - ?f (\<b> P j) j)"
  proof (rule sum.cong)
    fix j
    assume "j \<in> {1..n}"
    hence "Suc 0 \<le> j" and "0 < j" and "j \<le> n" by simp_all
    from \<open>finite P\<close> this(1) have "\<b> P j \<le> \<b> P (Suc 0)" by (rule \<b>_decreasing)
    also have "\<dots> \<le> d" by fact
    finally have "\<b> P j \<le> d" .
    from \<open>finite P\<close> have "\<b> P (Suc j) \<le> \<b> P j" by (rule \<b>_decreasing) simp
    hence "\<b> P (Suc j) \<le> d" using \<open>\<b> P j \<le> d\<close> by (rule le_trans)
    from \<open>0 < j\<close> have int_j: "int (j - Suc 0) = int j - 1" by simp
    have "(\<Sum>(t, U)\<in>{(t', U'). (t', U') \<in> P\<^sub>+ \<and> card U' = j}. ?f (deg_pm t) (card U - 1)) =
         (\<Sum>(t, U)\<in>(\<Union>d0\<in>{\<b> P (Suc j)..int (\<b> P j) - 1}. {(t', U'). (t', U') \<in> P\<^sub>+ \<and> int (deg_pm t') = d0 \<and> card U' = j}).
            ?f (deg_pm t) (card U - 1))"
      using _ refl
    proof (rule sum.cong)
      show "{(t', U'). (t', U') \<in> P\<^sub>+ \<and> card U' = j} =
            (\<Union>d0\<in>{\<b> P (Suc j)..int (\<b> P j) - 1}. {(t', U'). (t', U') \<in> P\<^sub>+ \<and> int (deg_pm t') = d0 \<and> card U' = j})"
      proof (rule Set.set_eqI, rule)
        fix x
        assume "x \<in> {(t', U'). (t', U') \<in> P\<^sub>+ \<and> card U' = j}"
        moreover obtain t U where x: "x = (t, U)" using prod.exhaust by blast
        ultimately have "(t, U) \<in> P\<^sub>+" and "card U = j" by simp_all
        with assms(1) \<open>finite P\<close> assms(3, 4) \<open>Suc 0 \<le> j\<close> \<open>j \<le> n\<close> have "\<b> P (Suc j) \<le> deg_pm t"
          unfolding n_def by (rule lem_6_1_4)
        moreover from \<open>finite P\<close> have "deg_pm t < \<b> P j"
        proof (rule \<b>)
          from \<open>(t, U) \<in> P\<^sub>+\<close> show "(t, U) \<in> P" by (simp add: pos_decomp_def)
        next
          show "j \<le> card U" by (simp add: \<open>card U = j\<close>)
        qed
        ultimately have "deg_pm t \<in> {\<b> P (Suc j)..int (\<b> P j) - 1}" by simp
        moreover from \<open>(t, U) \<in> P\<^sub>+\<close> have "(t, U) \<in> {(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = deg_pm t \<and> card U' = card U}"
          by simp
        ultimately show "x \<in> (\<Union>d0\<in>{\<b> P (Suc j)..int (\<b> P j) - 1}.
                                {(t', U'). (t', U') \<in> P\<^sub>+ \<and> int (deg_pm t') = d0 \<and> card U' = j})"
          by (simp add: x \<open>card U = j\<close>)
      qed blast
    qed
    also have "\<dots> = (\<Sum>d0=\<b> P (Suc j)..int (\<b> P j) - 1.
                    \<Sum>(t, U)\<in>{(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = d0 \<and> card U' = j}. ?f (deg_pm t) (card U - 1))"
    proof (intro sum.UNION_disjoint ballI)
      fix d0::int
      have "{(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = d0 \<and> card U' = j} \<subseteq> P\<^sub>+" by blast
      thus "finite {(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = d0 \<and> card U' = j}"
        using fin1 by (rule finite_subset)
    qed blast+
    also from refl have "\<dots> = (\<Sum>d0=\<b> P (Suc j)..int (\<b> P j) - 1. ?f d0 (j - 1))"
    proof (rule sum.cong)
      fix d0
      assume "d0 \<in> {\<b> P (Suc j)..int (\<b> P j) - 1}"
      hence "\<b> P (Suc j) \<le> d0" and "d0 < int (\<b> P j)" by simp_all
      hence "\<b> P (Suc j) \<le> nat d0" and "nat d0 < \<b> P j" by simp_all
      have "(\<Sum>(t, U)\<in>{(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = d0 \<and> card U' = j}. ?f (deg_pm t) (card U - 1)) =
            (\<Sum>(t, U)\<in>{(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = d0 \<and> card U' = j}. ?f d0 (j - 1))"
        using refl by (rule sum.cong) auto
      also have "\<dots> = card {(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = nat d0 \<and> card U' = j} * ?f d0 (j - 1)"
        using \<open>\<b> P (Suc j) \<le> d0\<close> by (simp add: int_eq_iff)
      also have "\<dots> = ?f d0 (j - 1)"
        using \<open>finite P\<close> assms(3, 4) \<open>Suc 0 \<le> j\<close> \<open>j \<le> n\<close> \<open>\<b> P (Suc j) \<le> nat d0\<close> \<open>nat d0 < \<b> P j\<close>
        by (simp only: n_def lem_6_1_3'(3))
      finally show "(\<Sum>(t, U)\<in>{(t', U'). (t', U') \<in> P\<^sub>+ \<and> deg_pm t' = d0 \<and> card U' = j}. ?f (deg_pm t) (card U - 1)) =
                    ?f d0 (j - 1)" .
    qed
    also have "\<dots> = (\<Sum>d0\<in>(-) (int d) ` {\<b> P (Suc j)..int (\<b> P j) - 1}. d0 + int (j - 1) gchoose (j - 1))"
    proof -
      have "inj_on ((-) (int d)) {\<b> P (Suc j)..int (\<b> P j) - 1}" by (auto simp: inj_on_def)
      thus ?thesis by (simp only: sum.reindex o_def)
    qed
    also have "\<dots> = (\<Sum>d0\<in>{0..int d - (\<b> P (Suc j))}-{0..int d - \<b> P j}. d0 + int (j - 1) gchoose (j - 1))"
      using _ refl
    proof (rule sum.cong)
      have "(-) (int d) ` {\<b> P (Suc j)..int (\<b> P j) - 1} = {int d - (int (\<b> P j) - 1)..int d - int (\<b> P (Suc j))}"
        by (simp only: image_diff_atLeastAtMost)
      also have "\<dots> = {0..int d - int (\<b> P (Suc j))} - {0..int d - int (\<b> P j)}"
      proof -
        from \<open>\<b> P j \<le> d\<close> have "int (\<b> P j) - 1 \<le> int d" by simp
        thus ?thesis by auto
      qed
      finally show "(-) (int d) ` {\<b> P (Suc j)..int (\<b> P j) - 1} =
                    {0..int d - int (\<b> P (Suc j))} - {0..int d - int (\<b> P j)}" .
    qed
    also have "\<dots> = (\<Sum>d0=0..int d - (\<b> P (Suc j)). d0 + int (j - 1) gchoose (j - 1)) -
                    (\<Sum>d0=0..int d - \<b> P j. d0 + int (j - 1) gchoose (j - 1))"
      by (rule sum_diff) (auto simp: \<open>\<b> P (Suc j) \<le> \<b> P j\<close>)
    also from \<open>\<b> P (Suc j) \<le> d\<close> \<open>\<b> P j \<le> d\<close> have "\<dots> = ?f (\<b> P (Suc j)) j - ?f (\<b> P j) j"
      by (simp add: gchoose_rising_sum, simp add: int_j ac_simps \<open>0 < j\<close>)
    finally show "(\<Sum>(t, U)\<in>{(t', U'). (t', U') \<in> P\<^sub>+ \<and> card U' = j}. ?f (deg_pm t) (card U - 1)) =
                    ?f (\<b> P (Suc j)) j - ?f (\<b> P j) j" .
  qed
  also have "\<dots> = (\<Sum>j=1..n. ?f (\<b> P (Suc j)) j) - (\<Sum>j=1..n. ?f (\<b> P j) j)"
    by (fact sum_subtractf)
  also have "\<dots> = ?f (\<b> P (Suc n)) n + (\<Sum>j=1..n-1. ?f (\<b> P (Suc j)) j) - (\<Sum>j=1..n. ?f (\<b> P j) j)"
    by (simp only: sum_tail_nat[OF \<open>0 < n\<close> \<open>1 \<le> n\<close>])
  also have "\<dots> = ?f (\<b> P (Suc n)) n - ?f (\<b> P 1) 1 +
                  ((\<Sum>j=1..n-1. ?f (\<b> P (Suc j)) j) - (\<Sum>j=1..n-1. ?f (\<b> P (Suc j)) (Suc j)))"
    by (simp only: sum_head_Suc[OF \<open>1 \<le> n\<close>] sum_atLeast_Suc_shift[OF \<open>0 < n\<close> \<open>1 \<le> n\<close>])
  also have "\<dots> = ?f (\<b> P (Suc n)) n - ?f (\<b> P 1) 1 -
                  (\<Sum>j=1..n-1. ?f (\<b> P (Suc j)) (Suc j) - ?f (\<b> P (Suc j)) j)"
    by (simp only: sum_subtractf)
  also have "\<dots> = ?f (\<b> P (Suc n)) n - 1 - ((int d - \<b> P (Suc 0)) gchoose (Suc 0)) -
                  (\<Sum>j=1..n-1. (int d - \<b> P (Suc j) + j) gchoose (Suc j))"
  proof -
    have "?f (\<b> P 1) 1 = 1 + ((int d - \<b> P (Suc 0)) gchoose (Suc 0))"
      by (simp add: plus_Suc_gbinomial)
    moreover from refl have "(\<Sum>j=1..n-1. ?f (\<b> P (Suc j)) (Suc j) - ?f (\<b> P (Suc j)) j) =
                              (\<Sum>j=1..n-1. (int d - \<b> P (Suc j) + j) gchoose (Suc j))"
      by (rule sum.cong) (simp add: plus_Suc_gbinomial)
    ultimately show ?thesis by (simp only:)
  qed
  also have "\<dots> = ?f (\<b> P (Suc n)) n - 1 - (\<Sum>j=0..n-1. (int d - \<b> P (Suc j) + j) gchoose (Suc j))"
    by (simp only: sum_head_Suc[OF le0], simp)
  also have "\<dots> = ?f (\<b> P (Suc n)) n - 1 - (\<Sum>j=Suc 0..Suc (n-1). (int d - \<b> P j + j - 1) gchoose j)"
    by (simp only: sum_shift_bounds_cl_Suc_ivl, simp add: ac_simps)
  also have "\<dots> = Hilbert_poly (\<b> P) d" using \<open>0 < n\<close> by (simp add: Hilbert_poly_def Let_def n_def)
  finally have eq2: "int (\<Sum>(t, U)\<in>P\<^sub>+. Hilbert_fun (cone t U) d) = Hilbert_poly (\<b> P) (int d)" .

  from assms(2) \<open>finite_decomp P\<close> have "Hilbert_fun T d = (\<Sum>(t, U)\<in>P. Hilbert_fun (cone t U) d)"
    by (rule Hilbert_fun_cone_decomp)
  also have "\<dots> = (\<Sum>(t, U)\<in>(P - P\<^sub>+) \<union> P\<^sub>+. Hilbert_fun (cone t U) d)" by (simp only: eq0)
  also have "\<dots> = (\<Sum>(t, U)\<in>P - P\<^sub>+. Hilbert_fun (cone t U) d) + (\<Sum>(t, U)\<in>P\<^sub>+. Hilbert_fun (cone t U) d)"
    using fin2 fin1 by (rule sum.union_disjoint) blast
  also have "\<dots> = card {t. (t, {}) \<in> P \<and> deg_pm t = d} + (\<Sum>(t, U)\<in>P\<^sub>+. Hilbert_fun (cone t U) d)"
    by (simp only: eq1)
  also have "int \<dots> = card {t. (t, {}) \<in> P \<and> deg_pm t = d} + Hilbert_poly (\<b> P) d"
    by (simp only: eq2 int_plus)
  finally show ?thesis .
qed

corollary Hilbert_fun_eq_Hilbert_poly:
  assumes "finite X" and "cone_decomp T P" and "standard_decomp k P" and "exact_decomp 0 P"
    and "\<b> P 0 \<le> d"
  shows "int (Hilbert_fun T d) = Hilbert_poly (\<b> P) d"
proof -
  from assms(2) have "finite P" by (rule cone_decompD)
  hence "\<b> P (Suc 0) \<le> \<b> P 0" using le0 by (rule \<b>_decreasing)
  also have "\<dots> \<le> d" by fact
  finally have "\<b> P (Suc 0) \<le> d" .
  with assms(1-4) have "int (Hilbert_fun T d) =
                int (card {t. (t, {}) \<in> P \<and> deg_pm t = d}) + Hilbert_poly (\<b> P) (int d)"
    by (rule Hilbert_fun_eq_Hilbert_poly_plus_card)
  also have "\<dots> = Hilbert_poly (\<b> P) (int d)"
  proof -
    have eq: "{t. (t, {}) \<in> P \<and> deg_pm t = d} = {}"
    proof -
      {
        fix t
        assume "(t, {}) \<in> P" and "deg_pm t = d"
        from \<open>finite P\<close> this(1) le0 have "deg_pm t < \<b> P 0" by (rule \<b>)
        with assms(5) have False by (simp add: \<open>deg_pm t = d\<close>)
      }
      thus ?thesis by blast
    qed
    show ?thesis by (simp add: eq)
  qed
  finally show ?thesis .
qed

end

end (* theory *)
