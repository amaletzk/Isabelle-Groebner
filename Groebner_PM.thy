(* Author: Alexander Maletzky *)

theory Groebner_PM
  imports MPoly_PM Groebner_Bases.Reduced_GB
begin

text \<open>We prove results that hold specifically for Gr\"obner bases in polynomial rings, where the
  polynomials really have @{emph \<open>indeterminates\<close>}.\<close>

context pm_powerprod
begin

lemmas finite_reduced_GB_Polys =
  punit.finite_reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_reduced_GB_Polys =
  punit.reduced_GB_is_reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_GB_Polys =
  punit.reduced_GB_is_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_auto_reduced_Polys =
  punit.reduced_GB_is_auto_reduced_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_is_monic_set_Polys =
  punit.reduced_GB_is_monic_set_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_nonzero_Polys =
  punit.reduced_GB_nonzero_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_ideal_Polys =
  punit.reduced_GB_pmdl_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_unique_Polys =
  punit.reduced_GB_unique_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas reduced_GB_Polys =
  punit.reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]
lemmas ideal_eq_UNIV_iff_reduced_GB_eq_one_Polys =
  ideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set[simplified, OF dickson_grading_varnum_wrt, where m=0, simplified dgrad_p_set_varnum_wrt]

subsection \<open>Homogeneity\<close>

lemma is_reduced_GB_homogeneous:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "punit.is_reduced_GB G" and "ideal G = ideal F"
    and "g \<in> G"
  shows "homogeneous g"
proof (rule homogeneousI)
  fix s t
  have 1: "deg_pm u = deg_pm (punit.lt g)" if "u \<in> keys g" for u
  proof -
    from assms(4) have "g \<in> ideal G" by (rule ideal.generator_in_module)
    hence "g \<in> ideal F" by (simp only: assms(3))
    from that have "u \<in> Keys (hom_components g)" by (simp only: Keys_hom_components)
    then obtain q where q: "q \<in> hom_components g" and "u \<in> keys q" by (rule in_KeysE)
    from assms(1) \<open>g \<in> ideal F\<close> q have "q \<in> ideal F" by (rule homogeneous_ideal')
    from assms(2) have "punit.is_Groebner_basis G" by (rule punit.reduced_GB_D1)
    moreover from \<open>q \<in> ideal F\<close> have "q \<in> ideal G" by (simp only: assms(3))
    moreover from q have "q \<noteq> 0" by (rule hom_components_nonzero)
    ultimately obtain g' where "g' \<in> G" and "g' \<noteq> 0" and adds: "punit.lt g' adds punit.lt q"
      by (rule punit.GB_adds_lt[simplified])
    from \<open>q \<noteq> 0\<close> have "punit.lt q \<in> keys q" by (rule punit.lt_in_keys)
    also from q have "\<dots> \<subseteq> Keys (hom_components g)" by (rule keys_subset_Keys)
    finally have "punit.lt q \<in> keys g" by (simp only: Keys_hom_components)
    with _ \<open>g' \<noteq> 0\<close> have red: "punit.is_red {g'} g"
      using adds by (rule punit.is_red_addsI[simplified]) simp
    from assms(2) have "punit.is_auto_reduced G" by (rule punit.reduced_GB_D2)
    hence "\<not> punit.is_red (G - {g}) g" using assms(4) by (rule punit.is_auto_reducedD)
    with red have "\<not> {g'} \<subseteq> G - {g}" using punit.is_red_subset by blast
    with \<open>g' \<in> G\<close> have "g' = g" by simp
    from \<open>punit.lt q \<in> keys g\<close> have "punit.lt q \<preceq> punit.lt g" by (rule punit.lt_max_keys)
    moreover from adds have "punit.lt g \<preceq> punit.lt q"
      unfolding \<open>g' = g\<close> by (rule punit.ord_adds_term[simplified])
    ultimately have eq: "punit.lt q = punit.lt g" by (rule ordered_powerprod_lin.antisym)
    from q have "homogeneous q" by (rule hom_components_homogeneous)
    hence "deg_pm u = deg_pm (punit.lt q)"
      using \<open>u \<in> keys q\<close> \<open>punit.lt q \<in> keys q\<close> by (rule homogeneousD)
    thus ?thesis by (simp only: eq)
  qed
  assume "s \<in> keys g"
  hence 2: "deg_pm s = deg_pm (punit.lt g)" by (rule 1)
  assume "t \<in> keys g"
  hence "deg_pm t = deg_pm (punit.lt g)" by (rule 1)
  with 2 show "deg_pm s = deg_pm t" by simp
qed

lemma lp_dehomogenize:
  assumes "is_hom_ord x" and "homogeneous p"
  shows "punit.lt (dehomogenize x p) = except (punit.lt p) {x}"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  hence "punit.lt p \<in> keys p" by (rule punit.lt_in_keys)
  with assms(2) have "except (punit.lt p) {x} \<in> keys (dehomogenize x p)"
    by (rule keys_dehomogenizeI)
  thus ?thesis
  proof (rule punit.lt_eqI_keys)
    fix t
    assume "t \<in> keys (dehomogenize x p)"
    then obtain s where "s \<in> keys p" and t: "t = except s {x}" by (rule keys_dehomogenizeE)
    from this(1) have "s \<preceq> punit.lt p" by (rule punit.lt_max_keys)
    moreover from assms(2) \<open>s \<in> keys p\<close> \<open>punit.lt p \<in> keys p\<close> have "deg_pm s = deg_pm (punit.lt p)"
      by (rule homogeneousD)
    ultimately show "t \<preceq> except (punit.lt p) {x}" using assms(1) by (simp add: t is_hom_ordD)
  qed
qed

lemma isGB_dehomogenize:
  assumes "is_hom_ord x" and "finite X" and "G \<subseteq> P[X]" and "punit.is_Groebner_basis G"
    and "\<And>g. g \<in> G \<Longrightarrow> homogeneous g"
  shows "punit.is_Groebner_basis (dehomogenize x ` G)"
  using dickson_grading_varnum_wrt
proof (rule punit.isGB_I_adds_lt[simplified])
  from assms(2) show "finite (X - {x})" by simp
next
  have "dehomogenize x ` G \<subseteq> P[X - {x}]"
  proof
    fix g
    assume "g \<in> dehomogenize x ` G"
    then obtain g' where "g' \<in> G" and g: "g = dehomogenize x g'" ..
    from this(1) assms(3) have "g' \<in> P[X]" ..
    hence "indets g' \<subseteq> X" by (rule PolysD)
    have "indets g \<subseteq> indets g' - {x}" by (simp only: g indets_dehomogenize)
    also from \<open>indets g' \<subseteq> X\<close> subset_refl have "\<dots> \<subseteq> X - {x}" by (rule Diff_mono)
    finally show "g \<in> P[X - {x}]" by (rule PolysI_alt)
  qed
  thus "dehomogenize x ` G \<subseteq> punit.dgrad_p_set (varnum_wrt (X - {x})) 0"
    by (simp only: dgrad_p_set_varnum_wrt)
next
  fix p
  assume "p \<in> ideal (dehomogenize x ` G)"
  then obtain G0 q where "G0 \<subseteq> dehomogenize x ` G" and "finite G0" and p: "p = (\<Sum>g\<in>G0. q g * g)"
    by (rule ideal.in_moduleE)
  from this(1) obtain G' where "G' \<subseteq> G" and G0: "G0 = dehomogenize x ` G'"
    and inj: "inj_on (dehomogenize x) G'" by (rule subset_imageE_inj)
  define p' where "p' = (\<Sum>g\<in>G'. q (dehomogenize x g) * g)"
  have "p' \<in> ideal G'" unfolding p'_def by (rule ideal.sum_in_moduleI)
  also from \<open>G' \<subseteq> G\<close> have "\<dots> \<subseteq> ideal G" by (rule ideal.module_mono)
  finally have "p' \<in> ideal G" .
  with assms(5) have "homogenize x p' \<in> ideal G" (is "?p \<in> _") by (rule homogeneous_ideal_homogenize)

  assume "p \<in> punit.dgrad_p_set (varnum_wrt (X - {x})) 0"
  hence "p \<in> P[X - {x}]" by (simp only: dgrad_p_set_varnum_wrt)
  hence "indets p \<subseteq> X - {x}" by (rule PolysD)
  hence "x \<notin> indets p" by blast
  have "p = dehomogenize x p" by (rule sym) (simp add: \<open>x \<notin> indets p\<close>)
  also from inj have "\<dots> = dehomogenize x (\<Sum>g\<in>G'. q (dehomogenize x g) * dehomogenize x g)"
    by (simp add: p G0 sum.reindex)
  also have "\<dots> = dehomogenize x ?p"
    by (simp add: dehomogenize_sum dehomogenize_times p'_def)
  finally have p: "p = dehomogenize x ?p" .
  moreover assume "p \<noteq> 0"
  ultimately have "?p \<noteq> 0" by (auto simp del: dehomogenize_homogenize)
  with assms(4) \<open>?p \<in> ideal G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and adds: "punit.lt g adds punit.lt ?p"
    by (rule punit.GB_adds_lt[simplified])
  from this(1) have "homogeneous g" by (rule assms(5))
  show "\<exists>g\<in>dehomogenize x ` G. g \<noteq> 0 \<and> punit.lt g adds punit.lt p"
  proof (intro bexI conjI notI)
    assume "dehomogenize x g = 0"
    hence "g = 0" using \<open>homogeneous g\<close> by (rule dehomogenize_zeroD)
    with \<open>g \<noteq> 0\<close> show False ..
  next
    from assms(1) \<open>homogeneous g\<close> have "punit.lt (dehomogenize x g) = except (punit.lt g) {x}"
      by (rule lp_dehomogenize)
    also from adds have "\<dots> adds except (punit.lt ?p) {x}"
      by (simp add: adds_pm le_pm_def le_fun_def lookup_except)
    also from assms(1) homogeneous_homogenize have "\<dots> = punit.lt (dehomogenize x ?p)"
      by (rule lp_dehomogenize[symmetric])
    finally show "punit.lt (dehomogenize x g) adds punit.lt p" by (simp only: p)
  next
    from \<open>g \<in> G\<close> show "dehomogenize x g \<in> dehomogenize x ` G" by (rule imageI)
  qed
qed

end (* pm_powerprod *)

context hom_ord_pm_powerprod
begin

lemma hom_ord_lp:
  assumes "x \<notin> indets p"
  shows "hom_ord.punit.lt x p = punit.lt p"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  hence "punit.lt p \<in> keys p" by (rule punit.lt_in_keys)
  thus ?thesis
  proof (rule hom_ord.punit.lt_eqI_keys)
    fix t
    assume "t \<in> keys p"
    hence "keys t \<subseteq> indets p" by (simp add: in_indetsI subsetI)
    with assms have "x \<notin> keys t" by blast
    hence 1: "except t {x} = t" and 2: "lookup t x = 0" by (simp_all add: except_id_iff)
    from \<open>punit.lt p \<in> keys p\<close> have "keys (punit.lt p) \<subseteq> indets p" by (simp add: in_indetsI subsetI)
    with assms have "x \<notin> keys (punit.lt p)" by blast
    hence 3: "except (punit.lt p) {x} = punit.lt p" and 4: "lookup (punit.lt p) x = 0"
      by (simp_all add: except_id_iff)
    from \<open>t \<in> keys p\<close> have "t \<preceq> punit.lt p" by (rule punit.lt_max_keys)
    thus "hom_ord_of x t (punit.lt p)"
      by (simp add: hom_ord_of_def 1 2 3 4 ordered_powerprod_lin.order.order_iff_strict)
  qed
qed

lemma dehomogenize_reduced_GB:
  assumes "finite X" and "F \<subseteq> P[X]" and "x \<notin> X"
  shows "punit.is_Groebner_basis (dehomogenize x ` hom_ord.punit.reduced_GB x (homogenize x ` F))"
          (is ?thesis1)
    and "ideal (dehomogenize x ` hom_ord.punit.reduced_GB x (homogenize x ` F)) = ideal F"
          (is ?thesis2)
    and "dehomogenize x ` hom_ord.punit.reduced_GB x (homogenize x ` F) \<subseteq> P[X]"
          (is ?thesis3)
proof -
  let ?G = "hom_ord.punit.reduced_GB x (homogenize x ` F)"
  from assms(1) have "finite (insert x X)" by (simp only: finite_insert)
  moreover have "homogenize x ` F \<subseteq> P[insert x X]"
  proof
    fix hf
    assume "hf \<in> homogenize x ` F"
    then obtain f where "f \<in> F" and hf: "hf = homogenize x f" ..
    from this(1) assms(2) have "f \<in> P[X]" ..
    hence "indets f \<subseteq> X" by (rule PolysD)
    hence "insert x (indets f) \<subseteq> insert x X" by blast
    with indets_homogenize_subset have "indets hf \<subseteq> insert x X" unfolding hf by (rule subset_trans)
    thus "hf \<in> P[insert x X]" by (rule PolysI_alt)
  qed
  ultimately have G_sub: "?G \<subseteq> P[insert x X]"
    and ideal_G: "ideal ?G = ideal (homogenize x ` F)"
    and GB_G: "hom_ord.punit.is_reduced_GB x ?G"
    by (rule hom_ord.reduced_GB_Polys, rule hom_ord.reduced_GB_ideal_Polys,
        rule hom_ord.reduced_GB_is_reduced_GB_Polys)

  show ?thesis3
  proof
    fix g
    assume "g \<in> dehomogenize x ` ?G"
    then obtain g' where "g' \<in> ?G" and g: "g = dehomogenize x g'" ..
    from this(1) G_sub have "g' \<in> P[insert x X]" ..
    hence "indets g' \<subseteq> insert x X" by (rule PolysD)
    have "indets g \<subseteq> indets g' - {x}" by (simp only: g indets_dehomogenize)
    also from \<open>indets g' \<subseteq> insert x X\<close> have "\<dots> \<subseteq> X" using assms(3) by blast
    finally show "g \<in> P[X]" by (rule PolysI_alt)
  qed

  from dickson_grading_varnum_wrt show ?thesis1
  proof (rule punit.isGB_I_adds_lt[simplified])
    from \<open>?thesis3\<close> show "dehomogenize x ` ?G \<subseteq> punit.dgrad_p_set (varnum_wrt X) 0"
      by (simp only: dgrad_p_set_varnum_wrt)
  next
    fix p :: "('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b"
    assume "p \<in> punit.dgrad_p_set (varnum_wrt X) 0"
    hence "p \<in> P[X]" by (simp only: dgrad_p_set_varnum_wrt)
    have "hom_ord.punit.is_Groebner_basis x (dehomogenize x ` ?G)"
      using hom_ord_is_hom_ord \<open>finite (insert x X)\<close> G_sub
    proof (rule hom_ord.isGB_dehomogenize)
      from GB_G show "hom_ord.punit.is_Groebner_basis x ?G" by (rule hom_ord.punit.reduced_GB_D1)
    next
      fix g
      assume "g \<in> ?G"
      with _ GB_G ideal_G show "homogeneous g"
      proof (rule hom_ord.is_reduced_GB_homogeneous)
        fix hf
        assume "hf \<in> homogenize x ` F"
        then obtain f where "hf = homogenize x f" ..
        thus "homogeneous hf" by (simp only: homogeneous_homogenize)
      qed
    qed
    moreover assume "p \<in> ideal (dehomogenize x ` ?G)" and "p \<noteq> 0"
    ultimately obtain g where "g \<in> dehomogenize x ` ?G" and "g \<noteq> 0"
      and "hom_ord.punit.lt x g adds hom_ord.punit.lt x p"
      by (rule hom_ord.punit.GB_adds_lt[simplified])
    from this(1) \<open>?thesis3\<close> have "g \<in> P[X]" ..
    show "\<exists>g\<in>dehomogenize x ` ?G. g \<noteq> 0 \<and> punit.lt g adds punit.lt p"
    proof (intro bexI conjI)
      have "punit.lt g = hom_ord.punit.lt x g"
      proof (rule sym, intro hom_ord_lp notI)
        assume "x \<in> indets g"
        also from \<open>g \<in> P[X]\<close> have "\<dots> \<subseteq> X" by (rule PolysD)
        finally have "x \<in> X" .
        with assms(3) show False ..
      qed
      also have "\<dots> adds hom_ord.punit.lt x p" by fact
      also have "\<dots> = punit.lt p"
      proof (intro hom_ord_lp notI)
        assume "x \<in> indets p"
        also from \<open>p \<in> P[X]\<close> have "\<dots> \<subseteq> X" by (rule PolysD)
        finally have "x \<in> X" .
        with assms(3) show False ..
      qed
      finally show "punit.lt g adds punit.lt p" .
    qed fact+
  qed (fact assms(1))

  from ideal_G show ?thesis2
  proof (rule ideal_dehomogenize)
    from assms(3) have "X \<subseteq> UNIV - {x}" by blast
    hence "P[X] \<subseteq> P[UNIV - {x}]" by (rule Polys_mono)
    with assms(2) show "F \<subseteq> P[UNIV - {x}]" by (rule subset_trans)
  qed
qed

end

end (* theory *)
