theory Reduced_GB
imports Groebner_Bases.Groebner_Bases Poly_Utils
begin

section \<open>Further Properties of Relations\<close>
  
context relation
begin
  
lemma wf_implies_nf_existence:
  fixes a
  assumes wf: "wfP (r^--1)"
  obtains b where "a \<rightarrow>\<^sup>* b" and "is_final b"
proof -
  from wf have "wf {(x, y). (r^--1) x y}" unfolding wfP_def .
  hence "wf {(y, x). x \<rightarrow> y}" (is "wf ?R") by simp
  let ?A = "{b. a \<rightarrow>\<^sup>* b}"
  have "a \<in> ?A" by simp
  show ?thesis
  proof (rule wfE_min[OF \<open>wf ?R\<close> \<open>a \<in> ?A\<close>])
    fix z
    assume A1: "z \<in> {b. a \<rightarrow>\<^sup>* b}" and A2: "\<And>y. (y, z) \<in> {(y, x). x \<rightarrow> y} \<Longrightarrow> y \<notin> {b. a \<rightarrow>\<^sup>* b}"
    from A1 have A3: "a \<rightarrow>\<^sup>* z" by simp
    show thesis
    proof (rule, rule A3)
      show "is_final z" unfolding is_final_def
      proof
        assume "\<exists>y. z \<rightarrow> y"
        then obtain y where "z \<rightarrow> y" ..
        hence "(y, z) \<in> {(y, x). x \<rightarrow> y}" by simp
        from A2[OF this] have "\<not> (a \<rightarrow>\<^sup>* y)" by simp
        with rtranclp_trans[OF A3, of y] \<open>z \<rightarrow> y\<close> show False by auto
      qed
    qed
  qed
qed
  
lemma unique_nf_implies_confluence:
  assumes major: "\<And>a b1 b2. (a \<rightarrow>\<^sup>* b1) \<Longrightarrow> (a \<rightarrow>\<^sup>* b2) \<Longrightarrow> is_final b1 \<Longrightarrow> is_final b2 \<Longrightarrow> b1 = b2"
    and wf: "wfP (r^--1)"
  shows "is_confluent"
  unfolding is_confluent_def
proof (intro allI, intro impI)
  fix a b1 b2
  assume "a \<rightarrow>\<^sup>* b1 \<and> a \<rightarrow>\<^sup>* b2"
  hence "a \<rightarrow>\<^sup>* b1" and "a \<rightarrow>\<^sup>* b2" by simp_all
  from wf_implies_nf_existence[OF wf] obtain c1 where "b1 \<rightarrow>\<^sup>* c1" and "is_final c1" .
  from wf_implies_nf_existence[OF wf] obtain c2 where "b2 \<rightarrow>\<^sup>* c2" and "is_final c2" .
  have "c1 = c2" by (rule major, rule rtranclp_trans[OF \<open>a \<rightarrow>\<^sup>* b1\<close>], fact, rule rtranclp_trans[OF \<open>a \<rightarrow>\<^sup>* b2\<close>], fact+)
  show "b1 \<down>\<^sup>* b2" unfolding cs_def
  proof (intro exI, intro conjI)
    show "b1 \<rightarrow>\<^sup>* c1" by fact
  next
    show "b2 \<rightarrow>\<^sup>* c1" unfolding \<open>c1 = c2\<close> by fact
  qed
qed

end (* relation *)

section \<open>Properties of Reducibility\<close>

context ordered_powerprod
begin
  
lemma is_red_union: "is_red (A \<union> B) p \<longleftrightarrow> (is_red A p \<or> is_red B p)"
  unfolding is_red_alt red_union by auto

lemma red_single_0_lp:
  fixes f h t
  assumes "red_single f 0 h t"
  shows "lp f = lp h + t"
proof -
  from red_single_nonzero1[OF assms] have "f \<noteq> 0" .
  {
    assume "h \<noteq> 0" and neq: "lookup f (t + lp h) \<noteq> 0" and
      eq: "f = monom_mult (lookup f (t + lp h) / lc h) t h"
    from lc_not_0[OF \<open>h \<noteq> 0\<close>] have "lc h \<noteq> 0" .
    with neq have "(lookup f (t + lp h) / lc h) \<noteq> 0" by simp
    from eq lp_mult[OF this \<open>h \<noteq> 0\<close>, of t] have "lp f = t + lp h" by simp
    hence "lp f = lp h + t" by (simp add: ac_simps)
  }
  with assms show ?thesis unfolding red_single_def by auto
qed

lemma red_single_lp_distinct_lp:
  fixes f g h t
  assumes rs: "red_single f g h t" and "g \<noteq> 0" and "lp g \<noteq> lp f"
  shows "lp f = lp h + t"
proof -
  from red_single_nonzero1[OF rs] have "f \<noteq> 0" .
  from red_single_ord[OF rs] have "g \<preceq>p f" by simp
  from ord_p_lp[OF this \<open>g \<noteq> 0\<close>] \<open>lp g \<noteq> lp f\<close> have "lp g \<prec> lp f" by simp
  {
    assume "h \<noteq> 0" and neq: "lookup f (t + lp h) \<noteq> 0" and
      eq: "f = g + monom_mult (lookup f (t + lp h) / lc h) t h" (is "f = g + ?R")
    from lc_not_0[OF \<open>h \<noteq> 0\<close>] have "lc h \<noteq> 0" .
    with neq have "(lookup f (t + lp h) / lc h) \<noteq> 0" (is "?c \<noteq> 0") by simp
    from eq lp_mult[OF this \<open>h \<noteq> 0\<close>, of t] have lpR: "lp ?R = t + lp h" by simp
    from monom_mult_0_iff[of ?c t h] \<open>?c \<noteq> 0\<close> \<open>h \<noteq> 0\<close> have "?R \<noteq> 0" by auto
    from lp_plus_precE[of g] eq \<open>lp g \<prec> lp f\<close> have "lp g \<prec> lp ?R" by auto
    from lp_plus_eqI[OF this] eq lpR have "lp f = lp h + t" by (simp add: ac_simps)
  }
  with assms show ?thesis unfolding red_single_def by auto
qed

lemma zero_reducibility_implies_lp_divisibility':
  assumes "(red F)\<^sup>*\<^sup>* f 0" and "f \<noteq> 0"
  shows "\<exists>h\<in>F. h \<noteq> 0 \<and> (lp h adds lp f)"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step f g)
  show ?case
  proof (cases "g = 0")
    case True
    with step.hyps have "red F f 0" by simp
    from red_setE[OF this] obtain h t where "h \<in> F" and rs: "red_single f 0 h t" by auto
    show ?thesis
    proof
      from red_single_0_lp[OF rs] have "lp h adds lp f" by simp
      also from rs have "h \<noteq> 0" by (simp add: red_single_def) 
      ultimately show "h \<noteq> 0 \<and> lp h adds lp f" by simp
    qed (rule \<open>h \<in> F\<close>)
  next
    case False
    show ?thesis
    proof (cases "lp g = lp f")
      case True
      with False step.hyps show ?thesis by simp
    next
      case False
      from red_setE[OF \<open>red F f g\<close>] obtain h t where "h \<in> F" and rs: "red_single f g h t" by auto
      show ?thesis
      proof
        from red_single_lp_distinct_lp[OF rs \<open>g \<noteq> 0\<close> False] have "lp h adds lp f" by simp
        also from rs have "h \<noteq> 0" by (simp add: red_single_def) 
        ultimately show "h \<noteq> 0 \<and> lp h adds lp f" by simp
      qed (rule \<open>h \<in> F\<close>)
    qed
  qed
qed
  
lemma zero_reducibility_implies_lp_divisibility:
  assumes "(red F)\<^sup>*\<^sup>* f 0" and "f \<noteq> 0"
  obtains h where "h \<in> F" and "h \<noteq> 0" and "lp h adds lp f"
  using zero_reducibility_implies_lp_divisibility'[OF assms] by auto

lemma is_red_addsI:
  assumes "f \<in> F" and "f \<noteq> 0" and "t \<in> (keys p)" and "lp f adds t"
  shows "is_red F p"
  using assms
proof (induction p rule: poly_mapping_tail_induct)
  case 0
  from \<open>t \<in> (keys 0)\<close> keys_eq_empty_iff[of 0] show ?case by auto
next
  case (tail p)
  from "tail.IH"[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> _ \<open>lp f adds t\<close>] have imp: "t \<in> (keys (tail p)) \<Longrightarrow> is_red F (tail p)" .
  show ?case
  proof (cases "t = lp p")
    case True
    show ?thesis
    proof (rule is_red_indI1[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> \<open>p \<noteq> 0\<close>])
      from \<open>lp f adds t\<close> True show "lp f adds lp p" by simp
    qed
  next
    case False
    with \<open>t \<in> (keys p)\<close> \<open>p \<noteq> 0\<close> have "t \<in> (keys (tail p))"
      by (simp add: lookup_tail_2 in_keys_iff del: lookup_not_eq_zero_eq_in_keys) 
    from is_red_indI2[OF \<open>p \<noteq> 0\<close> imp[OF this]] show ?thesis .
  qed
qed

lemma is_red_addsE':
  assumes "is_red F p"
  shows "\<exists>f\<in>F. \<exists>t\<in>(keys p). f \<noteq> 0 \<and> lp f adds t"
  using assms
proof (induction p rule: poly_mapping_tail_induct)
  case 0
  with irred_0[of F] show ?case by simp
next
  case (tail p)
  from is_red_indE[OF \<open>is_red F p\<close>] show ?case
  proof
    assume "\<exists>f\<in>F. f \<noteq> 0 \<and> lp f adds lp p"
    then obtain f where "f \<in> F" and "f \<noteq> 0" and "lp f adds lp p" by auto
    show ?case
    proof
      show "\<exists>t\<in>keys p. f \<noteq> 0 \<and> lp f adds t"
      proof (intro bexI, intro conjI)
        from \<open>p \<noteq> 0\<close> show "lp p \<in> (keys p)" by (metis in_keys_iff lc_def lc_not_0)
      qed (rule \<open>f \<noteq> 0\<close>, rule \<open>lp f adds lp p\<close>)
    qed (rule \<open>f \<in> F\<close>)
  next
    assume "is_red F (tail p)"
    from "tail.IH"[OF this] obtain f t
      where "f \<in> F" and "f \<noteq> 0" and t_in_keys_tail: "t \<in> (keys (tail p))" and "lp f adds t" by auto
    from "tail.hyps" t_in_keys_tail have t_in_keys: "t \<in> (keys p)" by (metis lookup_tail in_keys_iff)
    show ?case
    proof
      show "\<exists>t\<in>keys p. f \<noteq> 0 \<and> lp f adds t"
        by (intro bexI, intro conjI, rule \<open>f \<noteq> 0\<close>, rule \<open>lp f adds t\<close>, rule t_in_keys)
    qed (rule \<open>f \<in> F\<close>)
  qed
qed

lemma is_red_addsE:
  assumes "is_red F p"
  obtains f t where "f \<in> F" and "t \<in> (keys p)" and "f \<noteq> 0" and "lp f adds t"
  using is_red_addsE'[OF assms] by auto

lemma is_red_adds_iff:
  shows "(is_red F p) \<longleftrightarrow> (\<exists>f\<in>F. \<exists>t\<in>(keys p). f \<noteq> 0 \<and> lp f adds t)"
  using is_red_addsE' is_red_addsI by auto
    
lemma is_red_subset:
  assumes red: "is_red A p" and sub: "A \<subseteq> B"
  shows "is_red B p"
proof -
  from red obtain f t where "f \<in> A" and "t \<in> keys p" and "f \<noteq> 0" and "lp f adds t" by (rule is_red_addsE)
  show ?thesis by (rule is_red_addsI, rule, fact+)
qed

lemma red_diff_in_pideal:
  assumes "red F p q"
  shows "p - q \<in> pideal F"
  using assms unfolding red_def
proof
  fix f
  assume "f \<in> F" and A: "\<exists>t. red_single p q f t"
  from A obtain t where "red_single p q f t" ..
  hence q_def: "q = p - monom_mult (lookup p (t + lp f) / lc f) t f" unfolding red_single_def by simp
  from monom_mult_in_pideal[OF \<open>f \<in> F\<close>] show ?thesis unfolding q_def by simp
qed
  
lemma red_rtranclp_diff_in_pideal:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "p - q \<in> pideal F"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  from zero_in_pideal show "?case" by simp
next
  case (step p0 q)
  from red_diff_in_pideal[OF \<open>red F p0 q\<close>] have "p0 - q \<in> pideal F" .
  from pideal_closed_plus[OF \<open>p - p0 \<in> pideal F\<close> this] show ?case by simp
qed
  
corollary red_rtranclp_0_in_pideal:
  assumes "(red F)\<^sup>*\<^sup>* p 0"
  shows "p \<in> pideal F"
  using assms red_rtranclp_diff_in_pideal by fastforce

lemma pideal_closed_red:
  assumes "pideal B \<subseteq> pideal A" and "p \<in> pideal A" and "red B p q"
  shows "q \<in> pideal A"
proof -
  have "q - p \<in> pideal A"
  proof
    have "p - q \<in> pideal B" by (rule red_diff_in_pideal, fact)
    hence "- (p - q) \<in> pideal B" by (rule pideal_closed_uminus)
    thus "q - p \<in> pideal B" by simp
  qed fact
  from pideal_closed_plus[OF this \<open>p \<in> pideal A\<close>] show ?thesis by simp
qed
  
lemma is_red_monic: "is_red B (monic p) \<longleftrightarrow> is_red B p"
  unfolding is_red_adds_iff keys_monic ..

lemma is_red_monic_set: "is_red (monic_set B) p \<longleftrightarrow> is_red B p"
proof
  assume "is_red (monic_set B) p"
  then obtain b t where bin: "b \<in> monic_set B" and "t \<in> keys p" and "b \<noteq> 0" and "lp b adds t"
    by (rule is_red_addsE)
  from bin obtain b' where b_def: "b = monic b'" and "b' \<in> B" unfolding monic_set_def ..
  have lpb': "lp b' = lp b" unfolding b_def by (rule lp_monic[symmetric])
  show "is_red B p"
  proof (rule is_red_addsI, fact \<open>b' \<in> B\<close>)
    from \<open>b \<noteq> 0\<close> show "b' \<noteq> 0" unfolding b_def by (simp add: monic_0_iff)
  next
    from \<open>lp b adds t\<close> show "lp b' adds t" unfolding lpb' .
  qed fact
next
  assume "is_red B p"
  then obtain b t where bin: "b \<in> B" and "t \<in> keys p" and "b \<noteq> 0" and "lp b adds t"
    by (rule is_red_addsE)
  let ?b = "monic b"
  have lp: "lp ?b = lp b" by (rule lp_monic)
  show "is_red (monic_set B) p"
  proof (rule is_red_addsI)
    from bin show "?b \<in> monic_set B" unfolding monic_set_def by (rule imageI)
  next
    from \<open>b \<noteq> 0\<close> show "?b \<noteq> 0" by (simp add: monic_0_iff)
  next
    from \<open>lp b adds t\<close> show "lp ?b adds t" unfolding lp .
  qed fact
qed

section \<open>Properties of Gr\"obner Bases\<close>

lemma GB_implies_zero_reducibility:
  assumes "is_Groebner_basis G" and "f \<in> (pideal G)"
  shows "(red G)\<^sup>*\<^sup>* f 0"
proof -
  from in_pideal_srtc[OF \<open>f \<in> (pideal G)\<close>] \<open>is_Groebner_basis G\<close> have "relation.cs (red G) f 0"
    unfolding is_Groebner_basis_def relation.is_ChurchRosser_def by simp
  then obtain s where rfs: "(red G)\<^sup>*\<^sup>* f s" and r0s: "(red G)\<^sup>*\<^sup>* 0 s" unfolding relation.cs_def by auto
  from rtrancl_0[OF r0s] and rfs show ?thesis by simp
qed

lemma GB_implies_reducibility:
  assumes "is_Groebner_basis G" and "f \<noteq> 0" and "f \<in> pideal G"
  shows "is_red G f"
    using assms by (meson GB_implies_zero_reducibility is_red_def relation.rtrancl_is_final)

end (* ordered_powerprod *)

subsection \<open>Weak Gr\"obner Bases and Strong Gr\"obner Bases\<close>

context od_powerprod
begin

lemma is_red_implies_0_red:
  assumes "pideal B \<subseteq> pideal A" and major: "\<And>q. q \<in> (pideal A) \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> is_red B q"
    and in_ideal: "p \<in> (pideal A)"
  shows "(red B)\<^sup>*\<^sup>* p 0"
  using in_ideal
proof (induction p rule: wfP_induct[OF ord_p_wf])
  fix p
  assume IH: "\<forall>q. q \<prec>p p \<longrightarrow> q \<in> pideal A \<longrightarrow> (red B)\<^sup>*\<^sup>* q 0" and "p \<in> (pideal A)"
  show "(red B)\<^sup>*\<^sup>* p 0"
  proof (cases "p = 0")
    case True
    then show ?thesis by simp
  next
    case False
    from major[OF \<open>p \<in> (pideal A)\<close> False] obtain q where redpq: "red B p q" unfolding is_red_alt ..
    from redpq have "q \<prec>p p" using red_ord by auto
    from \<open>pideal B \<subseteq> pideal A\<close> \<open>p \<in> pideal A\<close> \<open>red B p q\<close> have "q \<in> pideal A"
      by (rule pideal_closed_red)
    from IH[rule_format, OF \<open>q \<prec>p p\<close> this] have "(red B)\<^sup>*\<^sup>* q 0" .
    show ?thesis by (rule converse_rtranclp_into_rtranclp, rule redpq, fact)
  qed
qed

lemma GB_implies_unique_nf:
  assumes isGB: "is_Groebner_basis G"
  shows "\<exists>! h. (red G)\<^sup>*\<^sup>* f h \<and> \<not> is_red G h"
proof -
  from relation.wf_implies_nf_existence[OF red_wf] obtain h
    where ftoh: "(red G)\<^sup>*\<^sup>* f h" and irredh: "relation.is_final (red G) h" by auto
  show ?thesis
  proof
    from ftoh and irredh show "(red G)\<^sup>*\<^sup>* f h \<and> \<not> is_red G h" unfolding is_red_def by simp
  next
    fix h'
    assume "(red G)\<^sup>*\<^sup>* f h' \<and> \<not> is_red G h'"
    hence ftoh': "(red G)\<^sup>*\<^sup>* f h'" and irredh': "relation.is_final (red G) h'" unfolding is_red_def by simp_all
    show "h' = h"
    proof (rule relation.ChurchRosser_unique_final)
      from isGB show "relation.is_ChurchRosser (red G)" unfolding is_Groebner_basis_def .
    qed (fact+)
  qed
qed

lemma translation_property':
  assumes "p \<noteq> 0" and red_p_0: "(red F)\<^sup>*\<^sup>* p 0"
  shows "is_red F (p + q) \<or> is_red F q"
proof (rule disjCI)
  assume not_red: "\<not> is_red F q"
  from zero_reducibility_implies_lp_divisibility[OF red_p_0 \<open>p \<noteq> 0\<close>] obtain f
    where "f \<in> F" and "f \<noteq> 0" and lp_adds: "lp f adds lp p" .
  show "is_red F (p + q)"
  proof (cases "q = 0")
    case True
    with is_red_indI1[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> \<open>p \<noteq> 0\<close> lp_adds] show ?thesis by simp
  next
    case False
    from not_red is_red_addsI[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> _ lp_adds, of q] have "\<not> lp p \<in> (keys q)" by blast
    hence "lookup q (lp p) = 0" by simp
    with lp_in_keys[OF \<open>p \<noteq> 0\<close>] have "lp p \<in> (keys (p + q))" unfolding in_keys_iff by (simp add: lookup_add)
    from is_red_addsI[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> this lp_adds] show ?thesis .
  qed
qed
  
lemma translation_property:
  assumes "p \<noteq> q" and red_0: "(red F)\<^sup>*\<^sup>* (p - q) 0"
  shows "is_red F p \<or> is_red F q"
proof -
  from \<open>p \<noteq> q\<close> have "p - q \<noteq> 0" by simp
  from translation_property'[OF this red_0, of q] show ?thesis by simp
qed

lemma weak_GB_is_strong_GB:
  assumes "\<And>f. f \<in> (pideal G) \<Longrightarrow> (red G)\<^sup>*\<^sup>* f 0"
  shows "is_Groebner_basis G"
  unfolding is_Groebner_basis_def
proof (rule relation.confluence_implies_ChurchRosser, rule relation.unique_nf_implies_confluence, rule ccontr)
  fix f p q
  assume redfp: "(red G)\<^sup>*\<^sup>* f p" and redfq: "(red G)\<^sup>*\<^sup>* f q"
    and finp: "relation.is_final (red G) p" and finq: "relation.is_final (red G) q"
    and "p \<noteq> q"
  from red_rtranclp_diff_in_pideal[OF redfp] have "f - p \<in> pideal G" .
  from red_rtranclp_diff_in_pideal[OF redfq] have "f - q \<in> pideal G" .
  from pideal_closed_minus[OF this \<open>f - p \<in> pideal G\<close>] have "p - q \<in> pideal G" by simp
  from translation_property[OF \<open>p \<noteq> q\<close> assms[OF this]] have "is_red G p \<or> is_red G q" .
  thus False
  proof
    assume "is_red G p"
    with finp show ?thesis unfolding is_red_def by simp
  next
    assume "is_red G q"
    with finq show ?thesis unfolding is_red_def by simp
  qed
qed (rule red_wf)
  
lemma GB_alt_1: "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> (pideal G). (red G)\<^sup>*\<^sup>* f 0)"
  using weak_GB_is_strong_GB GB_implies_zero_reducibility by blast

lemma GB_alt_2: "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> (pideal G). f \<noteq> 0 \<longrightarrow> is_red G f)"
proof
  assume "is_Groebner_basis G"
  show "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> is_red G f"
  proof (intro ballI, intro impI)
    fix f
    assume "f \<in> (pideal G)" and "f \<noteq> 0"
    show "is_red G f" by (rule GB_implies_reducibility, fact+)
  qed
next
  assume a2: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> is_red G f"
  show "is_Groebner_basis G" unfolding GB_alt_1
  proof
    fix f
    assume "f \<in> pideal G"
    show "(red G)\<^sup>*\<^sup>* f 0"
    proof (rule is_red_implies_0_red, rule subset_refl)
      fix q
      assume "q \<in> pideal G" and "q \<noteq> 0"
      from a2[rule_format, OF this] show "is_red G q" .
    qed (fact)
  qed
qed
  
lemma GB_adds_lp:
  assumes "is_Groebner_basis G" and "f \<in> pideal G" and "f \<noteq> 0"
  obtains g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f"
proof -
  from \<open>is_Groebner_basis G\<close> have "\<forall>f\<in>pideal G. (red G)\<^sup>*\<^sup>* f 0" unfolding GB_alt_1 .
  from this \<open>f \<in> pideal G\<close> have "(red G)\<^sup>*\<^sup>* f 0" ..
  show ?thesis by (rule zero_reducibility_implies_lp_divisibility, fact+)
qed

lemma GB_alt_3: "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> (pideal G). f \<noteq> 0 \<longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp f))"
  unfolding GB_alt_1
proof
  assume a1: "\<forall>f\<in>pideal G. (red G)\<^sup>*\<^sup>* f 0"
  show "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)"
  proof (intro ballI, intro impI)
    fix f
    assume "f \<in> (pideal G)" and "f \<noteq> 0"
    with a1 have "(red G)\<^sup>*\<^sup>* f 0" by simp
    from zero_reducibility_implies_lp_divisibility'[OF this \<open>f \<noteq> 0\<close>] show "\<exists>h\<in>G. h \<noteq> 0 \<and> lp h adds lp f" .
  qed
next
  assume a2: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)"
  show "\<forall>f\<in>pideal G. (red G)\<^sup>*\<^sup>* f 0"
  proof (intro ballI)
    fix f
    assume "f \<in> (pideal G)"
    show "(red G)\<^sup>*\<^sup>* f 0"
    proof (rule is_red_implies_0_red, rule subset_refl)
      fix q
      assume "q \<in> (pideal G)" and "q \<noteq> 0"
      with a2 have "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp q" by simp
      then obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp q" by auto
      thus "is_red G q" using \<open>q \<noteq> 0\<close> is_red_indI1 by blast
    qed (fact)
  qed
qed
  
lemma GB_insert:
  assumes "is_Groebner_basis G" and "f \<in> pideal G"
  shows "is_Groebner_basis (insert f G)"
  using assms by (metis GB_alt_1 GB_implies_zero_reducibility pideal_insert red_rtrancl_subset subset_insertI)

lemma GB_subset:
  assumes "is_Groebner_basis G" and "G \<subseteq> G'" and "pideal G' = pideal G"
  shows "is_Groebner_basis G'"
  using GB_alt_2 assms(1) assms(2) assms(3) is_red_subset by blast
  
lemma monic_set_GB: "is_Groebner_basis (monic_set G) \<longleftrightarrow> is_Groebner_basis G"
  unfolding GB_alt_2 monic_set_pideal is_red_monic_set ..

end (* od_powerprod *)
  
subsection \<open>Replacing Elements in Gr\"obner Bases\<close>

context ordered_powerprod
begin

lemma replace_lp_adds_stable_is_red:
  assumes red: "is_red F f" and "q \<noteq> 0" and "lp q adds lp p"
  shows "is_red (replace p q F) f"
proof -
  from red obtain g t where "g \<in> F" and "g \<noteq> 0" and "t \<in> keys f" and "lp g adds t" by (rule is_red_addsE)
  show ?thesis
  proof (cases "g = p")
    case True
    show ?thesis
    proof (rule is_red_addsI)
      show "q \<in> replace p q F" by (rule in_replaceI1)
    next
      have "lp q adds lp p" by fact
      also have "... adds t" using \<open>lp g adds t\<close> unfolding True .
      finally show "lp q adds t" .
    qed (fact+)
  next
    case False
    show ?thesis by (rule is_red_addsI, rule in_replaceI2, fact+)
  qed
qed
  
lemma conversion_property:
  assumes "is_red {p} f" and "red {r} p q"
  shows "is_red {q} f \<or> is_red {r} f"
proof -
  from \<open>is_red {p} f\<close> obtain t where "t \<in> keys f" and "lp p adds t" and "p \<noteq> 0" by (rule is_red_addsE, simp)
  from red_indE[OF \<open>red {r} p q\<close>]
    have "(r \<noteq> 0 \<and> lp r adds lp p \<and> q = p - monom_mult (lc p / lc r) (lp p - lp r) r) \<or>
          red {r} (tail p) (q - monomial (lc p) (lp p))" by simp
  thus ?thesis
  proof
    assume "r \<noteq> 0 \<and> lp r adds lp p \<and> q = p - monom_mult (lc p / lc r) (lp p - lp r) r"
    hence "r \<noteq> 0" and "lp r adds lp p" by simp_all
    show ?thesis by (intro disjI2, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  next
    assume "red {r} (tail p) (q - monomial (lc p) (lp p))" (is "red _ ?p' ?q'")
    with red_ord have "?q' \<prec>p ?p'" .
    hence "?p' \<noteq> 0"
      and assm: "(?q' = 0 \<or> ((lp ?q') \<prec> (lp ?p') \<or> (lp ?q') = (lp ?p')))"
      unfolding ord_strict_p_rec[of ?q' ?p'] by (auto simp add: Let_def lc_def)
    have "lp ?p' \<prec> lp p" by (rule lp_tail, fact)
    let ?m = "monomial (lc p) (lp p)"
    from monomial_0D[of "lp p" "lc p"] lc_not_0[OF \<open>p \<noteq> 0\<close>] have "?m \<noteq> 0" by blast
    have "lp ?m = lp p" by (rule lp_monomial, rule lc_not_0, fact)
    have "q \<noteq> 0 \<and> lp q = lp p"
    proof (cases "?q' = 0")
      case True
      hence "q = ?m" by simp
      with \<open>?m \<noteq> 0\<close> \<open>lp ?m = lp p\<close> show ?thesis by simp
    next
      case False
      from assm show ?thesis
      proof
        assume "(lp ?q') \<prec> (lp ?p') \<or> (lp ?q') = (lp ?p')"
        hence "lp ?q' \<preceq> lp ?p'" by auto
        also have "... \<prec> lp p" by fact
        finally have "lp ?q' \<prec> lp p" .
        hence "lp ?q' \<prec> lp ?m" unfolding \<open>lp ?m = lp p\<close> .
        from lp_plus_eqI[OF this] \<open>lp ?m = lp p\<close> have "lp q = lp p" by simp
        show ?thesis
        proof (intro conjI, rule ccontr)
          assume "\<not> q \<noteq> 0"
          hence "q = 0" by simp
          hence "?q' = -?m" by simp
          hence "lp ?q' = lp (-?m)" by simp
          also have "... = lp ?m" using lp_uminus[OF \<open>?m \<noteq> 0\<close>] .
          finally have "lp ?q' = lp ?m" .
          with \<open>lp ?q' \<prec> lp ?m\<close> show False by simp
        qed (fact)
      next
        assume "?q' = 0"
        with False show ?thesis ..
      qed
    qed
    hence "q \<noteq> 0" and "lp q adds lp p" by simp_all
    show ?thesis by (intro disjI1, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  qed
qed
  
lemma replace_red_stable_is_red:
  assumes a1: "is_red F f" and a2: "red (remove p F) p q"
  shows "is_red (replace p q F) f" (is "is_red ?F' f")
proof -
  from a1 obtain g where "g \<in> F" and "is_red {g} f" by (rule is_red_singletonI)
  show ?thesis
  proof (cases "g = p")
    case True
    from a2 obtain h where "h \<in> (remove p F)" and "red {h} p q" unfolding red_def by auto
    from \<open>is_red {g} f\<close> have "is_red {p} f" unfolding True .
    have "is_red {q} f \<or> is_red {h} f" by (rule conversion_property, fact+)
    thus ?thesis
    proof
      assume "is_red {q} f"
      show ?thesis
      proof (rule is_red_singletonD)
        show "q \<in> ?F'" by (rule in_replaceI1)
      qed fact
    next
      assume "is_red {h} f"
      show ?thesis
      proof (rule is_red_singletonD)
        from \<open>h \<in> (remove p F)\<close> show "h \<in> ?F'" unfolding in_remove in_replace by simp
      qed fact
    qed
  next
    case False
    show ?thesis
    proof (rule is_red_singletonD)
      show "g \<in> ?F'" by (rule in_replaceI2, fact+)
    qed fact
  qed
qed
  
lemma red_in_pideal:
  assumes "p \<in> pideal A" and "B \<subseteq> A" and "red B p q"
  shows "q \<in> pideal A"
proof -
  have "red A p q" by (rule red_subset, rule \<open>red B p q\<close>, rule \<open>B \<subseteq> A\<close>)
  hence "(red A)\<^sup>*\<^sup>* p q" by simp
  hence "relation.srtc (red A) p q" by (rule relation.rtc_implies_srtc)
  hence "relation.srtc (red A) q p" by (rule relation.srtc_symmetric)
  hence "q - p \<in> pideal A" by (rule srtc_in_pideal)
  from pideal_closed_plus[OF this \<open>p \<in> pideal A\<close>] show "q \<in> pideal A" by simp
qed

lemma GB_remove_0_stable_GB:
  assumes "is_Groebner_basis G"
  shows "is_Groebner_basis (remove 0 G)"
  using assms by (simp only: remove_def is_Groebner_basis_def red_minus_singleton_zero)

end (* ordered_powerprod *)

context od_powerprod
begin

lemma GB_replace_lp_adds_stable_GB:
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and q: "q \<in> (pideal G)" and "lp q adds lp p"
  shows "is_Groebner_basis (replace p q G)" (is "is_Groebner_basis ?G'")
  using isGB unfolding GB_alt_3
proof (intro ballI, intro impI)
  fix f
  assume f1: "f \<in> (pideal ?G')" and "f \<noteq> 0"
    and a1: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)"
  from f1 replace_pideal[OF q, of p] have "f \<in> pideal G" ..
  from a1[rule_format, OF this \<open>f \<noteq> 0\<close>] obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by auto
  show "\<exists>g\<in>?G'. g \<noteq> 0 \<and> lp g adds lp f"
  proof (cases "g = p")
    case True
    show ?thesis
    proof
      from \<open>lp q adds lp p\<close> have "lp q adds lp g" unfolding True .
      also have "... adds lp f" by fact
      finally have "lp q adds lp f" .
      with \<open>q \<noteq> 0\<close> show "q \<noteq> 0 \<and> lp q adds lp f" ..
    next
      show "q \<in> ?G'" by (rule in_replaceI1)
    qed
  next
    case False
    show ?thesis
    proof
      show "g \<noteq> 0 \<and> lp g adds lp f" by (rule, fact+)
    next
      show "g \<in> ?G'" by (rule in_replaceI2, fact+)
    qed
  qed
qed
  
lemma GB_replace_lp_adds_stable_pideal:
  fixes G p q
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and "q \<in> pideal G" and "lp q adds lp p"
  shows "pideal (replace p q G) = pideal G" (is "pideal ?G' = pideal G")
proof (rule, rule replace_pideal, fact, rule)
  fix f
  assume "f \<in> pideal G"
  have "is_Groebner_basis ?G'" by (rule GB_replace_lp_adds_stable_GB, fact+)
  hence "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf)
  then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
  have "\<not> is_red G h"
  proof
    assume "is_red G h"
    have "is_red ?G' h" by (rule replace_lp_adds_stable_is_red, fact+)
    with irredh show False ..
  qed
  have "f - h \<in> pideal ?G'" by (rule red_rtranclp_diff_in_pideal, rule ftoh)
  have "f - h \<in> pideal G" by (rule, fact, rule replace_pideal, fact)
  from pideal_closed_minus[OF this \<open>f \<in> pideal G\<close>] have "-h \<in> pideal G" by simp
  from pideal_closed_uminus[OF this] have "h \<in> pideal G" by simp
  with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_implies_reducibility by auto
  with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
  thus "f \<in> pideal ?G'" by (simp add: red_rtranclp_0_in_pideal)
qed
  
lemma GB_replace_red_stable_GB:
  fixes G p q
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and q: "red (remove p G) p q"
  shows "is_Groebner_basis (replace p q G)" (is "is_Groebner_basis ?G'")
  using isGB unfolding GB_alt_2
proof (intro ballI, intro impI)
  fix f
  assume f1: "f \<in> (pideal ?G')" and "f \<noteq> 0"
    and a1: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> is_red G f"
  have "q \<in> pideal G"
  proof (rule red_in_pideal)
    from generator_subset_pideal \<open>p \<in> G\<close> show "p \<in> pideal G" ..
  next
    show "(remove p G) \<subseteq> G" by (rule remove_subset)
  qed (rule q)
  from f1 replace_pideal[OF this, of p] have "f \<in> pideal G" ..
  have "is_red G f" by (rule a1[rule_format], fact+)
  show "is_red ?G' f" by (rule replace_red_stable_is_red, fact+)
qed

lemma GB_replace_red_stable_pideal:
  fixes G p q
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "red (remove p G) p q"
  shows "pideal (replace p q G) = pideal G" (is "pideal ?G' = _")
proof -
  from \<open>p \<in> G\<close> generator_subset_pideal have "p \<in> pideal G" ..
  have "q \<in> pideal G" by (rule red_in_pideal, rule \<open>p \<in> pideal G\<close>, rule remove_subset, rule ptoq)
  show ?thesis
  proof (rule, rule replace_pideal, fact, rule)
    fix f
    assume "f \<in> pideal G"
    have "is_Groebner_basis ?G'" by (rule GB_replace_red_stable_GB, fact+)
    hence "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf)
    then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
    have "\<not> is_red G h"
    proof
      assume "is_red G h"
      have "is_red ?G' h" by (rule replace_red_stable_is_red, fact+)
      with irredh show False ..
    qed
    have "f - h \<in> pideal ?G'" by (rule red_rtranclp_diff_in_pideal, rule ftoh)
    have "f - h \<in> pideal G" by (rule, fact, rule replace_pideal, fact)
    from pideal_closed_minus[OF this \<open>f \<in> pideal G\<close>] have "-h \<in> pideal G" by simp
    from pideal_closed_uminus[OF this] have "h \<in> pideal G" by simp
    with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_implies_reducibility by auto
    with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
    thus "f \<in> pideal ?G'" by (simp add: red_rtranclp_0_in_pideal)
  qed
qed
  
lemma GB_replace_red_rtranclp_stable_GB:
  fixes G p q
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (remove p G))\<^sup>*\<^sup>* p q"
  shows "is_Groebner_basis (replace p q G)"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from isGB replace_same[OF \<open>p \<in> G\<close>] show ?case by simp
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    show ?thesis proof (rule GB_replace_red_stable_GB, fact, fact)
      from \<open>red (remove p G) y z\<close> show "red (remove p G) p z" unfolding True .
    qed
  next
    case False
    show ?thesis
      proof (cases "y \<in> G")
        case True
        have "y \<in> (remove p G)" (is "_ \<in> ?G'") by (intro in_removeI, fact+)
        hence "replace p y G = ?G'" unfolding replace_def by auto
        with \<open>is_Groebner_basis (replace p y G)\<close> have "is_Groebner_basis ?G'" by simp
        from \<open>y \<in> ?G'\<close> generator_subset_pideal have "y \<in> pideal ?G'" ..
        have "z \<in> pideal ?G'" by (rule pideal_closed_red, rule subset_refl, fact+)
        have "is_Groebner_basis (insert z ?G')" by (rule GB_insert, fact+)
        thus ?thesis unfolding replace_def .
      next
        case False
        have "is_Groebner_basis (replace y z (replace p y G))"
        proof (rule GB_replace_red_stable_GB, fact, rule in_replaceI1)
          from \<open>red (remove p G) y z\<close> show "red (remove y (replace p y G)) y z"
            unfolding replace_remove[OF False, of p] .
        qed
        moreover have "... = (replace p z G)" by (rule replace_replace, rule False)
        ultimately show ?thesis by simp
      qed
  qed
qed
  
lemma GB_replace_red_rtranclp_stable_pideal:
  fixes G p q
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (remove p G))\<^sup>*\<^sup>* p q"
  shows "pideal (replace p q G) = pideal G"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from replace_same[OF \<open>p \<in> G\<close>] show ?case by simp
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    show ?thesis proof (rule GB_replace_red_stable_pideal, fact, fact)
      from \<open>red (remove p G) y z\<close> show "red (remove p G) p z" unfolding True .
    qed
  next
    case False
    have "is_Groebner_basis (replace p y G)" by (rule GB_replace_red_rtranclp_stable_GB, fact+)
    show ?thesis
      proof (cases "y \<in> G")
        case True
        have "y \<in> (remove p G)" (is "_ \<in> ?G'") by (intro in_removeI, fact+)
        hence eq: "?G' = replace p y G" unfolding replace_def by auto
        from \<open>y \<in> ?G'\<close> generator_subset_pideal have "y \<in> pideal ?G'" ..
        have "z \<in> pideal ?G'" by (rule pideal_closed_red, rule subset_refl, fact+)
        hence "pideal (insert z ?G') = pideal ?G'" by (rule pideal_insert)
        moreover have "... = pideal G" unfolding eq by fact
        ultimately show ?thesis unfolding replace_def by simp
      next
        case False
        have "pideal (replace p z G) = pideal (replace y z (replace p y G))"
          using replace_replace[OF False] by simp
        moreover have "... = pideal (replace p y G)"
        proof (rule GB_replace_red_stable_pideal, fact, rule in_replaceI1)
          from \<open>red (remove p G) y z\<close> show "red (remove y (replace p y G)) y z"
            unfolding replace_remove[OF False, of p] .
        qed
        moreover have "... = pideal G" by fact
        ultimately show ?thesis by simp
      qed
  qed
qed

end (* od_powerprod *)
  
section \<open>Reduced Gr\"obner Bases\<close>

context ordered_powerprod
begin

definition is_auto_reduced :: "('a, 'b::field) poly_mapping set \<Rightarrow> bool" where
  "is_auto_reduced B \<equiv> (\<forall>b\<in>B. \<not> is_red (remove b B) b)"
  
definition is_reduced_GB :: "('a, 'b::field) poly_mapping set \<Rightarrow> bool" where
  "is_reduced_GB B \<equiv> is_Groebner_basis B \<and> is_auto_reduced B \<and> is_monic_set B \<and> 0 \<notin> B"
  
lemma is_auto_reducedD:
  assumes "is_auto_reduced B" and "b \<in> B"
  shows "\<not> is_red (remove b B) b"
  using assms unfolding is_auto_reduced_def by auto
  
lemma reduced_GB_D1:
  assumes "is_reduced_GB G"
  shows "is_Groebner_basis G"
  using assms unfolding is_reduced_GB_def by simp

lemma reduced_GB_D2:
  assumes "is_reduced_GB G"
  shows "is_auto_reduced G"
  using assms unfolding is_reduced_GB_def by simp

 lemma reduced_GB_D3:
  assumes "is_reduced_GB G"
  shows "is_monic_set G"
  using assms unfolding is_reduced_GB_def by simp
     
lemma reduced_GB_D4:
  assumes "is_reduced_GB G" and "g \<in> G"
  shows "g \<noteq> 0"
  using assms unfolding is_reduced_GB_def by auto
    
lemma reduced_GB_lc:
  assumes major: "is_reduced_GB G" and "g \<in> G"
  shows "lc g = 1"
by (rule is_monic_setD, rule reduced_GB_D3, fact major, fact \<open>g \<in> G\<close>, rule reduced_GB_D4, fact major, fact \<open>g \<in> G\<close>)

lemma (in od_powerprod) is_reduced_GB_subsetI:
  assumes Ared: "is_reduced_GB A" and BGB: "is_Groebner_basis B" and Bmon: "is_monic_set B"
    and *: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a - b \<noteq> 0 \<Longrightarrow> lp (a - b) \<in> keys b \<Longrightarrow> lp (a - b) \<prec> lp b \<Longrightarrow> False"
    and id_eq: "pideal A = pideal B"
  shows "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
    
  have "a \<noteq> 0" by (rule reduced_GB_D4, fact Ared, fact \<open>a \<in> A\<close>)
  have lca: "lc a = 1" by (rule reduced_GB_lc, fact Ared, fact \<open>a \<in> A\<close>)
  have AGB: "is_Groebner_basis A" by (rule reduced_GB_D1, fact Ared)
      
  from \<open>a \<in> A\<close> generator_subset_pideal have "a \<in> pideal A" ..
  also have "... = pideal B" using id_eq by simp
  finally have "a \<in> pideal B" .
      
  with \<open>a \<noteq> 0\<close> GB_alt_3 BGB obtain b where "b \<in> B" and "b \<noteq> 0" and baddsa: "lp b adds lp a" by auto
  from Bmon this(1) this(2) have lcb: "lc b = 1" by (rule is_monic_setD)
  from \<open>b \<in> B\<close> generator_subset_pideal have "b \<in> pideal B" ..
  also have "... = pideal A" using id_eq by simp
  finally have "b \<in> pideal A" .
      
  have lp_eq: "lp b = lp a"
  proof (rule ccontr)
    assume "lp b \<noteq> lp a"
    from \<open>b \<in> pideal A\<close> \<open>b \<noteq> 0\<close> GB_alt_3 AGB obtain a'
      where "a' \<in> A" and "a' \<noteq> 0" and a'addsb: "lp a' adds lp b" by auto
    have a'addsa: "lp a' adds lp a" by (rule adds_trans, fact a'addsb, fact baddsa)
    have "lp a' \<noteq> lp a"
    proof
      assume "lp a' = lp a"
      hence aaddsa': "lp a adds lp a'" by simp
      have "lp a adds lp b" by (rule adds_trans, fact aaddsa', fact a'addsb)
      have "lp a = lp b" by (rule adds_antisym, fact+)
      with \<open>lp b \<noteq> lp a\<close> show False by simp
    qed
    hence "a' \<noteq> a" by auto
    with \<open>a' \<in> A\<close> have "a' \<in> (remove a A)" by (intro in_removeI, auto)
    have is_red: "is_red (remove a A) a" by (intro is_red_addsI, fact, fact, rule lp_in_keys, fact+)
    have "\<not> is_red (remove a A) a" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Ared, fact+)
    with is_red show False by simp
  qed
  
  have "a - b = 0"
  proof (rule ccontr)
    let ?c = "a - b"
    assume "?c \<noteq> 0"
    have "?c \<in> pideal A" by (rule pideal_closed_minus, fact+)
    also have "... = pideal B" using id_eq by simp
    finally have "?c \<in> pideal B" .
        
    from \<open>b \<noteq> 0\<close> have "- b \<noteq> 0" by simp
    have "lp (-b) = lp a" unfolding lp_uminus[OF \<open>b \<noteq> 0\<close>] by fact
    have "lc (-b) = - lc a" unfolding lc_uminus[OF \<open>b \<noteq> 0\<close>] lca lcb ..
    from \<open>?c \<noteq> 0\<close> have "a + (-b) \<noteq> 0" by simp
    
    have "lp ?c \<in> keys ?c" by (rule lp_in_keys, fact)
    have "keys ?c \<subseteq> (keys a \<union> keys b)" by (fact keys_minus)
    with \<open>lp ?c \<in> keys ?c\<close> have "lp ?c \<in> keys a \<or> lp ?c \<in> keys b" by auto
    thus False
    proof
      assume "lp ?c \<in> keys a"
          
      from \<open>?c \<in> pideal A\<close> \<open>?c \<noteq> 0\<close> GB_alt_3[of A] AGB obtain a'
        where "a' \<in> A" and "a' \<noteq> 0" and a'addsc: "lp a' adds lp ?c" by auto

      have "lp a' \<preceq> lp ?c" by (rule ord_adds, fact a'addsc)
      also have "... = lp (a + (-b))" by simp
      also have "... \<prec> lp a" by (rule lp_plus_precI, fact+)
      finally have "lp a' \<prec> lp a" .
      hence "lp a' \<noteq> lp a" by simp
      hence "a' \<noteq> a" by auto
      with \<open>a' \<in> A\<close> have "a' \<in> (remove a A)" by (intro in_removeI, auto)
          
      have is_red: "is_red (remove a A) a" by (intro is_red_addsI, fact, fact, fact+)
      have "\<not> is_red (remove a A) a" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Ared, fact+)
      with is_red show False by simp
    next
      assume "lp ?c \<in> keys b"

      with \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>?c \<noteq> 0\<close> show False
      proof (rule *)
        have "lp ?c = lp ((-b) + a)" by simp
        also have "... \<prec> lp (-b)"
        proof (rule lp_plus_precI)
          from \<open>?c \<noteq> 0\<close> show "-b + a \<noteq> 0" by simp
        next
          from \<open>lp (-b) = lp a\<close> show "lp a = lp (-b)" by simp
        next
          from \<open>lc (-b) = - lc a\<close> show "lc a = - lc (-b)" by simp
        qed
        finally show "lp ?c \<prec> lp b" unfolding lp_uminus[OF \<open>b \<noteq> 0\<close>] .
      qed
    qed
  qed
  
  hence "a = b" by simp
  with \<open>b \<in> B\<close> show "a \<in> B" by simp
qed

lemma (in od_powerprod) is_reduced_GB_unique':
  assumes Ared: "is_reduced_GB A" and Bred: "is_reduced_GB B" and id_eq: "pideal A = pideal B"
  shows "A \<subseteq> B"
proof -
  from Bred have BGB: "is_Groebner_basis B" by (rule reduced_GB_D1)
  with assms(1) show ?thesis
  proof (rule is_reduced_GB_subsetI)
    from Bred show "is_monic_set B" by (rule reduced_GB_D3)
  next
    fix a b :: "('a, 'b) poly_mapping"
    let ?c = "a - b"
    assume "a \<in> A" and "b \<in> B" and "a \<noteq> 0" and "b \<noteq> 0" and "?c \<noteq> 0" and "lp ?c \<in> keys b" and "lp ?c \<prec> lp b"
  
    from \<open>a \<in> A\<close> have "a \<in> pideal B" by (simp only: id_eq[symmetric], rule generator_in_pideal)
    moreover from \<open>b \<in> B\<close> have "b \<in> pideal B" by (rule generator_in_pideal)
    ultimately have "?c \<in> pideal B" by (rule pideal_closed_minus)
    from this \<open>?c \<noteq> 0\<close> GB_alt_3[of B] BGB obtain b'
      where "b' \<in> B" and "b' \<noteq> 0" and b'addsc: "lp b' adds lp ?c" by auto
  
    have "lp b' \<preceq> lp ?c" by (rule ord_adds, fact b'addsc)
    also have "... \<prec> lp b" by fact
    finally have "lp b' \<prec> lp b" unfolding lp_uminus[OF \<open>b \<noteq> 0\<close>] .
    hence "lp b' \<noteq> lp b" by simp
    hence "b' \<noteq> b" by auto
    with \<open>b' \<in> B\<close> have "b' \<in> (remove b B)" by (intro in_removeI, auto)
        
    have is_red: "is_red (remove b B) b" by (intro is_red_addsI, fact, fact, fact+)
    have "\<not> is_red (remove b B) b" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Bred, fact+)
    with is_red show False by simp
  qed fact
qed
  
theorem (in od_powerprod) is_reduced_GB_unique:
  assumes Ared: "is_reduced_GB A" and Bred: "is_reduced_GB B" and id_eq: "pideal A = pideal B"
  shows "A = B"
proof
  from assms show "A \<subseteq> B" by (rule is_reduced_GB_unique')
next
  from Bred Ared id_eq[symmetric] show "B \<subseteq> A" by (rule is_reduced_GB_unique')
qed
  
section \<open>Computing Reduced Gr\"obner Bases\<close>
  
subsection \<open>Minimal Bases\<close>
  
definition is_minimal_basis :: "('a, 'b::zero) poly_mapping set \<Rightarrow> bool" where
  "is_minimal_basis B \<longleftrightarrow> ((\<forall>p\<in>B. p \<noteq> 0) \<and> (\<forall>p q. p \<in> B \<longrightarrow> q \<in> B \<longrightarrow> p \<noteq> q \<longrightarrow> \<not> lp p adds lp q))"
  
lemma is_minimal_basisI:
  assumes "\<And>p. p \<in> B \<Longrightarrow> p \<noteq> 0" and "\<And>p q. p \<in> B \<Longrightarrow> q \<in> B \<Longrightarrow> p \<noteq> q \<Longrightarrow> \<not> lp p adds lp q"
  shows "is_minimal_basis B"
  unfolding is_minimal_basis_def using assms by auto
    
lemma is_minimal_basisD1:
  assumes "is_minimal_basis B" and "p \<in> B"
  shows "p \<noteq> 0"
  using assms unfolding is_minimal_basis_def by auto
    
lemma is_minimal_basisD2:
  assumes "is_minimal_basis B" and "p \<in> B" and "q \<in> B" and "p \<noteq> q"
  shows "\<not> lp p adds lp q"
  using assms unfolding is_minimal_basis_def by auto
  
lemma is_minimal_basisD3:
  assumes "is_minimal_basis B" and "p \<in> B" and "q \<in> B" and "p \<noteq> q"
  shows "\<not> lp q adds lp p"
  using assms unfolding is_minimal_basis_def by auto
    
lemma is_minimal_basis_subset:
  assumes "is_minimal_basis B" and "A \<subseteq> B"
  shows "is_minimal_basis A"
proof (intro is_minimal_basisI)
  fix p
  assume "p \<in> A"
  with \<open>A \<subseteq> B\<close> have "p \<in> B" ..
  with \<open>is_minimal_basis B\<close> show "p \<noteq> 0" by (rule is_minimal_basisD1)
next
  fix p q
  assume "p \<in> A" and "q \<in> A" and "p \<noteq> q"
  from \<open>p \<in> A\<close> and \<open>q \<in> A\<close> have "p \<in> B" and "q \<in> B" using \<open>A \<subseteq> B\<close> by auto
  from \<open>is_minimal_basis B\<close> this \<open>p \<noteq> q\<close> show " \<not> lp p adds lp q" by (rule is_minimal_basisD2)
qed
  
lemma nadds_red:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lp q adds lp p" and red: "red B p r"
  shows "r \<noteq> 0 \<and> lp r = lp p"
proof -
  from red obtain q t where "q \<in> B" and rs: "red_single p r q t" by (rule red_setE)
  from rs have "q \<noteq> 0" and "lookup p (t + lp q) \<noteq> 0"
    and r_def: "r = p - monom_mult (lookup p (t + lp q) / lc q) t q" unfolding red_single_def by simp_all
  have "t + lp q \<preceq> lp p" by (rule lp_max, fact)
  moreover have "t + lp q \<noteq> lp p"
  proof
    assume "t + lp q = lp p"
    hence "lp q adds lp p" by (metis adds_triv_right) 
    with nadds[OF \<open>q \<in> B\<close>] show False ..
  qed
  ultimately have "t + lp q \<prec> lp p" by simp
  let ?m = "monom_mult (lookup p (t + lp q) / lc q) t q"
  from \<open>lookup p (t + lp q) \<noteq> 0\<close> lc_not_0[OF \<open>q \<noteq> 0\<close>] have c0: "lookup p (t + lp q) / lc q \<noteq> 0" by simp
  from \<open>q \<noteq> 0\<close> c0 have "?m \<noteq> 0" unfolding monom_mult_0_iff by simp
  hence "lp (-?m) = lp ?m" by (rule lp_uminus)
  also have lp1: "lp ?m = t + lp q" by (rule lp_mult, fact+)
  finally have lp2: "lp (-?m) = t + lp q" .
  
  show ?thesis
  proof
    show "r \<noteq> 0"
    proof
      assume "r = 0"
      hence "p = ?m" unfolding r_def by simp
      with lp1 \<open>t + lp q \<noteq> lp p\<close> show False by simp
    qed
  next
    have "lp (-?m + p) = lp p"
    proof (rule lp_plus_eqI)
      show "lp (-?m) \<prec> lp p" unfolding lp2 by fact
    qed
    thus "lp r = lp p" unfolding r_def by simp
  qed
qed
    
lemma nadds_red_nonzero:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lp q adds lp p" and "red B p r"
  shows "r \<noteq> 0"
  using nadds_red[OF assms] by simp
    
lemma nadds_red_lp:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lp q adds lp p" and "red B p r"
  shows "lp r = lp p"
  using nadds_red[OF assms] by simp
  
lemma nadds_red_rtrancl_lp:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lp q adds lp p" and rtrancl: "(red B)\<^sup>*\<^sup>* p r"
  shows "lp r = lp p"
  using rtrancl
proof (induct rule: rtranclp_induct)
  case base
  show ?case ..
next
  case (step y z)
  have "lp z = lp y"
  proof (rule nadds_red_lp)
    fix q
    assume "q \<in> B"
    thus "\<not> lp q adds lp y" unfolding \<open>lp y = lp p\<close> by (rule nadds)
  qed fact
  with \<open>lp y = lp p\<close> show ?case by simp
qed
  
lemma nadds_red_rtrancl_nonzero:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lp q adds lp p" and "p \<noteq> 0" and rtrancl: "(red B)\<^sup>*\<^sup>* p r"
  shows "r \<noteq> 0"
  using rtrancl
proof (induct rule: rtranclp_induct)
  case base
  show ?case by fact
next
  case (step y z)
  from nadds \<open>(red B)\<^sup>*\<^sup>* p y\<close> have "lp y = lp p" by (rule nadds_red_rtrancl_lp)
  show "z \<noteq> 0"
  proof (rule nadds_red_nonzero)
    fix q
    assume "q \<in> B"
    thus "\<not> lp q adds lp y" unfolding \<open>lp y = lp p\<close> by (rule nadds)
  qed fact
qed
  
lemma minimal_basis_red_rtrancl_nonzero:
  assumes "is_minimal_basis B" and "p \<in> B" and "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "r \<noteq> 0"
proof (rule nadds_red_rtrancl_nonzero)
  fix q
  assume "q \<in> (B - {p})"
  hence "q \<in> B" and "q \<noteq> p" by auto
  show "\<not> lp q adds lp p" by (rule is_minimal_basisD2, fact+)
next
  show "p \<noteq> 0" by (rule is_minimal_basisD1, fact+)
qed fact

lemma minimal_basis_red_rtrancl_lp:
  assumes "is_minimal_basis B" and "p \<in> B" and "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "lp r = lp p"
proof (rule nadds_red_rtrancl_lp)
  fix q
  assume "q \<in> (B - {p})"
  hence "q \<in> B" and "q \<noteq> p" by auto
  show "\<not> lp q adds lp p" by (rule is_minimal_basisD2, fact+)
qed fact
  
lemma is_minimal_basis_replace:
  assumes major: "is_minimal_basis B" and "p \<in> B" and red: "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "is_minimal_basis (replace p r B)"
proof (rule is_minimal_basisI)
  fix q
  assume "q \<in> replace p r B"
  hence "q = r \<or> q \<in> B \<and> q \<noteq> p" by (rule in_replaceD)
  thus "q \<noteq> 0"
  proof
    assume "q = r"
    from assms show ?thesis unfolding \<open>q = r\<close> by (rule minimal_basis_red_rtrancl_nonzero)
  next
    assume "q \<in> B \<and> q \<noteq> p"
    hence "q \<in> B" ..
    with major show ?thesis by (rule is_minimal_basisD1)
  qed
next
  fix a b
  assume "a \<in> replace p r B" and "b \<in> replace p r B" and "a \<noteq> b"
  from assms have lpr: "lp r = lp p" by (rule minimal_basis_red_rtrancl_lp)
  from \<open>b \<in> replace p r B\<close> have b: "b = r \<or> b \<in> B \<and> b \<noteq> p" by (rule in_replaceD)
  from \<open>a \<in> replace p r B\<close> have "a = r \<or> a \<in> B \<and> a \<noteq> p" by (rule in_replaceD)
  thus "\<not> lp a adds lp b"
  proof
    assume "a = r"
    hence lpa: "lp a = lp p" using lpr by simp
    from b show ?thesis
    proof
      assume "b = r"
      with \<open>a \<noteq> b\<close> show ?thesis unfolding \<open>a = r\<close> by simp
    next
      assume "b \<in> B \<and> b \<noteq> p"
      hence "b \<in> B" and "p \<noteq> b" by auto
      with major \<open>p \<in> B\<close> have "\<not> lp p adds lp b" by (rule is_minimal_basisD2)
      thus ?thesis unfolding lpa .
    qed
  next
    assume "a \<in> B \<and> a \<noteq> p"
    hence "a \<in> B" and "a \<noteq> p" by simp_all
    from b show ?thesis
    proof
      assume "b = r"
      from major \<open>a \<in> B\<close> \<open>p \<in> B\<close> \<open>a \<noteq> p\<close> have "\<not> lp a adds lp p" by (rule is_minimal_basisD2)
      thus ?thesis unfolding \<open>b = r\<close> lpr by simp
    next
      assume "b \<in> B \<and> b \<noteq> p"
      hence "b \<in> B" ..
      from major \<open>a \<in> B\<close> \<open>b \<in> B\<close> \<open>a \<noteq> b\<close> show ?thesis by (rule is_minimal_basisD2)
    qed
  qed
qed

lemma (in od_powerprod) minimal_basis_is_reduced_GB:
  assumes "is_minimal_basis B" and "is_monic_set B" and "is_reduced_GB G" and "G \<subseteq> B"
    and "pideal B = pideal G"
  shows "B = G"
  using _ assms(3) assms(5)
proof (rule is_reduced_GB_unique)
  from assms(3) have "is_Groebner_basis G" by (rule reduced_GB_D1)
  show "is_reduced_GB B" unfolding is_reduced_GB_def
  proof (intro conjI)
    show "0 \<notin> B"
    proof
      assume "0 \<in> B"
      with assms(1) have "0 \<noteq> (0::('a, 'b) poly_mapping)" by (rule is_minimal_basisD1)
      thus False by simp
    qed
  next
    from \<open>is_Groebner_basis G\<close> assms(4) assms(5) show "is_Groebner_basis B" by (rule GB_subset)
  next
    show "is_auto_reduced B" unfolding is_auto_reduced_def
    proof (intro ballI notI)
      fix b
      assume "b \<in> B"
      with assms(1) have "b \<noteq> 0" by (rule is_minimal_basisD1)
      assume "is_red (remove b B) b"
      then obtain f where "f \<in> remove b B" and "is_red {f} b" by (rule is_red_singletonI)
      from this(1) have "f \<in> B" and "f \<noteq> b" by (simp_all add: in_remove)

      from assms(1) \<open>f \<in> B\<close> have "f \<noteq> 0" by (rule is_minimal_basisD1)
      from \<open>f \<in> B\<close> have "f \<in> pideal B" by (rule generator_in_pideal)
      hence "f \<in> pideal G" by (simp only: assms(5))
      with \<open>is_Groebner_basis G\<close> have "f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)" unfolding GB_alt_3 ..
      from this \<open>f \<noteq> 0\<close> have "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f" ..
      then obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by auto
      from \<open>g \<in> G\<close> \<open>G \<subseteq> B\<close> have "g \<in> B" ..
      have "g = f"
      proof (rule ccontr)
        assume "g \<noteq> f"
        with assms(1) \<open>g \<in> B\<close> \<open>f \<in> B\<close> have "\<not> lp g adds lp f" by (rule is_minimal_basisD2)
        from this \<open>lp g adds lp f\<close> show False ..
      qed
      with \<open>g \<in> G\<close> have "f \<in> G" by simp
      with \<open>f \<noteq> b\<close> \<open>is_red {f} b\<close> have red: "is_red (remove b G) b"
        by (meson in_remove is_red_singletonD)

      from \<open>b \<in> B\<close> have "b \<in> pideal B" by (rule generator_in_pideal)
      hence "b \<in> pideal G" by (simp only: assms(5))
      with \<open>is_Groebner_basis G\<close> have "b \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp b)" unfolding GB_alt_3 ..
      from this \<open>b \<noteq> 0\<close> have "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp b" ..
      then obtain g' where "g' \<in> G" and "g' \<noteq> 0" and "lp g' adds lp b" by auto
      from \<open>g' \<in> G\<close> \<open>G \<subseteq> B\<close> have "g' \<in> B" ..
      have "g' = b"
      proof (rule ccontr)
        assume "g' \<noteq> b"
        with assms(1) \<open>g' \<in> B\<close> \<open>b \<in> B\<close> have "\<not> lp g' adds lp b" by (rule is_minimal_basisD2)
        from this \<open>lp g' adds lp b\<close> show False ..
      qed
      with \<open>g' \<in> G\<close> have "b \<in> G" by simp

      from assms(3) have "is_auto_reduced G" by (rule reduced_GB_D2)
      from this \<open>b \<in> G\<close> have "\<not> is_red (remove b G) b" by (rule is_auto_reducedD)
      from this red show False ..
    qed
  qed fact
qed

subsection \<open>Computing Minimal Bases\<close>
  
primrec comp_min_basis_aux :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::zero) poly_mapping list" where
  comp_min_basis_aux_base: "comp_min_basis_aux Nil ys = ys"|
  comp_min_basis_aux_rec: "comp_min_basis_aux (x # xs) ys =
    (if (\<exists>q\<in>(set xs \<union> set ys). lp q adds lp x) then
      (comp_min_basis_aux xs ys)
    else
      (comp_min_basis_aux xs (x # ys))
    )"
  
lemma subset_comp_min_basis_aux:
  shows "set ys \<subseteq> set (comp_min_basis_aux xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_min_basis_aux_base ..
next
  case (Cons a xs)
  have "set ys \<subseteq> set (a#ys)" by auto
  also have "set (a#ys) \<subseteq> set (comp_min_basis_aux xs (a#ys))" by (rule Cons.hyps)
  finally have "set ys \<subseteq> set (comp_min_basis_aux xs (a#ys))" .
  moreover have "set ys \<subseteq> set (comp_min_basis_aux xs ys)" by (rule Cons.hyps)
  ultimately show ?case unfolding comp_min_basis_aux_rec by simp
qed
    
lemma comp_min_basis_aux_subset:
  shows "set (comp_min_basis_aux xs ys) \<subseteq> set xs \<union> set ys"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_min_basis_aux_base by simp
next
  case (Cons a xs)
  from Cons.hyps have "set (comp_min_basis_aux xs ys) \<subseteq> set xs \<union> set ys" .
  also have "... \<subseteq> set (a#xs) \<union> set ys" by auto
  finally have c1: "set (comp_min_basis_aux xs ys) \<subseteq> set (a#xs) \<union> set ys" .
  
  from Cons.hyps have "set (comp_min_basis_aux xs (a#ys)) \<subseteq> set xs \<union> set (a#ys)" .
  also have "... = set (a#xs) \<union> set ys" by auto
  finally have c2: "set (comp_min_basis_aux xs (a#ys)) \<subseteq> set (a#xs) \<union> set ys" .
  
  from c1 c2 show ?case unfolding comp_min_basis_aux_rec by simp
qed

lemmas comp_min_basis_aux_empty_subset = comp_min_basis_aux_subset[of _ "[]", simplified]
  
lemma comp_min_basis_aux_notin:
  assumes "x \<in> set xs \<union> set ys" and "x \<notin> set (comp_min_basis_aux xs ys)" and "x \<noteq> 0"
  shows "\<exists>y\<in>set xs \<union> set ys. y \<noteq> 0 \<and> lp y adds lp x"
  using assms
proof (induct xs arbitrary: x ys)
  case Nil
  show ?case by (rule, intro conjI, fact, rule adds_refl, fact)
next
  case (Cons a xs)
  from Cons(3) show ?case unfolding comp_min_basis_aux_rec
  proof (simp only: split: if_splits)
    assume "\<exists>q\<in>set xs \<union> set ys. lp q adds lp a" and "x \<notin> set (comp_min_basis_aux xs ys)"
    from Cons(2) have "x = a \<or> x \<in> set xs \<union> set ys" by simp
    thus ?thesis
    proof
      assume "x = a"
      show ?thesis by (rule, intro conjI, fact, rule adds_refl, fact)
    next
      assume "x \<in> set xs \<union> set ys"
      have "\<exists>y\<in>set xs \<union> set ys. y \<noteq> 0 \<and> lp y adds lp x" by (rule Cons.hyps, fact+)
      then obtain y where "y \<in> set xs \<union> set ys" and "y \<noteq> 0 \<and> lp y adds lp x" ..
      show ?thesis
      proof (rule, fact)
        from \<open>y \<in> set xs \<union> set ys\<close> show "y \<in> set (a # xs) \<union> set ys" by simp
      qed
    qed
  next
    assume "\<not> (\<exists>q\<in>set xs \<union> set ys. lp q adds lp a)" and
      "x \<notin> set (comp_min_basis_aux xs (a # ys))"
    from Cons(2) have "x \<in> set xs \<union> set (a#ys)" by simp
    have "\<exists>y\<in>set xs \<union> set (a#ys). y \<noteq> 0 \<and> lp y adds lp x" by (rule Cons.hyps, fact+)
    then obtain y where "y \<in> set xs \<union> set (a#ys)" and "y \<noteq> 0 \<and> lp y adds lp x" ..
    show ?thesis
    proof (rule, fact)
      from \<open>y \<in> set xs \<union> set (a#ys)\<close> show "y \<in> set (a # xs) \<union> set ys" by simp
    qed
  qed
qed

lemma comp_min_basis_aux_adds:
  assumes pin: "p \<in> set xs"
    and "\<And>x. x \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> 0"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lp x adds lp y"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "\<exists>q\<in>set (comp_min_basis_aux xs ys). lp q adds lp p"
  using assms
proof (induct xs arbitrary: p ys)
  case Nil
  from \<open>p \<in> set []\<close> show ?case by simp
next
  case (Cons a xs)
  let ?A = "set (a # xs) \<union> set ys"
  let ?B = "set xs \<union> set ys"
  let ?C = "set xs \<union> set (a # ys)"
  have "?C = ?A" by simp
  have "?B \<subseteq> ?A" by auto
  have "\<And>x. x \<in> ?B \<Longrightarrow> x \<noteq> 0" by (auto simp add: \<open>?B \<subseteq> ?A\<close> Cons(3))
  have "\<And>x y. x \<in> ?B \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lp x adds lp y"
    by (auto simp add: \<open>?B \<subseteq> ?A\<close> Cons(4))
  have "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
    by (auto simp add: \<open>?B \<subseteq> ?A\<close> Cons(5))
      
  from \<open>p \<in> set (a # xs)\<close> have "p \<in> ?A" ..
  hence "p \<noteq> 0" by (rule Cons(3))
  from \<open>p \<in> set (a#xs)\<close> have "p = a \<or> p \<in> set xs" by auto
  thus ?case
  proof
    assume "p = a"
    with \<open>p \<noteq> 0\<close> have "a \<noteq> 0" by simp
    show ?case
    proof (cases "\<exists>q\<in>?B. lp q adds lp a")
      case True
      then obtain q where "q \<in> ?B" and "lp q adds lp a" ..
      from True have eq: "comp_min_basis_aux (a # xs) ys = comp_min_basis_aux xs ys"
        unfolding comp_min_basis_aux_rec by simp
      from \<open>q \<in> ?B\<close> show ?thesis
      proof
        assume "q \<in> set xs"
        have "\<exists>q1\<in>set (comp_min_basis_aux xs ys). lp q1 adds lp q" by (rule Cons.hyps, fact+)
        then obtain q1 where "q1 \<in> set (comp_min_basis_aux xs ys)" and "lp q1 adds lp q" ..
        show ?thesis
        proof
          show "q1 \<in> set (comp_min_basis_aux (a # xs) ys)" unfolding eq by fact
        next
          from \<open>lp q1 adds lp q\<close> \<open>lp q adds lp a\<close> show "lp q1 adds lp p" unfolding \<open>p = a\<close> by (rule adds_trans)
        qed
      next
        assume "q \<in> set ys"
        have "q \<in> set (comp_min_basis_aux xs ys)" by (rule, fact \<open>q \<in> set ys\<close>, rule subset_comp_min_basis_aux)
        show ?thesis
        proof
          show "q \<in> set (comp_min_basis_aux (a # xs) ys)" unfolding eq by fact
       next
          from \<open>lp q adds lp a\<close> show "lp q adds lp p" unfolding \<open>p = a\<close> .
        qed
      qed
    next
      case False
      show ?thesis
      proof
        have "a \<in> set (comp_min_basis_aux xs (a#ys))"
        proof
          show "a \<in> set (a#ys)" by simp
        next
          show "set (a # ys) \<subseteq> set (comp_min_basis_aux xs (a # ys))" by (rule subset_comp_min_basis_aux)
        qed
        with \<open>a \<noteq> 0\<close> False show "a \<in> set (comp_min_basis_aux (a # xs) ys)"
          unfolding comp_min_basis_aux_rec by auto
      next
        show "lp a adds lp p" unfolding \<open>p = a\<close> by (rule adds_refl)
      qed
    qed
  next
    assume "p \<in> set xs"
    have "\<exists>q\<in>set (comp_min_basis_aux xs ys). lp q adds lp p" by (rule Cons.hyps, fact+)
    then obtain q where qin: "q \<in> set (comp_min_basis_aux xs ys)" and "lp q adds lp p" ..
    show ?case
    proof (cases "\<exists>q\<in>?B. lp q adds lp a")
      case True
      hence eq: "comp_min_basis_aux (a # xs) ys = comp_min_basis_aux xs ys"
        unfolding comp_min_basis_aux_rec by simp
      show ?thesis unfolding eq by (rule, fact \<open>lp q adds lp p\<close>, fact)
    next
      case False
      hence eq: "comp_min_basis_aux (a#xs) ys = comp_min_basis_aux xs (a#ys)"
        unfolding comp_min_basis_aux_rec by auto
      from False have rl: "\<And>q. q \<in> ?B \<Longrightarrow> \<not> lp q adds lp a" by auto
      show ?thesis unfolding eq
      proof (rule Cons.hyps, fact)
        fix x
        assume "x \<in> ?C"
        thus "x \<noteq> 0" unfolding \<open>?C = ?A\<close> by (rule Cons(3))
      next
        fix x y
        assume "x \<in> ?C"
        hence "x \<in> ?A" unfolding \<open>?C = ?A\<close> .
        hence "x \<noteq> 0" by (rule Cons(3))
        assume "x \<noteq> y"
        assume "y \<in> set (a # ys)"
        hence "y = a \<or> y \<in> set ys" by simp
        thus "\<not> lp x adds lp y"
        proof
          assume "y = a"
          show ?thesis unfolding \<open>y = a\<close>
          proof (rule rl)
            from \<open>x \<in> ?A\<close> have "x = a \<or> x \<in> ?B" by simp
            thus "x \<in> ?B"
            proof
              assume "x = a"
              with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>y = a\<close> ..
            qed
          qed
        next
          assume "y \<in> set ys"
          from \<open>x \<in> ?A\<close> this \<open>x \<noteq> y\<close> show ?thesis by (rule Cons(4))
        qed
      next
        fix x y
        assume "x \<in> ?C" and "y \<in> ?C" and "x \<noteq> y"
        thus "lp x \<noteq> lp y" unfolding \<open>?C = ?A\<close> by (rule Cons(5))
      qed
    qed
  qed
qed

lemma comp_min_basis_aux_empty_adds:
  assumes "p \<in> set xs" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  obtains q where "q \<in> set (comp_min_basis_aux xs [])" and "lp q adds lp p"
proof -
  from assms(1) have "\<exists>q\<in>set (comp_min_basis_aux xs []). lp q adds lp p"
  proof (rule comp_min_basis_aux_adds)
    fix x
    assume "x \<in> set xs \<union> set []"
    hence "x \<in> set xs" by simp
    with assms(2) show "x \<noteq> 0" by auto
  next
    fix x y :: "('a, 'b) poly_mapping"
    assume "y \<in> set []"
    thus "\<not> lp x adds lp y" by simp
  next
    fix x y :: "('a, 'b) poly_mapping"
    assume "x \<in> set xs \<union> set []"
    hence x: "x \<in> set xs" by simp
    assume "y \<in> set xs \<union> set []"
    hence y: "y \<in> set xs" by simp
    assume "x \<noteq> y"
    from x y this show "lp x \<noteq> lp y" by (rule assms(3))
  qed
  then obtain q where "q \<in> set (comp_min_basis_aux xs [])" and "lp q adds lp p" ..
  thus ?thesis ..
qed
  
lemma comp_min_basis_aux_distinct:
  assumes "distinct ys"
  shows "distinct (comp_min_basis_aux xs ys)"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case unfolding comp_min_basis_aux_base .
next
  case (Cons a xs)
  show ?case unfolding comp_min_basis_aux_rec
  proof (split if_split, intro conjI impI, rule Cons.hyps, rule Cons(2))
    assume a: "\<not> (\<exists>q\<in>set xs \<union> set ys. lp q adds lp a)"
    show "distinct (comp_min_basis_aux xs (a # ys))"
    proof (rule Cons.hyps)
      have "a \<notin> set ys"
      proof
        assume "a \<in> set ys"
        hence "a \<in> set xs \<union> set ys" by simp
        have "\<exists>q\<in>set xs \<union> set ys. lp q adds lp a"
        proof
          show "lp a adds lp a" by (rule adds_refl)
        qed fact
        with a show False ..
      qed
      with Cons(2) show "distinct (a # ys)" by simp
    qed
  qed
qed

lemma comp_min_basis_aux_empty_is_red:
  assumes "is_red (set xs) f" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "is_red (set (comp_min_basis_aux xs [])) f"
proof -
  from assms(1) obtain x t where "x \<in> set xs" and "t \<in> keys f" and "lp x adds t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> assms(2) assms(3) obtain y
    where yin: "y \<in> set (comp_min_basis_aux xs [])" and "lp y adds lp x"
    by (rule comp_min_basis_aux_empty_adds)
  show ?thesis
  proof (rule is_red_addsI)
    from \<open>lp y adds lp x\<close> \<open>lp x adds t\<close> show "lp y adds t" by (rule adds_trans)
  next
    from comp_min_basis_aux_empty_subset yin have "y \<in> set xs" ..
    with assms(2) show "y \<noteq> 0" by auto
  qed fact+
qed
  
definition comp_min_basis_pre :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::zero) poly_mapping list" where
  "comp_min_basis_pre xs = remdups_by lp (filter (\<lambda>x. x \<noteq> 0) xs)"
  
lemma comp_min_basis_pre_subset:
  shows "set (comp_min_basis_pre xs) \<subseteq> set xs"
  unfolding comp_min_basis_pre_def by (meson filter_is_subset subset_remdups_by subset_trans)

lemma comp_min_basis_pre_nonzero:
  assumes "p \<in> set (comp_min_basis_pre xs)"
  shows "p \<noteq> 0"
  using assms unfolding comp_min_basis_pre_def using subset_remdups_by by fastforce

lemma comp_min_basis_pre_nonzero': "0 \<notin> set (comp_min_basis_pre xs)"
  using comp_min_basis_pre_nonzero by fastforce

lemma comp_min_basis_pre_distinct_lp:
  assumes pin: "p \<in> set (comp_min_basis_pre xs)" and qin: "q \<in> set (comp_min_basis_pre xs)" and "p \<noteq> q"
  shows "lp p \<noteq> lp q"
  using assms unfolding comp_min_basis_pre_def by (rule remdups_by_distinct_by)

lemma comp_min_basis_pre_lp:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_min_basis_pre xs)" and "lp q = lp p"
proof -
  from assms have pin: "p \<in> set (filter (\<lambda>x. x \<noteq> 0) xs)" (is "p \<in> set ?ys") by simp
  hence "lp p \<in> lp ` set ?ys" by simp
  also have "... = lp ` set (remdups_by lp ?ys)" by (simp add: set_remdups_by)
  finally have "lp p \<in> lp ` set (remdups_by lp ?ys)" .
  then obtain q where qin: "q \<in> set (remdups_by lp ?ys)" and "lp q = lp p" by auto
  show ?thesis
  proof
    from qin show "q \<in> set (comp_min_basis_pre xs)" unfolding comp_min_basis_pre_def .
  qed fact
qed

lemma comp_min_basis_pre_is_red:
  assumes "is_red (set xs) f"
  shows "is_red (set (comp_min_basis_pre xs)) f"
proof -
  from assms obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lp x adds t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_min_basis_pre xs)" and "lp y = lp x"
    by (rule comp_min_basis_pre_lp)
  show ?thesis
  proof (rule is_red_addsI)
    from \<open>lp x adds t\<close> show "lp y adds t" by (simp only: \<open>lp y = lp x\<close>)
  next
    from yin show "y \<noteq> 0" by (rule comp_min_basis_pre_nonzero)
  qed fact+
qed

definition comp_min_basis :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::zero) poly_mapping list" where
  "comp_min_basis xs = comp_min_basis_aux (comp_min_basis_pre xs) []"
  
lemma comp_min_basis_subset_comp_min_basis_pre:
  shows "set (comp_min_basis xs) \<subseteq> set (comp_min_basis_pre xs)"
  unfolding comp_min_basis_def by (rule comp_min_basis_aux_empty_subset)
  
lemma comp_min_basis_subset:
  shows "set (comp_min_basis xs) \<subseteq> set xs"
proof -
  have "set (comp_min_basis xs) \<subseteq> set (comp_min_basis_pre xs)"
    by (rule comp_min_basis_subset_comp_min_basis_pre)
  also have "... \<subseteq> set xs" by (rule comp_min_basis_pre_subset)
  finally show ?thesis .
qed
    
lemma comp_min_basis_nonzero:
  assumes "p \<in> set (comp_min_basis xs)"
  shows "p \<noteq> 0"
by (rule comp_min_basis_pre_nonzero, rule, fact assms, fact comp_min_basis_subset_comp_min_basis_pre)

lemma comp_min_basis_adds:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_min_basis xs)" and "lp q adds lp p"
proof -
  from assms obtain q1 where q1_in: "q1 \<in> set (comp_min_basis_pre xs)" and "lp q1 = lp p"
    by (rule comp_min_basis_pre_lp)
  have "0 \<notin> set (comp_min_basis_pre xs)" using comp_min_basis_pre_nonzero by auto
  with q1_in obtain q where "q \<in> set (comp_min_basis_aux (comp_min_basis_pre xs) [])" and "lp q adds lp q1"
  proof (rule comp_min_basis_aux_empty_adds)
    fix x y
    assume "x \<in> set (comp_min_basis_pre xs)" and "y \<in> set (comp_min_basis_pre xs)" and "x \<noteq> y"
    thus "lp x \<noteq> lp y" by (rule comp_min_basis_pre_distinct_lp)
  qed
  show ?thesis
  proof
    show "q \<in> set (comp_min_basis xs)" unfolding comp_min_basis_def by fact
  next
    from \<open>lp q adds lp q1\<close> show "lp q adds lp p" unfolding \<open>lp q1 = lp p\<close> .
  qed
qed
  
lemma comp_min_basis_is_red:
  assumes "is_red (set xs) f"
  shows "is_red (set (comp_min_basis xs)) f"
proof -
  from assms obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lp x adds t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_min_basis xs)" and "lp y adds lp x"
    by (rule comp_min_basis_adds)
  show ?thesis
  proof (rule is_red_addsI)
    from \<open>lp y adds lp x\<close> \<open>lp x adds t\<close> show "lp y adds t" by (rule adds_trans)
  next
    from yin show "y \<noteq> 0" by (rule comp_min_basis_nonzero)
  qed fact+
qed

end (* ordered_powerprod *)

context od_powerprod
begin

lemma comp_min_basis_aux_nadds:
  assumes "p \<in> set (comp_min_basis_aux xs ys)" and "q \<in> set xs \<union> set ys" and "p \<noteq> q"
    and "\<And>x. x \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> 0"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lp x adds lp y"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "\<not> lp q adds lp p"
  using assms
proof (induct xs arbitrary: p q ys)
  case Nil
  from Nil(1) Nil(2) have "p \<in> set ys" "q \<in> set ys" unfolding comp_min_basis_aux_base by simp_all
  show ?case
  proof (rule Nil(5))
    from \<open>q \<in> set ys\<close> show "q \<in> set [] \<union> set ys" by simp
  next
    from \<open>p \<noteq> q\<close> show "q \<noteq> p" by simp
  qed fact
next
  case (Cons a xs)
  let ?A = "set (a#xs) \<union> set ys"
  let ?B = "set xs \<union> set ys"
  let ?C = "set xs \<union> set (a#ys)"
  from Cons(2) show ?case unfolding comp_min_basis_aux_rec
  proof (simp only: split: if_splits)
    assume a1: "\<exists>q\<in>?B. lp q adds lp a"
      and "p \<in> set (comp_min_basis_aux xs ys)"
    have "\<And>x. x \<in> ?B \<Longrightarrow> x \<noteq> 0"
    proof -
      fix x
      assume "x \<in> ?B"
      hence "x \<in> ?A" by simp
      thus "x \<noteq> 0" by (rule Cons(5))
    qed
    have "\<And>x y. x \<in> ?B \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lp x adds lp y"
    proof -
      fix x y
      assume "x \<in> ?B"
      hence "x \<in> ?A" by simp
      assume "y \<in> set ys" and "x \<noteq> y"
      show "\<not> lp x adds lp y" by (rule Cons(6), fact+)
    qed
    have "\<And>x y. x \<in> ?B \<Longrightarrow> y \<in> ?B \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
    proof -
      fix x y
      assume "x \<in> ?B"
      hence "x \<in> ?A" by simp
      assume "y \<in> ?B"
      hence "y \<in> ?A" by simp
      assume "x \<noteq> y"
      show "lp x \<noteq> lp y" by (rule Cons(7), fact+)
    qed
    have "q \<noteq> 0" by (rule Cons(5), fact)
    from Cons(3) have "q = a \<or> q \<in> set xs \<union> set ys" by simp
    thus ?thesis
    proof
      assume "q = a"
      from a1 show ?thesis
      proof
        fix q1
        assume "q1 \<in> set xs \<union> set ys" and "lp q1 adds lp a"
        show ?thesis
        proof (cases "p = q1")
          case True
          from \<open>lp q1 adds lp a\<close> have "lp p adds lp q" unfolding True \<open>q = a\<close> .
          show ?thesis
          proof
            assume "lp q adds lp p"
            with \<open>lp p adds lp q\<close> have "lp p = lp q" by (rule adds_antisym)
            moreover have "lp p \<noteq> lp q"
            proof (rule Cons(7))
              from comp_min_basis_aux_subset Cons(2) show "p \<in> set (a # xs) \<union> set ys" by blast
            qed fact+
            ultimately show False by simp
          qed
        next
          case False
          have "\<not> lp q1 adds lp p" by (rule Cons.hyps, fact+)
          show ?thesis
          proof
            from \<open>lp q1 adds lp a\<close> have "lp q1 adds lp q" unfolding \<open>q = a\<close> .
            also assume "lp q adds lp p"
            finally show False using \<open>\<not> lp q1 adds lp p\<close> by simp
          qed
        qed
      qed
    next
      assume "q \<in> set xs \<union> set ys"
      show ?thesis by (rule Cons.hyps, fact+)
    qed
  next
    assume a: "\<not> (\<exists>q\<in>?B. lp q adds lp a)"
      and "p \<in> set (comp_min_basis_aux xs (a # ys))"
    show ?thesis
    proof (rule Cons.hyps, fact)
      from \<open>q \<in> ?A\<close> show "q \<in> ?C" by simp
    next
      fix x
      assume "x \<in> ?C"
      hence "x \<in> ?A" by simp
      thus "x \<noteq> 0" by (rule Cons(5))
    next
      fix x y
      assume "x \<in> ?C"
      hence "x \<in> ?A" by simp
      assume "x \<noteq> y"
      assume "y \<in> set (a # ys)"
      hence "y = a \<or> y \<in> set ys" by simp
      thus "\<not> lp x adds lp y"
      proof
        assume "y = a"
        from \<open>x \<in> ?A\<close> have "x = a \<or> x \<in> ?B" by simp
        thus ?thesis
        proof
          assume "x = a"
          with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>y = a\<close> ..
        next
          assume "x \<in> ?B"
          from a have "\<And>q. q \<in> ?B \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> \<not> lp q adds lp a" by auto
          thus ?thesis unfolding \<open>y = a\<close>
          proof this
            show "x \<in> ?B" by fact
          next
            show "x \<noteq> 0" by (rule Cons(5), fact)
          qed
        qed
      next
        assume "y \<in> set ys"
        show ?thesis by (rule Cons(6), fact+)
      qed
    next
      fix x y
      assume "x \<in> ?C"
      hence "x \<in> ?A" by simp
      assume "y \<in> ?C"
      hence "y \<in> ?A" by simp
      assume "x \<noteq> y"
      show "lp x \<noteq> lp y" by (rule Cons(7), fact+)
    qed fact
  qed
qed

lemma comp_min_basis_aux_empty_nadds:
  assumes "p \<in> set (comp_min_basis_aux xs [])" and "q \<in> set xs" and "p \<noteq> q" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "\<not> lp q adds lp p"
  using assms(1) _ assms(3)
proof (rule comp_min_basis_aux_nadds)
  from assms(2) show "q \<in> set xs \<union> set []" by simp
next
  fix x
  assume "x \<in> set xs \<union> set []"
  with assms(4) show "x \<noteq> 0" by auto
next
  fix x y :: "('a, 'b) poly_mapping"
  assume "y \<in> set []"
  thus "\<not> lp x adds lp y" by simp
next
  fix x y
  assume "x \<in> set xs \<union> set []" and "y \<in> set xs \<union> set []"
  hence "x \<in> set xs" and "y \<in> set xs" by simp_all
  moreover assume "x \<noteq> y"
  ultimately show "lp x \<noteq> lp y" by (rule assms(5))
qed

lemma comp_min_basis_aux_empty_GB:
  assumes "is_Groebner_basis (set xs)" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "is_Groebner_basis (set (comp_min_basis_aux xs []))"
  unfolding GB_alt_2
proof (intro ballI impI)
  fix f
  assume fin: "f \<in> pideal (set (comp_min_basis_aux xs []))" and "f \<noteq> 0"
  have "f \<in> pideal (set xs)" by (rule, fact fin, rule pideal_mono, fact comp_min_basis_aux_empty_subset)
  show "is_red (set (comp_min_basis_aux xs [])) f"
  proof (rule comp_min_basis_aux_empty_is_red)
    from assms \<open>f \<noteq> 0\<close> \<open>f \<in> pideal (set xs)\<close> show "is_red (set xs) f" by (simp add: GB_alt_2)
  qed (fact+)
qed

lemma comp_min_basis_aux_empty_pideal:
  assumes "is_Groebner_basis (set xs)" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lp x \<noteq> lp y"
  shows "pideal (set (comp_min_basis_aux xs [])) = pideal (set xs)"
proof -
  show ?thesis
  proof (rule, rule pideal_mono, fact comp_min_basis_aux_empty_subset)
    show "pideal (set xs) \<subseteq> pideal (set (comp_min_basis_aux xs []))"
    proof
      fix f
      assume "f \<in> pideal (set xs)"
      show "f \<in> pideal (set (comp_min_basis_aux xs []))"
      proof (cases "f = 0")
        case True
        show ?thesis unfolding True by (rule zero_in_pideal)
      next
        case False
        let ?xs = "comp_min_basis_aux xs []"
        have "(red (set ?xs))\<^sup>*\<^sup>* f 0"
        proof (rule is_red_implies_0_red, rule pideal_mono, fact comp_min_basis_aux_empty_subset)
          fix q
          assume "q \<noteq> 0" and "q \<in> pideal (set xs)"
          with assms(1) have "is_red (set xs) q" by (rule GB_implies_reducibility)
          from this assms(2) assms(3) show "is_red (set ?xs) q" by (rule comp_min_basis_aux_empty_is_red)
        qed fact
        thus ?thesis by (rule red_rtranclp_0_in_pideal)
      qed
    qed
  qed
qed

lemma comp_min_basis_pre_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_min_basis_pre xs))"
  unfolding GB_alt_3
proof (intro ballI impI)
  fix f
  assume fin: "f \<in> pideal (set (comp_min_basis_pre xs))" and "f \<noteq> 0"
  have "f \<in> pideal (set xs)" by (rule, fact fin, rule pideal_mono, rule comp_min_basis_pre_subset)
  with assms have "f \<noteq> 0 \<longrightarrow> (\<exists>g \<in> set xs. g \<noteq> 0 \<and> lp g adds lp f)" unfolding GB_alt_3 ..
  from this \<open>f \<noteq> 0\<close> have "\<exists>g \<in> set xs. g \<noteq> 0 \<and> lp g adds lp f" ..
  then obtain g where "g \<in> set xs" and "g \<noteq> 0" and "lp g adds lp f" by auto
  from this(1) this(2) obtain g' where g'_in: "g' \<in> set (comp_min_basis_pre xs)" and "lp g' = lp g"
    by (rule comp_min_basis_pre_lp)
  from this(1) show "\<exists>g\<in>set (comp_min_basis_pre xs). g \<noteq> 0 \<and> lp g adds lp f"
  proof (rule, intro conjI)
    from g'_in show "g' \<noteq> 0" by (rule comp_min_basis_pre_nonzero)
  next
    from \<open>lp g adds lp f\<close> show "lp g' adds lp f" by (simp only: \<open>lp g' = lp g\<close>)
  qed
qed

lemma comp_min_basis_pre_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_min_basis_pre xs)) = pideal (set xs)"
proof -
  show ?thesis
  proof (rule, rule pideal_mono, rule comp_min_basis_pre_subset, rule)
    fix f
    assume "f \<in> pideal (set xs)"
    show "f \<in> pideal (set (comp_min_basis_pre xs))"
    proof (cases "f = 0")
      case True
      show ?thesis unfolding True by (rule zero_in_pideal)
    next
      case False
      let ?xs = "comp_min_basis_pre xs"
      have "(red (set ?xs))\<^sup>*\<^sup>* f 0"
      proof (rule is_red_implies_0_red, rule pideal_mono, rule comp_min_basis_pre_subset)
        fix q
        assume "q \<noteq> 0" and "q \<in> pideal (set xs)"
        with assms have "is_red (set xs) q" by (rule GB_implies_reducibility)
        thus "is_red (set ?xs) q" by (rule comp_min_basis_pre_is_red)
      qed fact
      thus ?thesis by (rule red_rtranclp_0_in_pideal)
    qed
  qed
qed

lemma comp_min_basis_nadds:
  assumes pin: "p \<in> set (comp_min_basis xs)" and qin: "q \<in> set (comp_min_basis xs)" and "p \<noteq> q"
  shows "\<not> lp q adds lp p"
proof (rule comp_min_basis_aux_empty_nadds)
  from pin show "p \<in> set (comp_min_basis_aux (comp_min_basis_pre xs) [])" unfolding comp_min_basis_def .
next
  show "q \<in> set (comp_min_basis_pre xs)"
    by (rule, fact qin, fact comp_min_basis_subset_comp_min_basis_pre)
qed (fact, fact comp_min_basis_pre_nonzero', fact comp_min_basis_pre_distinct_lp)

lemma comp_min_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_min_basis xs))"
  unfolding comp_min_basis_def
  by (rule comp_min_basis_aux_empty_GB, rule comp_min_basis_pre_GB, fact,
      fact comp_min_basis_pre_nonzero', fact comp_min_basis_pre_distinct_lp)

lemma comp_min_basis_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_min_basis xs)) = pideal (set xs)"
proof -
  have "pideal (set (comp_min_basis xs)) = pideal (set (comp_min_basis_pre xs))"
    unfolding comp_min_basis_def
    by (rule comp_min_basis_aux_empty_pideal, rule comp_min_basis_pre_GB, fact,
        fact comp_min_basis_pre_nonzero', fact comp_min_basis_pre_distinct_lp)
  also from assms have "... = pideal (set xs)" by (rule comp_min_basis_pre_pideal)
  finally show ?thesis .
qed

lemma comp_min_basis_is_minimal_basis:
  shows "is_minimal_basis (set (comp_min_basis xs))"
  by (rule is_minimal_basisI, rule comp_min_basis_nonzero, assumption, rule comp_min_basis_nadds,
      assumption+, simp)

lemma comp_min_basis_distinct:
  shows "distinct (comp_min_basis xs)"
  unfolding comp_min_basis_def
  by (rule comp_min_basis_aux_distinct, simp)

subsection \<open>Computing Reduced Bases\<close>

lemma is_minimal_basis_trd_is_minimal_basis:
  assumes min: "is_minimal_basis (set (x # xs))" and notin: "x \<notin> set xs"
  shows "is_minimal_basis (set ((trd xs x) # xs))"
  unfolding replace_Cons[OF notin, of "trd xs x"] using min
proof (rule is_minimal_basis_replace, simp)
  from notin have eq: "set (x # xs) - {x} = set xs" by simp
  show "(red (set (x # xs) - {x}))\<^sup>*\<^sup>* x (trd xs x)" unfolding eq by (rule trd_red_rtrancl)
qed

lemma is_minimal_basis_trd_distinct:
  assumes min: "is_minimal_basis (set (x # xs))" and dist: "distinct (x # xs)"
  shows "distinct ((trd xs x) # xs)"
proof -
  let ?y = "trd xs x"
  from min have lpy: "lp ?y = lp x"
  proof (rule minimal_basis_red_rtrancl_lp, simp)
    from dist have "x \<notin> set xs" by simp
    hence eq: "set (x # xs) - {x} = set xs" by simp
    show "(red (set (x # xs) - {x}))\<^sup>*\<^sup>* x (trd xs x)" unfolding eq by (rule trd_red_rtrancl)
  qed
  have "?y \<notin> set xs"
  proof
    assume "?y \<in> set xs"
    hence "?y \<in> set (x # xs)" by simp
    with min have "\<not> lp ?y adds lp x"
    proof (rule is_minimal_basisD2, simp)
      show "?y \<noteq> x"
      proof
        assume "?y = x"
        from dist have "x \<notin> set xs" by simp
        with \<open>?y \<in> set xs\<close> show False unfolding \<open>?y = x\<close> by simp
      qed
    qed
    thus False unfolding lpy by simp
  qed
  moreover from dist have "distinct xs" by simp
  ultimately show ?thesis by simp
qed

primrec comp_red_basis_aux :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::field) poly_mapping list" where
  comp_red_basis_aux_base: "comp_red_basis_aux Nil ys = ys"|
  comp_red_basis_aux_rec: "comp_red_basis_aux (x # xs) ys = comp_red_basis_aux xs ((trd (xs @ ys) x) # ys)"
  
lemma subset_comp_red_basis_aux:
  shows "set ys \<subseteq> set (comp_red_basis_aux xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base ..
next
  case (Cons a xs)
  have "set ys \<subseteq> set ((trd (xs @ ys) a) # ys)" by auto
  also have "... \<subseteq> set (comp_red_basis_aux xs ((trd (xs @ ys) a) # ys))" by (rule Cons.hyps)
  finally show ?case unfolding comp_red_basis_aux_rec .
qed

lemma comp_red_basis_aux_nonzero:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)" and "p \<in> set (comp_red_basis_aux xs ys)"
  shows "p \<noteq> 0"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case
  proof (rule is_minimal_basisD1)
    from Nil(1) show "is_minimal_basis (set ys)" by simp
  next
    from Nil(3) show "p \<in> set ys" unfolding comp_red_basis_aux_base .
  qed
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  have "a \<in> set (a # xs @ ys)" by simp
  from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?ys = "trd (xs @ ys) a # ys"
  show ?case
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  next
    from Cons(4) show "p \<in> set (comp_red_basis_aux xs ?ys)" unfolding comp_red_basis_aux_rec .
  qed
qed
  
lemma comp_red_basis_aux_lp:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
  shows "lp ` set (xs @ ys) = lp ` set (comp_red_basis_aux xs ys)"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a: "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  from Cons(2) have "lp ?b = lp a" unfolding eq
  proof (rule minimal_basis_red_rtrancl_lp, simp)
    from a have eq2: "set (a # xs @ ys) - {a} = set (xs @ ys)" by simp
    show "(red (set (a # xs @ ys) - {a}))\<^sup>*\<^sup>* a ?b" unfolding eq2 by (rule trd_red_rtrancl)
  qed
  hence "lp ` set ((a # xs) @ ys) = lp ` set ((?b # xs) @ ys)" by simp
  also have "... = lp ` set (xs @ (?b # ys))" by simp
  finally have eq2: "lp ` set ((a # xs) @ ys) = lp ` set (xs @ (?b # ys))" .
  show ?case unfolding comp_red_basis_aux_rec eq2
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  qed
qed
  
lemma comp_red_basis_aux_pideal:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
  shows "pideal (set (comp_red_basis_aux xs ys)) \<subseteq> pideal (set (xs @ ys))"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a: "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  have "pideal (set (comp_red_basis_aux xs ?ys)) \<subseteq> pideal (set (xs @ ?ys))"
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  qed
  also have "... = pideal (set (?b # xs @ ys))" by simp
  also have "... = pideal (replace a ?b (set (a # xs @ ys)))" unfolding replace_Cons[OF a, of ?b] ..
  also have "... \<subseteq> pideal (set (a # xs @ ys))"
  proof (rule replace_pideal)
    have "a - (trd (xs @ ys) a) \<in> pideal (set (xs @ ys))" by (rule trd_in_pideal)
    have "a - (trd (xs @ ys) a) \<in> pideal (set (a # xs @ ys))"
    proof
      show "pideal (set (xs @ ys)) \<subseteq> pideal (set (a # xs @ ys))" by (rule pideal_mono, auto)
    qed fact
    hence "- (a - (trd (xs @ ys) a)) \<in> pideal (set (a # xs @ ys))" by (rule pideal_closed_uminus)
    hence "(trd (xs @ ys) a) - a \<in> pideal (set (a # xs @ ys))" by simp
    hence "((trd (xs @ ys) a) - a) + a \<in> pideal (set (a # xs @ ys))"
    proof (rule pideal_closed_plus)
      show "a \<in> pideal (set (a # xs @ ys))"
      proof
        show "a \<in> set (a # xs @ ys)" by simp
      qed (rule generator_subset_pideal)
    qed
    thus "trd (xs @ ys) a \<in> pideal (set (a # xs @ ys))" by simp
  qed
  also have "... = pideal (set ((a # xs) @ ys))" by simp
  finally show ?case unfolding comp_red_basis_aux_rec .
qed
  
lemma comp_red_basis_aux_irred:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
    and "\<And>y. y \<in> set ys \<Longrightarrow> \<not> is_red (set (xs @ ys) - {y}) y"
    and "p \<in> set (comp_red_basis_aux xs ys)"
  shows "\<not> is_red (set (comp_red_basis_aux xs ys) - {p}) p"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  have "\<not> is_red (set ([] @ ys) - {p}) p"
  proof (rule Nil(3))
    from Nil(4) show "p \<in> set ys" unfolding comp_red_basis_aux_base .
  qed
  thus ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a_notin: "a \<notin> set (xs @ ys)" unfolding eq by simp
  from Cons(2) have is_min: "is_minimal_basis (set (a # xs @ ys))" unfolding eq .
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  have dist: "distinct (?b # (xs @ ys))"
  proof (rule is_minimal_basis_trd_distinct, fact is_min)
    from Cons(3) show "distinct (a # xs @ ys)" unfolding eq .
  qed
  
  show ?case unfolding comp_red_basis_aux_rec
  proof (rule Cons.hyps)
    from Cons(2) a_notin show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from dist show "distinct (xs @ ?ys)" unfolding distinct_reorder .
  next
    fix y
    assume "y \<in> set ?ys"
    hence "y = ?b \<or> y \<in> set ys" by simp
    thus "\<not> is_red (set (xs @ ?ys) - {y}) y"
    proof
      assume "y = ?b"
      from dist have "?b \<notin> set (xs @ ys)" by simp
      hence eq3: "set (xs @ ?ys) - {?b} = set (xs @ ys)" unfolding set_reorder by simp
      have "\<not> is_red (set (xs @ ys)) ?b" by (rule trd_irred)
      thus ?thesis unfolding \<open>y = ?b\<close> eq3 .
    next
      assume "y \<in> set ys"
      hence irred: "\<not> is_red (set ((a # xs) @ ys) - {y}) y" by (rule Cons(4))
      from \<open>y \<in> set ys\<close> a_notin have "y \<noteq> a" by auto
      hence eq3: "set ((a # xs) @ ys) - {y} = {a} \<union> (set (xs @ ys) - {y})" by auto
      from irred have i1: "\<not> is_red {a} y" and i2: "\<not> is_red (set (xs @ ys) - {y}) y"
        unfolding eq3 is_red_union by simp_all
      show ?thesis unfolding set_reorder
      proof (cases "y = ?b")
        case True
        from i2 show "\<not> is_red (set (?b # xs @ ys) - {y}) y" unfolding True by simp
      next
        case False
        hence eq4: "set (?b # xs @ ys) - {y} = {?b} \<union> (set (xs @ ys) - {y})" by auto
        show "\<not> is_red (set (?b # xs @ ys) - {y}) y" unfolding eq4
        proof
          assume "is_red ({?b} \<union> (set (xs @ ys) - {y})) y"
          thus False unfolding is_red_union
          proof
            have lpb: "lp ?b = lp a"
            proof (rule minimal_basis_red_rtrancl_lp, fact is_min)
              show "a \<in> set (a # xs @ ys)" by simp
            next
              from a_notin have eq: "set (a # xs @ ys) - {a} = set (xs @ ys)" by simp
              show "(red (set (a # xs @ ys) - {a}))\<^sup>*\<^sup>* a ?b" unfolding eq by (rule trd_red_rtrancl)
            qed
            assume "is_red {?b} y"
            then obtain t where "t \<in> keys y" and "lp ?b adds t" unfolding is_red_adds_iff by auto
            with lpb have "lp a adds t" by simp
            have "is_red {a} y"
              by (rule is_red_addsI, rule, rule is_minimal_basisD1, fact is_min, simp, fact+)
            with i1 show False ..
          next
            assume "is_red (set (xs @ ys) - {y}) y"
            with i2 show False ..
          qed
        qed
      qed
    qed
  next
    from Cons(5) show "p \<in> set (comp_red_basis_aux xs ?ys)" unfolding comp_red_basis_aux_rec .
  qed
qed

definition comp_red_basis :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::field) poly_mapping list" where
  "comp_red_basis xs = comp_red_basis_aux (comp_min_basis xs) []"
  
lemma comp_red_basis_nonzero:
  assumes "p \<in> set (comp_red_basis xs)"
  shows "p \<noteq> 0"
proof -
  have "is_minimal_basis (set ((comp_min_basis xs) @ []))" by (simp add: comp_min_basis_is_minimal_basis)
  moreover have "distinct ((comp_min_basis xs) @ [])" by (simp add: comp_min_basis_distinct)
  moreover from assms have "p \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def .
  ultimately show ?thesis by (rule comp_red_basis_aux_nonzero)
qed

lemma comp_red_basis_adds:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_red_basis xs)" and "lp q adds lp p"
proof -
  from assms obtain q1 where "q1 \<in> set (comp_min_basis xs)" and "lp q1 adds lp p"
    by (rule comp_min_basis_adds)
  from \<open>q1 \<in> set (comp_min_basis xs)\<close> have "lp q1 \<in> lp ` set (comp_min_basis xs)" by simp
  also have "... = lp ` set ((comp_min_basis xs) @ [])" by simp
  also have "... = lp ` set (comp_red_basis_aux (comp_min_basis xs) [])"
    by (rule comp_red_basis_aux_lp, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
  finally obtain q where "q \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" and "lp q = lp q1"
    by auto
  show ?thesis
  proof
    show "q \<in> set (comp_red_basis xs)" unfolding comp_red_basis_def by fact
  next
    from \<open>lp q1 adds lp p\<close> show "lp q adds lp p" unfolding \<open>lp q = lp q1\<close> .
  qed
qed
  
lemma comp_red_basis_lp:
  assumes "p \<in> set (comp_red_basis xs)"
  obtains q where "q \<in> set xs" and "q \<noteq> 0" and "lp q = lp p"
proof -
  have eq: "lp ` set ((comp_min_basis xs) @ []) = lp ` set (comp_red_basis_aux (comp_min_basis xs) [])"
    by (rule comp_red_basis_aux_lp, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
  from assms have "lp p \<in> lp ` set (comp_red_basis xs)" by simp
  also have "... = lp ` set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def ..
  also have "... = lp ` set (comp_min_basis xs)" unfolding eq[symmetric] by simp
  finally obtain q where "q \<in> set (comp_min_basis xs)" and "lp q = lp p" by auto
  show ?thesis
  proof
    show "q \<in> set xs" by (rule, fact, rule comp_min_basis_subset)
  next
    show "q \<noteq> 0" by (rule comp_min_basis_nonzero, fact)
  qed fact
qed

lemma comp_red_basis_is_red:
  shows "is_red (set (comp_red_basis xs)) f \<longleftrightarrow> is_red (set xs) f"
proof
  assume "is_red (set (comp_red_basis xs)) f"
  then obtain x t where "x \<in> set (comp_red_basis xs)" and "t \<in> keys f" and "x \<noteq> 0" and "lp x adds t"
    by (rule is_red_addsE)
  from \<open>x \<in> set (comp_red_basis xs)\<close> obtain y where yin: "y \<in> set xs" and "y \<noteq> 0" and "lp y = lp x"
    by (rule comp_red_basis_lp)
  show "is_red (set xs) f"
  proof (rule is_red_addsI)
    from \<open>lp x adds t\<close> show "lp y adds t" unfolding \<open>lp y = lp x\<close> .
  qed fact+
next
  assume "is_red (set xs) f"
  then obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lp x adds t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_red_basis xs)" and "lp y adds lp x"
    by (rule comp_red_basis_adds)
  show "is_red (set (comp_red_basis xs)) f"
  proof (rule is_red_addsI)
    from \<open>lp y adds lp x\<close> \<open>lp x adds t\<close> show "lp y adds t" by (rule adds_trans)
  next
    from yin show "y \<noteq> 0" by (rule comp_red_basis_nonzero)
  qed fact+
qed

lemma comp_red_basis_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_red_basis xs)) = pideal (set xs)"
proof -
  have a: "pideal (set (comp_red_basis xs)) \<subseteq> pideal (set xs)"
  proof
    fix f
    assume fin: "f \<in> pideal (set (comp_red_basis xs))"
    have "f \<in> pideal (set (comp_min_basis xs))"
    proof
      from fin show  "f \<in> pideal (set (comp_red_basis_aux (comp_min_basis xs) []))"
        unfolding comp_red_basis_def .
    next
      have "pideal (set (comp_red_basis_aux (comp_min_basis xs) [])) \<subseteq> pideal (set ((comp_min_basis xs) @ []))"
        by (rule comp_red_basis_aux_pideal, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
      thus "pideal (set (comp_red_basis_aux (comp_min_basis xs) [])) \<subseteq> pideal (set (comp_min_basis xs))"
        by simp
    qed
    thus "f \<in> pideal (set xs)" unfolding comp_min_basis_pideal[OF assms] .
  qed
  show ?thesis
  proof (rule, fact a, rule)
    fix f
    assume "f \<in> pideal (set xs)"
    show "f \<in> pideal (set (comp_red_basis xs))"
    proof (cases "f = 0")
      case True
      show ?thesis unfolding True by (rule zero_in_pideal)
    next
      case False
      let ?xs = "comp_red_basis xs"
      have "(red (set ?xs))\<^sup>*\<^sup>* f 0"
      proof (rule is_red_implies_0_red, fact a)
        fix q
        assume "q \<noteq> 0" and "q \<in> pideal (set xs)"
        with assms have "is_red (set xs) q" by (rule GB_implies_reducibility)
        thus "is_red (set (comp_red_basis xs)) q" unfolding comp_red_basis_is_red .
      qed fact
      thus ?thesis by (rule red_rtranclp_0_in_pideal)
    qed
  qed
qed
  
lemma comp_red_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_red_basis xs))"
  unfolding GB_alt_2
proof (intro ballI impI)
  fix f
  assume fin: "f \<in> pideal (set (comp_red_basis xs))"
  hence "f \<in> pideal (set xs)" unfolding comp_red_basis_pideal[OF assms] .
  assume "f \<noteq> 0"
  from assms \<open>f \<noteq> 0\<close> \<open>f \<in> pideal (set xs)\<close> show "is_red (set (comp_red_basis xs)) f"
    unfolding comp_red_basis_is_red GB_alt_2 by simp
qed
    
lemma comp_red_basis_is_auto_reduced:
  shows "is_auto_reduced (set (comp_red_basis xs))"
  unfolding is_auto_reduced_def remove_def
proof (intro ballI)
  fix x
  assume xin: "x \<in> set (comp_red_basis xs)"
  show "\<not> is_red (set (comp_red_basis xs) - {x}) x" unfolding comp_red_basis_def
  proof (rule comp_red_basis_aux_irred, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
    from xin show "x \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def .
  qed
qed
  
subsection \<open>Computing Reduced Gr\"obner Bases\<close>
  
text \<open>The converse of the following lemma is only true if @{term B} is minimal!\<close>
lemma monic_set_is_auto_reduced:
  assumes "is_auto_reduced B"
  shows "is_auto_reduced (monic_set B)"
  unfolding is_auto_reduced_def
proof
  fix b
  assume "b \<in> monic_set B"
  then obtain b' where b_def: "b = monic b'" and "b' \<in> B" unfolding monic_set_def ..
  from assms \<open>b' \<in> B\<close> have nred: "\<not> is_red (remove b' B) b'" by (rule is_auto_reducedD)
  show "\<not> is_red (remove b (monic_set B)) b"
  proof
    assume red: "is_red (remove b (monic_set B)) b"
    have "remove b (monic_set B) \<subseteq> monic_set (remove b' B)"
      unfolding monic_set_def remove_def b_def by auto
    with red have "is_red (monic_set (remove b' B)) b" by (rule is_red_subset)
    hence "is_red (remove b' B) b'" unfolding b_def is_red_monic_set is_red_monic .
    with nred show False ..
  qed
qed

definition comp_red_monic_basis :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::field) poly_mapping list" where
  "comp_red_monic_basis xs = map monic (comp_red_basis xs)"
  
lemma comp_red_monic_basis_set:
  shows "set (comp_red_monic_basis xs) = monic_set (set (comp_red_basis xs))"
  unfolding comp_red_monic_basis_def monic_set_def by simp

lemma comp_red_monic_basis_nonzero:
  assumes "p \<in> set (comp_red_monic_basis xs)"
  shows "p \<noteq> 0"
proof -
  from assms obtain p' where p_def: "p = monic p'" and p': "p' \<in> set (comp_red_basis xs)"
    unfolding comp_red_monic_basis_set monic_set_def ..
  from p' have "p' \<noteq> 0" by (rule comp_red_basis_nonzero)
  thus ?thesis unfolding p_def monic_0_iff .
qed
  
lemma comp_red_monic_basis_is_monic_set:
  shows "is_monic_set (set (comp_red_monic_basis xs))"
  unfolding comp_red_monic_basis_set by (rule monic_set_is_monic_set)
    
lemma comp_red_monic_basis_pideal:
  assumes "is_Groebner_basis (set xs)"
  shows "pideal (set (comp_red_monic_basis xs)) = pideal (set xs)"
  unfolding comp_red_monic_basis_set monic_set_pideal comp_red_basis_pideal[OF assms] ..
    
lemma comp_red_monic_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_red_monic_basis xs))"
  unfolding comp_red_monic_basis_set monic_set_GB using assms by (rule comp_red_basis_GB)
    
lemma comp_red_monic_basis_is_auto_reduced:
  shows "is_auto_reduced (set (comp_red_monic_basis xs))"
  unfolding comp_red_monic_basis_set by (rule monic_set_is_auto_reduced, rule comp_red_basis_is_auto_reduced)
    
lemma comp_red_monic_basis_is_reduced_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_reduced_GB (set (comp_red_monic_basis xs))"
  unfolding is_reduced_GB_def
proof (intro conjI, rule comp_red_monic_basis_GB, fact assms,
       rule comp_red_monic_basis_is_auto_reduced, rule comp_red_monic_basis_is_monic_set, intro notI)
  assume "0 \<in> set (comp_red_monic_basis xs)"
  hence "0 \<noteq> (0::('a, 'b) poly_mapping)" by (rule comp_red_monic_basis_nonzero)
  thus False by simp
qed
  
lemma comp_red_monic_basis_of_gb_is_reduced_GB:
  shows "is_reduced_GB (set (comp_red_monic_basis (gb xs)))"
  by (rule comp_red_monic_basis_is_reduced_GB, rule gb_isGB)
    
lemma comp_red_monic_basis_of_gb_pideal:
  shows "pideal (set (comp_red_monic_basis (gb xs))) = pideal (set xs)"
proof -
  have "pideal (set (comp_red_monic_basis (gb xs))) = pideal (set (gb xs))"
    by (rule comp_red_monic_basis_pideal, rule gb_isGB)
  also have "... = pideal (set xs)" by (rule gb_pideal)
  finally show ?thesis .
qed
  
theorem exists_unique_reduced_GB:
  assumes "finite B"
  shows "\<exists>!G. is_reduced_GB G \<and> pideal G = pideal B"
proof -
  from finite_list[OF assms] obtain xs where set: "set xs = B" ..
  let ?G = "set (comp_red_monic_basis (gb xs))"
  have rgb: "is_reduced_GB ?G" by (rule comp_red_monic_basis_of_gb_is_reduced_GB)
  have eq: "pideal ?G = pideal B" unfolding set[symmetric] by (rule comp_red_monic_basis_of_gb_pideal)
  show ?thesis
  proof (rule, intro conjI)
    fix G'
    assume "is_reduced_GB G' \<and> pideal G' = pideal B"
    hence "is_reduced_GB G'" and "pideal G' = pideal B" by simp_all
    show "G' = ?G" by (rule is_reduced_GB_unique, fact, fact, unfold eq, fact)
  qed (fact rgb, fact eq)
qed
  
definition reduced_GB :: "('a, 'b) poly_mapping set \<Rightarrow> ('a, 'b::field) poly_mapping set"
  where "reduced_GB B = (THE G. is_reduced_GB G \<and> pideal G = pideal B)"

definition rgb :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::field) poly_mapping list"
  where "rgb bs = comp_red_monic_basis (gb bs)"

lemma reduced_GB_is_reduced_GB:
  assumes "finite B"
  shows "is_reduced_GB (reduced_GB B)"
  unfolding reduced_GB_def
  by (rule the1I2, rule exists_unique_reduced_GB, fact, auto)
    
lemma reduced_GB_is_GB:
  assumes "finite B"
  shows "is_Groebner_basis (reduced_GB B)"
proof -
  from assms have "is_reduced_GB (reduced_GB B)" by (rule reduced_GB_is_reduced_GB)
  thus ?thesis unfolding is_reduced_GB_def ..
qed
    
lemma reduced_GB_is_auto_reduced:
  assumes "finite B"
  shows "is_auto_reduced (reduced_GB B)"
proof -
  from assms have "is_reduced_GB (reduced_GB B)" by (rule reduced_GB_is_reduced_GB)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed
    
lemma reduced_GB_is_monic_set:
  assumes "finite B"
  shows "is_monic_set (reduced_GB B)"
proof -
  from assms have "is_reduced_GB (reduced_GB B)" by (rule reduced_GB_is_reduced_GB)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed
  
lemma reduced_GB_nonzero:
  assumes "finite B"
  shows "0 \<notin> reduced_GB B"
proof -
  from assms have "is_reduced_GB (reduced_GB B)" by (rule reduced_GB_is_reduced_GB)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed

lemma reduced_GB_pideal:
  assumes "finite B"
  shows "pideal (reduced_GB B) = pideal B"
  unfolding reduced_GB_def
  by (rule the1I2, rule exists_unique_reduced_GB, fact, auto)

lemma reduced_GB_unique:
  assumes "finite B" and "is_reduced_GB G" and "pideal G = pideal B"
  shows "reduced_GB B = G"
  unfolding reduced_GB_def
  by (rule the1_equality, rule exists_unique_reduced_GB, fact, rule conjI, fact+)

lemma reduced_GB_comp:
  shows "reduced_GB (set xs) = set (rgb xs)"
  by (rule reduced_GB_unique, simp_all add: rgb_def, rule comp_red_monic_basis_of_gb_is_reduced_GB,
      rule comp_red_monic_basis_of_gb_pideal)

section \<open>Properties of the Reduced Gr\"obner Basis of an Ideal\<close>

lemma pideal_eq_UNIV_iff_contains_one:
  "pideal F = UNIV \<longleftrightarrow> (1::('a, 'b::semiring_1) poly_mapping) \<in> pideal F"
proof
  assume *: "1 \<in> pideal F"
  show "pideal F = UNIV"
  proof
    show "UNIV \<subseteq> pideal F"
    proof
      fix p
      from * have "p * 1 \<in> pideal F" by (rule pideal_closed_times)
      thus "p \<in> pideal F" by simp
    qed
  qed simp
qed simp

lemma not_is_red_empty: "\<not> is_red {} f"
  by (simp add: is_red_adds_iff)

lemma is_Groebner_basis_empty: "is_Groebner_basis {}"
  by (rule Buchberger_criterion, simp)

lemma is_Groebner_basis_singleton: "is_Groebner_basis {f}"
  by (rule Buchberger_criterion, simp add: spoly_same)

lemma pideal_eq_UNIV_iff_reduced_GB_eq_one:
  assumes "finite F"
  shows "pideal F = UNIV \<longleftrightarrow> reduced_GB F = {1}"
proof
  assume "pideal F = UNIV"
  from assms show "reduced_GB F = {1}"
  proof (rule reduced_GB_unique)
    show "is_reduced_GB {1}" unfolding is_reduced_GB_def
    proof (intro conjI, fact is_Groebner_basis_singleton)
      show "is_auto_reduced {1}" unfolding is_auto_reduced_def
        by (rule ballI, simp add: remove_def not_is_red_empty)
    next
      show "is_monic_set {1}"
        by (rule is_monic_setI, simp del: single_one add: single_one[symmetric] lc_monomial)
    qed simp
  next
    show "pideal {1} = pideal F"
      by (simp only: \<open>pideal F = UNIV\<close> pideal_eq_UNIV_iff_contains_one, rule generator_in_pideal, simp)
  qed
next
  assume "reduced_GB F = {1}"
  hence "1 \<in> reduced_GB F" by simp
  hence "1 \<in> pideal (reduced_GB F)" by (rule generator_in_pideal)
  also from assms have "... = pideal F" by (rule reduced_GB_pideal)
  finally show "pideal F = UNIV" by (simp only: pideal_eq_UNIV_iff_contains_one)
qed
                                                                          
end (* od_powerprod *)
  
end (* theory *)