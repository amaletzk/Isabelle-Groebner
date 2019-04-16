(* Author: Alexander Maletzky *)

section \<open>Field-Theoretic Version of Hilbert's Nullstellensatz\<close>

theory Nullstellensatz_Field
  imports Nullstellensatz "HOL-Types_To_Sets.Types_To_Sets"
begin

text \<open>Building upon the geometric version of Hilbert's Nullstellensatz in
  @{theory Draft.Nullstellensatz}, we prove its field-theoretic version here. To that end we employ
  the `types to sets' methodology.\<close>

subsection \<open>Function \<open>map_indets\<close>\<close>

definition map_indets where "map_indets f = poly_subst (\<lambda>x. monomial 1 (Poly_Mapping.single (f x) 1))"

lemma
  shows map_indets_zero [simp]: "map_indets f 0 = 0"
    and map_indets_one [simp]: "map_indets f 1 = 1"
    and map_indets_uminus [simp]: "map_indets f (- r) = - map_indets f (r::_ \<Rightarrow>\<^sub>0 _::comm_ring_1)"
    and map_indets_plus: "map_indets f (p + q) = map_indets f p + map_indets f q"
    and map_indets_minus: "map_indets f (r - s) = map_indets f r - map_indets f s"
    and map_indets_times: "map_indets f (p * q) = map_indets f p * map_indets f q"
    and map_indets_power [simp]: "map_indets f (p ^ m) = map_indets f p ^ m"
    and map_indets_sum: "map_indets f (sum g A) = (\<Sum>a\<in>A. map_indets f (g a))"
    and map_indets_prod: "map_indets f (prod g A) = (\<Prod>a\<in>A. map_indets f (g a))"
  by (simp_all add: map_indets_def poly_subst_uminus poly_subst_plus poly_subst_minus poly_subst_times
      poly_subst_power poly_subst_sum poly_subst_prod)

lemma map_indets_monomial:
  "map_indets f (monomial c t) = monomial c (\<Sum>x\<in>keys t. Poly_Mapping.single (f x) (lookup t x))"
  by (simp add: map_indets_def poly_subst_monomial subst_pp_def monomial_power_map_scale
      punit.monom_mult_monomial flip: punit.monomial_prod_sum)

lemma map_indets_id: "(\<And>x. x \<in> indets p \<Longrightarrow> f x = x) \<Longrightarrow> map_indets f p = p"
  by (simp add: map_indets_def poly_subst_id)

lemma map_indets_map_indets: "map_indets f (map_indets g p) = map_indets (f \<circ> g) p"
  by (simp add: map_indets_def poly_subst_poly_subst poly_subst_monomial subst_pp_single)

lemma map_indets_cong: "p = q \<Longrightarrow> (\<And>x. x \<in> indets q \<Longrightarrow> f x = g x) \<Longrightarrow> map_indets f p = map_indets g q"
  unfolding map_indets_def by (simp cong: poly_subst_cong)

lemma poly_subst_map_indets: "poly_subst f (map_indets g p) = poly_subst (f \<circ> g) p"
  by (simp add: map_indets_def poly_subst_poly_subst poly_subst_monomial subst_pp_single comp_def)

lemma poly_eval_map_indets: "poly_eval a (map_indets g p) = poly_eval (a \<circ> g) p"
  by (simp add: poly_eval_def poly_subst_map_indets comp_def)
      (simp add: poly_subst_def lookup_sum lookup_times_zero subst_pp_def lookup_prod_zero
          lookup_power_zero flip: times_monomial_left)

lemma map_indets_in_Polys: "map_indets f (p::_ \<Rightarrow>\<^sub>0 'a::comm_semiring_1) \<in> P[f ` indets p]"
proof (intro PolysI_alt subsetI)
  fix x
  assume "x \<in> indets (map_indets f p)"
  then obtain y where "y \<in> indets p" and "x \<in> indets (monomial (1::'a) (Poly_Mapping.single (f y) 1))"
    unfolding map_indets_def by (rule in_indets_poly_substE)
  from this(2) have x: "x = f y" by (simp add: indets_monomial)
  from \<open>y \<in> indets p\<close> show "x \<in> f ` indets p" unfolding x by (rule imageI)
qed

lemma image_map_indets_Polys: "map_indets f ` P[X] = (P[f ` X]::(_ \<Rightarrow>\<^sub>0 'a::comm_semiring_1) set)"
proof (intro set_eqI iffI)
  fix p :: "_ \<Rightarrow>\<^sub>0 'a"
  assume "p \<in> map_indets f ` P[X]"
  then obtain q where "q \<in> P[X]" and "p = map_indets f q" ..
  note this(2)
  also have "map_indets f q \<in> P[f ` indets q]" by (fact map_indets_in_Polys)
  also from \<open>q \<in> _\<close> have "\<dots> \<subseteq> P[f ` X]" by (auto intro!: Polys_mono imageI dest: PolysD)
  finally show "p \<in> P[f ` X]" .
next
  fix p :: "_ \<Rightarrow>\<^sub>0 'a"
  assume "p \<in> P[f ` X]"
  define g where "g = (\<lambda>y. SOME x. x \<in> X \<and> f x = y)"
  have "g y \<in> X \<and> f (g y) = y" if "y \<in> indets p" for y
  proof -
    note that
    also from \<open>p \<in> _\<close> have "indets p \<subseteq> f ` X" by (rule PolysD)
    finally obtain x where "x \<in> X" and "y = f x" ..
    hence "x \<in> X \<and> f x = y" by simp
    thus ?thesis unfolding g_def by (rule someI)
  qed
  hence 1: "g y \<in> X" and 2: "f (g y) = y" if "y \<in> indets p" for y using that by simp_all
  show "p \<in> map_indets f ` P[X]"
  proof
    show "p = map_indets f (map_indets g p)"
      by (rule sym) (simp add: map_indets_map_indets map_indets_id 2)
  next
    have "map_indets g p \<in> P[g ` indets p]" by (fact map_indets_in_Polys)
    also have "\<dots> \<subseteq> P[X]" by (auto intro!: Polys_mono 1)
    finally show "map_indets g p \<in> P[X]" .
  qed
qed

corollary range_map_indets: "range (map_indets f) = P[range f]"
proof -
  have "range (map_indets f) = map_indets f ` P[UNIV]" by simp
  also have "\<dots> = P[range f]" by (simp only: image_map_indets_Polys)
  finally show ?thesis .
qed

lemma map_indets_inverseE:
  assumes "inj (f::'x \<Rightarrow> 'y)"
  obtains g where "g \<circ> f = id" and "map_indets g \<circ> map_indets f = (id::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
proof -
  from assms obtain g where eq: "g \<circ> f = id" unfolding inj_alt ..
  have "map_indets g \<circ> map_indets f = (id::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
  proof
    fix p :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"
    show "(map_indets g \<circ> map_indets f) p = id p"
      by (simp add: map_indets_map_indets eq map_indets_id)
  qed
  with eq show ?thesis ..
qed

lemma inj_map_indetsI:
  assumes "inj (f::'x \<Rightarrow> 'y)"
  shows "inj ((map_indets f)::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
proof -
  from assms obtain g where "map_indets g \<circ> map_indets f = (id::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
    by (rule map_indets_inverseE)
  thus ?thesis by (auto simp: inj_alt)
qed

lemma image_map_indets_ideal:
  assumes "inj f"
  shows "map_indets f ` ideal F = ideal (map_indets f ` (F::(_ \<Rightarrow>\<^sub>0 'a::comm_ring_1) set)) \<inter> P[range f]"
proof
  from map_indets_plus map_indets_times have "map_indets f ` ideal F \<subseteq> ideal (map_indets f ` F)"
    by (rule image_ideal_subset)
  moreover from subset_UNIV have "map_indets f ` ideal F \<subseteq> range (map_indets f)" by (rule image_mono)
  ultimately show "map_indets f ` ideal F \<subseteq> ideal (map_indets f ` F) \<inter> P[range f]"
    unfolding range_map_indets by blast
next
  show "ideal (map_indets f ` F) \<inter> P[range f] \<subseteq> map_indets f ` ideal F"
  proof
    fix p
    assume "p \<in> ideal (map_indets f ` F) \<inter> P[range f]"
    hence "p \<in> ideal (map_indets f ` F)" and "p \<in> range (map_indets f)"
      by (simp_all add: range_map_indets)
    from this(1) obtain F0 q where "F0 \<subseteq> map_indets f ` F" and p: "p = (\<Sum>f'\<in>F0. q f' * f')"
      by (rule ideal.spanE)
    from this(1) obtain F' where "F' \<subseteq> F" and F0: "F0 = map_indets f ` F'" by (rule subset_imageE)
    from assms obtain g where "map_indets g \<circ> map_indets f = (id::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a)"
      by (rule map_indets_inverseE)
    hence eq: "map_indets g (map_indets f p') = p'" for p'::"_ \<Rightarrow>\<^sub>0 'a"
      by (simp add: pointfree_idE)
    from assms have "inj (map_indets f)" by (rule inj_map_indetsI)
    from this subset_UNIV have "inj_on (map_indets f) F'" by (rule inj_on_subset)
    from \<open>p \<in> range _\<close> obtain p' where "p = map_indets f p'" ..
    hence "p = map_indets f (map_indets g p)" by (simp add: eq)
    also from \<open>inj_on _ F'\<close> have "\<dots> = map_indets f (\<Sum>f'\<in>F'. map_indets g (q (map_indets f f')) * f')"
      by (simp add: p F0 sum.reindex map_indets_sum map_indets_times eq)
    finally have "p = map_indets f (\<Sum>f'\<in>F'. map_indets g (q (map_indets f f')) * f')" .
    moreover have "(\<Sum>f'\<in>F'. map_indets g (q (map_indets f f')) * f') \<in> ideal F"
    proof
      show "(\<Sum>f'\<in>F'. map_indets g (q (map_indets f f')) * f') \<in> ideal F'" by (rule ideal.sum_in_spanI)
    next
      from \<open>F' \<subseteq> F\<close> show "ideal F' \<subseteq> ideal F" by (rule ideal.span_mono)
    qed
    ultimately show "p \<in> map_indets f ` ideal F" by (rule image_eqI)
  qed
qed

(*
lemma image_map_indets_ideal_of_variety_of:
  assumes "inj f"
  shows "map_indets f ` \<I> (\<V> F) = \<I> (\<V> (map_indets f ` (F::(_ \<Rightarrow>\<^sub>0 'a::comm_ring_1) set))) \<inter> P[range f]"
proof
  show "map_indets f ` \<I> (\<V> F) \<subseteq> \<I> (\<V> (map_indets f ` F)) \<inter> P[range f]"
    by (auto simp: ideal_of_def variety_of_def poly_eval_map_indets simp flip: range_map_indets)
next
  show "\<I> (\<V> (map_indets f ` F)) \<inter> P[range f] \<subseteq> map_indets f ` \<I> (\<V> F)"
  proof
    fix p
    assume "p \<in> \<I> (\<V> (map_indets f ` F)) \<inter> P[range f]"
    hence "p \<in> \<I> (\<V> (map_indets f ` F))" and "p \<in> range (map_indets f)"
      by (simp_all add: range_map_indets)
    from assms obtain g where "g \<circ> f = id" and "map_indets g \<circ> map_indets f = (id::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a)"
      by (rule map_indets_inverseE)
    hence eq: "map_indets g (map_indets f p') = p'" for p'::"_ \<Rightarrow>\<^sub>0 'a"
      by (simp add: pointfree_idE)
    from \<open>p \<in> range _\<close> obtain p' where "p = map_indets f p'" ..
    hence "p = map_indets f (map_indets g p)" by (simp add: eq)
    moreover have "map_indets g p \<in> \<I> (\<V> F)"
    proof (rule ideal_ofI)
      fix a
      assume "a \<in> \<V> F"
      have "a \<circ> g \<in> \<V> (map_indets f ` F)"
      proof (rule variety_ofI)
        fix q
        assume "q \<in> map_indets f ` F"
        then obtain r where "r \<in> F" and q: "q = map_indets f r" ..
        from \<open>a \<in> _\<close> this(1) have "poly_eval a r = 0" by (rule variety_ofD)
        thus "poly_eval (a \<circ> g) q = 0" by (simp add: q poly_eval_map_indets comp_assoc \<open>g \<circ> f = id\<close>)
      qed
      with \<open>p \<in> \<I> _\<close> have "poly_eval (a \<circ> g) p = 0" by (rule ideal_ofD)
      thus "poly_eval a (map_indets g p) = 0" by (simp add: poly_eval_map_indets)
    qed
    ultimately show "p \<in> map_indets f ` \<I> (\<V> F)" by (rule image_eqI)
  qed
qed

lemma image_map_indets_radical:
  assumes "inj f"
  shows "map_indets f ` \<surd>F = \<surd>(map_indets f ` (F::(_ \<Rightarrow>\<^sub>0 'a::comm_ring_1) set)) \<inter> P[range f]"
proof
  show "map_indets f ` \<surd>F \<subseteq> \<surd>(map_indets f ` F) \<inter> P[range f]"
    by (auto simp: radical_def simp flip: map_indets_power range_map_indets intro!: imageI)
next
  show "\<surd>(map_indets f ` F) \<inter> P[range f] \<subseteq> map_indets f ` \<surd>F"
  proof
    fix p
    assume "p \<in> \<surd>(map_indets f ` F) \<inter> P[range f]"
    hence "p \<in> \<surd>(map_indets f ` F)" and "p \<in> range (map_indets f)"
      by (simp_all add: range_map_indets)
    from this(1) obtain m where "p ^ m \<in> map_indets f ` F" by (rule radicalE)
    then obtain q where "q \<in> F" and p_m: "p ^ m = map_indets f q" ..
    from assms obtain g where "g \<circ> f = id" and "map_indets g \<circ> map_indets f = (id::_ \<Rightarrow> _ \<Rightarrow>\<^sub>0 'a)"
      by (rule map_indets_inverseE)
    hence eq: "map_indets g (map_indets f p') = p'" for p'::"_ \<Rightarrow>\<^sub>0 'a"
      by (simp add: pointfree_idE)
    from p_m have "map_indets g (p ^ m) = map_indets g (map_indets f q)" by (rule arg_cong)
    hence "(map_indets g p) ^ m = q" by (simp add: eq)
    from \<open>p \<in> range _\<close> obtain p' where "p = map_indets f p'" ..
    hence "p = map_indets f (map_indets g p)" by (simp add: eq)
    moreover have "map_indets g p \<in> \<surd>F"
    proof (rule radicalI)
      from \<open>q \<in> F\<close> show "map_indets g p ^ m \<in> F" by (simp add: p_m eq flip: map_indets_power)
    qed
    ultimately show "p \<in> map_indets f ` \<surd>F" by (rule image_eqI)
  qed
qed
*)

subsection \<open>Getting Rid of Sort Constraints in Geometric Version\<close>

text \<open>We can use the `types to sets' approach to get rid of the @{class countable} and @{class linorder}
  sort constraints on the type of indeterminates in the geometric version of the Nullstellensatz.\<close>

lemmas weak_Nullstellensatz_internalized = weak_Nullstellensatz[unoverload_type 'x]
lemmas strong_Nullstellensatz_internalized = strong_Nullstellensatz[unoverload_type 'x]
thm radical_ideal_iff[unoverload_type 'x]

lemma weak_Nullstellensatz':
  assumes "finite X" and "F \<subseteq> P[X]" and "\<V> F = ({}::('x \<Rightarrow> 'a::alg_closed_field) set)"
  shows "ideal F = UNIV"
proof -
  define Y where "Y = insert undefined X"
  from assms(1) have fin_Y: "finite Y" by (simp add: Y_def)
  have "X \<subseteq> Y" by (auto simp: Y_def)
  hence "P[X] \<subseteq> P[Y]" by (rule Polys_mono)
  with assms(2) have F_sub: "F \<subseteq> P[Y]" by (rule subset_trans)
  {
    text \<open>We define the type @{typ 'y} to be isomorphic to @{term Y}.\<close>
    assume "\<exists>(Rep :: 'y \<Rightarrow> 'x) Abs. type_definition Rep Abs Y"
    then obtain rep :: "'y \<Rightarrow> 'x" and abs :: "'x \<Rightarrow> 'y" where t: "type_definition rep abs Y"
      by blast
    then interpret y: type_definition rep abs Y .

    from well_ordering obtain le_y'::"('y \<times> 'y) set" where fld: "Field le_y' = UNIV"
      and wo: "Well_order le_y'" by meson
    define le_y where "le_y = (\<lambda>a b::'y. (a, b) \<in> le_y')"

    have 1: "map_indets (rep \<circ> abs) ` A = A" if "A \<subseteq> P[Y]" for A::"(_ \<Rightarrow>\<^sub>0 'a) set"
    proof
      from that show "map_indets (rep \<circ> abs) ` A \<subseteq> A"
        by (smt PolysD(2) comp_apply image_subset_iff map_indets_id subsetD y.Abs_inverse)
    next
      from that show "A \<subseteq> map_indets (rep \<circ> abs) ` A"
        by (smt PolysD(2) comp_apply image_eqI map_indets_id subsetD subsetI y.Abs_inverse)
    qed
    have 2: "inj rep" by (meson inj_onI y.Rep_inject)
    hence 3: "inj (map_indets rep)" by (rule inj_map_indetsI)
    from fin_Y have 4: "finite (abs ` Y)" by (rule finite_imageI)
    from wo have le_y_refl: "le_y x x" for x
      by (simp add: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                    preorder_on_def refl_on_def fld)
    have le_y_total: "le_y x y \<or> le_y y x" for x y
    proof (cases "x = y")
      case True
      thus ?thesis by (simp add: le_y_refl)
    next
      case False
      with wo show ?thesis
        by (simp add: le_y_def well_order_on_def linear_order_on_def total_on_def
                      Relation.total_on_def fld)
    qed

    from 4 finite_imp_inj_to_nat_seg y.Abs_image have "class.countable TYPE('y)"
      by unfold_locales fastforce
    moreover have "class.linorder le_y (strict le_y)"
      apply standard
      subgoal by (fact refl)
      subgoal by (fact le_y_refl)
      subgoal using wo
        by (auto simp: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                      preorder_on_def fld dest: transD)
      subgoal using wo
        by (simp add: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                      preorder_on_def antisym_def fld)
      subgoal by (fact le_y_total)
      done
    moreover note 4
    moreover have "map_indets abs ` F \<subseteq> P[abs ` Y]"
    proof (rule subset_trans)
      from F_sub show "map_indets abs ` F \<subseteq> map_indets abs ` P[Y]" by (rule image_mono)
    qed (simp only: image_map_indets_Polys)
    moreover have "\<V> (map_indets abs ` F) = {}"
    proof (intro set_eqI iffI)
      fix a
      assume "a \<in> \<V> (map_indets abs ` F)"
      also have "\<dots> = (\<lambda>b. b \<circ> abs) -` \<V> F"
        by (auto simp: variety_of_def poly_eval_map_indets)
      finally show "a \<in> {}" by (simp add: assms(3))
    qed simp
    ultimately have "ideal (map_indets abs ` F) = UNIV"
      by (rule weak_Nullstellensatz_internalized[where 'x='y, untransferred, simplified])
    hence "map_indets rep ` ideal (map_indets abs ` F) = P[range rep]"
      by (simp add: range_map_indets)
    with 2 F_sub have "ideal F \<inter> P[Y] = P[Y]"
      by (simp add: image_map_indets_ideal image_image map_indets_map_indets 1 y.Rep_range)
    with one_in_Polys have ?thesis by (auto simp: ideal_eq_UNIV_iff_contains_one)
  }
  note rl = this[cancel_type_definition]
  have "Y \<noteq> {}" by (simp add: Y_def)
  thus ?thesis by (rule rl)
qed

(*
lemma strong_Nullstellensatz':
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "\<I> (\<V> F) = \<surd>ideal (F::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
proof -
  define Y where "Y = insert undefined X"
  from assms(1) have fin_Y: "finite Y" by (simp add: Y_def)
  have "X \<subseteq> Y" by (auto simp: Y_def)
  hence "P[X] \<subseteq> P[Y]" by (rule Polys_mono)
  with assms(2) have F_sub: "F \<subseteq> P[Y]" by (rule subset_trans)
  {
    text \<open>We define the type @{typ 'y} to be isomorphic to @{term Y}.\<close>
    assume "\<exists>(Rep :: 'y \<Rightarrow> 'x) Abs. type_definition Rep Abs Y"
    then obtain rep :: "'y \<Rightarrow> 'x" and abs :: "'x \<Rightarrow> 'y" where t: "type_definition rep abs Y"
      by blast
    then interpret y: type_definition rep abs Y .

    from well_ordering obtain le_y'::"('y \<times> 'y) set" where "Well_order le_y'" by auto
    define le_y where "le_y = (\<lambda>a b::'y. (a, b) \<in> le_y')"

    have 1: "map_indets (rep \<circ> abs) ` A = A" if "A \<subseteq> P[Y]" for A::"(_ \<Rightarrow>\<^sub>0 'a) set"
    proof
      from that show "map_indets (rep \<circ> abs) ` A \<subseteq> A"
        by (smt PolysD(2) comp_apply image_subset_iff map_indets_id subsetD y.Abs_inverse)
    next
      from that show "A \<subseteq> map_indets (rep \<circ> abs) ` A"
        by (smt PolysD(2) comp_apply image_eqI map_indets_id subsetD subsetI y.Abs_inverse)
    qed
    have 2: "inj rep" by (meson inj_onI y.Rep_inject)
    hence 3: "inj (map_indets rep)" by (rule inj_map_indetsI)
    from fin_Y have 4: "finite (abs ` Y)" by (rule finite_imageI)

    have "class.countable TYPE('y)"
    proof
      from 4 show "\<exists>to_nat::'y \<Rightarrow> nat. inj to_nat" sorry
    qed
    moreover have "class.linorder le_y (strict le_y)" sorry
    moreover note 4
    moreover have "map_indets abs ` F \<subseteq> P[abs ` Y]" sorry
    ultimately have eq: "\<I> (\<V> (map_indets abs ` F)) = \<surd>ideal (map_indets abs ` F)"
      by (rule strong_Nullstellensatz_internalized[where 'x='y, untransferred, simplified])

    from 2 F_sub have "\<I> (\<V> F) \<inter> P[Y] = map_indets rep ` \<I> (\<V> (map_indets abs ` F))"
      by (simp add: image_map_indets_ideal_of_variety_of image_image map_indets_map_indets 1 y.Rep_range)
    also from 2 F_sub have "\<dots> = \<surd>(ideal F \<inter> P[Y]) \<inter> P[Y]"
      by (simp add: eq image_map_indets_radical image_map_indets_ideal image_image map_indets_map_indets
              1 y.Rep_range)
    finally have "\<I> (\<V> F) \<inter> P[Y] \<subseteq> \<surd>ideal F"
      using radical_mono[where F="ideal F \<inter> P[Y]" and G="ideal F"] by auto
    have "\<I> (\<V> F) \<subseteq> \<surd>ideal F" sorry
    moreover have "\<surd>ideal F \<subseteq> \<I> (\<V> F)"
      by (metis subsetI ideal_ofI variety_ofD variety_of_radical_ideal)
    ultimately have ?thesis ..
  }
  note rl = this[cancel_type_definition]
  have "Y \<noteq> {}" by (simp add: Y_def)
  thus ?thesis by (rule rl)
qed
*)

subsection \<open>Field-Theoretic Version of the Nullstellensatz\<close>

text \<open>Due to the possibility of infinite indeterminate-types, we have to explicitly add the set of
  indeterminates under consideration to the definition of maximal ideals.\<close>

definition generates_max_ideal :: "'x set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) set \<Rightarrow> bool"
  where "generates_max_ideal X F \<longleftrightarrow> (ideal F \<noteq> UNIV \<and>
                                      (\<forall>F'. F' \<subseteq> P[X] \<longrightarrow> ideal F \<subset> ideal F' \<longrightarrow> ideal F' = UNIV))"

lemma generates_max_idealI:
  assumes "ideal F \<noteq> UNIV" and "\<And>F'. F' \<subseteq> P[X] \<Longrightarrow> ideal F \<subset> ideal F' \<Longrightarrow> ideal F' = UNIV"
  shows "generates_max_ideal X F"
  using assms by (simp add: generates_max_ideal_def)

lemma generates_max_idealI_alt:
  assumes "ideal F \<noteq> UNIV" and "\<And>p. p \<in> P[X] \<Longrightarrow> p \<notin> ideal F \<Longrightarrow> 1 \<in> ideal (insert p F)"
  shows "generates_max_ideal X F"
  using assms(1)
proof (rule generates_max_idealI)
  fix F'
  assume "F' \<subseteq> P[X]" and sub: "ideal F \<subset> ideal F'"
  from this(2) ideal.span_subset_spanI have "\<not> F' \<subseteq> ideal F" by blast
  then obtain p where "p \<in> F'" and "p \<notin> ideal F" by blast
  from this(1) \<open>F' \<subseteq> P[X]\<close> have "p \<in> P[X]" ..
  hence "1 \<in> ideal (insert p F)" using \<open>p \<notin> _\<close> by (rule assms(2))
  also have "\<dots> \<subseteq> ideal (F' \<union> F)" by (rule ideal.span_mono) (simp add: \<open>p \<in> F'\<close>)
  also have "\<dots> = ideal (ideal F' \<union> ideal F)" by (simp add: ideal.span_Un ideal.span_span)
  also from sub have "ideal F' \<union> ideal F = ideal F'" by blast
  finally show "ideal F' = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one ideal.span_span)
qed

lemma generates_max_idealD:
  assumes "generates_max_ideal X F"
  shows "ideal F \<noteq> UNIV" and "F' \<subseteq> P[X] \<Longrightarrow> ideal F \<subset> ideal F' \<Longrightarrow> ideal F' = UNIV"
  using assms by (simp_all add: generates_max_ideal_def)

lemma generates_max_ideal_cases:
  assumes "generates_max_ideal X F" and "F' \<subseteq> P[X]" and "ideal F \<subseteq> ideal F'"
  obtains "ideal F = ideal F'" | "ideal F' = UNIV"
  using assms by (auto simp: generates_max_ideal_def)

lemma max_ideal_UNIV_radical:
  assumes "generates_max_ideal UNIV F"
  shows "\<surd>ideal F = ideal F"
proof (rule ccontr)
  assume "\<surd>ideal F \<noteq> ideal F"
  with radical_superset have "ideal F \<subset> \<surd>ideal F" by blast
  also have "\<dots> = ideal (\<surd>ideal F)" by simp
  finally have "ideal F \<subset> ideal (\<surd>ideal F)" .
  with assms _ have "ideal (\<surd>ideal F) = UNIV" by (rule generates_max_idealD) simp
  hence "\<surd>ideal F = UNIV" by simp
  hence "1 \<in> \<surd>ideal F" by simp
  hence "1 \<in> ideal F" by (auto elim: radicalE)
  hence "ideal F = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one)
  moreover from assms have "ideal F \<noteq> UNIV" by (rule generates_max_idealD)
  ultimately show False by simp
qed

lemma max_ideal_shape_aux:
  "(\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0) ` X \<subseteq> P[X]"
  by (auto intro!: Polys_closed_minus Polys_closed_monomial PPs_closed_single zero_in_PPs)

lemma max_ideal_shapeI:
  "generates_max_ideal X ((\<lambda>x. monomial (1::'a::field) (Poly_Mapping.single x 1) - monomial (a x) 0) ` X)"
    (is "generates_max_ideal X ?F")
proof (rule generates_max_idealI_alt)
  (* Proof modeled after https://math.stackexchange.com/a/1028331. *)

  show "ideal ?F \<noteq> UNIV"
  proof
    assume "ideal ?F = UNIV"
    hence "\<V> (ideal ?F) = \<V> UNIV" by (rule arg_cong)
    hence "\<V> ?F = {}" by simp
    moreover have "a \<in> \<V> ?F" by (rule variety_ofI) (auto simp: poly_eval_minus poly_eval_monomial)
    ultimately show False by simp
  qed
next
  fix p
  assume "p \<in> P[X]" and "p \<notin> ideal ?F"
  have "p \<in> ideal (insert p ?F)" by (rule ideal.span_base) simp
  let ?f = "\<lambda>x. monomial (1::'a) (Poly_Mapping.single x 1) - monomial (a x) 0"
  let ?g = "\<lambda>x. monomial (1::'a) (Poly_Mapping.single x 1) + monomial (a x) 0"
  define q where "q = poly_subst ?g p"
  have "p = poly_subst ?f q" unfolding q_def poly_subst_poly_subst
    by (rule sym, rule poly_subst_id)
        (simp add: poly_subst_plus poly_subst_monomial subst_pp_single flip: times_monomial_left)
  also have "\<dots> = (\<Sum>t\<in>keys q. punit.monom_mult (lookup q t) 0 (subst_pp ?f t))" by (fact poly_subst_def)
  also have "\<dots> = punit.monom_mult (lookup q 0) 0 (subst_pp ?f 0) +
                  (\<Sum>t\<in>keys q - {0}. monomial (lookup q t) 0 * subst_pp ?f t)"
      (is "_ = _ + ?r")
    by (cases "0 \<in> keys q") (simp_all add: sum.remove in_keys_iff flip: times_monomial_left)
  also have "\<dots> = monomial (lookup q 0) 0 + ?r" by (simp flip: times_monomial_left)
  finally have eq: "p - ?r = monomial (lookup q 0) 0" by simp
  have "?r \<in> ideal ?F"
  proof (intro ideal.span_sum ideal.span_scale)
    fix t
    assume "t \<in> keys q - {0}"
    hence "t \<in> keys q" and "keys t \<noteq> {}" by simp_all
    from this(2) obtain x where "x \<in> keys t" by blast
    hence "x \<in> indets q" using \<open>t \<in> keys q\<close> by (rule in_indetsI)
    then obtain y where "y \<in> indets p" and "x \<in> indets (?g y)" unfolding q_def
      by (rule in_indets_poly_substE)
    from this(2) indets_plus_subset have "x \<in> indets (monomial (1::'a) (Poly_Mapping.single y 1)) \<union>
                                                indets (monomial (a y) 0)" ..
    with \<open>y \<in> indets p\<close> have "x \<in> indets p" by (simp add: indets_monomial)
    also from \<open>p \<in> P[X]\<close> have "\<dots> \<subseteq> X" by (rule PolysD)
    finally have "x \<in> X" .
    from \<open>x \<in> keys t\<close> have "lookup t x \<noteq> 0" by (simp add: in_keys_iff)
    hence eq: "b ^ lookup t x = b ^ Suc (lookup t x - 1)" for b by simp

    have "subst_pp ?f t = (\<Prod>y\<in>keys t. ?f y ^ lookup t y)" by (fact subst_pp_def)
    also from \<open>x \<in> keys t\<close> have "\<dots> = ((\<Prod>y\<in>keys t - {x}. ?f y ^ lookup t y) * ?f x ^ (lookup t x - 1)) * ?f x"
      by (simp add: prod.remove mult.commute eq)
    also from \<open>x \<in> X\<close> have "\<dots> \<in> ideal ?F" by (intro ideal.span_scale ideal.span_base imageI)
    finally show "subst_pp ?f t \<in> ideal ?F" .
  qed
  also have "\<dots> \<subseteq> ideal (insert p ?F)" by (rule ideal.span_mono) blast
  finally have "?r \<in> ideal (insert p ?F)" .
  with \<open>p \<in> ideal _\<close> have "p - ?r \<in> ideal (insert p ?F)" by (rule ideal.span_diff)
  hence "monomial (lookup q 0) 0 \<in> ideal (insert p ?F)" by (simp only: eq)
  hence "monomial (inverse (lookup q 0)) 0 * monomial (lookup q 0) 0 \<in> ideal (insert p ?F)"
    by (rule ideal.span_scale)
  hence "monomial (inverse (lookup q 0) * lookup q 0) 0 \<in> ideal (insert p ?F)"
    by (simp add: times_monomial_monomial)
  moreover have "lookup q 0 \<noteq> 0"
  proof
    assume "lookup q 0 = 0"
    with eq \<open>?r \<in> ideal ?F\<close> have "p \<in> ideal ?F" by simp
    with \<open>p \<notin> ideal ?F\<close> show False ..
  qed
  ultimately show "1 \<in> ideal (insert p ?F)" by simp
qed

text \<open>We first prove the following lemma assuming that the type of indeterminates is finite, and then
  transfer the result to arbitrary types of indeterminates by using the `types to sets' methodology.
  This approach facilitates the proof considerably.\<close>

lemma max_ideal_shapeD_finite:
  assumes "generates_max_ideal UNIV (F::(('x::{finite,linorder} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::alg_closed_field) set)"
  obtains a where "ideal F = ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0))"
proof -
  have fin: "finite (UNIV::'x set)" by simp
  have "(\<Inter>a\<in>\<V> F. ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0))) = \<I> (\<V> F)"
    (is "?A = _")
  proof (intro set_eqI iffI ideal_ofI INT_I)
    fix p a
    assume "p \<in> ?A" and "a \<in> \<V> F"
    hence "p \<in> ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0))"
      (is "_ \<in> ideal ?B") ..
    have "a \<in> \<V> ?B"
    proof (rule variety_ofI)
      fix f
      assume "f \<in> ?B"
      then obtain x where "f = monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0" ..
      thus "poly_eval a f = 0" by (simp add: poly_eval_minus poly_eval_monomial)
    qed
    hence "a \<in> \<V> (ideal ?B)" by (simp only: variety_of_ideal)
    thus "poly_eval a p = 0" using \<open>p \<in> ideal _\<close> by (rule variety_ofD)
  next
    fix p a
    assume "p \<in> \<I> (\<V> F)" and "a \<in> \<V> F"
    hence eq: "poly_eval a p = 0" by (rule ideal_ofD)
    have "p \<in> \<surd>ideal (range (\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0))" (is "_ \<in> \<surd>ideal ?B")
      using fin max_ideal_shape_aux
    proof (rule Nullstellensatz)
      show "p \<in> \<I> (\<V> ?B)"
      proof (rule ideal_ofI)
        fix a0
        assume "a0 \<in> \<V> ?B"
        have "a0 = a"
        proof
          fix x
          have "monomial 1 (monomial 1 x) - monomial (a x) 0 \<in> ?B" by (rule rangeI)
          with \<open>a0 \<in> _\<close> have "poly_eval a0 (monomial 1 (monomial 1 x) - monomial (a x) 0) = 0"
            by (rule variety_ofD)
          thus "a0 x = a x" by (simp add: poly_eval_minus poly_eval_monomial)
        qed
        thus "poly_eval a0 p = 0" by (simp only: eq)
      qed
    qed
    also have "\<dots> = ideal (range (\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0))"
      using max_ideal_shapeI by (rule max_ideal_UNIV_radical)
    finally show "p \<in> ideal (range (\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0))" .
  qed
  also from fin have "\<dots> = \<surd>ideal F" by (rule strong_Nullstellensatz) simp
  also from assms have "\<dots> = ideal F" by (rule max_ideal_UNIV_radical)
  finally have eq: "?A = ideal F" .
  also from assms have "\<dots> \<noteq> UNIV" by (rule generates_max_idealD)
  finally obtain a where "a \<in> \<V> F"
    and "ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x (1::nat)) - monomial (a x) 0)) \<noteq> UNIV"
      (is "?B \<noteq> _") by auto
  from \<open>a \<in> \<V> F\<close> have "ideal F \<subseteq> ?B" by (auto simp flip: eq)
  with assms max_ideal_shape_aux show ?thesis
  proof (rule generates_max_ideal_cases)
    assume "ideal F = ?B"
    thus ?thesis ..
  next
    assume "?B = UNIV"
    with \<open>?B \<noteq> UNIV\<close> show ?thesis ..
  qed
qed

lemmas max_ideal_shapeD_internalized = max_ideal_shapeD_finite[unoverload_type 'x]

lemma max_ideal_shapeD:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "generates_max_ideal X (F::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::alg_closed_field) set)"
  obtains a where "ideal F = ideal ((\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0) ` X)"
proof (cases "X = {}")
  case True
  from assms(3) have "ideal F \<noteq> UNIV" by (rule generates_max_idealD)
  hence "1 \<notin> ideal F" by (simp add: ideal_eq_UNIV_iff_contains_one)
  have "F \<subseteq> {0}"
  proof
    fix f
    assume "f \<in> F"
    with assms(2) have "f \<in> P[X]" ..
    then obtain c where f: "f = monomial c 0" by (auto simp: True Polys_empty)
    with \<open>f \<in> F\<close> have "monomial c 0 \<in> ideal F" by (simp only: ideal.span_base)
    hence "monomial (inverse c) 0 * monomial c 0 \<in> ideal F" by (rule ideal.span_scale)
    hence "monomial (inverse c * c) 0 \<in> ideal F" by (simp add: times_monomial_monomial)
    with \<open>1 \<notin> ideal F\<close> left_inverse have "c = 0" by fastforce
    thus "f \<in> {0}" by (simp add: f)
  qed
  hence "ideal F = ideal ((\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (undefined x) 0) ` X)"
    by (simp add: True)
  thus ?thesis ..
next
  case False
  {
    text \<open>We define the type @{typ 'y} to be isomorphic to @{term X}.\<close>
    assume "\<exists>(Rep :: 'y \<Rightarrow> 'x) Abs. type_definition Rep Abs X"
    then obtain rep :: "'y \<Rightarrow> 'x" and abs :: "'x \<Rightarrow> 'y" where t: "type_definition rep abs X"
      by blast
    then interpret y: type_definition rep abs X .

    from well_ordering obtain le_y'::"('y \<times> 'y) set" where fld: "Field le_y' = UNIV"
      and wo: "Well_order le_y'" by meson
    define le_y where "le_y = (\<lambda>a b::'y. (a, b) \<in> le_y')"

    have 1: "map_indets (rep \<circ> abs) ` A = A" if "A \<subseteq> P[X]" for A::"(_ \<Rightarrow>\<^sub>0 'a) set"
    proof
      from that show "map_indets (rep \<circ> abs) ` A \<subseteq> A"
        by (smt PolysD(2) comp_apply image_subset_iff map_indets_id subsetD y.Abs_inverse)
    next
      from that show "A \<subseteq> map_indets (rep \<circ> abs) ` A"
        by (smt PolysD(2) comp_apply image_eqI map_indets_id subsetD subsetI y.Abs_inverse)
    qed
    have 2: "inj rep" by (meson inj_onI y.Rep_inject)
    hence 3: "inj (map_indets rep)" by (rule inj_map_indetsI)
    from wo have le_y_refl: "le_y x x" for x
      by (simp add: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                    preorder_on_def refl_on_def fld)
    have le_y_total: "le_y x y \<or> le_y y x" for x y
    proof (cases "x = y")
      case True
      thus ?thesis by (simp add: le_y_refl)
    next
      case False
      with wo show ?thesis
        by (simp add: le_y_def well_order_on_def linear_order_on_def total_on_def
                      Relation.total_on_def fld)
    qed

    have "class.finite TYPE('y)"
    proof
      from assms(1) have "finite (abs ` X)" by (rule finite_imageI)
      thus "finite (UNIV::'y set)" by (simp only: y.Abs_image)
    qed
    moreover have "class.linorder le_y (strict le_y)"
      apply standard
      subgoal by (fact refl)
      subgoal by (fact le_y_refl)
      subgoal using wo
        by (auto simp: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                      preorder_on_def fld dest: transD)
      subgoal using wo
        by (simp add: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                      preorder_on_def antisym_def fld)
      subgoal by (fact le_y_total)
      done
    moreover have "generates_max_ideal UNIV (map_indets abs ` F)"
    proof (intro generates_max_idealI notI)
      assume "ideal (map_indets abs ` F) = UNIV"
      hence "1 \<in> ideal (map_indets abs ` F)" by simp
      hence "map_indets rep 1 \<in> map_indets rep ` ideal (map_indets abs ` F)" by (rule imageI)
      also from map_indets_plus map_indets_times have "\<dots> \<subseteq> ideal (map_indets rep ` map_indets abs ` F)"
        by (rule image_ideal_subset)
      also from assms(2) have "map_indets rep ` map_indets abs ` F = F"
        by (simp only: image_image map_indets_map_indets 1)
      finally have "1 \<in> ideal F" by simp
      moreover from assms(3) have "ideal F \<noteq> UNIV" by (rule generates_max_idealD)
      ultimately show False by (simp add: ideal_eq_UNIV_iff_contains_one)
    next
      fix F'
      assume "ideal (map_indets abs ` F) \<subset> ideal F'"
      with inj_on_subset have "map_indets rep ` ideal (map_indets abs ` F) \<subset> map_indets rep ` ideal F'"
        by (rule inj_on_strict_subset) (fact 3, fact subset_UNIV)
      hence sub: "ideal F \<inter> P[X] \<subset> ideal (map_indets rep ` F') \<inter> P[X]" using 2 assms(2)
        by (simp add: image_map_indets_ideal image_image map_indets_map_indets 1 y.Rep_range)
      have "ideal F \<subset> ideal (map_indets rep ` F')"
      proof (intro psubsetI notI ideal.span_subset_spanI subsetI)
        fix p
        assume "p \<in> F"
        with assms(2) ideal.span_base sub show "p \<in> ideal (map_indets rep ` F')" by blast
      next
        assume "ideal F = ideal (map_indets rep ` F')"
        with sub show False by simp
      qed
      with assms(3) _ have "ideal (map_indets rep ` F') = UNIV"
      proof (rule generates_max_idealD)
        from subset_UNIV have "map_indets rep ` F' \<subseteq> range (map_indets rep)" by (rule image_mono)
        also have "\<dots> = P[X]" by (simp only: range_map_indets y.Rep_range)
        finally show "map_indets rep ` F' \<subseteq> P[X]" .
      qed
      hence "P[range rep] = ideal (map_indets rep ` F') \<inter> P[range rep]" by simp
      also from 2 have "\<dots> = map_indets rep ` ideal F'" by (simp only: image_map_indets_ideal)
      finally have "map_indets rep ` ideal F' = range (map_indets rep)"
        by (simp only: range_map_indets)
      with 3 show "ideal F' = UNIV" by (metis inj_image_eq_iff)
    qed
    ultimately obtain a
      where *: "ideal (map_indets abs ` F) =
                 ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x (Suc 0)) - monomial (a x) 0))"
        (is "_ = ?A")
      by (rule max_ideal_shapeD_internalized[where 'x='y, untransferred, simplified])
    hence "map_indets rep ` ideal (map_indets abs ` F) = map_indets rep ` ?A" by simp
    with 2 assms(2) have "ideal F \<inter> P[X] =
           ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single (rep x) 1) - monomial (a x) 0)) \<inter> P[X]"
        (is "_ = ideal ?B \<inter> _")
      by (simp add: image_map_indets_ideal y.Rep_range image_image map_indets_map_indets
              map_indets_minus map_indets_monomial 1)
    also have "?B = (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial ((a \<circ> abs) x) 0) ` X"
        (is "_ = ?C")
    proof
      show "?B \<subseteq> ?C" by (smt comp_apply image_iff image_subset_iff y.Abs_image y.Abs_inverse)
    next
      from y.Rep_inverse y.Rep_range show "?C \<subseteq> ?B" by auto
    qed
    finally have eq: "ideal F \<inter> P[X] = ideal ?C \<inter> P[X]" .
    have "ideal F = ideal ?C"
    proof (intro subset_antisym ideal.span_subset_spanI subsetI)
      fix p
      assume "p \<in> F"
      with assms(2) ideal.span_base have "p \<in> ideal F \<inter> P[X]" by blast
      thus "p \<in> ideal ?C" by (simp add: eq)
    next
      fix p
      assume "p \<in> ?C"
      then obtain x where "x \<in> X" and "p = monomial 1 (monomial 1 x) - monomial ((a \<circ> abs) x) 0" ..
      note this(2)
      also from \<open>x \<in> X\<close> have "\<dots> \<in> P[X]"
        by (intro Polys_closed_minus Polys_closed_monomial PPs_closed_single zero_in_PPs)
      finally have "p \<in> P[X]" .
      with \<open>p \<in> ?C\<close> have "p \<in> ideal ?C \<inter> P[X]" by (simp add: ideal.span_base)
      also have "\<dots> = ideal F \<inter> P[X]" by (simp only: eq)
      finally show "p \<in> ideal F" by simp
    qed
    hence ?thesis ..
  }
  note rl = this[cancel_type_definition]
  from False show ?thesis by (rule rl)
qed

theorem Nullstellensatz_field:
  assumes "finite X" and "F \<subseteq> P[X]" and "generates_max_ideal X (F::(_ \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
    and "x \<in> X"
  shows "{0} \<subset> ideal F \<inter> P[{x}]"
  unfolding subset_not_subset_eq
proof (intro conjI notI)
  show "{0} \<subseteq> ideal F \<inter> P[{x}]" by (auto intro: ideal.span_zero zero_in_Polys)
next
  from assms(1, 2, 3) obtain a
    where eq: "ideal F = ideal ((\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0) ` X)"
    by (rule max_ideal_shapeD)
  let ?p = "\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0"
  from assms(4) have "?p x \<in> ?p ` X" by (rule imageI)
  also have "\<dots> \<subseteq> ideal F" unfolding eq by (rule ideal.span_superset)
  finally have "?p x \<in> ideal F" .
  moreover have "?p x \<in> P[{x}]"
    by (auto intro!: Polys_closed_minus Polys_closed_monomial PPs_closed_single zero_in_PPs)
  ultimately have "?p x \<in> ideal F \<inter> P[{x}]" ..
  also assume "\<dots> \<subseteq> {0}"
  finally show False
    by (metis diff_eq_diff_eq diff_self monomial_0D monomial_inj one_neq_zero singletonD)
qed

end (* theory *)
