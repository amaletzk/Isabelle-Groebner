theory Macaulay_Groebner                            
  imports Power_Products_Fun Reduced_GB "Gauss_Jordan.Gauss_Jordan_IArrays"
begin

(* TODO: Pull "fun_powerprod" and "finite_nat" out, since they are also defined in "Binom_Mult.thy"
  and "Membership_Bound_Binomials.thy", respectively.
  Maybe it's even possible to replace "finite_nat" by some type class also used in "Gauss_Jordan". *)
locale fun_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"('n \<Rightarrow> nat) \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)

class finite_nat = finite + linorder + zero +
  assumes zero_min: "0 \<le> n"

subsection \<open>More about Matrices\<close>

lemma vec_lambda_plus: "(\<chi> j. f j + g j) = (\<chi> j. f j) + (\<chi> j. g j)"
  by (metis (no_types) UNIV_I plus_vec_def vec_lambda_inverse)

lemma vec_lambda_sum_commute: "(\<chi> j. sum (f j) A) = (\<Sum>a\<in>A. \<chi> j. f j a)"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty
    show ?case by (simp add: zero_vec_def)
  next
    case step: (insert a A)
    show ?case by (simp only: sum.insert[OF step(1) step(2)] vec_lambda_plus step(3))
  qed
next
  case False
  thus ?thesis by (simp add: zero_vec_def)
qed

lemma subspace_range_vec_times_matrix: "vec.subspace (range (\<lambda>v. v v* A))" (is "vec.subspace ?r")
proof (simp only: vec.subspace_def, intro conjI ballI allI)
  show "0 \<in> ?r"
  proof
    show "0 = 0 v* A" by (simp only: vector_matrix_zero)
  qed rule
next
  fix x y
  assume "x \<in> ?r"
  then obtain vx where x: "x = vx v* A" ..
  assume "y \<in> ?r"
  then obtain vy where y: "y = vy v* A" ..
  show "x + y \<in> ?r"
  proof
    show "x + y = (vx + vy) v* A" by (simp only: x y vector_matrix_left_distrib)
  qed rule
next
  fix c x
  assume "x \<in> ?r"
  then obtain vx where x: "x = vx v* A" ..
  show "c *s x \<in> ?r"
  proof
    show "c *s x = (c *s vx) v* A" by (simp only: x scalar_vector_matrix_assoc)
  qed rule
qed

lemma row_space_alt: "row_space A = range (\<lambda>v. v v* A)" (is "_ = ?r")
proof (simp only: row_space_def, rule)
  show "vec.span (rows A) \<subseteq> ?r" unfolding row_space_def
  proof (rule Generalizations.vec.span_minimal)
    show "rows A \<subseteq> ?r"
    proof
      fix v
      assume "v \<in> rows A"
      then obtain i where "v = row i A" unfolding rows_def by auto
      show "v \<in> ?r" unfolding \<open>v = row i A\<close>
      proof
        show "row i A = (\<chi> j. (if j = i then 1 else 0)) v* A"
          by (simp add: vector_matrix_mult_def if_distrib row_def cong: if_cong)
      qed rule
    qed
  qed (fact subspace_range_vec_times_matrix)
next
  show "?r \<subseteq> vec.span (rows A)"
  proof
    fix x
    assume "x \<in> ?r"
    then obtain vx where x: "x = vx v* A" ..
    show "x \<in> vec.span (rows A)" unfolding x vector_matrix_mult_def vec_lambda_sum_commute
    proof (rule Generalizations.vec.span_sum, simp, rule)
      fix i
      show "(\<chi> j. A $ i $ j * vx $ i) \<in> vec.span (rows A)"
        by (simp only: mult.commute vector_scalar_mult_def[symmetric], rule Generalizations.vec.span_mul,
          rule Generalizations.vec.span_superset, simp only: rows_def row_def vec_lambda_eta, rule+)
    qed
  qed
qed

definition row_space_iarray :: "('a::semiring_1) iarray iarray \<Rightarrow> 'a iarray set" where
  "row_space_iarray A = {v v*i A | v. IArray.length v = nrows_iarray A}"

lemma in_row_space_iarrayI:
  assumes "x = v v*i A" and "IArray.length v \<le> nrows_iarray A"
  shows "x \<in> row_space_iarray A"
proof -
  define w where "w = IArray ((IArray.list_of v) @ (replicate (nrows_iarray A - IArray.length v) 0))"
  have "IArray.length v \<le> IArray.length w" by (simp add: w_def)
  hence "{0..<IArray.length v} \<subseteq> {0..<IArray.length w}" by simp
  show ?thesis unfolding row_space_iarray_def
  proof (rule, rule, rule)
    have "map (\<lambda>j. \<Sum>i = 0..<IArray.length v. A !! i !! j * v !! i) [0..<ncols_iarray A] =
          map (\<lambda>j. \<Sum>i = 0..<IArray.length w. A !! i !! j * w !! i) [0..<ncols_iarray A]"
    proof (rule map_cong, rule refl)
      fix j
      assume "j \<in> set [0..<ncols_iarray A]"
      show "(\<Sum>i = 0..<IArray.length v. A !! i !! j * v !! i) =
            (\<Sum>i = 0..<IArray.length w. A !! i !! j * w !! i)"
      proof (rule sum.mono_neutral_cong_left, rule, fact, rule)
        fix i
        assume "i \<in> {0..<IArray.length w} - {0..<IArray.length v}"
        hence "IArray.length v \<le> i" and "i < IArray.length w" by simp_all
        hence "w !! i = 0" by (simp add: w_def nth_append)
        thus "A !! i !! j * w !! i = 0" by simp
      next
        fix i
        assume "i \<in> {0..<IArray.length v}"
        hence "i < IArray.length v" by simp
        hence "w !! i = v !! i" by (simp add: w_def nth_append)
        thus "A !! i !! j * v !! i = A !! i !! j * w !! i" by simp
      qed
    qed
    thus "x = w v*i A" by (simp add: assms(1) vector_matrix_mult_iarray_def)
  next
    from assms(2) have "\<not> nrows_iarray A < length (IArray.list_of v)" by simp
    from add_diff_inverse_nat[OF this] show "IArray.length w = nrows_iarray A" by (simp add: w_def)
  qed
qed

lemma in_row_space_iarrayE:
  assumes "x \<in> row_space_iarray A"
  obtains v where "x = v v*i A" and "IArray.length v = nrows_iarray A"
  using assms unfolding row_space_iarray_def by auto

lemma row_space_matrix_to_iarray:
  "row_space_iarray (matrix_to_iarray A) = vec_to_iarray ` row_space (A::'a::field^'n::mod_type^'m::mod_type)"
proof (simp del: IArray.length_def add: row_space_alt row_space_iarray_def image_comp o_def
      vec_to_iarray_vector_matrix_mult nrows_eq_card_rows)
  show "{v v*i matrix_to_iarray A |v. IArray.length v = CARD('m)} =
        range (\<lambda>v::'a^'m::mod_type. vec_to_iarray v v*i matrix_to_iarray A)"
    (is "?l = ?r")
  proof
    show "?l \<subseteq> ?r"
    proof
      fix x
      assume "x \<in> ?l"
      then obtain vx where x: "x = vx v*i matrix_to_iarray A" and vx: "IArray.length vx = CARD('m)" by auto
      show "x \<in> ?r" unfolding x
      proof
        show "vx v*i matrix_to_iarray A = vec_to_iarray ((iarray_to_vec vx)::'a^'m::mod_type) v*i matrix_to_iarray A"
          by (simp only: vec_to_iarray_iarray_to_vec[OF vx])
      qed rule
    qed
  next
    show "?r \<subseteq> ?l"
    proof
      fix x
      assume "x \<in> ?r"
      then obtain vx::"'a^'m::mod_type" where x: "x = vec_to_iarray vx v*i matrix_to_iarray A" ..
      show "x \<in> ?l" by (rule, rule, rule, fact, fact length_vec_to_iarray)
    qed
  qed
qed

(*
lemma row_space_iarray_rem_zero:
  assumes "IArray.all (\<lambda>r. IArray.length r = ncols_iarray A) A" and "IArray.exists (IArray.exists (\<lambda>x. x \<noteq> 0)) A"
  shows "row_space_iarray A = row_space_iarray (IArray (filter (IArray.exists (\<lambda>x. x \<noteq> 0)) (IArray.list_of A)))"
    (is "?l = ?r")
proof -
  have "0 < nrows_iarray (IArray (filter (IArray.exists (\<lambda>x. x \<noteq> 0)) (IArray.list_of A)))"
    (is "_ < nrows_iarray ?A") sorry
  hence "nrows_iarray ?A \<le> nrows_iarray A" sorry
  have ncols: "ncols_iarray ?A = ncols_iarray A" sorry
  show ?thesis
  proof
    show "?l \<subseteq> ?r"
    proof
      fix x
      assume "x \<in> ?l"
      then obtain vx where x: "x = vx v*i A" and vx: "IArray.length vx = nrows_iarray A"
        by (rule in_row_space_iarrayE)
      from vx have vx': "length (IArray.list_of vx) = length (IArray.list_of A)" by (simp add: nrows_iarray_def)
      define wx::"'a iarray" where
        "wx = IArray (map fst (filter (IArray.exists (\<lambda>x. x \<noteq> 0) \<circ> snd) (zip (IArray.list_of vx) (IArray.list_of A))))"
      have "IArray.length wx \<le> length (zip (IArray.list_of vx) (IArray.list_of A))" unfolding wx_def
        by (simp del: length_zip)
      also have "... \<le> IArray.length vx" by simp
      finally have "IArray.length wx \<le> IArray.length vx" .
      hence "{0..<IArray.length wx} \<subseteq> {0..<IArray.length vx}" by simp
      show "x \<in> ?r"
      proof (rule in_row_space_iarrayI)
        show "x = wx v*i IArray (filter (IArray.exists (\<lambda>x. x \<noteq> 0)) (IArray.list_of A))"
        proof (simp del: IArray.length_def add: x vector_matrix_mult_iarray_def, simp only: ncols,
              rule map_cong, rule refl)
          fix j
          assume "j \<in> set [0..<ncols_iarray A]"
          show "(\<Sum>i = 0..<IArray.length vx. IArray.list_of (IArray.list_of A ! i) ! j * IArray.list_of vx ! i) =
                (\<Sum>i = 0..<IArray.length wx. IArray.list_of (filter (IArray.exists (\<lambda>x. x \<noteq> 0)) (IArray.list_of A) ! i) ! j *
                  IArray.list_of wx ! i)"
          proof (rule sum.mono_neutral_cong_right, rule, fact, rule)
        qed
      next
        show "IArray.length wx \<le> nrows_iarray (IArray (filter (IArray.exists (\<lambda>x. x \<noteq> 0)) (IArray.list_of A)))" sorry
      qed
    qed
  next
    show "?r \<subseteq> ?l" sorry
  qed
qed

lemma row_space_iarray_remdups:
  "row_space_iarray A = row_space_iarray (IArray (remdups (IArray.list_of A)))"
  sorry
*)

lemma mult_iarray_alt: "mult_iarray x c = IArray (map (op * c) (IArray.list_of x))"
  by (simp add: mult_iarray_def nth_equalityI)

instantiation iarray :: (monoid_add) monoid_add
begin
instance sorry
end

lemma vector_matrix_mult_iarray_alt:
  assumes "IArray.length v = nrows_iarray A"
  shows "v v*i A = sum_list (map (\<lambda>x. mult_iarray (fst x) (snd x)) (zip (IArray.list_of A) (IArray.list_of v)))"
  sorry

thm vector_matrix_mult_def
thm row_space_def
thm vec.span_def
thm vec.subspace_def
thm row_space_is_preserved

thm Generalizations.vec.span_finite
thm Generalizations.vec.span_sum
thm Generalizations.vec.span_explicit
thm vector_matrix_mult_iarray_def
thm vec_to_iarray_vector_matrix_mult

subsection \<open>Function "Supp"\<close>

definition Supp :: "('a, 'b::zero) poly_mapping set \<Rightarrow> 'a set" where "Supp F = \<Union>(keys ` F)"

lemma in_Supp: "s \<in> Supp F \<longleftrightarrow> (\<exists>f\<in>F. s \<in> keys f)"
  unfolding Supp_def by simp

lemma in_SuppI:
  assumes "s \<in> keys f" and "f \<in> F"
  shows "s \<in> Supp F"
  unfolding in_Supp using assms ..

lemma in_SuppE:
  assumes "s \<in> Supp F"
  obtains f where "s \<in> keys f" and "f \<in> F"
  using assms unfolding in_Supp ..

lemma Supp_union: "Supp (A \<union> B) = Supp A \<union> Supp B"
  by (simp add: Supp_def)

lemma Supp_finite:
  assumes "finite F"
  shows "finite (Supp F)"
  unfolding Supp_def by (rule, fact assms, rule finite_keys)

lemma Supp_not_empty:
  assumes "f \<in> F" and "f \<noteq> 0"
  shows "Supp F \<noteq> {}"
proof
  assume "Supp F = {}"
  from \<open>f \<noteq> 0\<close> have "keys f \<noteq> {}" by simp
  then obtain s where "s \<in> keys f" by blast
  from this assms(1) have "s \<in> Supp F" by (rule in_SuppI)
  with \<open>Supp F = {}\<close> show False by simp
qed

lemma Supp_of_empty: "Supp {} = {}"
  by (simp add: Supp_def)

lemma Supp_of_zero: "Supp {0} = {}"
  by (simp add: Supp_def)

lemma keys_subset_Supp:
  assumes "f \<in> F"
  shows "keys f \<subseteq> Supp F"
  using in_SuppI[OF _ assms] by auto

lemma Supp_minus_zero: "Supp (A - {0::('a, 'b::zero) poly_mapping}) = Supp A"
proof (cases "0 \<in> A")
  case True
  hence "(A - {0}) \<union> {0} = A" by auto
  hence "Supp A = Supp ((A - {0}) \<union> {0})" by simp
  also have "... = Supp (A - {0}) \<union> Supp {0::('a, 'b) poly_mapping}" by (fact Supp_union)
  also have "... = Supp (A - {0})" by (simp add: Supp_of_zero)
  finally show ?thesis by simp
next
  case False
  hence "A - {0} = A" by simp
  thus ?thesis by simp
qed


subsection \<open>Converting Between Matrices and Polynomials\<close>

context ordered_powerprod
begin

text \<open>Function "pps_to_list" turns finite sets of power-products into sorted lists, where the lists
  are sorted descending (i.e. greater elements come before smaller ones).\<close>
definition pps_to_list :: "'a set \<Rightarrow> 'a list" where
  "pps_to_list S = rev (ordered_powerprod_lin.sorted_list_of_set S)"

definition poly_to_row :: "'a list \<Rightarrow> ('a, 'b::zero) poly_mapping \<Rightarrow> 'b iarray" where
  "poly_to_row ts p = IArray (map (lookup p) ts)"

definition polys_to_mat :: "('a, 'b::zero) poly_mapping list \<Rightarrow> ('b iarray) iarray" where
  "polys_to_mat ps = IArray (map (poly_to_row (pps_to_list (Supp (set ps)))) ps)"

primrec row_to_fun :: "'a list \<Rightarrow> ('b::zero) iarray \<Rightarrow> 'a \<Rightarrow> 'b" where
  row_to_fun_IArray: "row_to_fun ts (IArray cs) t = (case map_of (zip ts cs) t of Some c \<Rightarrow> c | None \<Rightarrow> 0)"

definition row_to_poly :: "'a list \<Rightarrow> 'b iarray \<Rightarrow> ('a, 'b::zero) poly_mapping" where
  "row_to_poly ts r = Abs_poly_mapping (row_to_fun ts r)"

primrec mat_to_polys :: "'a list \<Rightarrow> ('b iarray) iarray \<Rightarrow> ('a, 'b::zero) poly_mapping list" where
  mat_to_polys_IArray: "mat_to_polys ts (IArray rs) = map (row_to_poly ts) rs"

lemma pps_to_list_sorted_wrt: "sorted_wrt (op \<preceq>\<inverse>\<inverse>) (pps_to_list S)"
proof -
  have "transp (op \<preceq>)" by simp
  hence *: "transp (op \<preceq>\<inverse>\<inverse>)" using transp_def by force
  have **: "(\<lambda>x y. op \<preceq>\<inverse>\<inverse> y x) = (op \<preceq>)" by simp
  show ?thesis
    by (simp only: pps_to_list_def sorted_wrt_rev[OF *] ** ordered_powerprod_lin.sorted_iff_wrt[symmetric],
      rule ordered_powerprod_lin.sorted_sorted_list_of_set)
qed

lemma pps_to_list_distinct: "distinct (pps_to_list S)"
  unfolding pps_to_list_def distinct_rev by (rule ordered_powerprod_lin.distinct_sorted_list_of_set)

lemma pps_to_list_set:
  assumes "finite S"
  shows "set (pps_to_list S) = S"
  unfolding pps_to_list_def set_rev using assms by simp

lemma lookup_row_to_poly:
  "lookup (row_to_poly ts (IArray cs)) t = (case map_of (zip ts cs) t of Some c \<Rightarrow> c | None \<Rightarrow> 0)"
  sorry

lemma poly_to_row_scalar_mult:
  assumes "keys p \<subseteq> A" and "finite A"
  shows "row_to_poly (pps_to_list A) (mult_iarray (poly_to_row (pps_to_list A) p) c) = monom_mult c 0 p"
proof -
  have *: "row_to_fun (pps_to_list A) (mult_iarray (poly_to_row (pps_to_list A) p) c) = (\<lambda>t. c * lookup p t)"
  proof (rule, simp add: poly_to_row_def pps_to_list_set[OF assms(2)] mult_iarray_alt map_of_zip_map, rule)
    fix t
    assume "t \<notin> A"
    with assms(1) have "t \<notin> keys p" by auto
    thus "c * lookup p t = 0" by simp
  qed
  have **: "lookup (Abs_poly_mapping (row_to_fun (pps_to_list A) (mult_iarray (poly_to_row (pps_to_list A) p) c))) =
            (\<lambda>t. c * lookup p t)"
  proof (simp only: *, rule Abs_poly_mapping_inverse, simp, rule finite_subset, rule, simp)
    fix t
    assume "c * lookup p t \<noteq> 0"
    hence "lookup p t \<noteq> 0" using mult_not_zero by blast 
    thus "t \<in> keys p" by simp
  qed (fact finite_keys)
  show ?thesis unfolding row_to_poly_def
  proof (rule poly_mapping_eqI, simp only: **)
    fix t
    have "lookup (monom_mult c 0 p) (0 + t) = c * lookup p t" by (fact lookup_monom_mult)
    thus "c * lookup p t = lookup (monom_mult c 0 p) t" by simp
  qed
qed

lemma poly_to_row_to_poly:
  assumes "keys p \<subseteq> A" and "finite A"
  shows "row_to_poly (pps_to_list A) (poly_to_row (pps_to_list A) p) = (p::('a, 'b::semiring_1) poly_mapping)"
proof -
  have "mult_iarray (poly_to_row (pps_to_list A) p) 1 = poly_to_row (pps_to_list A) p"
    by (simp add: mult_iarray_alt poly_to_row_def)
  thus ?thesis using monom_mult_left1[of p] poly_to_row_scalar_mult[OF assms, of 1] by simp
qed

lemma row_to_poly_empty: "row_to_poly [] r = 0"
  sorry

lemma polys_to_mat_empty: "polys_to_mat [] = IArray []"
  sorry

lemma nrows_polys_to_mat: "nrows_iarray (polys_to_mat ps) = length ps"
  by (simp add: polys_to_mat_def nrows_iarray_def)

lemma ncols_polys_to_mat:
  assumes "ps \<noteq> []"
  shows "ncols_iarray (polys_to_mat ps) = card (Supp (set ps))"
  sorry

lemma polys_to_mat_to_polys:
  shows "mat_to_polys (pps_to_list (Supp (set ps))) (polys_to_mat ps) = (ps::('a, 'b::semiring_1) poly_mapping list)"
  unfolding polys_to_mat_def mat_to_polys_IArray map_map
  by (rule map_idI, simp only: o_def, rule poly_to_row_to_poly, rule keys_subset_Supp, assumption,
    rule Supp_finite, rule)

lemma vec_times_polys_to_mat:
  assumes "IArray.length v = length ps"
  shows "row_to_poly (pps_to_list (Supp (set ps))) (v v*i (polys_to_mat ps)) =
          (\<Sum>(c, p)\<leftarrow>zip (IArray.list_of v) ps. monom_mult c 0 p)" (is "?l = ?r")
proof (cases "ps = []")
  case True
  show ?thesis by (simp add: True polys_to_mat_empty Supp_def pps_to_list_def row_to_poly_empty)
next
  case False
  thm Abs_poly_mapping_inverse
  show ?thesis
    apply (rule poly_mapping_eqI, simp add: vector_matrix_mult_iarray_def assms lookup_row_to_poly) sorry
qed

lemma row_space_subset_phull:
  "row_to_poly (pps_to_list (Supp (set ps))) ` row_space_iarray (polys_to_mat ps) \<subseteq> phull (set ps)"
    (is "?r \<subseteq> ?h")
proof
  fix q
  assume "q \<in> ?r"
  then obtain x where x1: "x \<in> row_space_iarray (polys_to_mat ps)"
    and q1: "q = row_to_poly (pps_to_list (Supp (set ps))) x" ..
  from x1 obtain v where x: "x = v v*i polys_to_mat ps"
    and l: "IArray.length v = nrows_iarray (polys_to_mat ps)" by (rule in_row_space_iarrayE)
  from l have "IArray.length v = length ps" by (simp only: nrows_polys_to_mat)
  with x q1 have q: "q = (\<Sum>(c, p)\<leftarrow>zip (IArray.list_of v) ps. monom_mult c 0 p)"
    by (simp add: vec_times_polys_to_mat)
  show "q \<in> ?h" unfolding q by (rule in_phull_listI)
qed

lemma phull_subset_row_space:
  assumes "distinct ps"
  shows "phull (set ps) \<subseteq> row_to_poly (pps_to_list (Supp (set ps))) ` row_space_iarray (polys_to_mat ps)"
    (is "?h \<subseteq> ?r")
proof
  fix q
  assume "q \<in> ?h"
  with assms obtain cs where l: "length cs = length ps" and q: "q = (\<Sum>(c, p)\<leftarrow>zip cs ps. monom_mult c 0 p)"
    by (rule in_phull_listE)
  let ?v = "IArray cs"
  from l have *: "IArray.length ?v = length ps" by simp
  let ?q = "?v v*i polys_to_mat ps"
  show "q \<in> ?r"
  proof
    show "q = row_to_poly (pps_to_list (Supp (set ps))) ?q" by (simp add: vec_times_polys_to_mat[OF *] q)
  next
    show "?q \<in> row_space_iarray (polys_to_mat ps)"
      by (rule in_row_space_iarrayI, rule refl, simp only: * nrows_polys_to_mat)
  qed
qed

lemma row_space_eq_phull:
  assumes "distinct ps"
  shows "row_to_poly (pps_to_list (Supp (set ps))) ` row_space_iarray (polys_to_mat ps) = phull (set ps)"
  by (rule, fact row_space_subset_phull, rule phull_subset_row_space, fact)

lemma row_space_eq_phull':
  "row_to_poly (pps_to_list (Supp (set ps))) ` row_space_iarray (polys_to_mat (remdups ps)) = phull (set ps)"
proof -
  define qs where "qs = remdups ps"
  have *: "set qs = set ps" by (simp add: qs_def)
  have "distinct qs" unfolding qs_def ..
  hence "row_to_poly (pps_to_list (Supp (set qs))) ` row_space_iarray (polys_to_mat qs) = phull (set qs)"
    by (rule row_space_eq_phull)
  moreover have "Supp (set qs) = Supp (set ps)" by (simp only: *)
  moreover have "phull (set qs) = phull (set ps)" by (simp only: *)
  ultimately show ?thesis by (simp add: qs_def)
qed

end (* ordered_powerprod *)

(*
subsection \<open>Fixing a Finite, Non-empty Set of Polynomials\<close>

locale poly_set = fun_powerprod ord ord_strict
  for ord::"('n \<Rightarrow> nat) \<Rightarrow> ('n::finite_nat \<Rightarrow> nat) \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50) +
  (* The reason why we have to name the order relations again is that otherwise we cannot call the
    type variables 'n and 'b. *)
  fixes F :: "('n \<Rightarrow> nat, 'b::field) poly_mapping set"
  assumes fin: "finite F"
  assumes nz: "\<exists>f\<in>F. f \<noteq> 0"
begin

sublocale od_powerprod ..

lemma non_empty: "F \<noteq> {}"
proof
  assume "F = {}"
  from nz obtain f where "f \<in> F" ..
  with \<open>F = {}\<close> show False by simp
qed

end (* poly_set *)
*)

end (* theory *)