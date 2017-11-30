theory Macaulay_Groebner
  imports Power_Products_Fun Reduced_GB "Jordan_Normal_Form.Gauss_Jordan_Elimination"
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

text \<open>We build upon vectors and matrices represented by dimension and characteristic function, because
  later on we need to quantify the dimensions of certain matrices existentially. This is not possible
  (at least not easily possible) with a type-based approach, as in HOL-Multivariate Analysis.\<close>

subsection \<open>More about Vectors\<close>

lemma vec_of_list_alt: "vec_of_list xs = vec (length xs) (nth xs)"
  by (transfer, rule refl)

lemma list_of_vec_vec: "list_of_vec (vec n f) = (map f [0..<n])"
  apply (transfer)
  by (metis (mono_tags, lifting) atLeast_upt case_prod_conv lessThan_iff map_cong mk_vec_def)

lemma vec_of_list_index: "vec_of_list xs $ i = xs ! i"
proof (transfer, simp add: mk_vec_def undef_vec_def, rule)
  fix xs::"'a list" and i
  assume "\<not> i < length xs"
  hence "length xs \<le> i" by simp
  thus "[] ! (i - length xs) = xs ! i"
  proof (induct xs)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)
    thus ?case by (metis append_Nil2 not_le nth_append)
  qed
qed

lemma list_of_vec_nth:
  assumes "i < dim_vec v"
  shows "(list_of_vec v) ! i = v $ i"
  using assms by (transfer, auto)

lemma dim_vec_of_list: "dim_vec (vec_of_list xs) = length xs"
  by (transfer, simp)

lemma length_list_of_vec: "length (list_of_vec v) = dim_vec v"
  by (transfer, auto)

lemma list_of_vec_of_list: "list_of_vec (vec_of_list xs) = xs"
  apply (transfer)
  by (metis list_of_vec.rep_eq list_of_vec_vec map_nth vec.rep_eq)

lemma vec_cong:
  assumes "n = m" and "\<And>i. i < m \<Longrightarrow> f i = g i"
  shows "vec n f = vec m g"
  using assms by auto

lemma scalar_prod_comm:
  assumes "dim_vec v = dim_vec w"
  shows "v \<bullet> w = w \<bullet> (v::'a::comm_semiring_0 vec)"
  by (simp add: scalar_prod_def assms, rule sum.cong, rule refl, simp only: ac_simps)

definition mult_vec_mat :: "'a vec \<Rightarrow> 'a :: semiring_0 mat \<Rightarrow> 'a vec" (infixl "\<^sub>v*" 70)
  where "v \<^sub>v* A \<equiv> vec (dim_col A) (\<lambda>i. v \<bullet> col A i)"

definition resize_vec :: "nat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "resize_vec n v = vec n (vec_index v)"

lemma dim_resize_vec[simp]: "dim_vec (resize_vec n v) = n"
  by (simp add: resize_vec_def)

lemma resize_vec_carrier: "resize_vec n v \<in> carrier_vec n"
  by (simp add: carrier_dim_vec)

lemma resize_vec_dim[simp]: "resize_vec (dim_vec v) v = v"
  by (simp add: resize_vec_def eq_vecI)

lemma resize_vec_index:
  assumes "i < n"
  shows "resize_vec n v $ i = v $ i"
  using assms by (simp add: resize_vec_def)

lemma mult_mat_vec_resize:
  "v \<^sub>v* A = (resize_vec (dim_row A) v) \<^sub>v* A"
  by (simp add: mult_vec_mat_def scalar_prod_def, rule arg_cong2[of _ _ _ _ vec], rule, rule,
      rule sum.cong, rule, simp add: resize_vec_index)

lemma assoc_mult_vec_mat:
  assumes "v \<in> carrier_vec n1" and "A \<in> carrier_mat n1 n2" and "B \<in> carrier_mat n2 n3"
  shows "v \<^sub>v* (A * B) = (v \<^sub>v* A) \<^sub>v* B"
  using assms by (intro eq_vecI, auto simp add: mult_vec_mat_def mult_mat_vec_def assoc_scalar_prod)

lemma mult_vec_mat_transpose:
  assumes "dim_vec v = dim_row A"
  shows "v \<^sub>v* A = (transpose_mat A) *\<^sub>v (v::'a::comm_semiring_0 vec)"
proof (simp add: mult_vec_mat_def mult_mat_vec_def, rule vec_cong, rule refl, simp)
  fix i
  show "v \<bullet> col A i = col A i \<bullet> v" by (rule scalar_prod_comm, simp add: assms)
qed

subsection \<open>More about Matrices\<close>

lemma length_mat_to_list: "length (mat_to_list A) = dim_row A"
  by (simp add: mat_to_list_def)

lemma mat_to_list_nth:
  assumes "i < dim_row A"
  shows "mat_to_list A ! i = list_of_vec (row A i)"
  by (simp add: mat_to_list_def assms list_of_vec_vec row_def)

definition row_space :: "'a mat \<Rightarrow> 'a::semiring_0 vec set"
  where "row_space A = (\<lambda>v. mult_vec_mat v A) ` (carrier_vec (dim_row A))"

definition row_echelon :: "'a mat \<Rightarrow> 'a::field mat"
  where "row_echelon A = fst (gauss_jordan A (1\<^sub>m (dim_row A)))"

subsubsection \<open>@{const row_space}\<close>

lemma row_spaceI:
  assumes "x = v \<^sub>v* A"
  shows "x \<in> row_space A"
  unfolding row_space_def assms by (rule, fact mult_mat_vec_resize, fact resize_vec_carrier)

lemma row_spaceE:
  assumes "x \<in> row_space A"
  obtains v where "v \<in> carrier_vec (dim_row A)" and "x = v \<^sub>v* A"
  using assms unfolding row_space_def by auto

lemma row_space_alt: "row_space A = range (\<lambda>v. mult_vec_mat v A)"
proof
  show "row_space A \<subseteq> range (\<lambda>v. v \<^sub>v* A)" unfolding row_space_def by auto
next
  show "range (\<lambda>v. v \<^sub>v* A) \<subseteq> row_space A"
  proof
    fix x
    assume "x \<in> range (\<lambda>v. v \<^sub>v* A)"
    then obtain v where "x = v \<^sub>v* A" ..
    thus "x \<in> row_space A" by (rule row_spaceI)
  qed
qed

lemma row_space_mult:
  assumes "A \<in> carrier_mat nr nc" and "B \<in> carrier_mat nr nr"
  shows "row_space (B * A) \<subseteq> row_space A"
proof
  from assms(2) assms(1) have "B * A \<in> carrier_mat nr nc" by (rule mult_carrier_mat)
  hence "nr = dim_row (B * A)" by blast
  fix x
  assume "x \<in> row_space (B * A)"
  then obtain v where "v \<in> carrier_vec nr" and x: "x = v \<^sub>v* (B * A)"
    unfolding \<open>nr = dim_row (B * A)\<close> by (rule row_spaceE)
  from this(1) assms(2) assms(1) have "x = (v \<^sub>v* B) \<^sub>v* A" unfolding x by (rule assoc_mult_vec_mat)
  thus "x \<in> row_space A" by (rule row_spaceI)
qed

lemma row_space_mult_unit:
  assumes "P \<in> Units (ring_mat TYPE('a::semiring_1) (dim_row A) b)"
  shows "row_space (P * A) = row_space A"
proof -
  have A: "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  from assms have P: "P \<in> carrier (ring_mat TYPE('a) (dim_row A) b)" and
    *: "\<exists>Q\<in>(carrier (ring_mat TYPE('a) (dim_row A) b)).
            Q \<otimes>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub> P = \<one>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub>"
    unfolding Units_def by auto
  from P have P_in: "P \<in> carrier_mat (dim_row A) (dim_row A)" by (simp add: ring_mat_def)
  from * obtain Q where "Q \<in> carrier (ring_mat TYPE('a) (dim_row A) b)"
    and "Q \<otimes>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub> P = \<one>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub>" ..
  hence Q_in: "Q \<in> carrier_mat (dim_row A) (dim_row A)" and QP: "Q * P = 1\<^sub>m (dim_row A)"
    by (simp_all add: ring_mat_def)
  show ?thesis
  proof
    from A P_in show "row_space (P * A) \<subseteq> row_space A" by (rule row_space_mult)
  next
    from A P_in Q_in have "Q * (P * A) = (Q * P) * A" by (simp only: assoc_mult_mat)
    also from A have "... = A" by (simp add: QP)
    finally have eq: "row_space A = row_space (Q * (P * A))" by simp
    show "row_space A \<subseteq> row_space (P * A)" unfolding eq by (rule row_space_mult, rule mult_carrier_mat, fact+)
  qed
qed

subsubsection \<open>@{const row_echelon}\<close>

lemma row_eq_zero_iff_pivot_fun:
  assumes "pivot_fun A f (dim_col A)" and "i < dim_row (A::'a::zero_neq_one mat)"
  shows "(row A i = 0\<^sub>v (dim_col A)) \<longleftrightarrow> (f i = dim_col A)"
proof -
  have *: "dim_row A = dim_row A" ..
  show ?thesis
  proof
    assume a: "row A i = 0\<^sub>v (dim_col A)"
    show "f i = dim_col A"
    proof (rule ccontr)
      assume "f i \<noteq> dim_col A"
      with pivot_funD(1)[OF * assms] have **: "f i < dim_col A" by simp
      with * assms have "A $$ (i, f i) = 1" by (rule pivot_funD)
      with ** assms(2) have "row A i $ (f i) = 1" by simp
      hence "(1::'a) = (0\<^sub>v (dim_col A)) $ (f i)" by (simp only: a)
      also have "... = (0::'a)" using ** by simp
      finally show False by simp
    qed
  next
    assume a: "f i = dim_col A"
    show "row A i = 0\<^sub>v (dim_col A)"
    proof (rule, simp_all add: assms(2))
      fix j
      assume "j < dim_col A"
      hence "j < f i" by (simp only: a)
      with * assms show "A $$ (i, j) = 0" by (rule pivot_funD)
    qed
  qed
qed

lemma row_echelon_carrier:
  assumes "A \<in> carrier_mat nr nc"
  shows "row_echelon A \<in> carrier_mat nr nc"
proof -
  from assms have "dim_row A = nr" by simp
  let ?B = "1\<^sub>m (dim_row A)"
  note assms
  moreover have "?B \<in> carrier_mat nr nr" by (simp add: \<open>dim_row A = nr\<close>)
  moreover from surj_pair obtain A' B' where *: "gauss_jordan A ?B = (A', B')" by metis
  ultimately have "A' \<in> carrier_mat nr nc" by (rule gauss_jordan_carrier)
  thus ?thesis by (simp add: row_echelon_def *)
qed

lemma dim_row_echelon[simp]:
  shows "dim_row (row_echelon A) = dim_row A" and "dim_col (row_echelon A) = dim_col A"
proof -
  have "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  hence "row_echelon A \<in> carrier_mat (dim_row A) (dim_col A)" by (rule row_echelon_carrier)
  thus "dim_row (row_echelon A) = dim_row A" and "dim_col (row_echelon A) = dim_col A" by simp_all
qed

lemma row_echelon_transform:
  obtains P where "P \<in> Units (ring_mat TYPE('a::field) (dim_row A) b)" and "row_echelon A = P * A"
proof -
  let ?B = "1\<^sub>m (dim_row A)"
  have "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  moreover have "?B \<in> carrier_mat (dim_row A) (dim_row A)" by simp
  moreover from surj_pair obtain A' B' where *: "gauss_jordan A ?B = (A', B')" by metis
  ultimately have "\<exists>P\<in>Units (ring_mat TYPE('a) (dim_row A) b). A' = P * A \<and> B' = P * ?B"
    by (rule gauss_jordan_transform)
  then obtain P where "P \<in> Units (ring_mat TYPE('a) (dim_row A) b)" and **: "A' = P * A \<and> B' = P * ?B" ..
  from this(1) show ?thesis
  proof
    from ** have "A' = P * A" ..
    thus "row_echelon A = P * A" by (simp add: row_echelon_def *)
  qed
qed

lemma row_space_row_echelon[simp]: "row_space (row_echelon A) = row_space A"
proof -
  obtain P where *: "P \<in> Units (ring_mat TYPE('a::field) (dim_row A) Nil)" and **: "row_echelon A = P * A"
    by (rule row_echelon_transform)
  from * have "row_space (P * A) = row_space A" by (rule row_space_mult_unit)
  thus ?thesis by (simp only: **)
qed

lemma row_echelon_pivot_fun:
  obtains f where "pivot_fun (row_echelon A) f (dim_col A)"
proof -
  let ?B = "1\<^sub>m (dim_row A)"
  have "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  moreover from surj_pair obtain A' B' where *: "gauss_jordan A ?B = (A', B')" by metis
  ultimately have "row_echelon_form A'" by (rule gauss_jordan_row_echelon)
  then obtain f where "pivot_fun A' f (dim_col A')" unfolding row_echelon_form_def ..
  hence "pivot_fun (row_echelon A) f (dim_col (row_echelon A))" by (simp add: row_echelon_def *)
  hence "pivot_fun (row_echelon A) f (dim_col A)" by simp
  thus ?thesis ..
qed

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


subsection \<open>Converting Between Polynomials and Macaulay Matrices\<close>

context ordered_powerprod
begin

text \<open>Function "pps_to_list" turns finite sets of power-products into sorted lists, where the lists
  are sorted descending (i.e. greater elements come before smaller ones).\<close>
definition pps_to_list :: "'a set \<Rightarrow> 'a list" where
  "pps_to_list S = rev (ordered_powerprod_lin.sorted_list_of_set S)"

definition poly_to_row :: "'a list \<Rightarrow> ('a, 'b::zero) poly_mapping \<Rightarrow> 'b vec" where
  "poly_to_row ts p = vec_of_list (map (lookup p) ts)"

definition polys_to_mat :: "('a, 'b::zero) poly_mapping list \<Rightarrow> 'b mat" where
  "polys_to_mat ps = mat_of_row_fun (length ps) (card (Supp (set ps))) (\<lambda>i. (poly_to_row (pps_to_list (Supp (set ps)))) (ps ! i))"

definition list_to_fun :: "'a list \<Rightarrow> ('b::zero) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "list_to_fun ts cs t = (case map_of (zip ts cs) t of Some c \<Rightarrow> c | None \<Rightarrow> 0)"

definition list_to_poly :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a, 'b::zero) poly_mapping" where
  "list_to_poly ts cs = Abs_poly_mapping (list_to_fun ts cs)"

definition row_to_poly :: "'a list \<Rightarrow> 'b vec \<Rightarrow> ('a, 'b::zero) poly_mapping" where
  "row_to_poly ts r = list_to_poly ts (list_of_vec r)"

definition mat_to_polys :: "'a list \<Rightarrow> 'b mat \<Rightarrow> ('a, 'b::zero) poly_mapping list" where
  "mat_to_polys ts A = map (list_to_poly ts) (mat_to_list A)"

lemma distinct_pps_to_list: "distinct (pps_to_list S)"
  unfolding pps_to_list_def distinct_rev by (rule ordered_powerprod_lin.distinct_sorted_list_of_set)

lemma set_pps_to_list:
  assumes "finite S"
  shows "set (pps_to_list S) = S"
  unfolding pps_to_list_def set_rev using assms by simp

lemma length_pps_to_list: "length (pps_to_list S) = card S"
proof (cases "finite S")
  case True
  from distinct_card[OF distinct_pps_to_list] have "length (pps_to_list S) = card (set (pps_to_list S))"
    by simp
  also from True have "... = card S" by (simp only: set_pps_to_list)
  finally show ?thesis .
next
  case False
  thus ?thesis by (simp add: pps_to_list_def)
qed

lemma pps_to_list_sorted_wrt: "sorted_wrt (op \<preceq>\<inverse>\<inverse>) (pps_to_list S)"
proof -
  have "transp (op \<preceq>)" by simp
  have *: "(\<lambda>x y. op \<preceq>\<inverse>\<inverse> y x) = (op \<preceq>)" by simp
  show ?thesis
    by (simp only: pps_to_list_def sorted_wrt_rev * ordered_powerprod_lin.sorted_iff_wrt[symmetric],
      rule ordered_powerprod_lin.sorted_sorted_list_of_set)
qed

lemma pps_to_list_nth_leI:
  assumes "j \<le> i" and "i < card S"
  shows "(pps_to_list S) ! i \<preceq> (pps_to_list S) ! j"
proof -
  let ?ts = "pps_to_list S"
  have "transp (op \<preceq>\<inverse>\<inverse>)" unfolding transp_def by fastforce
  moreover have "reflp (op \<preceq>\<inverse>\<inverse>)" unfolding reflp_def by fastforce
  ultimately have "op \<preceq>\<inverse>\<inverse> (?ts ! j) (?ts ! i)" using pps_to_list_sorted_wrt assms(1)
  proof (rule sorted_wrt_refl_nth_mono)
    from assms(2) show "i < length ?ts" by (simp only: length_pps_to_list)
  qed
  thus ?thesis by simp
qed

lemma pps_to_list_nth_lessI:
  assumes "j < i" and "i < card S"
  shows "(pps_to_list S) ! i \<prec> (pps_to_list S) ! j"
proof -
  let ?ts = "pps_to_list S"
  from assms(1) have "j \<le> i" and "i \<noteq> j" by simp_all
  with assms(2) have "i < length ?ts" and "j < length ?ts" by (simp_all only: length_pps_to_list)
  show ?thesis
  proof (rule ordered_powerprod_lin.neq_le_trans)
    from \<open>i \<noteq> j\<close> show "?ts ! i \<noteq> ?ts ! j"
      by (simp add: nth_eq_iff_index_eq[OF distinct_pps_to_list \<open>i < length ?ts\<close> \<open>j < length ?ts\<close>])
  next
    from \<open>j \<le> i\<close> assms(2) show "?ts ! i \<preceq> ?ts ! j" by (rule pps_to_list_nth_leI)
  qed
qed

lemma pps_to_list_nth_leD:
  assumes "(pps_to_list S) ! i \<preceq> (pps_to_list S) ! j" and "j < card S"
  shows "j \<le> i"
proof (rule ccontr)
  assume "\<not> j \<le> i"
  hence "i < j" by simp
  from this \<open>j < card S\<close> have "(pps_to_list S) ! j \<prec> (pps_to_list S) ! i" by (rule pps_to_list_nth_lessI)
  with assms(1) show False by simp
qed

lemma pps_to_list_nth_lessD:
  assumes "(pps_to_list S) ! i \<prec> (pps_to_list S) ! j" and "j < card S"
  shows "j < i"
proof (rule ccontr)
  assume "\<not> j < i"
  hence "i \<le> j" by simp
  from this \<open>j < card S\<close> have "(pps_to_list S) ! j \<preceq> (pps_to_list S) ! i" by (rule pps_to_list_nth_leI)
  with assms(1) show False by simp
qed

lemma dim_poly_to_row: "dim_vec (poly_to_row ts p) = length ts"
  by (simp add: poly_to_row_def dim_vec_of_list)

lemma poly_to_row_index:
  assumes "i < length ts"
  shows "poly_to_row ts p $ i = lookup p (ts ! i)"
  by (simp add: poly_to_row_def vec_of_list_index assms)

lemma poly_to_row_scalar_mult:
  assumes "keys p \<subseteq> S" and fin: "finite S"
  shows "row_to_poly (pps_to_list S) (c \<cdot>\<^sub>v (poly_to_row (pps_to_list S) p)) = monom_mult c 0 p"
proof -
  have eq: "(vec (length (pps_to_list S)) (\<lambda>i. c * poly_to_row (pps_to_list S) p $ i)) =
        (vec (length (pps_to_list S)) (\<lambda>i. c * lookup p ((pps_to_list S) ! i)))"
    by (rule vec_cong, rule, simp only: poly_to_row_index)
  have *: "list_to_fun (pps_to_list S) (list_of_vec (c \<cdot>\<^sub>v (poly_to_row (pps_to_list S) p))) = (\<lambda>t. c * lookup p t)"
  proof (rule, simp add: list_to_fun_def smult_vec_def dim_poly_to_row eq,
        simp add: list_of_vec_vec map_upt[of "\<lambda>x. c * lookup p x"] map_of_zip_map set_pps_to_list[OF fin], rule)
    fix t
    assume "t \<notin> S"
    with assms(1) have "t \<notin> keys p" by auto
    thus "c * lookup p t = 0" by simp
  qed
  have **: "lookup (Abs_poly_mapping (list_to_fun (pps_to_list S) (list_of_vec (c \<cdot>\<^sub>v (poly_to_row (pps_to_list S) p))))) =
            (\<lambda>t. c * lookup p t)"
  proof (simp only: *, rule Abs_poly_mapping_inverse, simp, rule finite_subset, rule, simp)
    fix t
    assume "c * lookup p t \<noteq> 0"
    hence "lookup p t \<noteq> 0" using mult_not_zero by blast 
    thus "t \<in> keys p" by simp
  qed (fact finite_keys)
  show ?thesis unfolding row_to_poly_def
  proof (rule poly_mapping_eqI, simp only: list_to_poly_def **)
    fix t
    have "lookup (monom_mult c 0 p) (0 + t) = c * lookup p t" by (fact lookup_monom_mult)
    thus "c * lookup p t = lookup (monom_mult c 0 p) t" by simp
  qed
qed

lemma poly_to_row_to_poly:
  assumes "keys p \<subseteq> S" and "finite S"
  shows "row_to_poly (pps_to_list S) (poly_to_row (pps_to_list S) p) = (p::('a, 'b::semiring_1) poly_mapping)"
proof -
  have "1 \<cdot>\<^sub>v (poly_to_row (pps_to_list S) p) = poly_to_row (pps_to_list S) p" by simp
  thus ?thesis using monom_mult_left1[of p] poly_to_row_scalar_mult[OF assms, of 1] by simp
qed

lemma lookup_list_to_poly: "lookup (list_to_poly ts cs) = list_to_fun ts cs"
  unfolding list_to_poly_def
proof (rule Abs_poly_mapping_inverse, rule, rule finite_subset)
  show "{x. list_to_fun ts cs x \<noteq> 0} \<subseteq> set ts"
  proof (rule, simp)
    fix t
    assume "list_to_fun ts cs t \<noteq> 0"
    thus "t \<in> set ts" unfolding list_to_fun_def
      by (metis in_set_zipE map_of_SomeD not_None_eq option.simps(4))
  qed
qed simp

lemma list_to_fun_empty: "list_to_fun [] cs = 0"
  by (simp only: zero_fun_def, rule, simp add: list_to_fun_def)

lemma list_to_poly_empty: "list_to_poly [] cs = 0"
  by (rule poly_mapping_eqI, simp add: lookup_list_to_poly list_to_fun_empty)

lemma row_to_poly_empty: "row_to_poly [] r = 0"
  by (simp only: row_to_poly_def, fact list_to_poly_empty)

lemma lookup_row_to_poly:
  assumes "distinct ts" and "dim_vec r = length ts" and "i < length ts"
  shows "lookup (row_to_poly ts r) (ts ! i) = r $ i"
proof (simp only: row_to_poly_def lookup_list_to_poly)
  from assms(2) assms(3) have "i < dim_vec r" by simp
  have "map_of (zip ts (list_of_vec r)) (ts ! i) = Some ((list_of_vec r) ! i)"
    by (rule map_of_zip_nth, simp_all only: length_list_of_vec assms(2), fact, fact)
  also have "... = Some (r $ i)" by (simp only: list_of_vec_nth \<open>i < dim_vec r\<close>)
  finally show "list_to_fun ts (list_of_vec r) (ts ! i) = r $ i" by (simp add: list_to_fun_def)
qed

lemma keys_row_to_poly: "keys (row_to_poly ts r) \<subseteq> set ts"
proof
  fix t
  assume "t \<in> keys (row_to_poly ts r)"
  hence "lookup (row_to_poly ts r) t \<noteq> 0" by simp
  thus "t \<in> set ts"
  proof (simp add: row_to_poly_def lookup_list_to_poly list_to_fun_def del: lookup_not_eq_zero_eq_in_keys
              split: option.splits)
    fix c
    assume "map_of (zip ts (list_of_vec r)) t = Some c"
    thus "t \<in> set ts" by (meson in_set_zipE map_of_SomeD)
  qed
qed

lemma lookup_row_to_poly_not_zeroE:
  assumes "lookup (row_to_poly ts r) t \<noteq> 0"
  obtains i where "i < length ts" and "t = ts ! i"
proof -
  from assms have "t \<in> keys (row_to_poly ts r)" by simp
  have "t \<in> set ts" by (rule, fact, fact keys_row_to_poly)
  then obtain i where "i < length ts" and "t = ts ! i" by (metis in_set_conv_nth)
  thus ?thesis ..
qed

lemma row_to_poly_zero: "row_to_poly ts (0\<^sub>v (length ts)) = 0"
proof -
  have eq: "map (\<lambda>_. 0) [0..<length ts] = map (\<lambda>_. 0) ts" by (simp add: map_replicate_const)
  show ?thesis
    by (simp add: row_to_poly_def zero_vec_def list_of_vec_vec, rule poly_mapping_eqI,
      simp add: lookup_list_to_poly list_to_fun_def eq map_of_zip_map)
qed

lemma row_to_poly_zero_iff:
  assumes "distinct ts" and "row_to_poly ts r = 0" and "dim_vec r = length ts"
  shows "r = 0\<^sub>v (length ts)"
proof (rule, simp_all add: assms(3))
  fix i
  assume "i < length ts"
  from assms(2) have "0 = lookup (row_to_poly ts r) (ts ! i)" by simp
  also from assms(1) assms(3) \<open>i < length ts\<close> have "... = r $ i" by (rule lookup_row_to_poly)
  finally show "r $ i = 0" by simp
qed

lemma poly_to_row_empty: "poly_to_row [] p = vec 0 f"
proof -
  have "dim_vec (poly_to_row [] p) = 0" by (simp add: dim_poly_to_row)
  thus ?thesis by auto
qed

lemma polys_to_mat_empty: "polys_to_mat [] = mat 0 0 f"
  by (simp add: polys_to_mat_def Supp_of_empty mat_eq_iff)

lemma dim_row_polys_to_mat: "dim_row (polys_to_mat ps) = length ps"
  by (simp add: polys_to_mat_def)

lemma dim_col_polys_to_mat: "dim_col (polys_to_mat ps) = card (Supp (set ps))"
  by (simp add: polys_to_mat_def)

lemma polys_to_mat_index:
  assumes "i < length ps" and "j < card (Supp (set ps))"
  shows "(polys_to_mat ps) $$ (i, j) = lookup (ps ! i) (pps_to_list (Supp (set ps)) ! j)"
  by (simp only: polys_to_mat_def index_mat(2)[OF assms], rule poly_to_row_index,
      simp only: length_pps_to_list assms(2))

lemma row_polys_to_mat:
  assumes "i < length ps"
  shows "row (polys_to_mat ps) i = poly_to_row (pps_to_list (Supp (set ps))) (ps ! i)"
  unfolding polys_to_mat_def
  by (rule row_mat_of_row_fun, fact assms, simp only: dim_poly_to_row length_pps_to_list)

lemma col_polys_to_mat:
  assumes "j < card (Supp (set ps))"
  shows "col (polys_to_mat ps) j = vec_of_list (map (\<lambda>p. lookup p ((pps_to_list (Supp (set ps))) ! j)) ps)"
  by (simp add: vec_of_list_alt col_def dim_row_polys_to_mat, rule vec_cong, rule refl,
      simp add: polys_to_mat_index assms)

lemma mat_to_polys_nth:
  assumes "i < dim_row A"
  shows "(mat_to_polys ts A) ! i = row_to_poly ts (row A i)"
proof -
  from assms have "i < length (mat_to_list A)" by (simp only: length_mat_to_list)
  thus ?thesis by (simp add: mat_to_polys_def row_to_poly_def mat_to_list_nth[OF assms])
qed

lemma polys_to_mat_to_polys:
  "mat_to_polys (pps_to_list (Supp (set ps))) (polys_to_mat ps) = (ps::('a, 'b::semiring_1) poly_mapping list)"
proof (simp add: mat_to_polys_def mat_to_list_def dim_row_polys_to_mat dim_col_polys_to_mat,
    rule nth_equalityI, simp_all, intro allI impI)
  fix i
  assume "i < length ps"
  let ?S = "Supp (set ps)"
  have eq: "map (\<lambda>j. polys_to_mat ps $$ (i, j)) [0..<card ?S] =
            map (\<lambda>j. lookup (ps ! i) ((pps_to_list ?S) ! j)) [0..<length (pps_to_list ?S)]"
  proof (rule map_cong, simp_all add: length_pps_to_list)
    fix j
    assume "j < card ?S"
    hence "j < length (pps_to_list ?S)" by (simp only: length_pps_to_list)
    thus "polys_to_mat ps $$ (i, j) = lookup (ps ! i) (pps_to_list ?S ! j)"
      by (simp add: polys_to_mat_def index_mat(2)[OF \<open>i < length ps\<close> \<open>j < card ?S\<close>] poly_to_row_def vec_of_list_index)
  qed
  show "list_to_poly (pps_to_list ?S) (map (\<lambda>j. polys_to_mat ps $$ (i, j)) [0..<card ?S]) = ps ! i"
  proof (simp add: eq map_upt, rule poly_mapping_eqI, simp add: lookup_list_to_poly list_to_fun_def
        map_of_zip_map set_pps_to_list[OF Supp_finite, OF finite_set], rule)
    fix t
    assume "t \<notin> Supp (set ps)"
    moreover from \<open>i < length ps\<close> have "ps ! i \<in> set ps" by simp
    ultimately have "t \<notin> keys (ps ! i)" using in_SuppI[of t "ps ! i" "set ps"] by blast
    thus "lookup (ps ! i) t = 0" by simp
  qed
qed

subsection \<open>Properties of Macaulay Matrices\<close>

lemma vec_times_polys_to_mat:
  assumes "v \<in> carrier_vec (length ps)"
  shows "row_to_poly (pps_to_list (Supp (set ps))) (v \<^sub>v* (polys_to_mat ps)) =
          (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. monom_mult c 0 p)" (is "?l = ?r")
proof -
  from assms have *: "dim_vec v = length ps" by (simp only: carrier_dim_vec)
  let ?S = "Supp (set ps)"
  let ?ts = "pps_to_list ?S"
  have eq: "map (\<lambda>i. v \<bullet> col (polys_to_mat ps) i) [0..<card ?S] =
        map (\<lambda>s. v \<bullet> (vec_of_list (map (\<lambda>p. lookup p s) ps))) ?ts"
  proof (simp add: list_eq_iff_nth_eq length_pps_to_list, intro allI impI)
    fix i
    assume "i < card ?S"
    hence "col (polys_to_mat ps) i = vec_of_list (map (\<lambda>p. lookup p (?ts ! i)) ps)"
      by (rule col_polys_to_mat)
    thus "v \<bullet> col (polys_to_mat ps) i = v \<bullet> vec_of_list (map (\<lambda>p. lookup p (?ts ! i)) ps)" by simp
  qed
  show ?thesis
  proof (rule poly_mapping_eqI, simp add: mult_vec_mat_def row_to_poly_def lookup_list_to_poly
      list_of_vec_vec dim_col_polys_to_mat eq list_to_fun_def map_of_zip_map set_pps_to_list[OF Supp_finite]
      lookup_sum_list o_def, intro conjI impI)
    fix t
    assume "t \<in> ?S"
    have "v \<bullet> vec_of_list (map (\<lambda>p. lookup p t) ps) =
          (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. lookup (monom_mult c 0 p) t)"
    proof (simp add: scalar_prod_def dim_vec_of_list vec_of_list_index lookup_monom_mult_const)
      have "(\<Sum>i = 0..<length ps. v $ i * lookup (ps ! i) t) =
            (\<Sum>i = 0..<length ps. (list_of_vec v) ! i * lookup (ps ! i) t)"
        by (rule sum.cong, rule refl, simp add: list_of_vec_nth *)
      also have "... = (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. c * lookup p t)"
        by (simp only: sum_set_upt_eq_sum_list, rule sum_list_upt_zip, simp only: length_list_of_vec *)
      finally show "(\<Sum>i = 0..<length ps. v $ i * lookup (ps ! i) t) =
                    (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. c * lookup p t)" .
    qed
    thus "v \<bullet> vec_of_list (map (\<lambda>p. lookup p t) ps) =
          (\<Sum>x\<leftarrow>zip (list_of_vec v) ps. lookup (case x of (c, x) \<Rightarrow> monom_mult c 0 x) t)"
      by (metis (mono_tags, lifting) case_prod_conv cond_case_prod_eta)
  next
    fix t
    assume "t \<notin> ?S"
    have "(\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. lookup (monom_mult c 0 p) t) = 0"
    proof (rule sum_list_zeroI, rule, simp add: lookup_monom_mult_const)
      fix x
      assume "x \<in> (\<lambda>(c, p). c * lookup p t) ` set (zip (list_of_vec v) ps)"
      then obtain c p where cp: "(c, p) \<in> set (zip (list_of_vec v) ps)"
        and x: "x = c * lookup p t" by auto
      from cp have "p \<in> set ps" by (rule set_zip_rightD)
      with \<open>t \<notin> ?S\<close> have "t \<notin> keys p" by (auto intro: in_SuppI)
      thus "x = 0" by (simp add: x)
    qed
    thus "(\<Sum>x\<leftarrow>zip (list_of_vec v) ps. lookup (case x of (c, x) \<Rightarrow> monom_mult c 0 x) t) = 0"
      by (metis (mono_tags, lifting) case_prod_conv cond_case_prod_eta)
  qed
qed

lemma row_space_subset_phull:
  "row_to_poly (pps_to_list (Supp (set ps))) ` row_space (polys_to_mat ps) \<subseteq> phull (set ps)"
    (is "?r \<subseteq> ?h")
proof
  fix q
  assume "q \<in> ?r"
  then obtain x where x1: "x \<in> row_space (polys_to_mat ps)"
    and q1: "q = row_to_poly (pps_to_list (Supp (set ps))) x" ..
  from x1 obtain v where v: "v \<in> carrier_vec (dim_row (polys_to_mat ps))" and x: "x = v \<^sub>v* polys_to_mat ps"
    by (rule row_spaceE)
  from v have "v \<in> carrier_vec (length ps)" by (simp only: dim_row_polys_to_mat)
  with x q1 have q: "q = (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. monom_mult c 0 p)"
    by (simp add: vec_times_polys_to_mat)
  show "q \<in> ?h" unfolding q by (rule in_phull_listI)
qed

lemma phull_subset_row_space:
  assumes "distinct ps"
  shows "phull (set ps) \<subseteq> row_to_poly (pps_to_list (Supp (set ps))) ` row_space (polys_to_mat ps)"
    (is "?h \<subseteq> ?r")
proof
  fix q
  assume "q \<in> ?h"
  with assms obtain cs where l: "length cs = length ps" and q: "q = (\<Sum>(c, p)\<leftarrow>zip cs ps. monom_mult c 0 p)"
    by (rule in_phull_listE)
  let ?v = "vec_of_list cs"
  from l have *: "?v \<in> carrier_vec (length ps)" by (simp only: carrier_dim_vec dim_vec_of_list)
  let ?q = "?v \<^sub>v* polys_to_mat ps"
  show "q \<in> ?r"
  proof
    show "q = row_to_poly (pps_to_list (Supp (set ps))) ?q"
      by (simp add: vec_times_polys_to_mat[OF *] q list_of_vec_of_list)
  next
    show "?q \<in> row_space (polys_to_mat ps)" by (rule row_spaceI, rule)
  qed
qed

lemma row_space_eq_phull:
  assumes "distinct ps"
  shows "row_to_poly (pps_to_list (Supp (set ps))) ` row_space (polys_to_mat ps) = phull (set ps)"
  by (rule, fact row_space_subset_phull, rule phull_subset_row_space, fact)

lemma row_space_eq_phull':
  "row_to_poly (pps_to_list (Supp (set ps))) ` row_space (polys_to_mat (remdups ps)) = phull (set ps)"
proof -
  define qs where "qs = remdups ps"
  have *: "set qs = set ps" by (simp add: qs_def)
  have "distinct qs" unfolding qs_def ..
  hence "row_to_poly (pps_to_list (Supp (set qs))) ` row_space (polys_to_mat qs) = phull (set qs)"
    by (rule row_space_eq_phull)
  moreover have "Supp (set qs) = Supp (set ps)" by (simp only: *)
  moreover have "phull (set qs) = phull (set ps)" by (simp only: *)
  ultimately show ?thesis by (simp add: qs_def)
qed

lemma row_space_row_echelon_eq_phull:
  assumes "distinct ps"
  shows "row_to_poly (pps_to_list (Supp (set ps))) ` row_space (row_echelon (polys_to_mat ps)) = phull (set ps)"
  using assms by (simp add: row_space_eq_phull)

lemma lp_row_to_poly_pivot_fun:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)" and "i < dim_row A" and "f i < dim_col A"
  shows "lp ((mat_to_polys (pps_to_list S) A) ! i) = (pps_to_list S) ! (f i)"
proof -
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp add: length_pps_to_list assms(1))
  show ?thesis
  proof (simp add: mat_to_polys_nth[OF assms(3)], rule lp_eqI)
    have "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) = (row A i) $ (f i)"
      by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp_all add: len_ts assms(4))
    also have "... = A $$ (i, f i)" using assms(3) assms(4) by simp
    also have "... = 1" by (rule pivot_funD, rule refl, fact+)
    finally show "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) \<noteq> 0" by simp
  next
    fix s
    assume a: "lookup (row_to_poly ?ts (row A i)) s \<noteq> 0"
    then obtain j where j: "j < length ?ts" and s: "s = ?ts ! j"
      by (rule lookup_row_to_poly_not_zeroE)
    from j have "j < card S" and "j < dim_col A" by (simp only: length_pps_to_list, simp only: len_ts)
    from a have "0 \<noteq> lookup (row_to_poly ?ts (row A i)) (?ts ! j)" by (simp add: s)
    also have "lookup (row_to_poly ?ts (row A i)) (?ts ! j) = (row A i) $ j"
      by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp add: len_ts, fact)
    finally have "A $$ (i, j) \<noteq> 0" using assms(3) \<open>j < dim_col A\<close> by simp
    from _ \<open>j < card S\<close> show "s \<preceq> ?ts ! f i" unfolding s
    proof (rule pps_to_list_nth_leI)
      show "f i \<le> j"
      proof (rule ccontr)
        assume "\<not> f i \<le> j"
        hence "j < f i" by simp
        have "A $$ (i, j) = 0" by (rule pivot_funD, rule refl, fact+)
        with \<open>A $$ (i, j) \<noteq> 0\<close> show False ..
      qed
    qed
  qed
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