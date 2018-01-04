theory Groebner_Macaulay
  imports Power_Products_Fun Reduced_GB Jordan_Normal_Form.Gauss_Jordan_Elimination
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

lemma vec_scalar_mult_fun: "vec n (c \<cdot> f) = c \<cdot>\<^sub>v vec n f"
  by (simp add: scalar_mult_fun_def smult_vec_def, rule vec_cong, rule refl, simp)

definition mult_vec_mat :: "'a vec \<Rightarrow> 'a :: semiring_0 mat \<Rightarrow> 'a vec" (infixl "\<^sub>v*" 70)
  where "v \<^sub>v* A \<equiv> vec (dim_col A) (\<lambda>j. v \<bullet> col A j)"

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
  fix j
  show "v \<bullet> col A j = col A j \<bullet> v" by (rule scalar_prod_comm, simp add: assms)
qed

subsection \<open>More about Matrices\<close>

definition nzrows :: "'a::zero mat \<Rightarrow> 'a vec list"
  where "nzrows A = filter (\<lambda>r. r \<noteq> 0\<^sub>v (dim_col A)) (rows A)"

definition row_space :: "'a mat \<Rightarrow> 'a::semiring_0 vec set"
  where "row_space A = (\<lambda>v. mult_vec_mat v A) ` (carrier_vec (dim_row A))"

definition row_echelon :: "'a mat \<Rightarrow> 'a::field mat"
  where "row_echelon A = fst (gauss_jordan A (1\<^sub>m (dim_row A)))"

subsubsection \<open>@{const nzrows}\<close>

lemma length_nzrows: "length (nzrows A) \<le> dim_row A"
  by (simp add: nzrows_def length_rows[symmetric] del: length_rows)

lemma set_nzrows: "set (nzrows A) = set (rows A) - {0\<^sub>v (dim_col A)}"
  by (auto simp add: nzrows_def)

lemma nzrows_nth_not_zero:
  assumes "i < length (nzrows A)"
  shows "nzrows A ! i \<noteq> 0\<^sub>v (dim_col A)"
  using assms unfolding nzrows_def using nth_mem by force

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

lemma row_not_zero_iff_pivot_fun:
  assumes "pivot_fun A f (dim_col A)" and "i < dim_row (A::'a::zero_neq_one mat)"
  shows "(row A i \<noteq> 0\<^sub>v (dim_col A)) \<longleftrightarrow> (f i < dim_col A)"
proof (simp only: row_eq_zero_iff_pivot_fun[OF assms])
  have "f i \<le> dim_col A" by (rule pivot_funD[where ?f = f], rule refl, fact+)
  thus "(f i \<noteq> dim_col A) = (f i < dim_col A)" by auto
qed

lemma pivot_fun_stabilizes:
  assumes "pivot_fun A f nc" and "i1 \<le> i2" and "i2 < dim_row A" and "nc \<le> f i1"
  shows "f i2 = nc"
proof -
  from assms(2) have "i2 = i1 + (i2 - i1)" by simp
  then obtain k where "i2 = i1 + k" ..
  from assms(3) assms(4) show ?thesis unfolding \<open>i2 = i1 + k\<close>
  proof (induct k arbitrary: i1)
    case 0
    from this(1) have "i1 < dim_row A" by simp
    from _ assms(1) this have "f i1 \<le> nc" by (rule pivot_funD, intro refl)
    with \<open>nc \<le> f i1\<close> show ?case by simp
  next
    case (Suc k)
    from Suc(2) have "Suc (i1 + k) < dim_row A" by simp
    hence "Suc i1 + k < dim_row A" by simp
    hence "Suc i1 < dim_row A" by simp
    hence "i1 < dim_row A" by simp
    have "nc \<le> f (Suc i1)"
    proof -
      have "f i1 < f (Suc i1) \<or> f (Suc i1) = nc" by (rule pivot_funD, rule refl, fact+)
      with Suc(3) show ?thesis by auto
    qed
    with \<open>Suc i1 + k < dim_row A\<close> have "f (Suc i1 + k) = nc" by (rule Suc(1))
    thus ?case by simp
  qed
qed

lemma pivot_fun_mono_strict:
  assumes "pivot_fun A f nc" and "i1 < i2" and "i2 < dim_row A" and "f i1 < nc"
  shows "f i1 < f i2"
proof -
  from assms(2) have "i2 - i1 \<noteq> 0" and "i2 = i1 + (i2 - i1)" by simp_all
  then obtain k where "k \<noteq> 0" and "i2 = i1 + k" ..
  from this(1) assms(3) assms(4) show ?thesis unfolding \<open>i2 = i1 + k\<close>
  proof (induct k arbitrary: i1)
    case 0
    thus ?case by simp
  next
    case (Suc k)
    from Suc(3) have "Suc (i1 + k) < dim_row A" by simp
    hence "Suc i1 + k < dim_row A" by simp
    hence "Suc i1 < dim_row A" by simp
    hence "i1 < dim_row A" by simp
    have *: "f i1 < f (Suc i1)"
    proof -
      have "f i1 < f (Suc i1) \<or> f (Suc i1) = nc" by (rule pivot_funD, rule refl, fact+)
      with Suc(4) show ?thesis by auto
    qed
    show ?case
    proof (simp, cases "k = 0")
      case True
      show "f i1 < f (Suc (i1 + k))" by (simp add: True *)
    next
      case False
      have "f (Suc i1) \<le> f (Suc i1 + k)"
      proof (cases "f (Suc i1) < nc")
        case True
        from False \<open>Suc i1 + k < dim_row A\<close> True have "f (Suc i1) < f (Suc i1 + k)" by (rule Suc(1))
        thus ?thesis by simp
      next
        case False
        hence "nc \<le> f (Suc i1)" by simp
        from assms(1) _ \<open>Suc i1 + k < dim_row A\<close> this have "f (Suc i1 + k) = nc"
          by (rule pivot_fun_stabilizes[where ?f=f], simp)
        moreover have "f (Suc i1) = nc" by (rule pivot_fun_stabilizes[where ?f=f], fact, rule le_refl, fact+)
        ultimately show ?thesis by simp
      qed
      also have "... = f (i1 + Suc k)" by simp
      finally have "f (Suc i1) \<le> f (i1 + Suc k)" .
      with * show "f i1 < f (Suc (i1 + k))" by simp
    qed
  qed
qed

lemma pivot_fun_mono:
  assumes "pivot_fun A f nc" and "i1 \<le> i2" and "i2 < dim_row A"
  shows "f i1 \<le> f i2"
proof -
  from assms(2) have "i1 < i2 \<or> i1 = i2" by auto
  thus ?thesis
  proof
    assume "i1 < i2"
    show ?thesis
    proof (cases "f i1 < nc")
      case True
      from assms(1) \<open>i1 < i2\<close> assms(3) this have "f i1 < f i2" by (rule pivot_fun_mono_strict)
      thus ?thesis by simp
    next
      case False
      hence "nc \<le> f i1" by simp
      from assms(1) _ _ this have "f i1 = nc"
      proof (rule pivot_fun_stabilizes[where ?f=f], simp)
        from assms(2) assms(3) show "i1 < dim_row A" by (rule le_less_trans)
      qed
      moreover have "f i2 = nc" by (rule pivot_fun_stabilizes[where ?f=f], fact+)
      ultimately show ?thesis by simp
    qed
  next
    assume "i1 = i2"
    thus ?thesis by simp
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
  obtains f where "pivot_fun (row_echelon A) f (dim_col (row_echelon A))"
proof -
  let ?B = "1\<^sub>m (dim_row A)"
  have "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  moreover from surj_pair obtain A' B' where *: "gauss_jordan A ?B = (A', B')" by metis
  ultimately have "row_echelon_form A'" by (rule gauss_jordan_row_echelon)
  then obtain f where "pivot_fun A' f (dim_col A')" unfolding row_echelon_form_def ..
  hence "pivot_fun (row_echelon A) f (dim_col (row_echelon A))" by (simp add: row_echelon_def *)
  thus ?thesis ..
qed

lemma distinct_nzrows_row_echelon: "distinct (nzrows (row_echelon A))"
  unfolding nzrows_def
proof (rule distinct_filterI, simp del: dim_row_echelon)
  let ?B = "row_echelon A"
  fix i j::nat
  assume "i < j" and "j < dim_row ?B"
  hence "i \<noteq> j" and "i < dim_row ?B" by simp_all
  assume ri: "row ?B i \<noteq> 0\<^sub>v (dim_col ?B)" and rj: "row ?B j \<noteq> 0\<^sub>v (dim_col ?B)"
  obtain f where pf: "pivot_fun ?B f (dim_col ?B)" by (fact row_echelon_pivot_fun)
  from rj have "f j < dim_col ?B" by (simp only: row_not_zero_iff_pivot_fun[OF pf \<open>j < dim_row ?B\<close>])
  from _ pf \<open>j < dim_row ?B\<close> this \<open>i < dim_row ?B\<close> \<open>i \<noteq> j\<close> have *: "?B $$ (i, f j) = 0"
    by (rule pivot_funD(5), intro refl)
  show "row ?B i \<noteq> row ?B j"
  proof
    assume "row ?B i = row ?B j"
    hence "row ?B i $ (f j) = row ?B j $ (f j)" by simp
    with \<open>i < dim_row ?B\<close> \<open>j < dim_row ?B\<close> \<open>f j < dim_col ?B\<close> have "?B $$ (i, f j) = ?B $$ (j, f j)" by simp
    also from _ pf \<open>j < dim_row ?B\<close> \<open>f j < dim_col ?B\<close> have "... = 1" by (rule pivot_funD, intro refl)
    finally show False by (simp add: *)
  qed
qed

subsection \<open>Function @{term Supp}\<close>

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

definition polys_to_mat :: "'a list \<Rightarrow> ('a, 'b::zero) poly_mapping list \<Rightarrow> 'b mat" where
  "polys_to_mat ts ps = mat_of_row_fun (length ps) (length ts) (\<lambda>i. (poly_to_row ts (ps ! i)))"

definition list_to_fun :: "'a list \<Rightarrow> ('b::zero) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "list_to_fun ts cs t = (case map_of (zip ts cs) t of Some c \<Rightarrow> c | None \<Rightarrow> 0)"

definition list_to_poly :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a, 'b::zero) poly_mapping" where
  "list_to_poly ts cs = Abs_poly_mapping (list_to_fun ts cs)"

definition row_to_poly :: "'a list \<Rightarrow> 'b vec \<Rightarrow> ('a, 'b::zero) poly_mapping" where
  "row_to_poly ts r = list_to_poly ts (list_of_vec r)"

definition mat_to_polys :: "'a list \<Rightarrow> 'b mat \<Rightarrow> ('a, 'b::zero) poly_mapping list" where
  "mat_to_polys ts A = map (row_to_poly ts) (rows A)"

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
  assumes "keys p \<subseteq> set ts"
  shows "row_to_poly ts (c \<cdot>\<^sub>v (poly_to_row ts p)) = monom_mult c 0 p"
proof -
  have eq: "(vec (length ts) (\<lambda>i. c * poly_to_row ts p $ i)) =
        (vec (length ts) (\<lambda>i. c * lookup p (ts ! i)))"
    by (rule vec_cong, rule, simp only: poly_to_row_index)
  have *: "list_to_fun ts (list_of_vec (c \<cdot>\<^sub>v (poly_to_row ts p))) = (\<lambda>t. c * lookup p t)"
  proof (rule, simp add: list_to_fun_def smult_vec_def dim_poly_to_row eq,
        simp add: list_of_vec_vec map_upt[of "\<lambda>x. c * lookup p x"] map_of_zip_map, rule)
    fix t
    assume "t \<notin> set ts"
    with assms(1) have "t \<notin> keys p" by auto
    thus "c * lookup p t = 0" by simp
  qed
  have **: "lookup (Abs_poly_mapping (list_to_fun ts (list_of_vec (c \<cdot>\<^sub>v (poly_to_row ts p))))) =
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
  assumes "keys p \<subseteq> set ts"
  shows "row_to_poly ts (poly_to_row ts p) = (p::('a, 'b::semiring_1) poly_mapping)"
proof -
  have "1 \<cdot>\<^sub>v (poly_to_row ts p) = poly_to_row ts p" by simp
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

lemma list_to_fun_empty[simp]: "list_to_fun [] cs = 0"
  by (simp only: zero_fun_def, rule, simp add: list_to_fun_def)

lemma list_to_poly_empty[simp]: "list_to_poly [] cs = 0"
  by (rule poly_mapping_eqI, simp add: lookup_list_to_poly)

lemma row_to_poly_empty[simp]: "row_to_poly [] r = 0"
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

lemma row_to_poly_zero[simp]: "row_to_poly ts (0\<^sub>v (length ts)) = 0"
proof -
  have eq: "map (\<lambda>_. 0) [0..<length ts] = map (\<lambda>_. 0) ts" by (simp add: map_replicate_const)
  show ?thesis
    by (simp add: row_to_poly_def zero_vec_def list_of_vec_vec, rule poly_mapping_eqI,
      simp add: lookup_list_to_poly list_to_fun_def eq map_of_zip_map)
qed

lemma row_to_poly_zeroD:
  assumes "distinct ts" and "dim_vec r = length ts" and "row_to_poly ts r = 0"
  shows "r = 0\<^sub>v (length ts)"
proof (rule, simp_all add: assms(2))
  fix i
  assume "i < length ts"
  from assms(3) have "0 = lookup (row_to_poly ts r) (ts ! i)" by simp
  also from assms(1) assms(2) \<open>i < length ts\<close> have "... = r $ i" by (rule lookup_row_to_poly)
  finally show "r $ i = 0" by simp
qed

lemma row_to_poly_inj:
  assumes "distinct ts" and "dim_vec r1 = length ts" and "dim_vec r2 = length ts"
    and "row_to_poly ts r1 = row_to_poly ts r2"
  shows "r1 = r2"
proof (rule, simp_all add: assms(2) assms(3))
  fix i
  assume "i < length ts"
  have "r1 $ i = lookup (row_to_poly ts r1) (ts ! i)"
    by (simp only: lookup_row_to_poly[OF assms(1) assms(2) \<open>i < length ts\<close>])
  also from assms(4) have "... = lookup (row_to_poly ts r2) (ts ! i)" by simp
  also from assms(1) assms(3) \<open>i < length ts\<close> have "... = r2 $ i" by (rule lookup_row_to_poly)
  finally show "r1 $ i = r2 $ i" .
qed

lemma row_to_poly_vec_plus:
  assumes "distinct ts" and "length ts = n"
  shows "row_to_poly ts (vec n (f1 + f2)) = row_to_poly ts (vec n f1) + row_to_poly ts (vec n f2)"
proof (rule poly_mapping_eqI)
  fix t
  show "lookup (row_to_poly ts (vec n (f1 + f2))) t =
         lookup (row_to_poly ts (vec n f1) + row_to_poly ts (vec n f2)) t"
    (is "lookup ?l t = lookup (?r1 + ?r2) t")
  proof (cases "t \<in> set ts")
    case True
    then obtain j where j: "j < length ts" and t: "t = ts ! j" by (metis in_set_conv_nth)
    have d1: "dim_vec (vec n f1) = length ts" and d2: "dim_vec (vec n f2) = length ts"
      and da: "dim_vec (vec n (f1 + f2)) = length ts" by (simp_all add: assms(2))
    from j have j': "j < n" by (simp only: assms(2))
    show ?thesis
      by (simp only: t lookup_add lookup_row_to_poly[OF assms(1) d1 j]
              lookup_row_to_poly[OF assms(1) d2 j] lookup_row_to_poly[OF assms(1) da j] index_vec[OF j'],
             simp only: plus_fun_def)
  next
    case False
    with keys_row_to_poly[of ts "vec n (f1 + f2)"] keys_row_to_poly[of ts "vec n f1"]
      keys_row_to_poly[of ts "vec n f2"] have "t \<notin> keys ?l" and "t \<notin> keys ?r1" and "t \<notin> keys ?r2"
      by auto
    from this(2) this(3) have "t \<notin> keys (?r1 + ?r2)" using keys_add_subset[of ?r1 ?r2] by auto
    with \<open>t \<notin> keys ?l\<close> show ?thesis by simp
  qed
qed

lemma row_to_poly_vec_sum:
  assumes "distinct ts" and "length ts = n"
  shows "row_to_poly ts (vec n (\<lambda>j. \<Sum>i\<in>I. f i j)) = (\<Sum>i\<in>I. row_to_poly ts (vec n (f i)))"
proof (cases "finite I")
  case True
  thus ?thesis
  proof (induct I)
    case empty
    thus ?case by (simp add: zero_vec_def[symmetric] assms(2)[symmetric])
  next
    case (insert x I)
    have "row_to_poly ts (vec n (\<lambda>j. \<Sum>i\<in>insert x I. f i j)) = row_to_poly ts (vec n (\<lambda>j. f x j + (\<Sum>i\<in>I. f i j)))"
      by (simp only: sum.insert[OF insert(1) insert(2)])
    also have "... = row_to_poly ts (vec n (f x + (\<lambda>j. (\<Sum>i\<in>I. f i j))))" by (simp only: plus_fun_def)
    also from assms have "... = row_to_poly ts (vec n (f x)) + row_to_poly ts (vec n (\<lambda>j. (\<Sum>i\<in>I. f i j)))"
      by (rule row_to_poly_vec_plus)
    also have "... = row_to_poly ts (vec n (f x)) + (\<Sum>i\<in>I. row_to_poly ts (vec n (f i)))"
      by (simp only: insert(3))
    also have "... = (\<Sum>i\<in>insert x I. row_to_poly ts (vec n (f i)))"
      by (simp only: sum.insert[OF insert(1) insert(2)])
    finally show ?case .
  qed
next
  case False
  thus ?thesis by (simp add: zero_vec_def[symmetric] assms(2)[symmetric])
qed

lemma row_to_poly_smult:
  assumes "distinct ts" and "dim_vec r = length ts"
  shows "row_to_poly ts (c \<cdot>\<^sub>v r) = monom_mult c 0 (row_to_poly ts r)"
proof (rule poly_mapping_eqI, simp only: lookup_monom_mult_const)
  fix t
  show "lookup (row_to_poly ts (c \<cdot>\<^sub>v r)) t = c * lookup (row_to_poly ts r) t" (is "lookup ?l t = c * lookup ?r t")
  proof (cases "t \<in> set ts")
    case True
    then obtain j where j: "j < length ts" and t: "t = ts ! j" by (metis in_set_conv_nth)
    from assms(2) have dm: "dim_vec (c \<cdot>\<^sub>v r) = length ts" by simp
    from j have j': "j < dim_vec r" by (simp only: assms(2))
    show ?thesis
      by (simp add: t lookup_row_to_poly[OF assms j] lookup_row_to_poly[OF assms(1) dm j] index_smult_vec(1)[OF j'])
  next
    case False
    with keys_row_to_poly[of ts "c \<cdot>\<^sub>v r"] keys_row_to_poly[of ts r] have
      "t \<notin> keys ?l" and "t \<notin> keys ?r" by auto
    thus ?thesis by simp
  qed
qed

lemma poly_to_row_empty[simp]: "poly_to_row [] p = vec 0 f"
proof -
  have "dim_vec (poly_to_row [] p) = 0" by (simp add: dim_poly_to_row)
  thus ?thesis by auto
qed

lemma polys_to_mat_empty[simp]: "polys_to_mat ts [] = mat 0 (length ts) f"
  by (simp add: polys_to_mat_def mat_eq_iff)

lemma dim_row_polys_to_mat[simp]: "dim_row (polys_to_mat ts ps) = length ps"
  by (simp add: polys_to_mat_def)

lemma dim_col_polys_to_mat[simp]: "dim_col (polys_to_mat ts ps) = length ts"
  by (simp add: polys_to_mat_def)

lemma polys_to_mat_index:
  assumes "i < length ps" and "j < length ts"
  shows "(polys_to_mat ts ps) $$ (i, j) = lookup (ps ! i) (ts ! j)"
  by (simp only: polys_to_mat_def index_mat(2)[OF assms], rule poly_to_row_index,
      simp only: assms(2))

lemma row_polys_to_mat:
  assumes "i < length ps"
  shows "row (polys_to_mat ts ps) i = poly_to_row ts (ps ! i)"
  unfolding polys_to_mat_def
  by (rule row_mat_of_row_fun, fact assms, simp only: dim_poly_to_row)

lemma col_polys_to_mat:
  assumes "j < length ts"
  shows "col (polys_to_mat ts ps) j = vec_of_list (map (\<lambda>p. lookup p (ts ! j)) ps)"
  by (simp add: vec_of_list_alt col_def, rule vec_cong, rule refl, simp add: polys_to_mat_index assms)

lemma length_mat_to_polys[simp]: "length (mat_to_polys ts A) = dim_row A"
  by (simp add: mat_to_polys_def mat_to_list_def)

lemma mat_to_polys_nth:
  assumes "i < dim_row A"
  shows "(mat_to_polys ts A) ! i = row_to_poly ts (row A i)"
proof -
  from assms have "i < length (rows A)" by (simp only: length_rows)
  thus ?thesis by (simp add: mat_to_polys_def)
qed

lemma Supp_mat_to_polys: "Supp (set (mat_to_polys ts A)) \<subseteq> set ts"
proof
  fix t
  assume "t \<in> Supp (set (mat_to_polys ts A))"
  then obtain p where "p \<in> set (mat_to_polys ts A)" and t: "t \<in> keys p" by (rule in_SuppE)
  from this(1) obtain i where "i < length (mat_to_polys ts A)" and p: "p = (mat_to_polys ts A) ! i"
    by (metis in_set_conv_nth)
  from this(1) have "i < dim_row A" by simp
  with p have "p = row_to_poly ts (row A i)" by (simp only: mat_to_polys_nth)
  with t have "t \<in> keys (row_to_poly ts (row A i))" by simp
  also have "... \<subseteq> set ts" by (fact keys_row_to_poly)
  finally show "t \<in> set ts" .
qed

lemma polys_to_mat_to_polys:
  assumes "Supp (set ps) \<subseteq> set ts"
  shows "mat_to_polys ts (polys_to_mat ts ps) = (ps::('a, 'b::semiring_1) poly_mapping list)"
proof (simp add: mat_to_polys_def mat_to_list_def, rule nth_equalityI, simp_all, intro allI impI)
  fix i
  assume "i < length ps"
  have *: "keys (ps ! i) \<subseteq> set ts"
    using \<open>i < length ps\<close> assms keys_subset_Supp nth_mem by blast
  show "row_to_poly ts (row (polys_to_mat ts ps) i) = ps ! i"
    by (simp only: row_polys_to_mat[OF \<open>i < length ps\<close>] poly_to_row_to_poly[OF *])
qed

lemma mat_to_polys_to_mat:
  assumes "distinct ts" and "length ts = dim_col A"
  shows "(polys_to_mat ts (mat_to_polys ts A)) = A"
proof
  fix i j
  assume i: "i < dim_row A" and j: "j < dim_col A"
  hence i': "i < length (mat_to_polys ts A)" and j': "j < length ts" by (simp, simp only: assms(2))
  have r: "dim_vec (row A i) = length ts" by (simp add: assms(2))
  show "polys_to_mat ts (mat_to_polys ts A) $$ (i, j) = A $$ (i, j)"
    by (simp only: polys_to_mat_index[OF i' j'] mat_to_polys_nth[OF \<open>i < dim_row A\<close>]
        lookup_row_to_poly[OF assms(1) r j'] index_row(1)[OF i j])
qed (simp_all add: assms)

subsection \<open>Properties of Macaulay Matrices\<close>

lemma row_to_poly_vec_times:
  assumes "distinct ts" and "length ts = dim_col A"
  shows "row_to_poly ts (v \<^sub>v* A) = (\<Sum>i=0..<dim_row A. monom_mult (v $ i) 0 (row_to_poly ts (row A i)))"
proof (simp add: mult_vec_mat_def scalar_prod_def row_to_poly_vec_sum[OF assms], rule sum.cong, rule)
  fix i
  assume "i \<in> {0..<dim_row A}"
  hence "i < dim_row A" by simp
  have "dim_vec (row A i) = length ts" by (simp add: assms(2))
  have *: "vec (dim_col A) (\<lambda>j. col A j $ i) = vec (dim_col A) (\<lambda>j. A $$ (i, j))"
    by (rule vec_cong, rule refl, simp add: \<open>i < dim_row A\<close>)
  have "(\<lambda>j. v $ i * col A j $ i) = v $ i \<cdot> (\<lambda>j. col A j $ i)" by (simp add: scalar_mult_fun_def)
  hence "vec (dim_col A) (\<lambda>j. v $ i * col A j $ i) = v $ i \<cdot>\<^sub>v vec (dim_col A) (\<lambda>j. col A j $ i)"
    by (simp only: vec_scalar_mult_fun)
  also have "... = v $ i \<cdot>\<^sub>v (row A i)" by (simp only: * row_def[symmetric])
  finally show "row_to_poly ts (vec (dim_col A) (\<lambda>j. v $ i * col A j $ i)) =
                  monom_mult (v $ i) 0 (row_to_poly ts (row A i))"
    by (simp add: row_to_poly_smult[OF assms(1) \<open>dim_vec (row A i) = length ts\<close>])
qed

lemma vec_times_polys_to_mat:
  assumes "Supp (set ps) \<subseteq> set ts" and "v \<in> carrier_vec (length ps)"
  shows "row_to_poly ts (v \<^sub>v* (polys_to_mat ts ps)) = (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. monom_mult c 0 p)"
    (is "?l = ?r")
proof -
  from assms have *: "dim_vec v = length ps" by (simp only: carrier_dim_vec)
  have eq: "map (\<lambda>i. v \<bullet> col (polys_to_mat ts ps) i) [0..<length ts] =
        map (\<lambda>s. v \<bullet> (vec_of_list (map (\<lambda>p. lookup p s) ps))) ts"
  proof (rule nth_equalityI, simp, intro allI impI, simp)
    fix i
    assume "i < length ts"
    hence "col (polys_to_mat ts ps) i = vec_of_list (map (\<lambda>p. lookup p (ts ! i)) ps)"
      by (rule col_polys_to_mat)
    thus "v \<bullet> col (polys_to_mat ts ps) i = v \<bullet> vec_of_list (map (\<lambda>p. lookup p (ts ! i)) ps)" by simp
  qed
  show ?thesis
  proof (rule poly_mapping_eqI, simp add: mult_vec_mat_def row_to_poly_def lookup_list_to_poly
      list_of_vec_vec eq list_to_fun_def map_of_zip_map lookup_sum_list o_def, intro conjI impI)
    fix t
    assume "t \<in> set ts"
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
    assume "t \<notin> set ts"
    with assms(1) have "t \<notin> Supp (set ps)" by auto
    have "(\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. lookup (monom_mult c 0 p) t) = 0"
    proof (rule sum_list_zeroI, rule, simp add: lookup_monom_mult_const)
      fix x
      assume "x \<in> (\<lambda>(c, p). c * lookup p t) ` set (zip (list_of_vec v) ps)"
      then obtain c p where cp: "(c, p) \<in> set (zip (list_of_vec v) ps)"
        and x: "x = c * lookup p t" by auto
      from cp have "p \<in> set ps" by (rule set_zip_rightD)
      with \<open>t \<notin> Supp (set ps)\<close> have "t \<notin> keys p" by (auto intro: in_SuppI)
      thus "x = 0" by (simp add: x)
    qed
    thus "(\<Sum>x\<leftarrow>zip (list_of_vec v) ps. lookup (case x of (c, x) \<Rightarrow> monom_mult c 0 x) t) = 0"
      by (metis (mono_tags, lifting) case_prod_conv cond_case_prod_eta)
  qed
qed

lemma row_space_subset_phull:
  assumes "Supp (set ps) \<subseteq> set ts"
  shows "row_to_poly ts ` row_space (polys_to_mat ts ps) \<subseteq> phull (set ps)"
    (is "?r \<subseteq> ?h")
proof
  fix q
  assume "q \<in> ?r"
  then obtain x where x1: "x \<in> row_space (polys_to_mat ts ps)"
    and q1: "q = row_to_poly ts x" ..
  from x1 obtain v where v: "v \<in> carrier_vec (dim_row (polys_to_mat ts ps))" and x: "x = v \<^sub>v* polys_to_mat ts ps"
    by (rule row_spaceE)
  from v have "v \<in> carrier_vec (length ps)" by (simp only: dim_row_polys_to_mat)
  with x q1 have q: "q = (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. monom_mult c 0 p)"
    by (simp add: vec_times_polys_to_mat[OF assms])
  show "q \<in> ?h" unfolding q by (rule in_phull_listI)
qed

lemma phull_subset_row_space:
  assumes "Supp (set ps) \<subseteq> set ts"
  shows "phull (set ps) \<subseteq> row_to_poly ts ` row_space (polys_to_mat ts ps)"
    (is "?h \<subseteq> ?r")
proof
  fix q
  assume "q \<in> ?h"
  then obtain cs where l: "length cs = length ps" and q: "q = (\<Sum>(c, p)\<leftarrow>zip cs ps. monom_mult c 0 p)"
    by (rule in_phull_listE)
  let ?v = "vec_of_list cs"
  from l have *: "?v \<in> carrier_vec (length ps)" by (simp only: carrier_dim_vec dim_vec_of_list)
  let ?q = "?v \<^sub>v* polys_to_mat ts ps"
  show "q \<in> ?r"
  proof
    show "q = row_to_poly ts ?q"
      by (simp add: vec_times_polys_to_mat[OF assms *] q list_of_vec_of_list)
  next
    show "?q \<in> row_space (polys_to_mat ts ps)" by (rule row_spaceI, rule)
  qed
qed

lemma row_space_eq_phull:
  assumes "Supp (set ps) \<subseteq> set ts"
  shows "row_to_poly ts ` row_space (polys_to_mat ts ps) = phull (set ps)"
  by (rule, rule row_space_subset_phull, fact, rule phull_subset_row_space, fact)

lemma row_space_row_echelon_eq_phull:
  assumes "Supp (set ps) \<subseteq> set ts"
  shows "row_to_poly ts ` row_space (row_echelon (polys_to_mat ts ps)) = phull (set ps)"
  by (simp add: row_space_eq_phull[OF assms])

lemma phull_row_echelon:
  assumes "Supp (set ps) \<subseteq> set ts" and "distinct ts"
  shows "phull (set (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))) = phull (set ps)"
proof -
  have len_ts: "length ts = dim_col (row_echelon (polys_to_mat ts ps))" by simp
  have *: "Supp (set (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))) \<subseteq> set ts"
    by (fact Supp_mat_to_polys)
  show ?thesis
    by (simp only: row_space_eq_phull[OF *, symmetric] mat_to_polys_to_mat[OF assms(2) len_ts],
        rule row_space_row_echelon_eq_phull, fact)
qed

lemma pideal_row_echelon:
  assumes "Supp (set ps) \<subseteq> set ts" and "distinct ts"
  shows "pideal (set (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))) = pideal (set ps)"
    (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
    by (rule pideal_subset_pidealI, rule subset_trans, rule generator_subset_phull,
      simp only: phull_row_echelon[OF assms] phull_subset_pideal)
next
  show "?r \<subseteq> ?l"
    by (rule pideal_subset_pidealI, rule subset_trans, rule generator_subset_phull,
        simp only: phull_row_echelon[OF assms, symmetric] phull_subset_pideal)
qed

lemma lp_row_to_poly_pivot_fun:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i < dim_row A" and "f i < dim_col A"
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

lemma lc_row_to_poly_pivot_fun:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i < dim_row A" and "f i < dim_col A"
  shows "lc ((mat_to_polys (pps_to_list S) A) ! i) = 1"
proof -
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp only: length_pps_to_list assms(1))
  have "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) = (row A i) $ (f i)"
    by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp_all add: len_ts assms(4))
  also have "... = A $$ (i, f i)" using assms(3) assms(4) by simp
  finally have eq: "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) = A $$ (i, f i)" .
  show ?thesis
    by (simp only: lc_def lp_row_to_poly_pivot_fun[OF assms], simp only: mat_to_polys_nth[OF assms(3)] eq,
        rule pivot_funD, rule refl, fact+)
qed

lemma lp_row_to_poly_pivot_fun_less:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i1 < i2" and "i2 < dim_row A" and "f i1 < dim_col A" and "f i2 < dim_col A"
  shows "(pps_to_list S) ! (f i2) \<prec> (pps_to_list S) ! (f i1)"
proof -
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp add: length_pps_to_list assms(1))
  from assms(3) assms(4) have "i1 < dim_row A" by simp
  show ?thesis
    by (rule pps_to_list_nth_lessI, rule pivot_fun_mono_strict[where ?f=f], fact, fact, fact, fact,
        simp only: assms(1) assms(6))
qed

lemma lp_row_to_poly_pivot_fun_eqD:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i1 < dim_row A" and "i2 < dim_row A" and "f i1 < dim_col A" and "f i2 < dim_col A"
    and "(pps_to_list S) ! (f i1) = (pps_to_list S) ! (f i2)"
  shows "i1 = i2"
proof (rule linorder_cases)
  assume "i1 < i2"
  from assms(1) assms(2) this assms(4) assms(5) assms(6) have
    "(pps_to_list S) ! (f i2) \<prec> (pps_to_list S) ! (f i1)" by (rule lp_row_to_poly_pivot_fun_less)
  with assms(7) show ?thesis by auto
next
  assume "i2 < i1"
  from assms(1) assms(2) this assms(3) assms(6) assms(5) have
    "(pps_to_list S) ! (f i1) \<prec> (pps_to_list S) ! (f i2)" by (rule lp_row_to_poly_pivot_fun_less)
  with assms(7) show ?thesis by auto
qed

lemma lp_row_to_poly_pivot_in_keysD:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i1 < dim_row A" and "i2 < dim_row A" and "f i1 < dim_col A"
    and "(pps_to_list S) ! (f i1) \<in> keys ((mat_to_polys (pps_to_list S) A) ! i2)"
  shows "i1 = i2"
proof (rule ccontr)
  assume "i1 \<noteq> i2"
  hence "i2 \<noteq> i1" by simp
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp only: length_pps_to_list assms(1))
  from assms(6) have "0 \<noteq> lookup (row_to_poly ?ts (row A i2)) (?ts ! (f i1))"
    by (simp add: mat_to_polys_nth[OF assms(4)])
  also have "lookup (row_to_poly ?ts (row A i2)) (?ts ! (f i1)) = (row A i2) $ (f i1)"
    by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp_all add: len_ts assms(5))
  finally have "A $$ (i2, f i1) \<noteq> 0" using assms(4) assms(5) by simp
  moreover have "A $$ (i2, f i1) = 0" by (rule pivot_funD(5), rule refl, fact+)
  ultimately show False ..
qed

lemma lp_row_space_pivot_fun:
  assumes "card S = dim_col (A::'b::semiring_1_no_zero_divisors mat)" and "pivot_fun A f (dim_col A)"
    and "p \<in> row_to_poly (pps_to_list S) ` row_space A" and "p \<noteq> 0"
  shows "lp p \<in> lp_set (set (mat_to_polys (pps_to_list S) A))"
proof -
  let ?ts = "pps_to_list S"
  let ?I = "{0..<dim_row A}"
  have len_ts: "length ?ts = dim_col A" by (simp add: length_pps_to_list assms(1))
  from assms(3) obtain x where "x \<in> row_space A" and p: "p = row_to_poly ?ts x" ..
  from this(1) obtain v where "v \<in> carrier_vec (dim_row A)" and x: "x = v \<^sub>v* A" by (rule row_spaceE)
  
  have p': "p = (\<Sum>i\<in>?I. monom_mult (v $ i) 0 (row_to_poly ?ts (row A i)))"
    unfolding p x by (rule row_to_poly_vec_times, fact distinct_pps_to_list, fact len_ts)

  have "lp (\<Sum>i = 0..<dim_row A. monom_mult (v $ i) 0 (row_to_poly ?ts (row A i)))
          \<in> lp_set ((\<lambda>i. monom_mult (v $ i) 0 (row_to_poly ?ts (row A i))) ` {0..<dim_row A})"
  proof (rule lp_sum_distinct_in_lp_set, rule, simp add: p'[symmetric] \<open>p \<noteq> 0\<close>)
    fix i1 i2
    let ?p1 = "monom_mult (v $ i1) 0 (row_to_poly ?ts (row A i1))"
    let ?p2 = "monom_mult (v $ i2) 0 (row_to_poly ?ts (row A i2))"
    assume "i1 \<in> ?I" and "i2 \<in> ?I"
    hence "i1 < dim_row A" and "i2 < dim_row A" by simp_all

    assume "?p1 \<noteq> 0"
    hence "v $ i1 \<noteq> 0" and "row_to_poly ?ts (row A i1) \<noteq> 0"
      by (auto simp add: monom_mult_left0 monom_mult_right0)
    hence "row A i1 \<noteq> 0\<^sub>v (length ?ts)" by auto
    hence "f i1 < dim_col A"
      by (simp add: len_ts row_not_zero_iff_pivot_fun[OF assms(2) \<open>i1 < dim_row A\<close>])
    have "lp ?p1 = 0 + lp (row_to_poly ?ts (row A i1))" by (rule lp_mult, fact+)
    also have "... = lp (row_to_poly ?ts (row A i1))" by simp
    also have "... = lp ((mat_to_polys ?ts A) ! i1)" by (simp only: mat_to_polys_nth[OF \<open>i1 < dim_row A\<close>])
    also have "... = ?ts ! (f i1)" by (rule lp_row_to_poly_pivot_fun, fact+)
    finally have lp1: "lp ?p1 = ?ts ! (f i1)" .

    assume "?p2 \<noteq> 0"
    hence "v $ i2 \<noteq> 0" and "row_to_poly ?ts (row A i2) \<noteq> 0"
      by (auto simp add: monom_mult_left0 monom_mult_right0)
    hence "row A i2 \<noteq> 0\<^sub>v (length ?ts)" by auto
    hence "f i2 < dim_col A"
      by (simp add: len_ts row_not_zero_iff_pivot_fun[OF assms(2) \<open>i2 < dim_row A\<close>])
    have "lp ?p2 = 0 + lp (row_to_poly ?ts (row A i2))" by (rule lp_mult, fact+)
    also have "... = lp (row_to_poly ?ts (row A i2))" by simp
    also have "... = lp ((mat_to_polys ?ts A) ! i2)" by (simp only: mat_to_polys_nth[OF \<open>i2 < dim_row A\<close>])
    also have "... = ?ts ! (f i2)" by (rule lp_row_to_poly_pivot_fun, fact+)
    finally have lp2: "lp ?p2 = ?ts ! (f i2)" .

    assume "lp ?p1 = lp ?p2"
    with assms(1) assms(2) \<open>i1 < dim_row A\<close> \<open>i2 < dim_row A\<close> \<open>f i1 < dim_col A\<close> \<open>f i2 < dim_col A\<close>
    show "i1 = i2" unfolding lp1 lp2 by (rule lp_row_to_poly_pivot_fun_eqD)
  qed
  also have "... \<subseteq> lp_set ((\<lambda>i. row_to_poly ?ts (row A i)) ` {0..<dim_row A})"
  proof
    fix s
    assume "s \<in> lp_set ((\<lambda>i. monom_mult (v $ i) 0 (row_to_poly ?ts (row A i))) ` {0..<dim_row A})"
    then obtain f
      where "f \<in> (\<lambda>i. monom_mult (v $ i) 0 (row_to_poly ?ts (row A i))) ` {0..<dim_row A}"
        and "f \<noteq> 0" and "lp f = s" by (rule lp_setE)
    from this(1) obtain i where "i \<in> {0..<dim_row A}"
      and f: "f = monom_mult (v $ i) 0 (row_to_poly ?ts (row A i))" ..
    from this(2) \<open>f \<noteq> 0\<close> have "v $ i \<noteq> 0" and **: "row_to_poly ?ts (row A i) \<noteq> 0"
      by (auto simp add: monom_mult_left0 monom_mult_right0)
    from \<open>lp f = s\<close> have "s = lp (monom_mult (v $ i) 0 (row_to_poly ?ts (row A i)))" by (simp only: f)
    also from \<open>v $ i \<noteq> 0\<close> ** have "... = 0 + lp (row_to_poly ?ts (row A i))" by (rule lp_mult)
    also have "... = lp (row_to_poly ?ts (row A i))" by simp
    finally have s: "s = lp (row_to_poly ?ts (row A i))" .
    show "s \<in> lp_set ((\<lambda>i. row_to_poly ?ts (row A i)) ` {0..<dim_row A})"
      unfolding s by (rule lp_setI, rule, rule refl, fact+)
  qed
  also have "... = lp_set ((\<lambda>r. row_to_poly ?ts r) ` (row A ` {0..<dim_row A}))"
    by (simp only: image_comp o_def)
  also have "... = lp_set (set (map (\<lambda>r. row_to_poly ?ts r) (map (row A) [0..<dim_row A])))"
    by (metis image_set set_upt)
  also have "... = lp_set (set (mat_to_polys ?ts A))" by (simp only: mat_to_polys_def rows_def)
  finally show ?thesis unfolding p' .
qed

subsection \<open>Gr\"obner Bases\<close>

definition Macaulay_mat :: "('a, 'b) poly_mapping list \<Rightarrow> 'b::field mat"
  where "Macaulay_mat ps = polys_to_mat (pps_to_list (Supp (set ps))) ps"

definition Macaulay_list :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::field) poly_mapping list"
  where "Macaulay_list ps =
     filter (\<lambda>p. p \<noteq> 0) (mat_to_polys (pps_to_list (Supp (set ps))) (row_echelon (Macaulay_mat ps)))"

definition reduced_Macaulay_list :: "('a, 'b) poly_mapping list \<Rightarrow> ('a, 'b::field) poly_mapping list"
  where "reduced_Macaulay_list ps = comp_min_basis_aux (Macaulay_list ps) []"

text \<open>It is important to note that in @{const reduced_Macaulay_list} there is no need to remove
  duplicate leading power-products (because there are none), nor to make the polynomials monic
  (because they already are).\<close>

lemma dim_Macaulay_mat[simp]:
  "dim_row (Macaulay_mat ps) = length ps"
  "dim_col (Macaulay_mat ps) = card (Supp (set ps))"
  by (simp_all add: Macaulay_mat_def length_pps_to_list)

lemma set_Macaulay_list:
  "set (Macaulay_list ps) =
      set (mat_to_polys (pps_to_list (Supp (set ps))) (row_echelon (Macaulay_mat ps))) - {0}"
  by (auto simp add: Macaulay_list_def)

lemma in_Macaulay_listE:
  assumes "p \<in> set (Macaulay_list ps)"
    and "pivot_fun (row_echelon (Macaulay_mat ps)) f (dim_col (row_echelon (Macaulay_mat ps)))"
  obtains i where "i < dim_row (row_echelon (Macaulay_mat ps))"
    and "p = (mat_to_polys (pps_to_list (Supp (set ps))) (row_echelon (Macaulay_mat ps))) ! i"
    and "f i < dim_col (row_echelon (Macaulay_mat ps))"
proof -
  let ?ts = "pps_to_list (Supp (set ps))"
  let ?A = "Macaulay_mat ps"
  let ?E = "row_echelon ?A"

  from assms(1) have "p \<in> set (mat_to_polys ?ts ?E) - {0}" by (simp add: set_Macaulay_list)
  hence "p \<in> set (mat_to_polys ?ts ?E)" and "p \<noteq> 0" by auto
  from this(1) obtain i where "i < length (mat_to_polys ?ts ?E)" and p: "p = (mat_to_polys ?ts ?E) ! i"
    by (metis in_set_conv_nth)
  from this(1) have "i < dim_row ?E" and "i < dim_row ?A" by simp_all

  from this(1) p show ?thesis
  proof
    from \<open>p \<noteq> 0\<close> have "0 \<noteq> (mat_to_polys ?ts ?E) ! i" by (simp only: p)
    also have "(mat_to_polys ?ts ?E) ! i = row_to_poly ?ts (row ?E i)"
      by (simp only: Macaulay_list_def mat_to_polys_nth[OF \<open>i < dim_row ?E\<close>])
    finally have *: "row_to_poly ?ts (row ?E i) \<noteq> 0" by simp
    have "row ?E i \<noteq> 0\<^sub>v (length ?ts)"
    proof
      assume "row ?E i = 0\<^sub>v (length ?ts)"
      with * show False by simp
    qed
    hence "row ?E i \<noteq> 0\<^sub>v (dim_col ?E)" by (simp add: length_pps_to_list)
    thus "f i < dim_col ?E"
      by (simp only: row_not_zero_iff_pivot_fun[OF assms(2) \<open>i < dim_row ?E\<close>])
  qed
qed

lemma phull_Macaulay_list: "phull (set (Macaulay_list ps)) = phull (set ps)"
proof -
  have *: "Supp (set ps) \<subseteq> set (pps_to_list (Supp (set ps)))"
    by (simp add: Supp_finite set_pps_to_list)
  have "phull (set (Macaulay_list ps)) =
          phull (set (mat_to_polys (pps_to_list (Supp (set ps))) (row_echelon (Macaulay_mat ps))))"
    by (simp only: set_Macaulay_list phull_minus_singleton_zero)
  also have "... = phull (set ps)"
    by (simp only: Macaulay_mat_def phull_row_echelon[OF * distinct_pps_to_list])
  finally show ?thesis .
qed

lemma pideal_Macaulay_list: "pideal (set (Macaulay_list ps)) = pideal (set ps)"
proof -
  have *: "Supp (set ps) \<subseteq> set (pps_to_list (Supp (set ps)))"
    by (simp add: Supp_finite set_pps_to_list)
  have "pideal (set (Macaulay_list ps)) =
          pideal (set (mat_to_polys (pps_to_list (Supp (set ps))) (row_echelon (Macaulay_mat ps))))"
    by (simp only: set_Macaulay_list pideal_minus_singleton_zero)
  also have "... = pideal (set ps)"
    by (simp only: Macaulay_mat_def pideal_row_echelon[OF * distinct_pps_to_list])
  finally show ?thesis .
qed

lemma Macaulay_list_is_monic_set: "is_monic_set (set (Macaulay_list ps))"
proof (rule is_monic_setI)
  let ?ts = "pps_to_list (Supp (set ps))"
  let ?E = "row_echelon (Macaulay_mat ps)"

  fix p
  assume "p \<in> set (Macaulay_list ps)"
  obtain h where "pivot_fun ?E h (dim_col ?E)" by (rule row_echelon_pivot_fun)
  with \<open>p \<in> set (Macaulay_list ps)\<close> obtain i where "i < dim_row ?E"
    and p: "p = (mat_to_polys ?ts ?E) ! i" and "h i < dim_col ?E"
    by (rule in_Macaulay_listE)
  
  show "lc p = 1" unfolding p by (rule lc_row_to_poly_pivot_fun, simp, fact+)
qed

lemma Macaulay_list_not_zero: "0 \<notin> set (Macaulay_list ps)"
  by (simp add: Macaulay_list_def)

lemma Macaulay_list_distinct_lp:
  assumes "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)"
    and "x \<noteq> y"
  shows "lp x \<noteq> lp y"
proof
  let ?S = "Supp (set ps)"
  let ?ts = "pps_to_list ?S"
  let ?E = "row_echelon (Macaulay_mat ps)"

  assume "lp x = lp y"
  obtain h where pf: "pivot_fun ?E h (dim_col ?E)" by (rule row_echelon_pivot_fun)
  with assms(1) obtain i1 where "i1 < dim_row ?E"
    and x: "x = (mat_to_polys ?ts ?E) ! i1" and "h i1 < dim_col ?E"
    by (rule in_Macaulay_listE)
  from assms(2) pf obtain i2 where "i2 < dim_row ?E"
    and y: "y = (mat_to_polys ?ts ?E) ! i2" and "h i2 < dim_col ?E"
    by (rule in_Macaulay_listE)

  have "lp x = ?ts ! (h i1)" by (simp only: x, rule lp_row_to_poly_pivot_fun, simp, fact+)
  moreover have "lp y = ?ts ! (h i2)" by (simp only: y, rule lp_row_to_poly_pivot_fun, simp, fact+)
  ultimately have "?ts ! (h i1) = ?ts ! (h i2)" by (simp only: \<open>lp x = lp y\<close>)

  have "i1 = i2"
  proof (rule lp_row_to_poly_pivot_fun_eqD)
    show "card ?S = dim_col ?E" by simp
  qed (fact+)
  hence "x = y" by (simp only: x y)
  with \<open>x \<noteq> y\<close> show False ..
qed

lemma reduced_Macaulay_list_subset_Macaulay_list:
  "set (reduced_Macaulay_list ps) \<subseteq> set (Macaulay_list ps)"
  by (simp only: reduced_Macaulay_list_def, rule comp_min_basis_aux_empty_subset)

lemma reduced_Macaulay_list_not_zero: "0 \<notin> set (reduced_Macaulay_list ps)"
  using Macaulay_list_not_zero reduced_Macaulay_list_subset_Macaulay_list by auto
                                                               
lemma reduced_Macaulay_list_is_monic_set: "is_monic_set (set (reduced_Macaulay_list ps))"
proof (rule is_monic_setI)
  fix b
  assume "b \<in> set (reduced_Macaulay_list ps)"
  with reduced_Macaulay_list_subset_Macaulay_list have "b \<in> set (Macaulay_list ps)" ..
  moreover assume "b \<noteq> 0"
  ultimately show "lc b = 1" by (rule is_monic_setD[OF Macaulay_list_is_monic_set])
qed

end (* ordered_powerprod *)

context gd_powerprod
begin

lemma reduced_Macaulay_list_is_minimal_basis: "is_minimal_basis (set (reduced_Macaulay_list ps))"
proof (rule is_minimal_basisI)
  fix p
  assume "p \<in> set (reduced_Macaulay_list ps)"
  with reduced_Macaulay_list_not_zero show "p \<noteq> 0" by auto
next
  fix p q
  assume "p \<in> set (reduced_Macaulay_list ps)" and q_in: "q \<in> set (reduced_Macaulay_list ps)"
    and "p \<noteq> q"
  from reduced_Macaulay_list_subset_Macaulay_list this(1) have p_in: "p \<in> set (Macaulay_list ps)" ..
  from q_in have "q \<in> set (comp_min_basis_aux (Macaulay_list ps) [])"
    by (simp only: reduced_Macaulay_list_def)
  moreover note p_in
  moreover from \<open>p \<noteq> q\<close> have "q \<noteq> p" ..
  ultimately show "\<not> lp p adds lp q"
  proof (rule comp_min_basis_aux_empty_nadds)
    show "0 \<notin> set (Macaulay_list ps)" by (fact Macaulay_list_not_zero)
  next
    fix x y :: "('a, 'b) poly_mapping"
    assume "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)"
    moreover assume "x \<noteq> y"
    ultimately show "lp x \<noteq> lp y" by (rule Macaulay_list_distinct_lp)
  qed
qed

lemma pideal_reduced_Macaulay_list:
  assumes "is_Groebner_basis (set (Macaulay_list ps))"
  shows "pideal (set (reduced_Macaulay_list ps)) = pideal (set ps)"
proof -
  have "pideal (set (reduced_Macaulay_list ps)) = pideal (set (Macaulay_list ps))"
    unfolding reduced_Macaulay_list_def by (rule comp_min_basis_aux_empty_pideal, fact assms,
        fact Macaulay_list_not_zero, fact Macaulay_list_distinct_lp)
  also have "... = pideal (set ps)" by (simp only: pideal_Macaulay_list)
  finally show ?thesis .
qed

lemma Macaulay_list_lp:
  assumes "p \<in> phull (set ps)" and "p \<noteq> 0"
  obtains g where "g \<in> set (Macaulay_list ps)" and "g \<noteq> 0" and "lp p = lp g"
proof -
  let ?S = "Supp (set ps)"
  let ?ts = "pps_to_list ?S"
  let ?E = "row_echelon (Macaulay_mat ps)"
  let ?gs = "mat_to_polys ?ts ?E"
  have "finite ?S" by (rule Supp_finite, rule)
  have "?S \<subseteq> set ?ts" by (simp only: set_pps_to_list[OF \<open>finite ?S\<close>])
  
  from assms(1) \<open>?S \<subseteq> set ?ts\<close> have "p \<in> row_to_poly ?ts ` row_space ?E"
    by (simp only: Macaulay_mat_def row_space_row_echelon_eq_phull[symmetric])

  obtain f where "pivot_fun ?E f (dim_col ?E)" by (rule row_echelon_pivot_fun)

  have "lp p \<in> lp_set (set ?gs)"
    by (rule lp_row_space_pivot_fun, simp, fact+)
  then obtain g where "g \<in> set ?gs" and "g \<noteq> 0" and "lp g = lp p" by (rule lp_setE)
  
  show ?thesis
  proof
    from \<open>g \<in> set ?gs\<close> \<open>g \<noteq> 0\<close> show "g \<in> set (Macaulay_list ps)" by (simp add: set_Macaulay_list)
  next
    from \<open>lp g = lp p\<close> show "lp p = lp g" by simp
  qed fact
qed

lemma Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pideal (set ps) = pideal G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (Macaulay_list ps))"
proof (simp only: GB_alt_3_finite[OF finite_set] pideal_Macaulay_list, intro ballI impI)
  fix f
  assume "f \<in> pideal (set ps)"
  also from assms(2) have "... = pideal G" .
  finally have "f \<in> pideal G" .
  assume "f \<noteq> 0"
  with assms(1) \<open>f \<in> pideal G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by (rule GB_adds_lp)
  from assms(3) \<open>g \<in> G\<close> have "g \<in> phull (set ps)" ..
  from this \<open>g \<noteq> 0\<close> obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lp g = lp g'"
    by (rule Macaulay_list_lp)
  show "\<exists>g\<in>set (Macaulay_list ps). g \<noteq> 0 \<and> lp g adds lp f"
  proof (rule, rule)
    from \<open>lp g adds lp f\<close> show "lp g' adds lp f" by (simp only: \<open>lp g = lp g'\<close>)
  qed fact+
qed

lemma reduced_Macaulay_list_lp:
  assumes "p \<in> phull (set ps)" and "p \<noteq> 0"
  obtains g where "g \<in> set (reduced_Macaulay_list ps)" and "g \<noteq> 0" and "lp g adds lp p"
proof -
  from assms obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lp p = lp g'"
    by (rule Macaulay_list_lp)
  obtain g where "g \<in> set (reduced_Macaulay_list ps)" and "lp g adds lp g'"
  proof (simp only: reduced_Macaulay_list_def, rule comp_min_basis_aux_empty_adds)
    show "g' \<in> set (Macaulay_list ps)" by fact
  next
    show "0 \<notin> set (Macaulay_list ps)" by (fact Macaulay_list_not_zero)
  next
    fix x y
    assume "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)" and "x \<noteq> y"
    thus "lp x \<noteq> lp y" by (rule Macaulay_list_distinct_lp)
  qed

  from this(1) show ?thesis
  proof
    from \<open>g \<in> set (reduced_Macaulay_list ps)\<close> reduced_Macaulay_list_not_zero show "g \<noteq> 0" by auto
  next
    from \<open>lp g adds lp g'\<close> show "lp g adds lp p" by (simp only: \<open>lp p = lp g'\<close>)
  qed
qed

lemma reduced_Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pideal (set ps) = pideal G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (reduced_Macaulay_list ps))"
  unfolding reduced_Macaulay_list_def
apply (rule comp_min_basis_aux_empty_GB)
  subgoal by (rule Macaulay_list_is_GB, fact, fact, fact)
  subgoal by (fact Macaulay_list_not_zero)
  subgoal by (fact Macaulay_list_distinct_lp)
done

lemma reduced_Macaulay_list_is_reduced_GB:
  assumes "finite F" and "pideal (set ps) = pideal F" and "reduced_GB F \<subseteq> phull (set ps)"
  shows "set (reduced_Macaulay_list ps) = reduced_GB F"
proof -
  from assms(1) have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB)
  hence "is_Groebner_basis (reduced_GB F)" by (rule reduced_GB_D1)
  have aux: "pideal (reduced_GB F) = pideal (set ps)"
    by (simp only: assms(2), rule reduced_GB_pideal, fact)
  have pideal: "pideal (set (reduced_Macaulay_list ps)) = pideal (reduced_GB F)"
    unfolding aux
    by (rule pideal_reduced_Macaulay_list, rule Macaulay_list_is_GB, fact, simp only: aux, fact)
  show ?thesis
  proof (rule minimal_basis_is_reduced_GB, fact reduced_Macaulay_list_is_minimal_basis,
        fact reduced_Macaulay_list_is_monic_set, fact, rule is_reduced_GB_subsetI, fact,
        rule reduced_Macaulay_list_is_GB, fact, simp only: aux, fact,
        fact reduced_Macaulay_list_is_monic_set)
    fix a b :: "('a, 'b) poly_mapping"
    let ?c = "a - b"
    let ?S = "Supp (set ps)"
    let ?ts = "pps_to_list ?S"
    let ?A = "Macaulay_mat ps"
    let ?E = "row_echelon ?A"
    have "card ?S = dim_col ?E" by simp

    assume "b \<in> set (reduced_Macaulay_list ps)"
    with reduced_Macaulay_list_subset_Macaulay_list have "b \<in> set (Macaulay_list ps)" ..
    moreover obtain f where pf: "pivot_fun ?E f (dim_col ?E)" by (rule row_echelon_pivot_fun)
    ultimately obtain i1 where "i1 < dim_row ?E" and b: "b = mat_to_polys ?ts ?E ! i1"
      and "f i1 < dim_col ?E" by (rule in_Macaulay_listE)
    from \<open>card ?S = dim_col ?E\<close> pf this(1) this(3) have lpb: "lp b = ?ts ! (f i1)"
      by (simp only: b, rule lp_row_to_poly_pivot_fun)
    from \<open>b \<in> set (Macaulay_list ps)\<close> have "b \<in> phull (set (Macaulay_list ps))"
      by (rule generator_in_phull)
    hence "b \<in> phull (set ps)" by (simp only: phull_Macaulay_list)

    assume "a \<in> reduced_GB F"
    from assms(3) this have "a \<in> phull (set ps)" ..
    from this \<open>b \<in> phull (set ps)\<close> have "?c \<in> phull (set ps)" by (rule phull_closed_minus)
    moreover assume "?c \<noteq> 0"
    ultimately obtain r where "r \<in> set (Macaulay_list ps)" and "r \<noteq> 0" and "lp ?c = lp r"
      by (rule Macaulay_list_lp)
    from this(1) pf obtain i2 where "i2 < dim_row ?E" and r: "r = mat_to_polys ?ts ?E ! i2"
      and "f i2 < dim_col ?E" by (rule in_Macaulay_listE)
    from \<open>card ?S = dim_col ?E\<close> pf this(1) this(3) have lpr: "lp r = ?ts ! (f i2)"
      by (simp only: r, rule lp_row_to_poly_pivot_fun)

    assume "lp ?c \<in> keys b"
    hence "(?ts ! (f i2)) \<in> keys (mat_to_polys ?ts ?E ! i1)"
      by (simp only: \<open>lp ?c = lp r\<close> lpr b[symmetric])
    with \<open>card ?S = dim_col ?E\<close> pf \<open>i2 < dim_row ?E\<close> \<open>i1 < dim_row ?E\<close> \<open>f i2 < dim_col ?E\<close> have "i2 = i1"
      by (rule lp_row_to_poly_pivot_in_keysD)
    hence "r = b" by (simp only: r b)
    hence "lp ?c = lp b" by (simp only: \<open>lp ?c = lp r\<close>)

    moreover assume "lp ?c \<prec> lp b"
    ultimately show False by simp
  next
    show "pideal (reduced_GB F) = pideal (set (reduced_Macaulay_list ps))" by (simp only: pideal)
  qed fact
qed

subsection \<open>Bounds\<close>

definition is_cofactor_bound :: "('a, 'b::semiring_0) poly_mapping set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_cofactor_bound F d \<longleftrightarrow> (\<forall>p\<in>pideal F. \<exists>q. p = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f\<in>F. q f \<noteq> 0 \<longrightarrow> deg (q f) \<le> deg p + d))"

definition is_GB_bound :: "('a, 'b::field) poly_mapping set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_GB_bound F d \<longleftrightarrow> (\<forall>g\<in>reduced_GB F. deg g \<le> d)"

theorem Hermann_bound:
  assumes "finite F"
  shows "is_cofactor_bound F (\<Sum>j=0..<card (UNIV::'a set). (card F * maxdeg F)^(2^j))"
  sorry

theorem Dube_bound:
  assumes "finite F"
  shows "is_GB_bound F (2 * ((maxdeg F)^2 / 2 + maxdeg F)^(2^(card (UNIV::'a set))))"
  sorry

end (* gd_powerprod *)

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
