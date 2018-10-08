theory Number_Classes
  imports Polynomials.Power_Products
begin

subsection \<open>Class @{term div_semiring}\<close>

class div_semiring = linordered_nonzero_semiring +
  fixes div_ceil div_floor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes div_ceil_geq_pos: "0 < b \<Longrightarrow> a \<le> b * (div_ceil a b)"
  assumes div_ceil_min_pos: "0 < b \<Longrightarrow> a \<le> b * c \<Longrightarrow> div_ceil a b \<le> c"
  assumes div_ceil_leq_neg: "b < 0 \<Longrightarrow> b * (div_ceil a b) \<le> a"
  assumes div_ceil_min_neg: "b < 0 \<Longrightarrow> b * c \<le> a \<Longrightarrow> div_ceil a b \<le> c"
  assumes div_floor_leq_pos: "0 < b \<Longrightarrow> b * (div_floor a b) \<le> a"
  assumes div_floor_max_pos: "0 < b \<Longrightarrow> b * c \<le> a \<Longrightarrow> c \<le> div_floor a b"
  assumes div_floor_geq_neg: "b < 0 \<Longrightarrow> a \<le> b * (div_floor a b)"
  assumes div_floor_max_neg: "b < 0 \<Longrightarrow> a \<le> b * c \<Longrightarrow> c \<le> div_floor a b"

subsection \<open>Class @{term number_dom_pre}\<close>

class number_dom_pre = comm_semiring_1_cancel + div_semiring +
    semiring_no_zero_divisors + ordered_ab_semigroup_add_imp_le + add_linorder +
  assumes mult_right_less_iff: "a * c < b * c \<longleftrightarrow> ((0 < c \<and> a < b) \<or> (c < 0 \<and> b < a))"
begin

lemma mult_cancel_right:
  assumes "c \<noteq> 0"
  shows "(a * c = b * c) \<longleftrightarrow> (a = b)"
proof
  assume a: "a * c = b * c"
  from assms have c: "0 < c \<or> c < 0" by auto
  show "a = b"
  proof (rule linorder_cases)
    assume "a < b"
    from c have "a * c \<noteq> b * c"
    proof
      assume "0 < c"
      with \<open>a < b\<close> have "a * c < b * c" unfolding mult_right_less_iff by simp
      thus ?thesis by simp
    next
      assume "c < 0"
      with \<open>a < b\<close> have "b * c < a * c" unfolding mult_right_less_iff by simp
      thus ?thesis by simp
    qed
    from this a show ?thesis ..
  next
    assume "b < a"
    from c have "a * c \<noteq> b * c"
    proof
      assume "0 < c"
      with \<open>b < a\<close> have "b * c < a * c" unfolding mult_right_less_iff by simp
      thus ?thesis by simp
    next
      assume "c < 0"
      with \<open>b < a\<close> have "a * c < b * c" unfolding mult_right_less_iff by simp
      thus ?thesis by simp
    qed
    from this a show ?thesis ..
  qed
next
  assume "a = b"
  thus "a * c = b * c" by simp
qed
  
lemma mult_right_leq_iff: "a * c \<le> b * c \<longleftrightarrow> (c = 0 \<or> (0 < c \<and> a \<le> b) \<or> (c < 0 \<and> b \<le> a))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  hence "a * c < b * c \<or> a * c = b * c" by auto
  thus ?R
  proof
    assume "a * c < b * c"
    thus ?thesis unfolding mult_right_less_iff by auto
  next
    assume a: "a * c = b * c"
    show ?thesis
    proof (rule linorder_cases)
      assume "0 < c"
      hence "c \<noteq> 0" by simp
      from \<open>0 < c\<close> a show ?thesis unfolding mult_cancel_right[OF \<open>c \<noteq> 0\<close>] by simp
    next
      assume "c < 0"
      hence "c \<noteq> 0" by simp
      from \<open>c < 0\<close> a show ?thesis unfolding mult_cancel_right[OF \<open>c \<noteq> 0\<close>] by simp
    next
      assume "0 = c"
      thus ?thesis by simp
    qed
  qed
next
  assume ?R
  thus ?L
  proof (elim disjE)
    assume "c = 0"
    thus ?thesis by simp
  next
    assume "0 < c \<and> a \<le> b"
    hence "0 < c" and "a \<le> b" by simp_all
    from \<open>a \<le> b\<close> have "a < b \<or> a = b" by auto
    thus ?thesis
    proof
      assume "a < b"
      with \<open>0 < c\<close> have "a * c < b * c" unfolding mult_right_less_iff by simp
      thus ?thesis by simp
    next
      assume "a = b"
      hence "a * c = b * c" by simp
      thus ?thesis by simp
    qed
  next
    assume "c < 0 \<and> b \<le> a"
    hence "c < 0" and "b \<le> a" by simp_all
    from \<open>b \<le> a\<close> have "b < a \<or> a = b" by auto
    thus ?thesis
    proof
      assume "b < a"
      with \<open>c < 0\<close> have "a * c < b * c" unfolding mult_right_less_iff by simp
      thus ?thesis by simp
    next
      assume "a = b"
      hence "a * c = b * c" by simp
      thus ?thesis by simp
    qed
  qed
qed

lemma mult_left_less_iff: "c * a < c * b \<longleftrightarrow> ((0 < c \<and> a < b) \<or> (c < 0 \<and> b < a))"
  using mult_right_less_iff[of a c b] by (simp add: ac_simps)

lemma mult_left_leq_iff: "c * a \<le> c * b \<longleftrightarrow> (c = 0 \<or> (0 < c \<and> a \<le> b) \<or> (c < 0 \<and> b \<le> a))"
  using mult_right_leq_iff[of a c b] by (simp add: ac_simps)

lemma mult_cancel_left:
  assumes "c \<noteq> 0"
  shows "(c * a = c * b) \<longleftrightarrow> (a = b)"
  using mult_cancel_right[OF assms, of a b] by (simp add: ac_simps)

lemma div_floor_leq_div_ceil:
  assumes "b \<noteq> 0"
  shows "div_floor a b \<le> div_ceil a b"
proof (rule linorder_cases)
  assume "b < 0"
  hence "b * div_ceil a b \<le> a" by (rule div_ceil_leq_neg)
  also from \<open>b < 0\<close> have "... \<le> b * div_floor a b" by (rule div_floor_geq_neg)
  finally have "b * div_ceil a b \<le> b * div_floor a b" .
  with \<open>b < 0\<close> show ?thesis unfolding mult_left_leq_iff by auto
next
  assume "0 < b"
  hence "b * div_floor a b \<le> a" by (rule div_floor_leq_pos)
  also from \<open>0 < b\<close> have "... \<le> b * div_ceil a b" by (rule div_ceil_geq_pos)
  finally have "b * div_floor a b \<le> b * div_ceil a b" .
  with \<open>0 < b\<close> show ?thesis unfolding mult_left_leq_iff by auto
next
  assume "b = 0"
  with assms show ?thesis by simp
qed

lemma div_floor_dvd':
  assumes "b \<noteq> 0"
  shows "div_floor (b * c) b = c"
proof -
  let ?a = "b * c"
  have leq: "?a \<le> ?a" ..
  have "b * (div_floor (b * c) b) = b * c"
  proof (rule linorder_cases)
    assume "b < 0"
    from this leq have "c \<le> div_floor ?a b" by (rule div_floor_max_neg)
    with \<open>b < 0\<close> have "b * (div_floor ?a b) \<le> ?a" unfolding mult_left_leq_iff by simp
    from this div_floor_geq_neg[OF \<open>b < 0\<close>, of ?a] show ?thesis by (rule antisym)
  next
    assume "0 < b"
    from this leq have "c \<le> div_floor ?a b" by (rule div_floor_max_pos)
    with \<open>0 < b\<close> have "?a \<le> b * (div_floor ?a b)" unfolding mult_left_leq_iff by simp
    with div_floor_leq_pos[OF \<open>0 < b\<close>, of ?a] show ?thesis by (rule antisym)
  next
    assume "b = 0"
    with \<open>b \<noteq> 0\<close> show ?thesis ..
  qed
  thus ?thesis unfolding mult_cancel_left[OF \<open>b \<noteq> 0\<close>] .
qed

lemma div_ceil_dvd':
  assumes "b \<noteq> 0"
  shows "div_ceil (b * c) b = c"
proof -
  let ?a = "b * c"
  have leq: "?a \<le> ?a" ..
  have "b * (div_ceil (b * c) b) = b * c"
  proof (rule linorder_cases)
    assume "b < 0"
    from this leq have "div_ceil ?a b \<le> c" by (rule div_ceil_min_neg)
    with \<open>b < 0\<close> have "?a \<le> b * (div_ceil ?a b)" unfolding mult_left_leq_iff by simp
    with div_ceil_leq_neg[OF \<open>b < 0\<close>, of ?a] show ?thesis by (rule antisym)
  next
    assume "0 < b"
    from this leq have "div_ceil ?a b \<le> c" by (rule div_ceil_min_pos)
    with \<open>0 < b\<close> have "b * (div_ceil ?a b) \<le> ?a" unfolding mult_left_leq_iff by simp
    from this div_ceil_geq_pos[OF \<open>0 < b\<close>, of ?a] show ?thesis by (rule antisym)
  next
    assume "b = 0"
    with \<open>b \<noteq> 0\<close> show ?thesis ..
  qed
  thus ?thesis unfolding mult_cancel_left[OF \<open>b \<noteq> 0\<close>] .
qed

lemma div_floor_dvd:
  assumes "b dvd a"
  shows "b * (div_floor a b) = a"
proof -
  from assms obtain c where eq: "a = b * c" unfolding dvd_def ..
  show ?thesis
  proof (cases "b = 0")
    case True
    hence "a = 0" unfolding eq by simp
    with True show ?thesis by simp
  next
    case False
    hence "div_floor a b = c" unfolding eq by (rule div_floor_dvd')
    with eq show ?thesis by simp
  qed
qed

lemma div_ceil_dvd:
  assumes "b dvd a"
  shows "b * (div_ceil a b) = a"
proof -
  from assms obtain c where eq: "a = b * c" unfolding dvd_def ..
  show ?thesis
  proof (cases "b = 0")
    case True
    hence "a = 0" unfolding eq by simp
    with True show ?thesis by simp
  next
    case False
    hence "div_ceil a b = c" unfolding eq by (rule div_ceil_dvd')
    with eq show ?thesis by simp
  qed
qed

lemma div_floor_eq_div_ceil_iff:
  assumes "b \<noteq> 0"
  shows "div_floor a b = div_ceil a b \<longleftrightarrow> b dvd a"
proof
  assume "div_floor a b = div_ceil a b" (is "?f = ?c")
  hence eq: "b * ?f = b * ?c" by simp
  show "b dvd a" unfolding dvd_def
  proof
    show "a = b * ?f"
    proof (rule linorder_cases)
      assume a: "a < b * ?f"
      hence "\<not> b * ?f \<le> a" by simp
      hence "\<not> 0 < b" using div_floor_leq_pos[of b a] by auto
      hence "b < 0" using assms by simp
      from div_ceil_leq_neg[OF this, of a] a have "b * ?c < b * ?f" by simp
      thus ?thesis unfolding eq by simp
    next
      assume a: "b * ?f < a"
      hence "\<not> a \<le> b * ?f" by simp
      hence "\<not> b < 0" using div_floor_geq_neg[of b a] by auto
      hence "0 < b" using assms by simp
      from div_ceil_geq_pos[OF this, of a] a have "b * ?f < b * ?c" by simp
      thus ?thesis unfolding eq by simp
    qed
  qed
next
  assume "b dvd a"
  hence "b * div_ceil a b = a" and "b * div_floor a b = a" by (rule div_ceil_dvd, rule div_floor_dvd)
  hence "b * div_floor a b = b * div_ceil a b" by simp
  thus "div_floor a b = div_ceil a b" unfolding mult_cancel_left[OF assms] .
qed
  
lemma div_ceil_1: "div_ceil a 1 = a"
proof -
  have "1 \<noteq> 0" by simp
  hence "div_ceil (1 * a) 1 = a" by (rule div_ceil_dvd')
  thus ?thesis by simp
qed
    
lemma div_floor_1: "div_floor a 1 = a"
proof -
  have "1 \<noteq> 0" by simp
  hence "div_floor (1 * a) 1 = a" by (rule div_floor_dvd')
  thus ?thesis by simp
qed
    
lemma div_ceil_same:
  assumes "a \<noteq> 0"
  shows "div_ceil a a = 1"
proof -
  from assms have "div_ceil (a * 1) a = 1" by (rule div_ceil_dvd')
  thus ?thesis by simp
qed
    
lemma div_floor_same:
  assumes "a \<noteq> 0"
  shows "div_floor a a = 1"
proof -
  from assms have "div_floor (a * 1) a = 1" by (rule div_floor_dvd')
  thus ?thesis by simp
qed

end (* number_dom_pre *)
  
subsection \<open>Class @{term number_dom}\<close>
  
class number_dom = number_dom_pre + assumes dvd_sum: "c dvd a \<Longrightarrow> c dvd (a + b) \<Longrightarrow> c dvd b"

subsection \<open>Class @{term number_dom_min}\<close>

class number_dom_min = number_dom_pre + add_linorder_min
begin

lemma mult_right_less_iff_min: "a * c < b * c \<longleftrightarrow> (c \<noteq> 0 \<and> a < b)"
  unfolding mult_right_less_iff using zero_min[of c] not_gr_zero by fastforce

lemma mult_right_leq_iff_min: "a * c \<le> b * c \<longleftrightarrow> (c \<noteq> 0 \<longrightarrow> a \<le> b)" (is "?L \<longleftrightarrow> ?R")
  unfolding mult_right_leq_iff using zero_min[of c] not_gr_zero by fastforce

lemma mult_left_less_iff_min: "c * a < c * b \<longleftrightarrow> (c \<noteq> 0 \<and> a < b)"
  using mult_right_less_iff_min[of a c b] by (simp add: ac_simps)

lemma mult_left_leq_iff_min: "c * a \<le> c * b \<longleftrightarrow> (c \<noteq> 0 \<longrightarrow> a \<le> b)"
  using mult_right_leq_iff_min[of a c b] by (simp add: ac_simps)

subclass number_dom
proof
  fix a b c
  assume "c dvd a" and "c dvd (a + b)"
  show "c dvd b"
  proof (cases "b = 0")
    case True
    show ?thesis unfolding True ..
  next
    case False
    from \<open>c dvd a\<close> obtain k1 where eq0: "a = c * k1" unfolding dvd_def ..
    from \<open>c dvd (a + b)\<close> obtain k2 where eq1: "a + b = c * k2" unfolding dvd_def ..
    hence eq2: "b + c * k1 = c * k2" unfolding eq0 by (simp add: ac_simps)
    have "a \<le> a + b" by (fact leq_add_right)
    hence "c * k1 \<le> c * k2" unfolding eq1 unfolding eq0 .
    hence "c * k2 = c * k1 + (c * k2 - c * k1)" by (rule le_imp_inv)
    with eq2 have "b + c * k1 = (c * k2 - c * k1) + c * k1" by (simp add: ac_simps)
    hence eq3: "b = c * k2 - c * k1" unfolding add_right_cancel .
    show ?thesis unfolding dvd_def
    proof
      from eq3 show "b = c * (k2 - k1)" unfolding right_diff_distrib' .
    qed
  qed
qed

end (* number_dom_min *)

class number_wellorder = number_dom_min + wellorder
begin
  
subclass add_wellorder ..
  
end

subsection \<open>Class @{term number_ring}\<close>

class number_ring = number_dom_pre + ring
begin

subclass number_dom
proof
  fix a b c
  assume "c dvd a" and "c dvd (a + b)"
  from dvd_add_right_iff[OF \<open>c dvd a\<close>, of b] \<open>c dvd (a + b)\<close> show "c dvd b" by simp
qed

end (* number_ring *)

subsection \<open>Class @{term number_field}\<close>
  
sublocale linordered_field \<subseteq> div_semiring 1 "(*)" "(\<le>)" "(<)" "(+)" 0 "(/)" "(/)"
by (standard, simp_all add: mult_imp_div_pos_le neg_divide_le_eq mult_imp_le_div_pos neg_le_divide_eq  mult_commute)
  
class number_field = div_semiring + linordered_field
begin

subclass number_dom_pre
proof
  fix a b
  assume "a \<le> b"
  hence "b = a + (b - a)" by simp
  thus "\<exists>c. b = a + c" ..
qed (fact mult_less_cancel_right_disj)
  
subclass number_ring ..

lemma div_ceil_field:
  assumes "y \<noteq> 0"
  shows "div_ceil x y = x / y"
proof -
  from assms have "div_ceil (y * (x / y)) y = x / y" by (rule div_ceil_dvd')
  moreover from assms have "y * (x / y) = x" by (simp add: field_simps)
  ultimately show ?thesis by simp
qed

lemma div_floor_field:
  assumes "y \<noteq> 0"
  shows "div_floor x y = x / y"
proof -
  from assms have "div_floor (y * (x / y)) y = x / y" by (rule div_floor_dvd')
  moreover from assms have "y * (x / y) = x" by (simp add: field_simps)
  ultimately show ?thesis by simp
qed

end

subsection \<open>Conversions\<close>

definition to_nat :: "'a::floor_ceiling \<Rightarrow> nat" where "to_nat = nat o floor"
  
definition of_nat_fun :: "('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> 'b::semiring_1" where "of_nat_fun f = of_nat o f"

definition of_int_fun :: "('a \<Rightarrow> int) \<Rightarrow> 'a \<Rightarrow> 'b::ring_1" where "of_int_fun f = of_int o f"

definition to_int_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> 'a \<Rightarrow> int" where "to_int_fun f = floor o f"
  
definition of_rat_fun :: "('a \<Rightarrow> rat) \<Rightarrow> 'a \<Rightarrow> 'b::field_char_0" where "of_rat_fun f = of_rat o f"

definition to_nat_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> 'a \<Rightarrow> nat" where "to_nat_fun f = to_nat o f"
  
definition is_int :: "'b::{floor_ceiling} \<Rightarrow> bool" where
  "is_int x = (of_int (floor x) = x)"

definition is_int_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> bool" where
  "is_int_fun f = (\<forall>x. is_int (f x))"

definition is_nat :: "'b::floor_ceiling \<Rightarrow> bool" where
  "is_nat x = (of_nat (to_nat x) = x)"

definition is_nat_fun :: "('a \<Rightarrow> 'b::floor_ceiling) \<Rightarrow> bool" where
  "is_nat_fun f = (\<forall>x. is_nat (f x))"
  
lemma to_nat_comp_of_nat: "to_nat o of_nat = id" unfolding to_nat_def by auto

lemma to_int_fun_comp_of_int_fun: "to_int_fun (of_int_fun x) = x"
  unfolding to_int_fun_def of_int_fun_def by force

lemma to_nat_fun_comp_of_nat_fun: "to_nat_fun (of_nat_fun x) = x"
  unfolding to_nat_fun_def of_nat_fun_def to_int_fun_def to_nat_def by force

lemma to_nat_fun_comp_of_int_fun: "to_nat_fun (of_int_fun x) = nat \<circ> x"
  unfolding to_nat_fun_def of_int_fun_def to_nat_def by force

lemma to_int_fun_comp_of_int_fun': "to_int_fun o of_int_fun = id"
  unfolding o_def to_int_fun_comp_of_int_fun id_def ..

lemma to_nat_fun_comp_of_nat_fun': "to_nat_fun o of_nat_fun = id"
  unfolding o_def to_nat_fun_comp_of_nat_fun id_def ..

lemma nat_comp_of_nat_fun: "nat o (of_nat_fun f) = f"
  unfolding o_def of_nat_fun_def by simp

lemma of_int_fun_comp_to_int_fun:
  assumes "is_int_fun f"
  shows "of_int_fun (to_int_fun f) = f"
  unfolding of_int_fun_def to_int_fun_def o_def
proof
  fix x
  from assms show "of_int \<lfloor>f x\<rfloor> = f x" unfolding is_int_fun_def is_int_def ..
qed

lemma of_int_fun_comp_of_nat_fun: "of_int_fun (of_nat_fun f) = of_nat_fun f"
  by (rule, simp add: of_int_fun_def of_nat_fun_def)

lemma of_nat_fun_comp_nat:
  assumes "\<And>x. 0 \<le> f x"
  shows "of_nat_fun (nat o f) = (f::'a \<Rightarrow> int)"
  unfolding of_nat_fun_def o_def
proof
  fix x
  from assms[of x] show "int (nat (f x)) = f x" by simp
qed

lemma of_nat_fun_comp_to_nat_fun:
  assumes "is_nat_fun f"
  shows "of_nat_fun (to_nat_fun f) = f"
  unfolding of_nat_fun_def to_nat_fun_def o_def
proof
  fix x
  from assms show "of_nat (to_nat (f x)) = f x" unfolding is_nat_fun_def is_nat_def ..
qed

lemma of_nat_fun_comp_to_nat_fun_eq_to_int_fun:
  assumes "is_nat_fun (f::'a \<Rightarrow> 'b::floor_ceiling)"
  shows "of_nat_fun (to_nat_fun f) = to_int_fun f"
  unfolding of_nat_fun_def to_nat_fun_def to_nat_def to_int_fun_def o_def
proof
  fix x
  from assms have "is_nat (f x)" unfolding is_nat_fun_def ..
  hence "of_nat (nat \<lfloor>f x\<rfloor>) = f x" unfolding is_nat_def to_nat_def o_def .
  hence "\<lfloor>(of_nat (nat \<lfloor>f x\<rfloor>))::'b\<rfloor> = \<lfloor>f x\<rfloor>" by simp
  thus "int (nat \<lfloor>f x\<rfloor>) = \<lfloor>f x\<rfloor>" by simp
qed
  
lemma nat_is_int:
  assumes "is_nat x"
  shows "is_int x"
  using assms unfolding is_nat_def is_int_def by (metis floor_of_nat of_int_of_nat_eq)

lemma nat_fun_is_int_fun:
  assumes "is_nat_fun f"
  shows "is_int_fun f"
  using assms unfolding is_nat_fun_def is_int_fun_def using nat_is_int by auto

lemma is_nat_geq_zero:
  assumes "is_nat x"
  shows "0 \<le> x"
  using assms unfolding is_nat_def by (metis of_nat_0_le_iff)

lemma int_is_nat:
  assumes "is_int x" and "0 \<le> x"
  shows "is_nat x"
proof -
  from assms(1) have "x = of_int \<lfloor>x\<rfloor>" unfolding is_int_def by auto
  with assms(2) show "is_nat x" unfolding is_nat_def
    by (metis comp_def of_int_le_iff of_int_0 of_nat_nat to_nat_def)
qed

lemma int_fun_is_nat_fun:
  assumes "is_int_fun f" and "\<And>x. 0 \<le> f x"
  shows "is_nat_fun f"
  unfolding is_nat_fun_def
proof
  fix x
  from assms(1) have "is_int (f x)" unfolding is_int_fun_def ..
  moreover from assms(2) have "0 \<le> f x" .
  ultimately show "is_nat (f x)" by (rule int_is_nat)
qed

lemma of_nat_is_nat: "is_nat (of_nat n)"
  unfolding is_nat_def to_nat_def by simp
    
lemma of_int_is_int: "is_int (of_int a)"
  unfolding is_int_def by simp

lemma of_nat_fun_is_nat_fun: "is_nat_fun (of_nat_fun f)"
  unfolding is_nat_fun_def of_nat_fun_def o_def by (simp add: of_nat_is_nat)

lemma of_int_fun_is_int_fun: "is_int_fun (of_int_fun f)"
  unfolding is_int_fun_def of_int_fun_def o_def by (simp add: of_int_is_int)

lemma max_of_nat:
  assumes "\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1,ord}) \<longleftrightarrow> m \<le> n"
  shows "max (of_nat a) (of_nat b) = ((of_nat (max a b::nat))::'b::{semiring_1,ord})"
  unfolding max_def assms by simp

lemma min_of_nat:
  assumes "\<And>m n::nat. of_nat m \<le> ((of_nat n)::'b::{semiring_1,ord}) \<longleftrightarrow> m \<le> n"
  shows "min (of_nat a) (of_nat b) = ((of_nat (min a b::nat))::'b::{semiring_1,ord})"
  unfolding min_def assms by simp

lemmas max_of_nat_linordered_semidom = max_of_nat[OF Nat.linordered_nonzero_semiring_class.of_nat_le_iff]
lemmas min_of_nat_linordered_semidom = min_of_nat[OF Nat.linordered_nonzero_semiring_class.of_nat_le_iff]
    
lemma floor_real_of_rat: "\<lfloor>x\<rfloor> = \<lfloor>real_of_rat x\<rfloor>"
  using real_floor_code by auto

lemma ceil_real_of_rat: "\<lceil>x\<rceil> = \<lceil>real_of_rat x\<rceil>"
  unfolding ceiling_def floor_real_of_rat[of "-x"] by (simp add: of_rat_minus)

lemma leq_of_nat_fun: "of_nat_fun f \<le> ((of_nat_fun g)::'a \<Rightarrow> ('b::linordered_semidom)) \<longleftrightarrow> f \<le> g"
  by (simp add: of_nat_fun_def le_fun_def)

lemma less_of_nat_fun: "of_nat_fun f < ((of_nat_fun g)::'a \<Rightarrow> ('b::linordered_semidom)) \<longleftrightarrow> f < g"
  by (simp add: leq_of_nat_fun Orderings.less_fun_def)

lemma leq_of_int_fun: "of_int_fun f \<le> ((of_int_fun g)::'a \<Rightarrow> ('b::linordered_idom)) \<longleftrightarrow> f \<le> g"
  by (simp add: of_int_fun_def le_fun_def)

lemma less_of_int_fun: "of_int_fun f < ((of_int_fun g)::'a \<Rightarrow> ('b::linordered_idom)) \<longleftrightarrow> f < g"
  by (simp add: leq_of_int_fun Orderings.less_fun_def)

lemma leq_to_nat_fun:
  assumes "f \<le> g"
  shows "to_nat_fun f \<le> to_nat_fun g"
  using assms unfolding to_nat_fun_def o_def le_fun_def to_nat_def
proof -
  assume *: "\<forall>x. f x \<le> g x"
  show "\<forall>x. nat \<lfloor>f x\<rfloor> \<le> nat \<lfloor>g x \<rfloor>"
  proof
    fix x
    from * have "f x \<le> g x" ..
    hence "\<lfloor>f x\<rfloor> \<le> \<lfloor>g x\<rfloor>" by (rule floor_mono)
    thus "nat \<lfloor>f x\<rfloor> \<le> nat \<lfloor>g x\<rfloor>" by simp
  qed
qed

lemma leq_to_int_fun:
  assumes "f \<le> g"
  shows "to_int_fun f \<le> to_int_fun g"
  using assms unfolding to_int_fun_def o_def le_fun_def using floor_mono by auto

subsection \<open>Closure Properties of @{const is_nat} and @{const is_int}\<close>
  
subsubsection \<open>0 and 1\<close>

lemma zero_is_nat: "is_nat 0"
  by (metis of_nat_0 of_nat_is_nat) 

lemma one_is_nat: "is_nat 1"
  by (metis of_nat_1 of_nat_is_nat) 

subsubsection \<open>@{const plus} and @{const minus}\<close>

lemma plus_is_nat:
  assumes "is_nat x" and "is_nat y"
  shows "is_nat (x + y)"
  using assms unfolding is_nat_def
proof -
  assume a1: "of_nat (to_nat x) = x"
  assume a2: "of_nat (to_nat y) = y"
  have f3: "to_nat (x + y) = nat \<lfloor>x + y\<rfloor>" by (metis comp_apply to_nat_def)
  have "x + y = of_nat (to_nat x) + of_nat (to_nat y)" using a2 a1 by presburger
  thus "of_nat (to_nat (x + y)) = x + y" using f3 by simp
qed

lemma diff_is_nat:
  assumes "is_int x" and "is_int y"
  shows "is_nat (x - y) \<longleftrightarrow> y \<le> x"
  using assms unfolding is_nat_def is_int_def
  by (metis diff_ge_0_iff_ge int_is_nat is_nat_def of_int_diff of_int_is_int of_nat_0_le_iff)

lemma plus_is_int:
  assumes "is_int x" and "is_int y"
  shows "is_int (x + y)"
  by (metis assms is_int_def of_int_floor_cancel of_int_add)

lemma diff_is_int:
  assumes "is_int x" and "is_int y"
  shows "is_int (x - y)"
  by (metis assms is_int_def of_int_floor_cancel of_int_diff)

lemma minus_is_int:
  assumes "is_int x"
  shows "is_int (- x)"
  by (metis assms is_int_def of_int_floor_cancel of_int_minus)

subsubsection \<open>@{const times}\<close>
  
lemma times_is_nat:
  assumes "is_nat x" and "is_nat y"
  shows "is_nat (x * y)"
  by (metis is_nat_def assms of_nat_is_nat of_nat_mult)

lemma times_is_int:
  assumes "is_int x" and "is_int y"
  shows "is_int (x * y)"
  by (metis assms is_int_def of_int_floor_cancel of_int_mult)

subsubsection \<open>@{const min} and @{const max}\<close>

lemma min_is_nat:
  assumes "is_nat x" and "is_nat y"
  shows "is_nat (min x y)"
  unfolding min_def using assms by simp

lemma max_is_nat:
  assumes "is_nat x" and "is_nat y"
  shows "is_nat (max x y)"
  unfolding max_def using assms by simp

lemma max_is_nat':
  assumes "is_nat x" and "is_int y"
  shows "is_nat (max x y)"
  by (metis assms int_is_nat is_nat_geq_zero le_max_iff_disj max_def)

lemma min_is_int:
  assumes "is_int x" and "is_int y"
  shows "is_int (min x y)"
  unfolding min_def using assms by simp

lemma max_is_int:
  assumes "is_int x" and "is_int y"
  shows "is_int (max x y)"
  unfolding max_def using assms by simp
  
end (* theory *)
