(* Author: Alexander Maletzky *)

section \<open>Zariski Topology\<close>

theory Zariski_Topology
  imports Nullstellensatz
begin

text \<open>The Zariski topology on a vector space \<open>K^n\<close> is the topology where the closed sets are precisely
  the algebraic sets, i.e. sets of the form @{term "\<V> F"} for some set @{term F} of polynomials.\<close>

definition Zariski_open :: "'x set \<Rightarrow> ('x \<Rightarrow> 'a::comm_semiring_1) set \<Rightarrow> bool"
  where "Zariski_open X A \<longleftrightarrow> - A \<in> \<V> ` Pow P[X]"

lemma Zariski_openI: "A = - \<V> F \<Longrightarrow> F \<subseteq> P[X] \<Longrightarrow> Zariski_open X A"
  by (auto simp: Zariski_open_def)

lemma Zariski_openE:
  assumes "Zariski_open X A"
  obtains F where "F \<subseteq> P[X]" and "A = - \<V> F"
  using assms by (auto simp: Zariski_open_def)

lemma Zariski_open_UNIV: "Zariski_open UNIV A \<longleftrightarrow> - A \<in> range \<V>"
  by (simp add: Zariski_open_def)

interpretation Zariski: topological_space "(Zariski_open X :: ('x \<Rightarrow> 'a::idom) set \<Rightarrow> _)"
proof
  show "Zariski_open X (UNIV::(_ \<Rightarrow> 'a) set)"
  proof (rule Zariski_openI)
    have "\<V> {1::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a} = \<V> (ideal {1})" by simp
    also have "\<dots> = \<V> UNIV"
      by (rule arg_cong[where f=\<V>]) (simp add: ideal_eq_UNIV_iff_contains_one ideal.span_base)
    finally show "UNIV = - \<V> {1::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a}" by simp
  qed (simp add: one_in_Polys)
next
  fix A B :: "('x \<Rightarrow> 'a) set"
  assume "Zariski_open X A"
  then obtain FA where "FA \<subseteq> P[X]" and A: "A = - \<V> FA" by (rule Zariski_openE)
  assume "Zariski_open X B"
  then obtain FB where "FB \<subseteq> P[X]" and B: "B = - \<V> FB" by (rule Zariski_openE)
  show "Zariski_open X (A \<inter> B)"
  proof (rule Zariski_openI)
    have "A \<inter> B = - (\<V> FA \<union> \<V> FB)" by (simp add: A B)
    also have "\<V> FA \<union> \<V> FB = \<V> (case_prod (*) ` (FA \<times> FB))"
      by (auto simp: variety_of_def poly_eval_times)
    finally show "A \<inter> B = - \<V> (case_prod (*) ` (FA \<times> FB))" .
  next
    from \<open>FA \<subseteq> P[X]\<close> \<open>FB \<subseteq> P[X]\<close> show "case_prod (*) ` (FA \<times> FB) \<subseteq> P[X]"
      by (auto intro: Polys_closed_times)
  qed
next
  fix K :: "('x \<Rightarrow> 'a) set set"
  assume *: "\<forall>A\<in>K. Zariski_open X A"
  define F where "F = (\<lambda>A::('x \<Rightarrow> 'a) set. SOME F'. F' \<subseteq> P[X] \<and> A = - \<V> F')"
  have "F A \<subseteq> P[X] \<and> A = - \<V> (F A)" if "A \<in> K" for A
  proof -
    from * that have "Zariski_open X A" ..
    then obtain F' where "F' \<subseteq> P[X]" and "A = - \<V> F'" by (rule Zariski_openE)
    hence "F' \<subseteq> P[X] \<and> A = - \<V> F'" ..
    thus ?thesis unfolding F_def by (rule someI)
  qed
  hence F_sub: "F A \<subseteq> P[X]" and A: "A = - \<V> (F A)" if "A \<in> K" for A using that by simp_all
  show "Zariski_open X (\<Union> K)"
  proof (rule Zariski_openI)
    from A have "\<Union> K = - \<Inter> ((\<V> \<circ> F) ` K)" by auto
    also have "\<Inter> ((\<V> \<circ> F) ` K) = \<V> (\<Union> (F ` K))" by (auto simp: variety_of_def)
    finally show "\<Union> K = - \<V> (\<Union> (F ` K))" .
  next
    from F_sub show "\<Union> (F ` K) \<subseteq> P[X]" by auto
  qed
qed

lemma Zariski_closed_alt: "Zariski.closed X A \<longleftrightarrow> A \<in> \<V> ` Pow P[X]"
  by (simp add: Zariski.closed_def Zariski_open_def)

lemma Zariski_closedI: "A = \<V> F \<Longrightarrow> F \<subseteq> P[X] \<Longrightarrow> Zariski.closed X A"
  by (auto simp: Zariski_closed_alt)

lemma Zariski_closedE:
  assumes "Zariski.closed X A"
  obtains F where "F \<subseteq> P[X]" and "A = \<V> F"
  using assms by (auto simp: Zariski_closed_alt)

lemma Zariski_closed_singleton: "Zariski.closed UNIV {a::'x \<Rightarrow> 'a::idom}"
proof -
  define F where "F = range (\<lambda>x::'x. monomial 1 (Poly_Mapping.single x (1::nat)) - monomial (a x) 0)"
  show ?thesis
  proof (rule Zariski_closedI)
    have "a \<in> \<V> F" by (rule variety_ofI) (auto simp: F_def poly_eval_minus poly_eval_monomial)
    moreover have "b = a" if "b \<in> \<V> F" for b
    proof (rule ccontr)
      assume "b \<noteq> a"
      then obtain x where "b x \<noteq> a x" by blast
      have "monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0 \<in> F"
        by (simp add: F_def)
      with that have "poly_eval b (monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0) = 0"
        by (rule variety_ofD)
      with \<open>b x \<noteq> a x\<close> show False by (simp add: poly_eval_minus poly_eval_monomial)
    qed
    ultimately show "{a} = \<V> F" by blast
  qed simp
qed

interpretation Zariski: t1_space "(Zariski_open UNIV :: ('x \<Rightarrow> 'a::idom) set \<Rightarrow> _)"
proof
  fix a b :: "'x \<Rightarrow> 'a"
  assume "a \<noteq> b"
  show "\<exists>U. Zariski_open UNIV U \<and> a \<in> U \<and> b \<notin> U"
  proof (intro exI conjI)
    show "Zariski_open UNIV (- {b})" by (simp add: Zariski.open_closed Zariski_closed_singleton)
  next
    from \<open>a \<noteq> b\<close> show "a \<in> - {b}" by simp
  qed simp
qed

interpretation Zariski: t2_space "(Zariski_open UNIV :: ('x::finite \<Rightarrow> 'a::{finite,idom}) set \<Rightarrow> _)"
proof
  fix a b :: "'x \<Rightarrow> 'a"
  assume "a \<noteq> b"
  show "\<exists>U V. Zariski_open UNIV U \<and> Zariski_open UNIV V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}"
  proof (intro exI conjI)
    show "Zariski_open UNIV (- (\<Union>c\<in>{c'. c' \<noteq> a}. {c}))"
      by (intro Zariski.open_Compl Zariski.closed_UN Zariski_closed_singleton ballI) simp
  next
    show "Zariski_open UNIV (- (\<Union>c\<in>{c'. c' \<noteq> b}. {c}))"
      by (intro Zariski.open_Compl Zariski.closed_UN Zariski_closed_singleton ballI) simp
  next
    from \<open>a \<noteq> b\<close> show "- (\<Union>c\<in>{c'. c' \<noteq> a}. {c}) \<inter> - (\<Union>c\<in>{c'. c' \<noteq> b}. {c}) = {}" by blast
  qed simp_all
qed

lemma Zariski_closure: "\<V> (\<I> A \<inter> P[X]) = (\<Inter> {C. Zariski.closed X C \<and> A \<subseteq> C})" (is "?L = ?R")
proof
  have "A \<subseteq> ?R" by blast
  have "Zariski.closed X ?R" by (rule Zariski.closed_Inter) simp
  then obtain F where "F \<subseteq> P[X]" and R: "?R = \<V> F" by (rule Zariski_closedE)
  from \<open>A \<subseteq> _\<close> have A_sub: "A \<subseteq> \<V> F" by (simp only: R)
  have "F \<subseteq> \<I> A"
  proof (intro subsetI ideal_ofI)
    fix f a
    assume "a \<in> A"
    with A_sub have "a \<in> \<V> F" ..
    moreover assume "f \<in> F"
    ultimately show "poly_eval a f = 0" by (rule variety_ofD)
  qed
  with \<open>F \<subseteq> P[X]\<close> have "F \<subseteq> \<I> A \<inter> P[X]" by blast
  thus "?L \<subseteq> ?R" unfolding R by (rule variety_of_antimono)
next
  from refl have "Zariski.closed X ?L" by (rule Zariski_closedI) simp
  moreover have "A \<subseteq> ?L" by (meson Int_lower1 ideal_ofD subset_eq variety_ofI)
  ultimately show "?R \<subseteq> ?L" by blast
qed

end (* theory *)
