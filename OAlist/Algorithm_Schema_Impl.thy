(* Author: Alexander Maletzky *)

section \<open>Code Equations and Useful Functions related to the Computation of Gr\"obner Bases\<close>

theory Algorithm_Schema_Impl
  imports "../Groebner_Bases/Algorithm_Schema" MPoly_Type_Class_OAlist
begin

lemma compute_card_keys [code]: "card_keys (Pm_oalist xs) = length (list_of_oalist xs)"
  apply (simp only: card_keys_def compute_keys_pm image_set o_def)
  sorry

instantiation natural :: wellorder
begin

instance sorry

end

instantiation natural :: countable
begin

instance sorry

end

instantiation natural :: add_wellorder
begin

instance sorry

end

instantiation natural :: compare
begin

definition compare_natural :: "natural comparator" where
  "compare_natural = comparator_of_le"

instance sorry

end

subsection \<open>Generating Cyclic Polynomials\<close>

definition cycl_pp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (natural \<Rightarrow>\<^sub>0 natural)"
  where "cycl_pp n d i = sparse\<^sub>0 (map (\<lambda>k. (natural_of_nat (modulo (k + i) n), 1)) [0..<d])"

definition cyclic :: "nat \<Rightarrow> ((natural \<Rightarrow>\<^sub>0 natural) \<Rightarrow>\<^sub>0 'a::{zero,one,uminus}) list"
  where "cyclic n =
            (let xs = [0..<n] in
              (map (\<lambda>d. sparse\<^sub>0 (map (\<lambda>i. (cycl_pp n d i, 1)) xs)) [1..<n]) @ [sparse\<^sub>0 [(cycl_pp n n 0, 1), (0, -1)]]
            )"

text \<open>\<open>cyclic n\<close> is a system of \<open>n\<close> polynomials in \<open>n\<close> indeterminates, with maximum degree \<open>n\<close>.\<close>

subsection \<open>Generating Katsura Polynomials\<close>

definition Katsura_poly :: "nat \<Rightarrow> nat \<Rightarrow> ((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 rat)"
  where "Katsura_poly n i =
            (\<Sum>j=-(int n)..<(int n) + 1 - i. Var\<^sub>0 (nat (abs j)) * Var\<^sub>0 (nat (abs j + i))) - Var\<^sub>0 i"

definition Katsura :: "nat \<Rightarrow> ((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 rat) list"
  where "Katsura n =
          (let xs = [0..<n] in
            (sparse\<^sub>0 ((sparse\<^sub>0 [(0, 1)], 1) # (map (\<lambda>i. (sparse\<^sub>0 [(Suc i, 1)], 2)) xs) @ [(0, -1)])) # (map (Katsura_poly n) xs)
          )"

text \<open>\<open>Katsura n\<close> is a system of \<open>n + 1\<close> polynomials in \<open>n + 1\<close> indeterminates, with maximum degree \<open>2\<close>.\<close>

end (* theory *)
