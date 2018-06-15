(* Author: Alexander Maletzky *)

section \<open>Code Equations and Useful Functions related to the Computation of Gr\"obner Bases\<close>

theory Algorithm_Schema_Impl
  imports "../Groebner_Bases/Algorithm_Schema" MPoly_Type_Class_OAlist
begin

lemma compute_card_keys [code]: "card_keys (MP_oalist xs) = length (fst (list_of_oalist_ntm xs))"
  apply (simp only: card_keys_def keys_MP_oalist image_set o_def)
  sorry

subsection \<open>Generating Cyclic Polynomials\<close>

definition cycl_pp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) pp"
  where "cycl_pp n d i = sparse\<^sub>0 (map (\<lambda>k. (modulo (k + i) n, 1)) [0..<d])"

definition cyclic :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::{zero,one,uminus}) list"
  where "cyclic to n =
            (let xs = [0..<n] in
              (map (\<lambda>d. distr\<^sub>0 to (map (\<lambda>i. (cycl_pp n d i, 1)) xs)) [1..<n]) @ [distr\<^sub>0 to [(cycl_pp n n 0, 1), (0, -1)]]
            )"

text \<open>\<open>cyclic n\<close> is a system of \<open>n\<close> polynomials in \<open>n\<close> indeterminates, with maximum degree \<open>n\<close>.\<close>

subsection \<open>Generating Katsura Polynomials\<close>

definition Katsura_poly :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 rat)"
  where "Katsura_poly to n i =
            change_ord to ((\<Sum>j=-(int n)..<(int n) + 1 - i. V\<^sub>0 (nat (abs j)) * V\<^sub>0 (nat (abs j + i))) - V\<^sub>0 i)"

definition Katsura :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 rat) list"
  where "Katsura to n =
          (let xs = [0..<n] in
            (distr\<^sub>0 to ((sparse\<^sub>0 [(0, 1)], 1) # (map (\<lambda>i. (sparse\<^sub>0 [(Suc i, 1)], 2)) xs) @ [(0, -1)])) # (map (Katsura_poly to n) xs)
          )"

text \<open>\<open>Katsura n\<close> is a system of \<open>n + 1\<close> polynomials in \<open>n + 1\<close> indeterminates, with maximum degree \<open>2\<close>.\<close>

end (* theory *)
