(* Author: Alexander Maletzky *)

section \<open>Code Equations and Useful Functions related to the Computation of Gr\"obner Bases\<close>

theory Algorithm_Schema_Impl
  imports Algorithm_Schema Polynomials.MPoly_Type_Class_FMap
begin

definition keys_list :: "('a \<times> 'b::zero) list \<Rightarrow> 'a list"
  where "keys_list xs = map fst [x\<leftarrow>AList.clearjunk xs. snd x \<noteq> 0]"

lemma distinct_keys_list: "distinct (keys_list xs)"
  unfolding keys_list_def using distinct_clearjunk by (rule distinct_map_filter)

lemma compute_keys_alt [code]: "keys (Pm_fmap (fmap_of_list xs)) = set (keys_list xs)"
proof (simp add: compute_keys_pp clearjunk0_def fmlookup_of_list fmdom'_alt_def fset_of_list.rep_eq
      keys_list_def)
  show "{x. map_of xs x \<noteq> Some 0} \<inter> fst ` set xs = fst ` {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}"
      (is "?l = ?r")
  proof
    show "?l \<subseteq> ?r"
    proof (rule, simp, elim conjE)
      fix t
      assume "map_of xs t \<noteq> Some 0" and "t \<in> fst ` set xs"
      hence "map_of (AList.clearjunk xs) t \<noteq> Some 0" and "t \<in> fst ` set (AList.clearjunk xs)"
        by (simp_all add: map_of_clearjunk dom_clearjunk)
      then obtain c where "(t, c) \<in> set (AList.clearjunk xs)" and "c \<noteq> 0"
        by (metis domD dom_map_of_conv_image_fst map_of_SomeD)
      hence "(t, c) \<in> {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}" by simp
      thus "t \<in> fst ` {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}" by force
    qed
  next
    show "?r \<subseteq> ?l"
    proof (rule, simp)
      fix t
      assume "t \<in> fst ` {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}"
      then obtain c where "(t, c) \<in> {x \<in> set (AList.clearjunk xs). snd x \<noteq> 0}" by fastforce
      hence 1: "(t, c) \<in> set (AList.clearjunk xs)" and "c \<noteq> 0" by simp_all
      from 1 have "map_of (AList.clearjunk xs) t = Some c" by simp
      hence "map_of xs t = Some c" by (simp only: map_of_clearjunk)
      with \<open>c \<noteq> 0\<close> have "map_of xs t \<noteq> Some 0" by simp
      moreover from 1 have "t \<in> fst ` set xs"
      proof -
        from 1 have "t \<in> fst ` set (AList.clearjunk xs)" by force
        thus ?thesis by (simp only: dom_clearjunk)
      qed
      ultimately show "map_of xs t \<noteq> Some 0 \<and> t \<in> fst ` set xs" ..
    qed
  qed
qed

lemma compute_card_keys [code]:
  "card_keys (Pm_fmap (fmap_of_list xs)) = length [x\<leftarrow>AList.clearjunk xs . snd x \<noteq> 0]"
proof -
  from distinct_keys_list have "card (set (keys_list xs)) = length (keys_list xs)"
    by (rule distinct_card)
  also have "... = length [x\<leftarrow>AList.clearjunk xs . snd x \<noteq> 0]" by (simp add: keys_list_def)
  finally show ?thesis by (simp only: card_keys_def o_def compute_keys_alt)
qed

lemma compute_plus_alt [code]:
  "Pm_fmap xs + Pm_fmap ys = Pm_fmap (clearjunk0 (fmmap_keys (\<lambda>k v. lookup0 xs k + lookup0 ys k) (xs ++\<^sub>f ys)))"
  by (simp only: compute_plus_pp PM_clearjunk0_cong)

lemma compute_minus_alt [code]:
  "Pm_fmap xs - Pm_fmap ys = Pm_fmap (clearjunk0 (fmmap_keys (\<lambda>k v. lookup0 xs k - lookup0 ys k) (xs ++\<^sub>f ys)))"
  by (simp only: compute_minus_pp PM_clearjunk0_cong)

subsection \<open>Generating Cyclic Polynomials\<close>

definition cycl_pp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat)"
  where "cycl_pp n d i = sparse\<^sub>0 (map (\<lambda>k. (modulo (k + i) n, 1)) [0..<d])"

definition cyclic :: "nat \<Rightarrow> ((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 rat) list"
  where "cyclic n =
            (let xs = [0..<n] in
              (map (\<lambda>d. sparse\<^sub>0 (map (\<lambda>i. (cycl_pp n d i, 1)) xs)) [1..<n]) @ [sparse\<^sub>0 [(cycl_pp n n 0, 1), (0, -1)]]
            )"

end (* theory *)