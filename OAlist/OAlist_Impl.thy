(*  Author: Florian Haftmann, TU Muenchen
    Author: Andreas Lochbihler, ETH Zurich
*)

section \<open>Ordered association lists\<close>

theory OAlist_Impl
imports Compare
begin

lemma set_map_filter: "set (List.map_filter f xs) = (\<Union>x\<in>set xs. set_option (f x))"
by(auto simp add: map_filter_def intro: rev_image_eqI)

context comparator_on_base
begin

fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option"
where
  "lookup [] x = None"
| "lookup ((k, v) # xs) x =
  (case compare x k of LESS \<Rightarrow> None
   | EQUAL \<Rightarrow> Some v
   | GREATER \<Rightarrow> lookup xs x)"

context
  fixes dflt :: "'b"
begin

fun lookup_default :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b"
where
  "lookup_default [] x = dflt"
| "lookup_default ((k, v) # xs) x =
  (case compare x k of LESS \<Rightarrow> dflt
   | EQUAL \<Rightarrow> v
   | GREATER \<Rightarrow> lookup_default xs x)"

end

lemma lookup_default_alt_def:
  "lookup_default dflt xs k = (case lookup xs k of None \<Rightarrow> dflt | Some v \<Rightarrow> v)"
by(induction xs k rule: lookup_default.induct)(simp_all split: comparison.split)

end

context comparator_on begin \<comment>\<open>Move\<close>

lemma dsorted_by_filter: "\<lbrakk> dsorted_by xs; xs \<in> lists D \<rbrakk> \<Longrightarrow> dsorted_by (filter P xs)"
by(induction xs)(auto simp add: dsorted_above_conv_dsorted_by intro!: dsorted_above_dsorted_byI)

end

lemma map_in_lists: "map f xs \<in> lists A \<longleftrightarrow> xs \<in> lists (f -` A)"
by auto

lemma filter_in_listsI [simp]: "xs \<in> lists A \<Longrightarrow> filter P xs \<in> lists A"
by auto

context comparator_eq_on begin

lemma lookup_conv_map_of:
  "\<lbrakk> c.dsorted_by (compare_vimage fst compare) xs; map fst xs \<in> lists D; k \<in> D \<rbrakk>
  \<Longrightarrow> lookup xs k = map_of xs k"
apply(induction xs)
apply(auto 4 4 split: comparison.split simp add: dsorted_above_vimage dsorted_by_vimage dsorted_above_conv_dsorted_by in_lists_conv_set compare_refl map_of_eq_None_iff dest: compare_trans' compare_eq_EQUALD intro: sym)
done

lemma lookup_map_value:
  "\<lbrakk> k \<in> D; map fst xs \<in> lists D \<rbrakk>
  \<Longrightarrow> lookup (map (\<lambda>(k, v). (k, f k v)) xs) k = map_option (f k) (lookup xs k)"
by(induct xs)(auto split: comparison.split dest: compare_eq_EQUALD)

lemma lookup_eq_None_iff:
  "\<lbrakk> c.dsorted_by (compare_vimage fst compare) xs; map fst xs \<in> lists D; k \<in> D \<rbrakk> 
  \<Longrightarrow> lookup xs k = None \<longleftrightarrow> k \<notin> fst ` set xs"
by(induction xs)(auto 4 3 split: comparison.splits simp add: compare_refl comparator_on.dsorted_above_conv_dsorted_by[OF comparator_on_vimage] map_in_lists compare_vimage_def dest: compare_eq_EQUALD compare_trans')

lemma lookup_eq_Some_iff:
  "\<lbrakk> c.dsorted_by (compare_vimage fst compare) xs; map fst xs \<in> lists D; k \<in> D \<rbrakk> 
  \<Longrightarrow> lookup xs k = Some v \<longleftrightarrow> (k, v) \<in> set xs"
by(induction xs)(auto 4 3 split: comparison.splits simp add: compare_refl comparator_on.dsorted_above_conv_dsorted_by[OF comparator_on_vimage] map_in_lists compare_vimage_def dest: compare_eq_EQUALD compare_trans')

lemma lookup_filter:
  "\<lbrakk> c.dsorted_by (compare_vimage fst compare) xs; k \<in> D; map fst xs \<in> lists D \<rbrakk>
  \<Longrightarrow> lookup (filter P xs) k = (case lookup xs k of None \<Rightarrow> None | Some v \<Rightarrow> if P (k, v) then Some v else None)"
by(auto 4 3 split: option.split simp add: lookup_eq_None_iff lookup_eq_Some_iff comparator_on.dsorted_by_filter[OF comparator_on_vimage] map_in_lists dest: comparator_on.dsorted_by_distinct[OF comparator_on, THEN eq_key_imp_eq_value, folded dsorted_by_vimage])

lemma dom_lookup_default_subset:
  "fst ` set xs \<subseteq> D
  \<Longrightarrow> {k\<in>D. lookup_default dflt xs k \<noteq> dflt} \<subseteq> fst ` set xs"
by(induct xs)(auto split: comparison.split_asm dest: compare_eq_EQUALD)

lemma lookup_default_eq_default:
  "\<lbrakk> c.dsorted_by (compare_vimage fst compare) xs; map fst xs \<in> lists D; k \<in> D \<rbrakk>
  \<Longrightarrow> lookup_default dflt xs k = dflt \<longleftrightarrow> (k \<in> fst ` set xs \<longrightarrow> (k, dflt) \<in> set xs)"
by(auto simp add: lookup_default_alt_def lookup_conv_map_of dsorted_by_vimage split: option.split dest!: dsorted_by_distinct intro: rev_image_eqI)

lemma dom_lookup_default:
  "\<lbrakk> c.dsorted_by (compare_vimage fst compare) xs; map fst xs \<in> lists D \<rbrakk>
  \<Longrightarrow> {k\<in>D. lookup_default dflt xs k \<noteq> dflt} = fst ` set [(k, v)\<leftarrow>xs. v \<noteq> dflt]"
apply(rule set_eqI)
apply(rule iffI)
 apply(fastforce simp add: lookup_default_eq_default in_lists_conv_set intro: rev_image_eqI)
apply(subgoal_tac "x \<in> D")
 apply(clarsimp simp add: lookup_default_eq_default in_lists_conv_set dsorted_by_vimage)
 apply(auto 4 3 dest: eq_key_imp_eq_value intro: rev_image_eqI dest!: dsorted_by_distinct)
done

lemma finite_dom_lookup_default:
  "fst ` set xs \<subseteq> D \<Longrightarrow> finite {k\<in>D. lookup_default dflt xs k \<noteq> dflt}"
by(rule finite_subset[OF dom_lookup_default_subset]) simp_all

end

lemma lookup_conv_map_of':
  "\<lbrakk> comparator_eq cmp; c.dsorted_by (compare_vimage fst cmp) xs \<rbrakk>
  \<Longrightarrow> c.lookup cmp xs = map_of xs"
by(auto intro: comparator_eq_on.lookup_conv_map_of)

lemma dom_lookup_default:
  "\<lbrakk> c.dsorted_by (compare_vimage fst cmp) xs; comparator_eq cmp \<rbrakk>
  \<Longrightarrow> {k. c.lookup_default cmp dflt xs k \<noteq> dflt} = fst ` set [(k, v)\<leftarrow>xs. v \<noteq> dflt]"
by(drule (1) comparator_eq_on.dom_lookup_default[where dflt=dflt]) simp_all

lemma finite_dom_lookup_default:
  "comparator_eq cmp \<Longrightarrow> finite {k. comparator_on_base.lookup_default cmp dflt xs k \<noteq> dflt}"
using comparator_eq_on.finite_dom_lookup_default[of cmp UNIV xs dflt] by simp

context
  fixes cmp :: "'a comparator"
  assumes "comparator cmp"
begin

interpretation c: comparator_on cmp UNIV by fact
interpretation c': comparator_on "compare_vimage fst cmp" UNIV by(rule comparator_vimageI) fact

lemma lookup_default_eqI:
  "\<lbrakk> (k, v) \<in> set xs; c.dsorted_by (compare_vimage fst cmp) xs \<rbrakk>
  \<Longrightarrow> c.lookup_default cmp dflt xs k = v"
by(induction xs)(auto 4 3 split: comparison.split simp add: c.compare_refl c'.dsorted_above_conv_dsorted_by compare_vimage_def dest: c.compare_trans')

end

lemma range_lookup_default: "Set.range (c.lookup_default cmp dflt xs) - {dflt} = ran (c.lookup cmp xs) - {dflt}"
by(auto 4 3 simp add: c.lookup_default_alt_def[abs_def] ran_def split: option.splits intro: rev_image_eqI)

context 
  fixes cmp :: "'a comparator"
  assumes "comparator_eq cmp"
begin

interpretation c: comparator_eq_on cmp UNIV by fact

lemma lookup_default_eq_default: "k \<notin> fst ` set xs \<Longrightarrow> c.lookup_default cmp dflt xs k = dflt"
by(induction xs)(auto 4 3 split: comparison.split dest: c.compare_eq_EQUALD)

interpretation c': comparator_on "compare_vimage fst cmp" UNIV by (rule comparator_vimageI, rule c.comparator_on_axioms) 

lemma lookup_default_filter:
  "c.dsorted_by (compare_vimage fst cmp) xs
  \<Longrightarrow> c.lookup_default cmp dflt (filter P xs) k =
     (let v = c.lookup_default cmp dflt xs k in if P (k, v) then v else dflt)"
by(induction xs)(fastforce split: comparison.splits simp add: Let_def c'.dsorted_above_conv_dsorted_by compare_vimage_def c.compare_refl dest: c.compare_eq_EQUALD c.compare_trans' intro: lookup_default_eq_default)+

end

context comparator_on_base begin

context fixes k :: 'a and v :: "'b" begin

fun update_by :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list"
where
  "update_by [] = [(k, v)]"
| "update_by ((k', v') # xs) =
  (case compare k k' of LESS \<Rightarrow> (k, v) # (k', v') # xs
                     | EQUAL \<Rightarrow> (k, v) # xs
                   | GREATER \<Rightarrow> (k', v') # update_by xs)"

end

lemma set_update_by_subset:
  "set (update_by k v xs) \<subseteq> insert (k, v) (set xs)"
by(induction xs)(auto split: comparison.splits)

lemma in_set_update_by_weakD:
  "x \<in> set (update_by k v xs) \<Longrightarrow> x = (k, v) \<or> x \<in> set xs"
using set_update_by_subset[of k v xs] by auto

end

context
  fixes cmp :: "'a comparator"
  and D :: "'a set"
  assumes cmp: "comparator_on cmp D"
begin

interpretation c: comparator_on cmp D by fact

lemma dsorted_above_update_by:
  "\<lbrakk> c.dsorted_above (compare_vimage fst cmp) (x, y) xs; k \<in> D; map fst xs \<in> lists D; cmp x k = LESS \<rbrakk>
  \<Longrightarrow> c.dsorted_above (compare_vimage fst cmp) (x, y) (c.update_by cmp k v xs)"
apply(induction xy\<equiv>"(x, y)" xs arbitrary: x y rule: c.dsorted_above.induct)
 apply(simp add: compare_vimage_def)
apply(clarsimp simp add: dsorted_above_vimage c.compare_eq_GREATER split: comparison.splits)
apply(auto dest: c.compare_trans' simp add: c.dsorted_above_subst_EQUAL in_lists_conv_set compare_vimage_def)
done

lemma dsorted_by_update_by:
  "\<lbrakk> c.dsorted_by (compare_vimage fst cmp) xs; k \<in> D; map fst xs \<in> lists D \<rbrakk>
  \<Longrightarrow> c.dsorted_by (compare_vimage fst cmp) (c.update_by cmp k v xs)"
apply(induct rule: c.dsorted_by.induct)
apply(fastforce split: comparison.splits simp add: dsorted_above_vimage dsorted_by_vimage c.dsorted_above_subst_EQUAL in_lists_conv_set c.compare_eq_GREATER intro!: dsorted_above_update_by[unfolded dsorted_above_vimage fst_conv])+
done

end

context
  fixes cmp :: "'a comparator"
  and D :: "'a set"
  assumes cmp: "comparator_eq_on cmp D"
begin

interpretation c: comparator_eq_on cmp D by fact

lemma set_update_by:
  "\<lbrakk> c.dsorted_by (compare_vimage fst cmp) xs; k \<in> D; map fst xs \<in> lists D \<rbrakk>
  \<Longrightarrow> set (c.update_by cmp k v xs) = set xs - {k} \<times> UNIV \<union> {(k, v)}"
apply(induction xs)
 apply simp
apply(clarsimp split: comparison.split simp add: c.dsorted_above_conv_dsorted_by dsorted_above_vimage dsorted_by_vimage)
apply(fastforce dest: c.compare_trans' c.compare_eq_EQUALD simp add: c.compare_refl)+
done

end

context comparator_on_base begin

fun remove_by :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove_by x [] = []"
| "remove_by x (y # ys) = (case compare x y of
     LESS    \<Rightarrow> (y # ys)
   | EQUAL   \<Rightarrow> ys
   | GREATER \<Rightarrow> (y # remove_by x ys))"

lemma set_remove_by_subset:
  "set (remove_by x xs) \<subseteq> set xs"
by(induct xs)(auto split: comparison.split)

lemma in_set_remove_byD:
  "y \<in> set (remove_by x xs) \<Longrightarrow> y \<in> set xs"
using set_remove_by_subset[of x xs] by auto

end

context comparator_on begin

lemma dsorted_above_remove_by:
  "\<lbrakk> dsorted_above x xs; x \<in> D; xs \<in> lists D; y \<in> D \<rbrakk>
  \<Longrightarrow> dsorted_above x (remove_by y xs)"
by(induction rule: dsorted_above.induct)(auto split: comparison.split simp add: dsorted_above_conv_dsorted_by in_lists_conv_set dest: compare_trans')

lemma dsorted_by_remove_by:
  "\<lbrakk> dsorted_by xs; xs \<in> lists D; x \<in> D \<rbrakk>
  \<Longrightarrow> dsorted_by (remove_by x xs)"
by(cases xs)(auto simp add: dsorted_above_remove_by dsorted_above_conv_dsorted_by in_lists_conv_set split: comparison.split)

end

lemma map_remove_by:
  assumes "inj f"
  shows "map f (c.remove_by cmp x xs) = c.remove_by (compare_vimage (inv f) cmp) (f x) (map f xs)"
by(induction xs)(auto simp add: compare_vimage_def assms split: comparison.split)

lemma remove_by_cong:
  assumes "xs = xs'"
  and "\<And>y. y \<in> set xs' \<Longrightarrow> cmp x y = cmp' x' y"
  shows "c.remove_by cmp x xs = c.remove_by cmp' x' xs'"
unfolding assms(1) using assms(2)
by(induction xs')(auto split: comparison.split)

context comparator_eq_on begin

lemma set_remove_by:
  "\<lbrakk> dsorted_by xs; xs \<in> lists D; x \<in> D \<rbrakk>
  \<Longrightarrow> set (remove_by x xs) = set xs - {x}"
apply(induction xs)
apply(simp_all add: dsorted_above_conv_dsorted_by compare_refl split: comparison.split)
apply(fastforce simp add: compare_refl dest: compare_trans' compare_eq_EQUALD)
done

end

context comparator_on_base begin

function merge_by :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge_by [] ys = ys"
| "merge_by xs [] = xs"
| "merge_by (x # xs) (y # ys) =
  (case compare x y of LESS \<Rightarrow> x # merge_by xs (y # ys)
                    | EQUAL \<Rightarrow> x # merge_by xs ys
                  | GREATER \<Rightarrow> y # merge_by (x # xs) ys)"
by pat_completeness auto
termination by lexicographic_order

end

context comparator_on begin

lemma dsorted_above_merge_by:
  "\<lbrakk> dsorted_above x xs; dsorted_above x ys; x \<in> D; xs \<in> lists D; ys \<in> lists D \<rbrakk>
  \<Longrightarrow> dsorted_above x (merge_by xs ys)"
by(induction xs ys arbitrary: x rule: merge_by.induct)
  (auto split: comparison.split intro: dsorted_above_mono simp add: compare_eq_GREATER compare_refl intro: dsorted_above_subst)

lemma dsorted_by_merge_by:
  "\<lbrakk> dsorted_by xs; dsorted_by ys; xs \<in> lists D; ys \<in> lists D \<rbrakk> \<Longrightarrow> dsorted_by (merge_by xs ys)"
by(cases "(xs, ys)" rule: merge_by.cases)(auto split: comparison.split intro!: dsorted_above_merge_by simp add: compare_eq_GREATER intro: dsorted_above_subst)

end

context comparator_eq_on begin

lemma set_merge_by:
  "\<lbrakk> dsorted_by xs; dsorted_by ys; xs \<in> lists D; ys \<in> lists D \<rbrakk>
  \<Longrightarrow> set (merge_by xs ys) = set xs \<union> set ys"
by(induction xs ys rule: merge_by.induct)(auto split: comparison.split simp add: dsorted_above_conv_dsorted_by dest: compare_eq_EQUALD)

end


lemma distinct_map_filter: "distinct (map f xs) \<Longrightarrow> distinct (map f (filter P xs))"
by(induction xs) auto


context 
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c option"
begin

definition filter_map2 :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'c) list"
where "filter_map2 xs = map (\<lambda>(k, v). (k, the v)) (filter (\<lambda>(k, v). v \<noteq> None) (map (\<lambda>(k, v). (k, f k v)) xs))"

lemma filter_map2_code [code]:
  "filter_map2 [] = []"
  "filter_map2 ((k, v) # xs) =
  (case f k v of None \<Rightarrow> filter_map2 xs
   | Some w \<Rightarrow> (k, w) # filter_map2 xs)"
by(auto simp add: filter_map2_def Let_def)

lemma set_filter_map2: "set (filter_map2 xs) = {(k, the (f k v)) | k v. (k, v) \<in> set xs \<and> f k v \<noteq> None}"
by(auto 4 4 simp add: filter_map2_def intro: rev_image_eqI elim: sym)

lemma distinct_filter_map2: "distinct (map fst xs) \<Longrightarrow> distinct (map fst (filter_map2 xs))"
by(simp add: filter_map2_def o_def split_beta distinct_map_filter)

end

context
  fixes cmp :: "'a comparator"
  assumes comparator_eq: "comparator_eq cmp"
begin

interpretation c: comparator_eq_on cmp UNIV by fact
interpretation c': comparator_on "compare_vimage fst cmp" UNIV
by(rule comparator_vimageI) unfold_locales

lemma dsorted_by_filter_map2:
  "\<lbrakk> c.dsorted_by (compare_vimage fst cmp) xs; xs \<in> lists (D \<times> UNIV) \<rbrakk>
  \<Longrightarrow> c.dsorted_by (compare_vimage fst cmp) (filter_map2 f xs)"
by(simp add: c'.dsorted_by_filter filter_map2_def o_def split_def dsorted_by_vimage[symmetric])

lemma lookup_strip_map2:
  "c.dsorted_by (compare_vimage fst cmp) xs
  \<Longrightarrow> c.lookup cmp (filter_map2 f xs) k = Option.bind (c.lookup cmp xs k) (f k)"
by(simp add: filter_map2_def dsorted_by_vimage[symmetric] o_def split_beta Let_def c.lookup_map_value c.lookup_filter split: option.split)

end

lemma (in comparator_on) LESS_trans':
  "\<lbrakk> compare x y = LESS; compare y z = LESS; x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> compare z x = GREATER"
unfolding compare_eq_GREATER by(rule compare_trans')



context
  fixes cmp :: "'a comparator"
begin

context
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'd"
  and g :: "'a \<Rightarrow> 'c \<Rightarrow> 'd"
  and h :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"
begin

function oa_zip_with :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'c) list \<Rightarrow> ('a \<times> 'd) list"
where
  "oa_zip_with [] ys = map (\<lambda>(k, v). (k, g k v)) ys"
| "oa_zip_with xs [] = map (\<lambda>(k, v). (k, f k v)) xs"
| "oa_zip_with ((k, v) # xs) ((k', v') # ys) =
  (case cmp k k' of
     LESS \<Rightarrow> (k, f k v) # oa_zip_with xs ((k', v') # ys)
   | EQUAL \<Rightarrow> (k, h k v v') # oa_zip_with xs ys
   | GREATER \<Rightarrow> (k', g k' v') # oa_zip_with ((k, v) # xs) ys)"
by pat_completeness auto
termination by lexicographic_order

context
  assumes "comparator cmp"
begin

interpretation c: comparator_on cmp UNIV by fact

lemma dsorted_above_oa_zip_with:
  "\<lbrakk> c.dsorted_above cmp x (map fst xs);
     c.dsorted_above cmp x (map fst ys) \<rbrakk>
  \<Longrightarrow> c.dsorted_above cmp x (map fst (oa_zip_with xs ys))"
apply(induction xs ys arbitrary: x rule: oa_zip_with.induct)
apply(auto split: comparison.split simp add: c.dsorted_above_subst_EQUAL c.compare_eq_GREATER o_def split_beta)
done

lemma dsorted_by_oa_zip_with:
  "\<lbrakk> c.dsorted_by cmp (map fst xs);
     c.dsorted_by cmp (map fst ys) \<rbrakk>
  \<Longrightarrow> c.dsorted_by cmp (map fst (oa_zip_with xs ys))"
apply(cases "(xs, ys)" rule: oa_zip_with.cases)
apply(auto simp add: o_def split_beta c.dsorted_above_subst_EQUAL c.compare_eq_GREATER split: comparison.split intro!: dsorted_above_oa_zip_with)
done

end

context
  assumes "comparator_eq cmp"
begin

interpretation c: comparator_eq_on cmp UNIV by fact

lemma lookup_oa_zip_with:
  "c.lookup cmp (oa_zip_with xs ys) k =
  (case (c.lookup cmp xs k, c.lookup cmp ys k) of
     (None, None) \<Rightarrow> None
   | (Some v, None) \<Rightarrow> Some (f k v)
   | (None, Some v') \<Rightarrow> Some (g k v')
   | (Some v, Some v') \<Rightarrow> Some (h k v v'))"
proof(induction xs ys rule: oa_zip_with.induct)
  case 3 thus ?case
    by(simp split: comparison.split option.split_asm cong: option.case_cong)
      (auto split: comparison.split_asm option.split_asm simp add: c.compare_eq_GREATER dest!: c.compare_eq_EQUALD dest: c.LESS_trans' simp add: c.compare_refl)
qed(simp_all add: c.lookup_map_value split: option.split)

lemma set_oa_zip_with:
  "\<lbrakk> c.dsorted_by (compare_vimage fst cmp) xs; c.dsorted_by (compare_vimage fst cmp) ys \<rbrakk>
  \<Longrightarrow> set (oa_zip_with xs ys) =
      (\<lambda>k. (k, case (c.lookup cmp xs k, c.lookup cmp ys k) of
                 (Some v, None) \<Rightarrow> f k v
               | (None, Some v') \<Rightarrow> g k v'
               | (Some v, Some v') \<Rightarrow> h k v v')) ` (fst ` set xs \<union> fst ` set ys)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> _ = ?l xs ys ` _")
proof(induction xs ys rule: oa_zip_with.induct)
  case (1 ys) thus ?case
    apply(simp add: image_image)
    apply(rule image_cong[OF refl])
    apply(auto split: option.split simp add: c.lookup_eq_None_iff c.lookup_eq_Some_iff dsorted_by_vimage dest: c.dsorted_by_distinct[THEN eq_key_imp_eq_value])
    done
next
  case (2 xs) thus ?case
    apply(simp add: image_image)
    apply(rule image_cong[OF refl])
    apply(auto split: option.split simp add: c.lookup_eq_None_iff c.lookup_eq_Some_iff dsorted_by_vimage dest: c.dsorted_by_distinct[THEN eq_key_imp_eq_value])
    done
next
  case (3 k v xs k' v' ys)
  from "3.prems"
  have xs: "c.dsorted_by (compare_vimage fst cmp) xs" 
    and ys: "c.dsorted_by (compare_vimage fst cmp) ys"
    by(simp_all add: c.dsorted_above_conv_dsorted_by dsorted_by_vimage dsorted_above_vimage)
  show ?case
  proof(cases "cmp k k'")
    case LESS
    moreover hence "cmp k' k = GREATER" by(simp add: c.compare_eq_GREATER)
    moreover note "3.IH"(1)[OF LESS xs "3.prems"(2)]
    moreover {
      fix x
      assume "x \<in> fst ` set xs \<union> fst ` set ys"
      moreover
      let ?thesis = "?l xs ((k', v') # ys) x = ?l ((k, v) # xs) ((k', v') # ys) x"
      { assume "x \<in> fst ` set xs" "x \<notin> fst ` set ys"
        moreover hence "cmp k x = LESS" "c.lookup cmp ys x = None" using "3.prems"(1) ys
          by(auto simp add: dsorted_above_vimage c.dsorted_above_conv_dsorted_by c.lookup_eq_None_iff)
        ultimately have ?thesis
          by(auto split: option.split comparison.split dest!: c.compare_eq_EQUALD dest: c.LESS_trans' simp add: c.compare_refl)
      } moreover {
        assume "x \<in> fst ` set ys" "x \<notin> fst ` set xs"
        moreover hence "cmp k' x = LESS" "c.lookup cmp xs x = None" using "3.prems" xs
          by(auto simp add: dsorted_above_vimage c.dsorted_above_conv_dsorted_by c.lookup_eq_None_iff)
        ultimately have ?thesis using LESS
          by(auto split: option.split comparison.split dest!: c.compare_eq_EQUALD dest: c.LESS_trans' simp add: c.compare_refl)
      } moreover {
        assume "x \<in> fst ` set xs" "x \<in> fst ` set ys"
        moreover hence "cmp k x = LESS" "cmp k' x = LESS" using "3.prems"
          by(auto simp add: dsorted_above_vimage c.dsorted_above_conv_dsorted_by)
        ultimately have ?thesis
          by(auto split: option.split comparison.split dest!: c.compare_eq_EQUALD dest: c.LESS_trans' simp add: c.compare_refl)
      }
      ultimately have ?thesis by blast }
    ultimately show ?thesis
      apply(simp add: c.compare_refl cong: comparison.case_cong option.case_cong)
      apply(subst (2) insert_commute)
      apply(rule arg_cong[where f="\<lambda>A. insert x (insert y A)" for x y])
      apply(rule image_cong, simp_all)
      done
  next
    case EQUAL
    hence [simp]: "k = k'" by(auto dest: c.compare_eq_EQUALD)
    note "3.IH"(2)[OF EQUAL xs ys]
    moreover {
      fix x
      assume "x \<in> fst ` set xs \<union> fst ` set ys"
      hence "cmp x k = GREATER" using "3.prems"
        by(auto simp add: dsorted_above_vimage c.dsorted_above_conv_dsorted_by c.compare_eq_GREATER)
      hence "?l xs ys x = ?l ((k, v) # xs) ((k', v') # ys) x" by(simp)
    }
    ultimately show ?thesis using EQUAL
      apply simp
      apply(rule arg_cong[where f="insert x" for x])
      apply(rule image_cong, simp_all)
      done
  next
    case GREATER
    moreover hence "cmp k' k = LESS" by(simp add: c.compare_eq_GREATER)
    moreover note "3.IH"(3)[OF GREATER "3.prems"(1) ys]
    moreover {
      fix x
      assume "x \<in> fst ` set xs \<union> fst ` set ys"
      moreover
      let ?thesis = "?l ((k, v) # xs) ys x = ?l ((k, v) # xs) ((k', v') # ys) x"
      { assume "x \<in> fst ` set xs" "x \<notin> fst ` set ys"
        moreover hence "cmp k x = LESS" "c.lookup cmp ys x = None" using "3.prems"(1) ys
          by(auto simp add: dsorted_above_vimage c.dsorted_above_conv_dsorted_by c.lookup_eq_None_iff)
        ultimately have ?thesis using GREATER
          by(auto split: option.split comparison.split dest!: c.compare_eq_EQUALD dest: c.LESS_trans' simp add: c.compare_refl)
      } moreover {
        assume "x \<in> fst ` set ys" "x \<notin> fst ` set xs"
        moreover hence "cmp k' x = LESS" "c.lookup cmp xs x = None" using "3.prems" xs
          by(auto simp add: dsorted_above_vimage c.dsorted_above_conv_dsorted_by c.lookup_eq_None_iff)
        ultimately have ?thesis
          by(auto split: option.split comparison.split dest!: c.compare_eq_EQUALD dest: c.LESS_trans' simp add: c.compare_refl)
      } moreover {
        assume "x \<in> fst ` set xs" "x \<in> fst ` set ys"
        moreover hence "cmp k x = LESS" "cmp k' x = LESS" using "3.prems"
          by(auto simp add: dsorted_above_vimage c.dsorted_above_conv_dsorted_by)
        ultimately have ?thesis
          by(auto split: option.split comparison.split dest!: c.compare_eq_EQUALD dest: c.LESS_trans' simp add: c.compare_refl)
      }
      ultimately have ?thesis by blast }
    ultimately show ?thesis
      apply(simp add: c.compare_refl)
      apply(rule arg_cong[where f="\<lambda>A. insert x (insert y A)" for x y])
      apply(rule image_cong, simp_all)
      done
  qed
qed

end

end

context
  assumes "comparator_eq cmp"
begin

interpretation c: comparator_eq_on cmp UNIV by fact

lemma oa_zip_with_map_value:
  "\<lbrakk> c.dsorted_by cmp xs; c.dsorted_by cmp ys \<rbrakk>
  \<Longrightarrow> oa_zip_with f g h (map (\<lambda>k. (k, p k)) xs) (map (\<lambda>k. (k, q k)) ys)
  = map (\<lambda>k. (k, if k \<in> set xs then if k \<in> set ys then h k (p k) (q k) else f k (p k) else g k (q k)))
     (c.merge_by cmp xs ys)"
proof(induction xs ys taking: cmp rule: c.merge_by.induct)
  case (3 x xs y ys)
  from "3.prems" have xs: "c.dsorted_by cmp xs" and ys: "c.dsorted_by cmp ys"
    by(simp_all add: c.dsorted_above_conv_dsorted_by)
  show ?case
  proof(cases "cmp x y")
    case LESS
    with "3.prems"
    have "x \<noteq> y" "x \<notin> set ys"
      by(auto simp add: c.dsorted_above_conv_dsorted_by c.compare_refl dest: c.compare_trans')
    thus ?thesis using LESS "3.IH"(1) xs "3.prems"(2)
      by(simp add: c.set_merge_by)
  next
    case EQUAL
    hence "x = y" "x \<notin> set xs" "y \<notin> set ys"
      using "3.prems" by(auto dest!: c.compare_eq_EQUALD dest: c.compare_trans' simp add: c.dsorted_above_conv_dsorted_by c.compare_refl)
    thus ?thesis using EQUAL "3.IH"(2) xs ys by(auto simp add: c.set_merge_by)
  next
    case GREATER
    with "3.prems"
    have "x \<noteq> y" "y \<notin> set xs"
      by(auto simp add: c.dsorted_above_conv_dsorted_by c.compare_refl dest: c.compare_trans')
    thus ?thesis using GREATER "3.IH"(3) ys "3.prems"(1)
      by(simp add: c.set_merge_by)
  qed
qed simp_all

end

context
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'd option"
  and g :: "'a \<Rightarrow> 'c \<Rightarrow> 'd option"
  and h :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd option"
begin

definition oa_zip_with' :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'c) list \<Rightarrow> ('a \<times> 'd) list"
where "oa_zip_with' xs ys = map (\<lambda>(k, v). (k, the v)) (filter (\<lambda>(k, v). v \<noteq> None) (oa_zip_with f g h xs ys))"

lemma oa_zip_with'_code [code]:
  "oa_zip_with' [] ys = filter_map2 g ys"
  "oa_zip_with' xs [] = filter_map2 f xs"
  "oa_zip_with' ((k, v) # xs) ((k', v') # ys) =
  (case cmp k k' of
     LESS \<Rightarrow> (case f k v of None \<Rightarrow> oa_zip_with' xs ((k', v') # ys)
              | Some w \<Rightarrow> (k, w) # oa_zip_with' xs ((k', v') # ys))
   | EQUAL \<Rightarrow> (case h k v v' of None \<Rightarrow> oa_zip_with' xs ys
               | Some w \<Rightarrow> (k, w) # oa_zip_with' xs ys)
   | GREATER \<Rightarrow> (case g k' v' of None \<Rightarrow> oa_zip_with' ((k, v) # xs) ys
                 | Some w \<Rightarrow> (k', w) # oa_zip_with' ((k, v) # xs) ys))"
by(simp_all add: oa_zip_with'_def filter_map2_def split: comparison.split option.split)

context
  assumes "comparator cmp"
begin

interpretation c: comparator_on cmp UNIV by fact

lemma dsorted_by_oa_zip_with':
  "\<lbrakk> c.dsorted_by cmp (map fst xs);
     c.dsorted_by cmp (map fst ys) \<rbrakk>
  \<Longrightarrow> c.dsorted_by cmp (map fst (oa_zip_with' xs ys))"
by(simp add: oa_zip_with'_def o_def split_beta dsorted_by_vimage[symmetric] comparator_on.dsorted_by_filter[OF comparator_vimageI[OF c.comparator_on]] dsorted_by_oa_zip_with[folded dsorted_by_vimage, OF c.comparator_on])

end

context
  assumes "comparator_eq cmp"
begin

interpretation c: comparator_eq_on cmp UNIV by fact

lemma lookup_oa_zip_with':
  "\<lbrakk> c.dsorted_by (compare_vimage fst cmp) xs; c.dsorted_by (compare_vimage fst cmp) ys \<rbrakk>
  \<Longrightarrow> c.lookup cmp (oa_zip_with' xs ys) k =
      (case (c.lookup cmp xs k, c.lookup cmp ys k) of
         (None, None) \<Rightarrow> None
       | (Some v, None) \<Rightarrow> f k v
       | (None, Some v') \<Rightarrow> g k v'
       | (Some v, Some v') \<Rightarrow> h k v v')"
by(simp add: oa_zip_with'_def c.lookup_map_value c.lookup_filter dsorted_by_vimage dsorted_by_oa_zip_with[OF c.comparator_on] lookup_oa_zip_with[OF c.comparator_eq_on] split: option.split)

lemma set_oa_zip_with':
  assumes xs: "c.dsorted_by (compare_vimage fst cmp) xs"
  and ys: "c.dsorted_by (compare_vimage fst cmp) ys"
  shows
  "set (oa_zip_with' xs ys) =
   (\<Union>k\<in>fst ` set xs \<union> fst ` set ys. Pair k ` (
       case (c.lookup cmp xs k, c.lookup cmp ys k) of
         (Some v, None) \<Rightarrow> set_option (f k v)
       | (None, Some v') \<Rightarrow> set_option (g k v')
       | (Some v, Some v') \<Rightarrow> set_option (h k v v')))"
  (is "_ = (\<Union>k\<in>_. _ ` ?f k)")
proof -
  let ?f' = "\<lambda>x. case (c.lookup cmp xs x, c.lookup cmp ys x) of
         (Some v, None) \<Rightarrow> f x v
       | (None, Some v') \<Rightarrow> g x v'
       | (Some v, Some v') \<Rightarrow> h x v v'"
  { fix x
    assume "x \<in> fst ` set xs \<union> fst ` set ys"
    hence "set_option (if ?f' x \<noteq> None then Some (x, the (?f' x)) else None) = Pair x ` ?f x"
     by(cases "c.lookup cmp xs x" "c.lookup cmp ys x" rule: option.exhaust[case_product option.exhaust])(simp_all, auto simp add: c.lookup_eq_None_iff xs ys)
  }
  then show ?thesis
    by(simp only: oa_zip_with'_def map_filter_map_filter set_oa_zip_with[OF c.comparator_eq_on assms] set_map_filter UN_simps prod.simps cong: SUP_cong)
qed

end

end

end

end
