theory "Filter_Index_List"
  imports "II_Modest_Base.More_List_Rel"
begin

section \<open>General Lemmas\<close>

text \<open>The following mset lemmas are remnants of an attempt to get rid of the prerequisite that 
  lists have to be distinct. It did not work because we remove by index but at an abstract level
  we don't know which indices have explicitly been removed. In the implementation it is important
  information.

  We kept these lemmas here for those interested.
\<close>
  lemma ENTAILS_trans_pre: "A \<turnstile> B \<Longrightarrow> ENTAILS B C \<Longrightarrow> ENTAILS A C"
    unfolding ENTAILS_def using entails_trans .

  lemma mset_nth_image: "(!) a `# mset [0..< length a] = mset a"
    apply(induction a)
    apply simp
    apply simp
    by (metis add_single_right_eq_add_mset image_mset_single image_mset_union length_Cons map_nth mset.simps(1,2) mset_map
        mset_upt nat_in_between_eq(1) union_code upt_append upt_conv_Cons upt_conv_Nil)

  lemma mset_nth_image_set: "(!) a `# mset_set {x. x < length a} = mset a"
    using mset_nth_image
    by (force simp flip: lessThan_atLeast0 lessThan_def)

  lemma mset_set_Diff':
    "finite A \<Longrightarrow> finite B \<Longrightarrow> mset_set (A - B) = mset_set A - mset_set B" 
    apply(induction A rule: finite_induct) 
    apply simp 
    subgoal for x F
      apply(rule multiset_eqI)
      subgoal for y
        apply(cases "x=y") 
        by (auto simp add: insert_Diff_if)
      done
    done

subsection \<open>Other general lemmas\<close>

  lemma image_nth_card_bound: "\<forall>a\<in>A. a < length xs \<Longrightarrow> card ((\<lambda> x. xs ! x) ` A) \<le> length xs" 
  proof -
    assume BND: "\<forall>a\<in>A. a < length xs"
    hence "((!) xs ` A) \<subseteq> set xs"
      by (simp add: image_subsetI)
    moreover have "finite ((!) xs ` A)" 
      using calculation finite_subset by blast
    ultimately have "card ((\<lambda> x. xs ! x) ` A) \<le> card (set xs)" 
      by (simp add: card_mono)
    thus ?thesis 
      using card_length dual_order.trans by blast
  qed

  lemma image_fun_nth_card_bound: "\<forall>a\<in>A. f a < length xs \<Longrightarrow> card ((\<lambda> x. xs ! (f x)) ` A) \<le> length xs" 
  proof -
    assume BND: "\<forall>a\<in>A. f a < length xs"
    hence "(\<lambda> x. xs ! (f x)) ` A \<subseteq> set xs"
      by (simp add: image_subsetI)
    moreover have "finite ((\<lambda> x. xs ! (f x)) ` A)" 
      using calculation finite_subset by blast
    ultimately have "card ((\<lambda> x. xs ! f x) ` A) \<le> card (set xs)" 
      by (simp add: card_mono)
    thus ?thesis 
      using card_length dual_order.trans by blast
  qed

  lemma ex_list_with_elems: "\<exists> xs. length xs = n \<and> (\<forall> i < length xs. xs ! i = f i)"
    proof(induction n)
      case 0
      then show ?case 
        by auto
    next
      case (Suc n)
      then obtain xs where "length xs = n" and "(\<forall>i<length xs. xs ! i = f i)" by blast
      then show ?case
        using less_Suc_eq by(auto intro!: exI[where?x="xs @ [f n]"])
    qed

  lemma distinctI: "(\<And> i j. i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i = xs ! j \<Longrightarrow> i = j) \<Longrightarrow> distinct xs"
    using distinct_conv_nth by blast

  lemma option_assn_option_rel: "hr_comp snat.option_assn (\<langle>nat_rel\<rangle>option_rel) = snat.option_assn"
    unfolding hn_ctxt_def hr_comp_def option_rel_def snat.option_assn_def 
    apply(rule ext)+
    by (auto simp: sep_algebra_simps)  


section \<open>Filter Set\<close>

text \<open>A Filter Set is a set of elements of a list that have not been filtered yet. For performance
  reasons we assume the list to be distinct. We filter by list index for performance reasons as
  well. This allows us to filter one element in O(1). Also, since we filter by index, we don't know
  on the abstract level which index has been removed and which one hasn't with this abstraction.\<close>

  type_synonym 'a filter_set = "'a list \<times> 'a set"
  type_synonym 'a filter_setc = "'a list \<times> sizeopt list"
  type_synonym 'ai filter_seti = "'ai \<times> size_t ptr"

subsection \<open>Abstract operations\<close>

  definition op_create_filter_set :: "'a list \<Rightarrow> 'a filter_set" where 
    "op_create_filter_set xs = (xs,set xs)"

  definition op_filter_elem_id :: "'a filter_set \<Rightarrow> nat \<Rightarrow> 'a filter_set" where 
    "op_filter_elem_id = (\<lambda> (xs, X) i. (xs, X - {(xs ! i)}))"


subsection \<open>Concrete operatons\<close>

  locale filter_set_invar_defs = 
    fixes FS :: "'a filter_setc"
  begin

    definition "xs = (\<lambda> (xs,ids). xs) FS"
    definition "ids = (\<lambda> (xs,ids). ids) FS"

    definition "fs_\<alpha> = {(xs ! i) | i. i < length xs \<and> ids ! i \<noteq> None }"

    definition \<alpha> :: "'a filter_set" where "\<alpha> = (xs, fs_\<alpha>)"

    lemma \<alpha>_xs_eq: "\<alpha>=(xs',fs') \<Longrightarrow> xs' = xs"
      unfolding \<alpha>_def by blast

  end

  lemma FS_simps[simp]: 
    "filter_set_invar_defs.xs (xs,ids) = xs"
    "filter_set_invar_defs.ids (xs,ids) = ids"
    unfolding filter_set_invar_defs.xs_def filter_set_invar_defs.ids_def
    by auto


  definition create_filter_set_impl :: "'a list \<Rightarrow> 'a filter_setc" where 
    "create_filter_set_impl xs = (xs, replicate (length xs) (Some 0))"
  sepref_register create_filter_set_impl

  definition filter_elem_id_impl :: "'a filter_setc \<Rightarrow> nat \<Rightarrow> 'a filter_setc" where 
    "filter_elem_id_impl = (\<lambda> (xs, ids) i. (xs, ids[i:=None]))"
  sepref_register filter_elem_id_impl

  locale filter_set_invar = filter_set_invar_defs FS for FS +
    assumes Len_eq: "length ids = length xs"
    assumes Dist_xs: "distinct xs"
  begin

    lemma(in -) create_filter_set_impl_\<alpha>: "op_create_filter_set a = filter_set_invar_defs.\<alpha> (create_filter_set_impl a)"
      unfolding op_create_filter_set_def filter_set_invar_defs.\<alpha>_def filter_set_invar_defs.fs_\<alpha>_def create_filter_set_impl_def
      by( fastforce simp: in_set_conv_nth) 
  
    lemma(in -) create_filter_set_impl_invar: "distinct a \<Longrightarrow> filter_set_invar (create_filter_set_impl a)"
      unfolding create_filter_set_impl_def
      apply(unfold_locales)
      by auto
  
    lemma filter_elem_id_impl_\<alpha>: "(xs',ids') = \<alpha> \<Longrightarrow> i < length xs' \<Longrightarrow> filter_set_invar_defs.\<alpha> (filter_elem_id_impl FS i) = op_filter_elem_id \<alpha> i"
      unfolding filter_set_invar_defs.\<alpha>_def filter_set_invar_defs.fs_\<alpha>_def filter_elem_id_impl_def op_filter_elem_id_def 
      apply(cases FS)
      using Len_eq Dist_xs Len_eq nth_eq_iff_index_eq
      apply (auto simp: nth_list_update') 
      done

    lemma filter_elem_id_impl_invar: "i < length xs' \<Longrightarrow> (xs', ids') = \<alpha> \<Longrightarrow> filter_set_invar (filter_elem_id_impl FS i)"
      unfolding filter_elem_id_impl_def
      apply(cases FS)
      apply(unfold_locales)
      using Len_eq Dist_xs by auto
      
  end


subsection \<open>Refinement Relation\<close>

  definition "filter_set_rel = br filter_set_invar_defs.\<alpha> filter_set_invar"

  lemma filter_set_rel_lengthD: "((xs, ids), xs', fs) \<in> filter_set_rel \<Longrightarrow> length ids = length xs' \<and> length xs = length xs'"
    unfolding filter_set_rel_def
    apply(auto simp: in_br_conv filter_set_invar_def filter_set_invar_defs.\<alpha>_def)
    done

  lemma create_filter_set_impl_correct: "(create_filter_set_impl, op_create_filter_set) \<in> [distinct]\<^sub>f Id \<rightarrow> filter_set_rel"
    unfolding filter_set_rel_def
    apply(rule frefI)
    by(auto simp: in_br_conv create_filter_set_impl_\<alpha> create_filter_set_impl_invar) 
    
  lemma filter_elem_id_impl_correct: "(uncurry filter_elem_id_impl, uncurry op_filter_elem_id) \<in> [\<lambda> ((xs,ids),i). i < length xs]\<^sub>f filter_set_rel \<times>\<^sub>r nat_rel \<rightarrow> filter_set_rel"
    unfolding filter_set_rel_def
    apply(rule frefI)
    apply(auto simp: in_br_conv intro!: filter_set_invar.filter_elem_id_impl_\<alpha>[symmetric] filter_set_invar.filter_elem_id_impl_invar)
    done


  lemma filter_set_rel_eq_xs: "((xs,ids),xs',fs) \<in> filter_set_rel \<Longrightarrow> xs'=xs"
    unfolding filter_set_rel_def by(auto simp: in_br_conv filter_set_invar_defs.\<alpha>_def)


subsection \<open>Sepref implementation\<close>


locale filter_set_env_defs = 
  fixes L :: "'a list \<Rightarrow> 'li::llvm_rep \<Rightarrow> assn"
  and leni :: "'li \<Rightarrow> size_t llM"
begin

  definition "filter_set_assn_aux = L \<times>\<^sub>a IICF_Array.array_assn size_option_assn"

  definition "filter_set_assn = hr_comp filter_set_assn_aux filter_set_rel"

end


locale filter_index_env = filter_set_env_defs L leni for L :: "'a list \<Rightarrow> 'li::llvm_rep \<Rightarrow> assn" and leni +
  assumes leni_ref[sepref_fr_rules]: "(leni, (RETURN o op_list_length)) \<in> L\<^sup>k \<rightarrow>\<^sub>a size_assn"
begin
  sepref_register leni


  sepref_definition create_filter_set_impl_ll is "(RETURN o create_filter_set_impl)" :: "L\<^sup>d \<rightarrow>\<^sub>a filter_set_assn_aux"
    unfolding create_filter_set_impl_def filter_set_assn_aux_def
    apply (annot_snat_const "TYPE(size_T)")
    apply (rewrite array_fold_custom_replicate)
    apply sepref
    done

  sepref_definition filter_elem_id_impl_ll is "uncurry (RETURN oo filter_elem_id_impl)" :: "[\<lambda> ((xs,ids),i). i < length ids]\<^sub>a filter_set_assn_aux\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> filter_set_assn_aux"
    unfolding filter_elem_id_impl_def filter_set_assn_aux_def
    apply sepref
    done

  context 
    notes [fcomp_norm_unfold] = filter_set_assn_def[symmetric] 
    notes [simp] = filter_set_rel_lengthD
  begin

    lemmas create_filter_set_impl_hnr [sepref_fr_rules] = create_filter_set_impl_ll.refine[FCOMP create_filter_set_impl_correct]
    lemmas filter_elem_id_impl_hnr [sepref_fr_rules] = filter_elem_id_impl_ll.refine[FCOMP filter_elem_id_impl_correct]

  end

end




section \<open>Filter Index List\<close>

text \<open>
  The goal of this data structure is to turn a set into a distinct list. I.e. we apply an 
  indexing to the unfiltered entries. Any entry that maps to \<open>Some 0\<close> gets assigned a unique
  value x (i.e. they map to \<open>Some x\<close>). Entries that map to \<open>None\<close> remain unchanged.
\<close>

  (*TODO generalize to arbitrary word size*)
  type_synonym 'a filter_list = "'a list \<times> 'a list"
  type_synonym 'a filter_listc = "'a list \<times> sizeopt list \<times> nat"
  type_synonym 'ai filter_listi = "'ai \<times> size_t ptr \<times> size_t" 

  definition mop_create_filter :: "'a filter_set \<Rightarrow> 'a filter_list nres" where 
    "mop_create_filter = (\<lambda> (xs,fs). SPEC (\<lambda> (xs',fas). xs' = xs \<and> fs = set fas \<and> distinct xs' \<and> distinct fas))"

  definition op_length_filtered :: "'a filter_list \<Rightarrow> nat" where
    "op_length_filtered = (\<lambda> (xs,fs). length fs)"

  definition op_length_orig :: "'a filter_list \<Rightarrow> nat" where
    "op_length_orig = (\<lambda> (xs,fs). length xs)"

  definition op_is_filtered_index :: "'a filter_list \<Rightarrow> nat \<Rightarrow> bool" where
    "op_is_filtered_index = (\<lambda> (xs,fs) i. xs ! i \<notin> set fs)"

  definition mop_filter_index_select :: "'a filter_list \<Rightarrow> nat \<Rightarrow> nat option nres" where
    "mop_filter_index_select = (\<lambda> (xs,fs) i. SELECT (\<lambda> r. r < length fs \<and> fs ! r = xs ! i))"

  definition op_filter_index_from_orig :: "'a filter_list \<Rightarrow> nat \<Rightarrow> nat" where 
    "op_filter_index_from_orig = (\<lambda> (xs,fs) i. index fs (xs ! i))"

subsection \<open>Refinement Relation\<close>

  locale filter_list_defs = 
    fixes FA :: "'a filter_listc"
  begin

    definition "xs = (\<lambda> (xs,ids,c). xs) FA"
    definition "ids = (\<lambda> (xs,ids,c). ids) FA"
    definition "c = (\<lambda> (xs,ids,c). c) FA"

    definition filter_map :: "nat \<Rightarrow> 'a" where "filter_map i = xs ! (index ids (Some i))"

subsubsection \<open>Abstraction function\<close>

    definition "fas_index_map fas \<equiv> c = length fas \<and> (\<forall>i < length ids. case (ids ! i) of None \<Rightarrow> xs ! i \<notin> set fas | Some v \<Rightarrow> fas ! v = xs ! i)"
    definition "fas_\<alpha> = (THE fas. fas_index_map fas)"

    definition \<alpha> :: "'a filter_list" where "\<alpha> = (xs, fas_\<alpha>)"

    lemma \<alpha>_xs_eq: "\<alpha>=(xs',ids') \<Longrightarrow> xs' = xs"
      unfolding \<alpha>_def by blast


  end


subsubsection \<open>Invariant\<close>

  lemma FA_simps[simp]: 
    "filter_list_defs.xs (xs,ids,c) = xs"
    "filter_list_defs.ids (xs,ids,c) = ids"
    "filter_list_defs.c (xs,ids,c) = c"
    unfolding filter_list_defs.xs_def filter_list_defs.ids_def filter_list_defs.c_def
    by auto

  locale filter_list_invar = filter_list_defs FA for FA +
    assumes Len_eq: "length ids = length xs"
    assumes Dist_xs: "distinct xs"

    assumes Cover: "\<forall> j < c. \<exists> i < length ids. ids ! i = Some j"
    assumes Upper: "\<forall> i < length ids. \<forall>j. ids ! i = Some j \<longrightarrow> j < c"
    assumes Unique: "\<forall> i\<^sub>1 < length ids. \<forall> i\<^sub>2 < length ids. ids ! i\<^sub>2 \<noteq> None \<longrightarrow> ids ! i\<^sub>1 = ids ! i\<^sub>2 \<longrightarrow> i\<^sub>1 = i\<^sub>2"

  begin

    lemma fas_index_mapD1: "fas_index_map fas \<Longrightarrow> c = length fas"
      unfolding fas_index_map_def by blast

    lemma fas_index_mapD2: "fas_index_map fas \<Longrightarrow> (\<forall>i<length ids. case ids ! i of None \<Rightarrow> xs ! i \<notin> set fas | Some v \<Rightarrow> fas ! v = xs ! i)"
      unfolding fas_index_map_def
      by blast

    lemma fas_index_mapI: "c = length fas \<Longrightarrow> (\<forall>i<length ids. case ids ! i of None \<Rightarrow> xs ! i \<notin> set fas | Some v \<Rightarrow> fas ! v = xs ! i) \<Longrightarrow> fas_index_map fas"
      unfolding fas_index_map_def by blast

    lemma fas_index_mapD2': "fas_index_map fas \<Longrightarrow> (\<forall>i < length fas. fas ! i = filter_map i)"
      unfolding fas_index_map_def filter_map_def 
      by (auto split: option.splits simp: Cover in_set_conv_nth) 

    lemma fas_index_mapD': "fas_index_map fas \<Longrightarrow> c = length fas \<and> (\<forall>i < length fas. fas ! i = filter_map i)"
      unfolding fas_index_map_def filter_map_def 
      by (auto split: option.splits simp: Cover in_set_conv_nth) 

    lemma fas_index_mapI': "c = length fas \<Longrightarrow> (\<forall>i < length fas. fas ! i = filter_map i) \<Longrightarrow> fas_index_map fas"
      unfolding fas_index_map_def filter_map_def 
      apply (auto split: option.splits) 
      apply (metis Cover Dist_xs Len_eq index_less_size_conv index_nth_id nth_index nth_mem option.discI)
      by (metis Unique Upper index_less_size_conv nth_index nth_mem option.discI) (*TODO improve*)

    lemma fas_index_map_nth_None: "fas_index_map fas \<Longrightarrow> i < length xs \<Longrightarrow> ids ! i = None \<longleftrightarrow> xs ! i \<notin> set fas"
      unfolding fas_index_map_def 
      apply(clarsimp simp: Len_eq split: option.splits)
      by (metis Len_eq Upper not_None_eq2 nth_mem)

    lemma fas_index_map_nth_Some: "fas_index_map fas \<Longrightarrow> v < c \<Longrightarrow> i < length xs \<Longrightarrow> ids ! i = Some v \<longleftrightarrow> fas ! v = xs ! i"
      unfolding fas_index_map_def 
      apply(clarsimp simp: Len_eq split: option.splits)
      by (metis Cover Dist_xs Len_eq index_nth_id)
                                          
    lemma ex_filter_map: "\<exists> fas. c = length fas \<and> (\<forall>i < length fas. fas ! i = filter_map i)"
      using ex_list_with_elems filter_map_def by metis

    lemma ex_fas_index_map: "\<exists> fas. fas_index_map fas"
      by (metis ex_filter_map fas_index_mapI')

    lemma unique_filter_map: "\<And> fas\<^sub>1 fas\<^sub>2. c = length fas\<^sub>1 \<Longrightarrow> (\<forall>i < length fas\<^sub>1. fas\<^sub>1 ! i = filter_map i) \<Longrightarrow> c = length fas\<^sub>2 \<Longrightarrow> (\<forall>i < length fas\<^sub>2. fas\<^sub>2 ! i = filter_map i) \<Longrightarrow> fas\<^sub>1 = fas\<^sub>2" 
      apply(rule nth_equalityI) 
      apply argo
      by presburger

    lemma unique_fas_index_map: "\<And> fas\<^sub>1 fas\<^sub>2. fas_index_map fas\<^sub>1 \<Longrightarrow> fas_index_map fas\<^sub>2 \<Longrightarrow> fas\<^sub>1 = fas\<^sub>2"
      by (metis unique_filter_map fas_index_mapD1 fas_index_mapD2')

    lemma ex_unique_filter_map: "\<exists>! fas. c = length fas \<and> (\<forall>i < length fas. fas ! i = filter_map i)"
      using unique_filter_map ex_filter_map
      by auto

    lemma ex_unique_fas_index_map: "\<exists>! fas. fas_index_map fas"
      using ex_fas_index_map unique_fas_index_map by blast

    lemma fas_index_map_fas_\<alpha>[simp]: "fas_index_map fas_\<alpha>"
      unfolding fas_\<alpha>_def
      using theI'[OF ex_unique_fas_index_map] .

    lemma fas_index_map_eq_fas_\<alpha>: "fas_index_map fas \<Longrightarrow> fas = fas_\<alpha>"
      by (simp add: fas_index_map_fas_\<alpha> unique_fas_index_map)

    lemma ex_nth_ids: "j < c \<Longrightarrow> \<exists> i < length xs. i = index ids (Some j)"
      by (metis Cover Len_eq index_less_size_conv nth_mem)

    lemma xs_nth_eq_iff_index_eq: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i = xs ! j \<longleftrightarrow> i = j"
      by (simp add: Dist_xs nth_eq_iff_index_eq)

    lemma index_ids_eq_iff_val_eq: "x < c \<Longrightarrow> y < c \<Longrightarrow> index ids (Some x) = index ids (Some y) \<longleftrightarrow> x = y"
      by (metis Len_eq ex_nth_ids index_less_size_conv nth_index option.inject)

    lemmas xs_nth_eq_then_index_eq = xs_nth_eq_iff_index_eq[THEN iffD1]
    lemmas index_ids_eq_then_val_eq = index_ids_eq_iff_val_eq[THEN iffD1]

    lemma c_len_fas_\<alpha>: "c = length fas_\<alpha>"
      using fas_index_mapD1 fas_index_map_fas_\<alpha> by blast

    lemma inj_on_filter_map: "inj_on filter_map {..<c}"
      unfolding filter_map_def
      apply(rule inj_onI)
      apply(rule index_ids_eq_then_val_eq)
      apply blast
      apply blast
      apply(rule xs_nth_eq_then_index_eq)
      apply(auto dest: ex_nth_ids)
      done

    lemma c_leq_len_xs[simp]: "c \<le> length xs" 
    proof -
      have "c = card (filter_map ` {..<c})" 
        using inj_on_filter_map[THEN card_image, symmetric] 
        by simp
      moreover have "card (filter_map ` {..<c}) \<le> length xs"
        unfolding filter_map_def
        apply(rule image_fun_nth_card_bound)
        using ex_nth_ids by blast
      ultimately show ?thesis
        by presburger
    qed


    lemma ex_filter_index: "fas_index_map fas \<Longrightarrow> xs ! i \<in> set fas \<Longrightarrow>  i < length xs \<Longrightarrow> \<exists> v. ids ! i = Some v"
      unfolding fas_index_map_def by (auto split: option.splits simp: Len_eq) 

    lemma ex_ids_index:
      assumes FIM: "fas_index_map fas"
      assumes VL: "v < length fas"
      shows "\<exists> i < length xs. ids ! i = Some v \<and> fas ! v = xs ! i"
    proof -
      from FIM have "\<forall>i<length fas. fas ! i = filter_map i" 
        using fas_index_mapD2' by presburger
      with VL have A: "fas ! v = filter_map v" 
        by presburger

      from VL have VC: "v < c"
        using fas_index_mapD1[OF FIM] by simp
      with Cover obtain i where IL: "i < length ids" and IDSI: "ids ! i = Some v" 
        by blast
      with Unique have "\<forall> j < length ids. ids ! j = ids ! i \<longrightarrow> j = i"
        by force
      hence "index ids (Some v) = i"
        apply (simp add: index_eq_iff IL order_less_imp_le IDSI )
        using IL order_less_trans by blast
      with A have "fas ! v = xs ! i"
        using filter_map_def by presburger
      with IDSI IL show ?thesis
        by(auto simp: Len_eq)
    qed

    lemmas fas_\<alpha>_ex_ids_index = ex_ids_index[OF fas_index_map_fas_\<alpha>]

    lemma fas_index_map_distinct: "fas_index_map fas \<Longrightarrow> distinct fas"
    proof(rule distinctI)
      fix v w
      assume FIM: "fas_index_map fas"
      and VL: "v < length fas"
      and WL: "w < length fas"
      and EQ: "fas ! v = fas ! w"
      from FIM VL obtain i where IL: "i<length xs" and IV:"ids ! i = Some v" and FV: "fas ! v = xs ! i" 
        using ex_ids_index
        by blast
      from FIM WL obtain j where JL: "j<length xs" and JW:"ids ! j = Some w" and FW: "fas ! w = xs ! j" 
        using ex_ids_index
        by blast

      from EQ FV FW have "xs ! i = xs ! j" by presburger
      with Dist_xs IL JL have "i = j" unfolding distinct_conv_nth by blast
      with IV JW show "v = w" by auto
    qed

    lemma distinct_fas_\<alpha>[simp]: "distinct fas_\<alpha>"
      using fas_index_map_distinct fas_index_map_fas_\<alpha> by blast


    lemma set_fas_index_map_mem: "fas_index_map fas \<Longrightarrow> x \<in> set fas \<longleftrightarrow> (\<exists>i v. i < length xs \<and> v < length fas \<and> ids ! i = Some v \<and> x = fas ! v)"
      apply(force simp: in_set_conv_nth Len_eq dest: ex_ids_index)
      done
      
    lemma set_fas_\<alpha>_mem: "x \<in> set fas_\<alpha> \<longleftrightarrow> (\<exists>i v. i < length xs \<and> v < length fas_\<alpha> \<and> ids ! i = Some v \<and> x = fas_\<alpha> ! v)"
      using set_fas_index_map_mem by auto

    lemma fas_xs_nth_to_ids_nth1: "fas_index_map fas \<Longrightarrow> i < length xs \<Longrightarrow> ids ! i = Some v \<Longrightarrow> xs ! i = fas ! v"
      unfolding fas_index_map_def by(auto split: option.splits simp: Len_eq)


    lemma fas_xs_nth_to_ids_nth: 
      assumes FIM: "fas_index_map fas"
      and IL: "i < length xs"
      and VLC: "v < c"
      shows "xs ! i = fas ! v \<longleftrightarrow> ids ! i = Some v"
    proof
      assume ASM: "xs ! i = fas ! v"
      hence "ids ! i \<noteq> None"
        by (metis FIM IL VLC fas_index_mapD1 fas_index_map_nth_None nth_mem)
      then obtain v' where A: "ids ! i = Some v'" and VLC': "v' < c"
        using IL Len_eq Upper by auto
      hence "fas ! v' = xs ! i"
        using FIM IL fas_index_map_nth_Some by blast
      with VLC' ASM have "v' = v"
        by (metis FIM VLC distinct_conv_nth fas_index_mapD1 fas_index_map_distinct)
      with A show "ids ! i = Some v" 
        by presburger
    next 
      assume "ids ! i = Some v"
      thus "xs ! i = fas ! v"
        using fas_xs_nth_to_ids_nth1[OF FIM IL] by simp
    qed

    lemma fas_\<alpha>_xs_nth_to_ids_nth: "i < length xs \<Longrightarrow> v < c \<Longrightarrow> xs ! i = fas_\<alpha> ! v \<longleftrightarrow> ids ! i = Some v"
      using fas_xs_nth_to_ids_nth by simp

    lemmas fas_\<alpha>_nth_None = fas_index_map_nth_None[OF fas_index_map_fas_\<alpha>] 
    lemmas fas_\<alpha>_nth_Some = fas_index_map_nth_Some[OF fas_index_map_fas_\<alpha>]

    lemma fas_index_map_index_fas_eq_the_ids:
      assumes FIM: "fas_index_map fas"
      and OUT: "ids ! i = Some v"
      and IL: "i < length xs"
      shows "index fas (xs ! i) = the (ids ! i)"
    proof - 
      from OUT have "xs ! i = fas ! v" 
        using fas_xs_nth_to_ids_nth1[OF FIM IL] by presburger
      hence "v = index fas (xs ! i)" 
        by (metis FIM IL Len_eq OUT Upper c_len_fas_\<alpha> distinct_fas_\<alpha> ex_unique_fas_index_map fas_index_map_fas_\<alpha> index_nth_id)
      thus ?thesis 
        by (simp add: OUT)
    qed

    lemmas fas_\<alpha>_index_fas_eq_the_ids = fas_index_map_index_fas_eq_the_ids[OF fas_index_map_fas_\<alpha>]

  end

subsection \<open>Concrete operations\<close>


  locale create_filter_list_defs = 
    fixes N :: nat
    fixes xs :: "'a list"
    fixes ids\<^sub>0 :: "sizeopt list"
    fixes it :: "nat set"
    fixes cids :: "nat \<times> sizeopt list"
  begin
    definition "ci = (\<lambda> (c,ids). c) cids"
    definition "idsi = (\<lambda> (c,ids). ids) cids"
  end

  lemma cids_simps[simp]: 
    "create_filter_list_defs.ci (ci,idsi) = ci"
    "create_filter_list_defs.idsi (ci,idsi) = idsi"
    unfolding create_filter_list_defs.ci_def create_filter_list_defs.idsi_def
    by auto

  lemma card_A_minus_B_leq_card_A: "finite A \<Longrightarrow> card (A - B) \<le> card A"
    by (simp add: card_mono)  

  locale create_filter_list_invar = create_filter_list_defs +
    assumes Len_eq: "length idsi = N"
    assumes Len_eq2: "length ids\<^sub>0 = N"
    assumes Len_eq3: "length xs = N"
    assumes Cover: "\<forall> j < ci. \<exists> i \<in> {i. i < length xs \<and> i \<notin> it}. idsi ! i = Some j"
    assumes Upper: "(\<forall> i \<in> {i. i < length xs \<and> i \<notin> it}. \<forall>j. idsi ! i = Some j \<longrightarrow> j < ci)"
    assumes Unique: "\<forall> i \<in> {i. i < length xs \<and> i \<notin> it}. \<forall> j \<in> {i. i < length xs \<and> i \<notin> it}. idsi ! j \<noteq> None \<longrightarrow>  idsi ! i = idsi ! j \<longrightarrow> i = j"
    assumes Eq_set: "{i. i < length xs \<and> ids\<^sub>0 ! i \<noteq> None } = {i. i < length xs \<and> idsi ! i \<noteq> None }"
    assumes C_bound: "ci \<le> length xs - card (it) \<and> finite it \<and> card it \<le> length xs"
  begin

    lemma step:
      assumes XIT: "x \<in> it"
      assumes XLXS: "x < length xs"
      assumes CIDS: "cids = (c',ids')"
      assumes IDS: "ids' ! x \<noteq> None"
      shows "create_filter_list_invar N xs ids\<^sub>0 (it - {x}) (c' + 1, ids'[x := Some c'])"
    proof -

      have A[simp]: "c' = ci" "ids' = idsi"
        by (auto simp: CIDS)

      have AUX1: "\<exists>i<length xs. (i \<in> it \<longrightarrow> i = x) \<and> idsi[x := Some ci] ! i = Some j" if "j < Suc ci" for j
      proof(cases "j = ci")
        case True
        then show ?thesis 
          using Len_eq Len_eq3 XLXS by auto
      next
        case False
        with that have "j < ci"
          by simp
        with Cover obtain i where "i < length xs" and INI: "i \<notin> it" and "idsi ! i = Some j" 
          by blast
        moreover from XIT INI have "i \<noteq> x"
          by blast
        ultimately show ?thesis
          by force
      qed

      have AUX2: "idsi[x := Some ci] ! i = Some j \<Longrightarrow> j < Suc ci" if "i < length xs" and "i \<in> it \<longrightarrow> i = x" for i j
        apply(cases "j=ci")
        apply blast
        apply(cases "i \<in> it")
        using Len_eq that(1) that(2) using Len_eq3 apply auto[1]
        apply(subgoal_tac "i \<noteq> x") 
        using Upper that(1) apply auto[1]
        using XIT by blast

      have AUX3:"Suc ci \<le> length xs - (card it - 1)"
        apply(subst Suc_diff[symmetric])
        using C_bound XIT card_gt_0_iff nat_geq_1_eq_neqz by auto

        

      show ?thesis
        apply(unfold_locales)
        subgoal by (simp add: Len_eq)
        subgoal by (simp add: Len_eq2)
        subgoal by (simp add: Len_eq3)
        subgoal using AUX1 by auto
        subgoal using AUX2 by (auto simp: Len_eq)
        subgoal 
          apply (clarsimp simp: Len_eq Len_eq2 Len_eq3) (*TODO proper proof with case splits*)
          by (metis (no_types, lifting) Len_eq Len_eq3 Unique Upper XLXS less_not_refl mem_Collect_eq nth_list_update option.distinct(1))
        subgoal using Eq_set IDS by (auto simp: Len_eq nth_list_update')
        subgoal 
          using C_bound AUX3 by (auto simp: C_bound XIT le_imp_diff_le) 
        done
    qed

    lemma final_invar: "it = {} \<Longrightarrow> distinct xs \<Longrightarrow> filter_list_invar (xs,idsi,ci)"
      apply(unfold_locales)
      subgoal by (simp add: Len_eq Len_eq3)
      subgoal by auto
      subgoal using Cover Len_eq Len_eq3 by auto
      subgoal by (simp add: Len_eq Len_eq3 Upper)
      subgoal by (simp add: Len_eq Len_eq3 Unique)
      done

    lemma final_distinct:
      assumes ITE: "it = {}"
      assumes DIST: "distinct xs" 
      assumes ADEF: "filter_list_defs.\<alpha> (xs, idsi, ci) = (xs', fas')"
      shows "distinct fas'"
    proof -
      from final_invar ITE DIST interpret filter_list_invar "(xs,idsi,ci)" .
      
      show ?thesis
        using ADEF
        unfolding filter_list_defs.\<alpha>_def
        using distinct_fas_\<alpha> by auto
    qed

    lemma final_eq_set:
      assumes ITE: "it = {}"
      assumes DIST: "distinct xs"
      shows "filter_set_invar_defs.fs_\<alpha> (xs, ids\<^sub>0) = set (filter_list_defs.fas_\<alpha> (xs, idsi, ci))"
    proof -
      from final_invar ITE DIST interpret filter_list_invar "(xs,idsi,ci)" .
      
      have CID[simp]: "length fas_\<alpha> = ci"
        using fas_index_mapD1 by auto

      {
        fix i v
        assume "ids\<^sub>0 ! i = Some v" and IL: "i < length xs"
        then obtain v' where A: "idsi ! i = Some v'" 
          using Eq_set by blast 
        hence B: "v' < ci"
          using Len_eq Upper IL by auto
        have C: "xs ! i = fas_\<alpha> ! v'"  
          unfolding fas_\<alpha>_xs_nth_to_ids_nth[simplified, OF IL B]
          using A by blast
        from A B C have "\<exists>v'. idsi ! i = Some v' \<and> v' < ci \<and> xs ! i = fas_\<alpha> ! v'"
          by blast
      } note AUX1 = this

      {
        fix i v
        assume IL: "i < length xs" and VLC: "v < ci" and X: "idsi ! i = Some v"
        hence A: "xs ! i = fas_\<alpha> ! v"
          using fas_\<alpha>_xs_nth_to_ids_nth[simplified, OF IL VLC] by presburger
        have B: "ids\<^sub>0 ! i \<noteq> None" 
          using Eq_set IL X by auto
        from IL A B have "\<exists> i. fas_\<alpha> ! v = xs ! i \<and> i < length xs \<and> (\<exists>y. ids\<^sub>0 ! i = Some y)"
          by force
      } note AUX2 = this
      

      show ?thesis
        unfolding filter_set_invar_defs.fs_\<alpha>_def
        apply (force simp: set_fas_\<alpha>_mem dest: AUX1 AUX2)
        done
    qed
      
  end



  definition create_filter_list :: "'a filter_setc \<Rightarrow> 'a filter_listc nres" where "create_filter_list = (\<lambda> (xs,ids\<^sub>0). do{
    ASSERT(distinct xs);
    let N = length xs;
    (c,ids) \<leftarrow> nfoldli [0..<N] (\<lambda>_. True) (\<lambda> it (c,ids). do{
      ASSERT(it < N \<and> length ids = length xs);
      if is_None (ids ! it) then
        RETURN (c,ids)
      else do{
        let ids = ids[it:=Some c];
        ASSERT(c < N);
        RETURN (c+1,ids)
      }
    }) (0,ids\<^sub>0);
    RETURN (xs,ids,c)
  })"
  sepref_register create_filter_list :: "'a filter_setc \<Rightarrow> 'a filter_listc nres"

  definition fa_length_filtered :: "'a filter_listc \<Rightarrow> nat" where
    "fa_length_filtered = (\<lambda> (xs,ids,c). c)"
  sepref_register fa_length_filtered

  definition fa_length_orig :: "'a filter_listc \<Rightarrow> nat" where
    "fa_length_orig = (\<lambda> (xs,ids,c). length xs)"
  sepref_register fa_length_orig

  definition fa_is_filtered_index :: "'a filter_listc \<Rightarrow> nat \<Rightarrow> bool" where
    "fa_is_filtered_index = (\<lambda> (xs,ids,c) i. ids ! i = None)"
  sepref_register fa_is_filtered_index

  definition fa_filter_index_select :: "'a filter_listc \<Rightarrow> nat \<Rightarrow> nat option nres" where
    "fa_filter_index_select = (\<lambda> (xs,ids,c) i. do{ ASSERT (i < length ids); RETURN (ids ! i)})"
  sepref_register fa_filter_index_select

  definition fa_filter_index_from_orig :: "'a filter_listc \<Rightarrow> nat \<Rightarrow> nat" where
    "fa_filter_index_from_orig = (\<lambda> (xs,ids,c) i. the (ids ! i))"
  sepref_register fa_filter_index_from_orig


  lemma create_filter_list_invar1:
    assumes INV: "(\<forall>j<c. \<exists>i<length xs'. i \<notin> it \<and> ids ! i = Some j)"
    assumes XSD: "xs = xs'"
    assumes IL: "i < length xs'"
    assumes LC: "length ids = length xs'"
    assumes IIT: "i \<in> it"
    assumes CD[simp]: "c' = c + 1"
    assumes IDSD[simp]: "ids' = ids[i := Some c]"
    assumes JC': "(j::nat) < c'"
    shows "\<exists>ia<length xs'. ia \<notin> it - {i} \<and> ids' ! ia = Some j"
  proof(cases "j = c")
    case [simp]: True

    show ?thesis
      by(auto simp: IL LC intro!: exI[where ?x=i])
  next
    case False
    with JC' have JC: "j < c"
      by force
    then obtain i' where "i' < length xs'" and I'N: "i' \<notin> it" and "ids ! i' = Some j"
      using INV by auto
    moreover have "i' \<noteq> i"
      using IIT I'N by auto
    ultimately show ?thesis by(auto intro!: exI[where ?x=i']) 
  qed

  lemma create_filter_list_invar2:
    assumes IIT: "i \<in> it"
    assumes "i < length xs'"
    assumes OUT: "ids[i := Some c] ! i' = Some j"
    assumes I'L: "i' < length xs'"
    assumes INV: "\<forall>i. i < length xs' \<and> i \<notin> it \<longrightarrow> (\<forall>j. ids ! i = Some j \<longrightarrow> j < c)"
    assumes I'N: "i' \<notin> it"
    shows "j < Suc c" 
    by (metis IIT OUT I'L INV I'N less_SucI nth_list_update_neq)


subsubsection \<open>Refinement Relation and Proofs\<close>

  definition "filter_list_rel = br filter_list_defs.\<alpha> filter_list_invar"

  lemma create_filter_list_refine:
    assumes REL: "((xs,ids), xs', fs) \<in> filter_set_rel"
    shows "create_filter_list (xs,ids)
       \<le> \<Down> filter_list_rel (mop_create_filter (xs', fs))"
  proof -

    from REL interpret filter_set_invar "(xs, ids)"
      by(auto simp: in_br_conv filter_set_rel_def)

    from REL have [simp]: "xs = xs'" "fs = fs_\<alpha>"
      by(auto simp: in_br_conv filter_set_rel_def filter_set_invar_defs.\<alpha>_def)

    define create_filter_list_aux :: "'a filter_setc \<Rightarrow> 'a filter_listc nres"  where "create_filter_list_aux \<equiv> (\<lambda> (xs,ids\<^sub>0). do{
      ASSERT(distinct xs);
      let N = length xs;
      (c,ids) \<leftarrow> FOREACHi (create_filter_list_invar N xs ids\<^sub>0) {..<N} (\<lambda> it (c,ids). do{
        ASSERT(it < N \<and> length ids = length xs);
        if is_None (ids ! it) then
          RETURN (c,ids)
        else do{
          let ids = ids[it:=Some c];
          ASSERT(c < N);
          RETURN (c+1,ids)
        }
      }) (0,ids\<^sub>0);
      RETURN (xs,ids,c)
    })"

    have "create_filter_list_aux (xs,ids) \<le> \<Down> filter_list_rel (mop_create_filter (xs, fs))"
      unfolding mop_create_filter_def create_filter_list_aux_def filter_list_rel_def
      apply (clarsimp simp: build_rel_SPEC_conv)
      apply(refine_vcg )
      subgoal using Dist_xs by force
      subgoal by blast
      subgoal 
       apply(unfold_locales)
       using Len_eq by auto
      subgoal 
        by (simp add: create_filter_list_invar_def subset_eq)
      subgoal
        by (simp add: create_filter_list_invar_def)
      subgoal
        apply(unfold_locales)
        using create_filter_list_invar.Len_eq apply blast
        using create_filter_list_invar.Len_eq2 apply blast
        using create_filter_list_invar.Len_eq3 apply blast
        using create_filter_list_invar.Cover apply blast
        using create_filter_list_invar.Upper apply force
        using create_filter_list_invar.Unique apply force
        using create_filter_list_invar.Eq_set apply blast
        apply (fastforce dest: create_filter_list_invar.C_bound)
        done
      subgoal for x it \<sigma> c' ids' 
        using Len_eq apply clarsimp
        apply(frule create_filter_list_invar.C_bound)
        apply(frule create_filter_list_invar.Len_eq2)
        apply clarsimp
        by (metis card_0_eq diff_diff_cancel diff_is_0_eq emptyE i_hate_words_helper nless_le)
      subgoal for x it \<sigma> c' ids'
        using create_filter_list_invar.step by fastforce
      subgoal
        using create_filter_list_invar.final_invar by force
      subgoal
        by (auto dest: filter_list_defs.\<alpha>_xs_eq)
      subgoal
        unfolding filter_list_defs.\<alpha>_def 
        using create_filter_list_invar.final_eq_set by fastforce
      subgoal
        by (auto dest: filter_list_defs.\<alpha>_xs_eq)
      subgoal
        using create_filter_list_invar.final_distinct by fastforce
      done


    moreover have "create_filter_list (xs,ids) \<le> \<Down>Id (create_filter_list_aux (xs,ids))"
      unfolding create_filter_list_def create_filter_list_aux_def
      apply(refine_vcg LFOi_refine[where ?A=Id and ?R=Id])
      apply blast
      apply(auto simp: Len_eq zero_upt_list_set_rel)[]
      apply auto 
      done

    ultimately show ?thesis
      by simp

  qed

  lemma fa_filter_index_select_refine:
    assumes IXS: "i < length xs'"
    assumes REL: "((xs, ids, c), xs', fs) \<in> filter_list_rel"
    shows "fa_filter_index_select (xs, ids, c) i \<le> mop_filter_index_select (xs', fs) i"
  proof -

    from REL interpret filter_list_invar "(xs, ids, c)"
      by(auto simp: in_br_conv filter_list_rel_def)

    from REL have [simp]: "xs' = xs" "fs = fas_\<alpha>"
      by(auto simp: in_br_conv filter_list_rel_def \<alpha>_def)

    {
      fix x
      assume A: "ids ! i = None" "x < length fas_\<alpha>" "fas_\<alpha> ! x = xs ! i"
      hence "xs ! i \<in> set fas_\<alpha>"
        using in_set_conv_nth by force
  
      with A(1) have "False"
        using IXS fas_\<alpha>_nth_None by auto
    } note AUX1 = this

    show ?thesis
      unfolding fa_filter_index_select_def mop_filter_index_select_def
      using IXS Upper c_len_fas_\<alpha> fas_\<alpha>_nth_Some 
      by (auto simp: refine_pw_simps pw_le_iff Len_eq[simplified] intro: AUX1) 

  qed


  lemma create_filter_list_correct: "(create_filter_list, mop_create_filter) 
      \<in> filter_set_rel \<rightarrow> \<langle>filter_list_rel\<rangle>nres_rel"
    by (auto simp: in_nres_rel_iff intro: create_filter_list_refine)

  lemma fa_length_filtered_correct: "(fa_length_filtered, op_length_filtered) \<in> filter_list_rel \<rightarrow> nat_rel"
    unfolding fa_length_filtered_def op_length_filtered_def filter_list_rel_def
    by(auto simp: in_br_conv filter_list_defs.\<alpha>_def dest!: filter_list_invar.c_len_fas_\<alpha>) 

  lemma fa_length_orig_correct: "(fa_length_orig, op_length_orig) \<in> filter_list_rel \<rightarrow> nat_rel"
    unfolding fa_length_orig_def op_length_orig_def filter_list_rel_def
    by(auto simp: in_br_conv filter_list_defs.\<alpha>_def dest!: filter_list_invar.c_len_fas_\<alpha>) 

  lemma fa_is_filtered_index_correct: "(uncurry fa_is_filtered_index, uncurry op_is_filtered_index) \<in> [\<lambda> ((xs,ids),i). i < length xs]\<^sub>f filter_list_rel \<times>\<^sub>r nat_rel \<rightarrow> bool_rel"
    unfolding fa_is_filtered_index_def op_is_filtered_index_def filter_list_rel_def
    apply(rule frefI)
    by (auto simp: in_br_conv filter_list_defs.\<alpha>_def dest!: filter_list_invar.fas_\<alpha>_nth_None) 

  lemma fa_filter_index_select_correct: "(uncurry fa_filter_index_select, uncurry mop_filter_index_select) 
    \<in> [\<lambda> ((xs,ids),i). i < length xs]\<^sub>f filter_list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>\<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel"
    by (auto intro!: frefI nres_relI fa_filter_index_select_refine)


  lemma fa_filter_index_from_orig_correct: "(uncurry fa_filter_index_from_orig, uncurry op_filter_index_from_orig) 
    \<in> [\<lambda> ((xs,ids),i). i < length xs \<and> \<not>op_is_filtered_index (xs,ids) i]\<^sub>f filter_list_rel \<times>\<^sub>r nat_rel \<rightarrow> nat_rel"
    unfolding fa_filter_index_from_orig_def op_filter_index_from_orig_def filter_list_rel_def op_is_filtered_index_def
    apply(rule frefI)
    apply (clarsimp simp: in_br_conv filter_list_defs.\<alpha>_def) 
    apply(frule filter_list_invar.fas_\<alpha>_nth_None)
    apply simp
    subgoal for xs ids c i
      apply(auto dest: filter_list_invar.fas_\<alpha>_index_fas_eq_the_ids[where ?v="the(ids!i)"])
      done
    done


lemma filter_list_rel_eq_xs: "((xs,ids,c),xs',fs) \<in> filter_list_rel \<Longrightarrow> xs'=xs"
  unfolding filter_list_rel_def by(auto simp: in_br_conv filter_list_defs.\<alpha>_def)

lemma filter_list_rel_eq_len: "((xs,ids,c),xs',fs) \<in> filter_list_rel \<Longrightarrow> length ids = length xs'"
  unfolding filter_list_rel_def by(auto simp: in_br_conv filter_list_defs.\<alpha>_def dest: filter_list_invar.Len_eq)

lemma filter_list_rel_filtered: "((xs,ids,c),xs',fs) \<in> filter_list_rel \<Longrightarrow> i < length xs' \<Longrightarrow> \<not> op_is_filtered_index (xs',fs) i \<Longrightarrow> \<exists>v. ids ! i = Some v "
  apply(frule filter_list_rel_eq_len)
  unfolding filter_list_rel_def op_is_filtered_index_def filter_list_defs.\<alpha>_def
  apply(clarsimp simp: in_br_conv)  
  apply(frule filter_list_invar.ex_filter_index)
  apply(erule filter_list_invar.fas_index_map_fas_\<alpha>)
  apply auto
  done


subsubsection \<open>Refinement to LLVM\<close>

context filter_set_env_defs
begin

  definition "filter_list_assn_aux = L \<times>\<^sub>a IICF_Array.array_assn size_option_assn \<times>\<^sub>a size_assn"

  definition "filter_list_assn = hr_comp filter_list_assn_aux filter_list_rel"

end

context filter_index_env
begin

  sepref_definition create_filter_list_ll is "create_filter_list" :: "filter_set_assn_aux\<^sup>d \<rightarrow>\<^sub>a filter_list_assn_aux"
    unfolding create_filter_list_def filter_set_assn_aux_def filter_list_assn_aux_def nfoldli_upt_by_while
    apply (annot_snat_const "TYPE(size_T)")
    apply sepref
    done

  sepref_definition fa_length_filtered_ll is "RETURN o fa_length_filtered" :: "filter_list_assn_aux\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding fa_length_filtered_def filter_list_assn_aux_def
    apply sepref
    done

  sepref_definition fa_length_orig_ll is "RETURN o fa_length_orig" :: "filter_list_assn_aux\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding fa_length_orig_def filter_list_assn_aux_def
    apply sepref
    done

  sepref_definition fa_is_filtered_index_ll is "uncurry (RETURN oo fa_is_filtered_index)" :: "[\<lambda> ((xs,ids,c),i). i < length ids]\<^sub>a filter_list_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
    unfolding fa_is_filtered_index_def filter_list_assn_aux_def
    apply sepref
    done

  sepref_definition fa_filter_index_select_ll is "uncurry fa_filter_index_select" :: "filter_list_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_option_assn" 
    unfolding fa_filter_index_select_def filter_list_assn_aux_def
    apply sepref
    done

  sepref_definition fa_filter_index_from_orig_ll is "uncurry (RETURN oo fa_filter_index_from_orig)"  :: "[\<lambda> ((xs,ids,c),i). i < length ids \<and> (\<exists> v. ids ! i = Some v)]\<^sub>a filter_list_assn_aux\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn"
    unfolding fa_filter_index_from_orig_def filter_list_assn_aux_def
    apply sepref
    done

  concrete_definition (in -) create_filter_list_ll' [llvm_code] is filter_index_env.create_filter_list_ll_def
  concrete_definition (in -) fa_length_filtered_ll' [llvm_code] is filter_index_env.fa_length_filtered_ll_def
  concrete_definition (in -) fa_length_orig_ll' [llvm_code] is filter_index_env.fa_length_orig_ll_def
  concrete_definition (in -) fa_is_filtered_index_ll' [llvm_code] is filter_index_env.fa_is_filtered_index_ll_def
  concrete_definition (in -) fa_filter_index_select_ll' [llvm_code] is filter_index_env.fa_filter_index_select_ll_def
  concrete_definition (in -) fa_filter_index_from_orig_ll' [llvm_code] is filter_index_env.fa_filter_index_from_orig_ll_def



  context
    notes[fcomp_norm_unfold] = filter_list_assn_def[symmetric] filter_set_assn_def[symmetric] option_assn_option_rel
    notes [simp] =  filter_list_rel_eq_len filter_list_rel_filtered 
  begin

    lemmas create_filter_list_hnr[sepref_fr_rules] = create_filter_list_ll.refine[FCOMP create_filter_list_correct, unfolded create_filter_list_ll'.refine[OF filter_index_env_axioms]]
    lemmas fa_length_filtered_hnr[sepref_fr_rules] = fa_length_filtered_ll.refine[FCOMP fa_length_filtered_correct, unfolded fa_length_filtered_ll'.refine[OF filter_index_env_axioms]]
    lemmas fa_length_orig_hnr[sepref_fr_rules] = fa_length_orig_ll.refine[FCOMP fa_length_orig_correct, unfolded fa_length_orig_ll'.refine[OF filter_index_env_axioms]]
    lemmas fa_is_filtered_index_hnr[sepref_fr_rules] = fa_is_filtered_index_ll.refine[FCOMP fa_is_filtered_index_correct, unfolded fa_is_filtered_index_ll'.refine[OF filter_index_env_axioms]]
    lemmas fa_filter_index_select_hnr[sepref_fr_rules] = fa_filter_index_select_ll.refine[FCOMP fa_filter_index_select_correct, unfolded fa_filter_index_select_ll'.refine[OF filter_index_env_axioms]]
    lemmas fa_filter_index_from_orig_hnr[sepref_fr_rules] = fa_filter_index_from_orig_ll.refine[FCOMP fa_filter_index_from_orig_correct, unfolded fa_filter_index_from_orig_ll'.refine[OF filter_index_env_axioms]]

  end

end


subsection \<open>Unfiltered Set Open Block\<close>

text \<open>
  This is a technicality that allows us to perform read-only operations to the unfiltered version
  of the list without destroying the assertion.
\<close>

definition unfiltered_set_open_block :: "'a filter_set \<Rightarrow> ('a list \<Rightarrow> 'b nres) \<Rightarrow> 'b nres" where "unfiltered_set_open_block = (\<lambda> (xs,fs) f. f xs)"

context filter_set_env_defs
begin
  
  lemma hn_open_filter_set[sepref_comb_rules]:
    assumes FR: "\<Gamma> \<turnstile> hn_ctxt filter_set_assn p' p ** \<Gamma>1"
    assumes Pair: "\<And> a1' a1. hn_refine (hn_ctxt L a1' a1 \<and>* \<Gamma>1) (f a1) (\<Gamma>1' a1' a1) R CP (f' a1')"
    assumes FR2: "\<And>a1' a1. \<Gamma>1' a1' a1 \<turnstile> hn_ctxt L a1' a1 ** \<Gamma>2'"        
    shows "hn_refine \<Gamma> (case p of (a, b) \<Rightarrow> f a) (hn_ctxt filter_set_assn p' p ** \<Gamma>2')
      R CP (unfiltered_set_open_block$p'$(\<lambda>\<^sub>2 x. f' x))"
      apply(rule hn_refine_cons_pre[OF FR])
      unfolding autoref_tag_defs PROTECT2_def filter_set_assn_def filter_set_assn_aux_def hr_comp_def
      apply(cases p; cases p')
      apply (clarsimp simp:  unfiltered_set_open_block_def hn_ctxt_def sep_conj_exists hnr_pre_ex_conv)
      apply(sepref_to_hoare)
      apply(rule htriple_pure_preI)
      apply(drule pure_part_split_conj, clarify)+
      apply (simp add: )
      apply(frule filter_set_rel_eq_xs)
      supply [vcg_rules] = Pair[THEN hn_refineD, unfolded hn_ctxt_def]
      apply vcg
      apply(rule ENTAILS_trans_pre)  
      apply(sep_drule FR2)
      apply(rule entails_refl)
      unfolding hn_ctxt_def
      apply vcg
      done

  lemma filter_set_open_block_mono[refine_mono]: 
    "\<lbrakk>\<And>a. f a \<le> f' a\<rbrakk> \<Longrightarrow> unfiltered_set_open_block x f \<le> unfiltered_set_open_block x f'"
    unfolding unfiltered_set_open_block_def
    apply(cases x)
    by auto

  lemma filter_set_open_block_arity[sepref_monadify_arity]: "unfiltered_set_open_block \<equiv> \<lambda>\<^sub>2x f. SP unfiltered_set_open_block$x$(\<lambda>\<^sub>2a. f$a)"
    by simp

  lemma filter_set_open_block_comb[sepref_monadify_comb]:  
    "unfiltered_set_open_block$x$f = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP unfiltered_set_open_block$x$f)"
    by simp

  lemma filter_set_open_block_mono_flat[refine_mono]: 
    "\<lbrakk>\<And>a. flat_ge (f a) (f' a)\<rbrakk> \<Longrightarrow> flat_ge (unfiltered_set_open_block x f) (unfiltered_set_open_block x f')"
    unfolding unfiltered_set_open_block_def
    apply(cases x) by simp

  lemma filter_set_SPLIT_rule[refine_vcg]:
      assumes "f (fst x) \<le> SPEC P"
      shows "unfiltered_set_open_block x f \<le> SPEC P"  
      using assms(1) unfolding unfiltered_set_open_block_def 
      apply(cases x)
      by simp

  lemma filter_set_split_refine[refine]:
      assumes "f' (fst x') \<le>\<Down>R (f (fst x))"
      shows "unfiltered_set_open_block x' f' \<le>\<Down>R (unfiltered_set_open_block x f)"
      unfolding unfiltered_set_open_block_def
      using assms
      apply(cases x; cases x')
      by auto

end



subsection \<open>Unfiltered List Open Block\<close>

definition unfiltered_list_open_block :: "'a filter_list \<Rightarrow> ('a list \<Rightarrow> 'b nres) \<Rightarrow> 'b nres" where "unfiltered_list_open_block = (\<lambda> (xs,fs) f. f xs)"

context filter_set_env_defs
begin

  
  lemma hn_open_filter_list[sepref_comb_rules]:
    assumes FR: "\<Gamma> \<turnstile> hn_ctxt filter_list_assn p' p ** \<Gamma>1"
    assumes Pair: "\<And> a1' a1. hn_refine (hn_ctxt L a1' a1 \<and>* \<Gamma>1) (f a1) (\<Gamma>1' a1' a1) R CP (f' a1')"
    assumes FR2: "\<And>a1' a1. \<Gamma>1' a1' a1 \<turnstile> hn_ctxt L a1' a1 ** \<Gamma>2'"        
    shows "hn_refine \<Gamma> (case p of (a, b) \<Rightarrow> f a) (hn_ctxt filter_list_assn p' p ** \<Gamma>2')
      R CP (unfiltered_list_open_block$p'$(\<lambda>\<^sub>2 x. f' x))"
      apply(rule hn_refine_cons_pre[OF FR])
      unfolding autoref_tag_defs PROTECT2_def filter_list_assn_def filter_list_assn_aux_def hr_comp_def
      apply(cases p; cases p')
      apply (clarsimp simp:  unfiltered_list_open_block_def hn_ctxt_def sep_conj_exists hnr_pre_ex_conv)
      apply(sepref_to_hoare)
      apply(rule htriple_pure_preI)
      apply(drule pure_part_split_conj, clarify)+
      apply (simp add: )
      apply(frule filter_list_rel_eq_xs)
      supply [vcg_rules] = Pair[THEN hn_refineD, unfolded hn_ctxt_def]
      apply vcg
      apply(rule ENTAILS_trans_pre)  
      apply(sep_drule FR2)
      apply(rule entails_refl)
      unfolding hn_ctxt_def
      apply vcg
      done

  lemma filter_list_open_block_mono[refine_mono]: 
    "\<lbrakk>\<And>a. f a \<le> f' a\<rbrakk> \<Longrightarrow> unfiltered_list_open_block x f \<le> unfiltered_list_open_block x f'"
    unfolding unfiltered_list_open_block_def
    apply(cases x)
    by auto

  lemma filter_list_open_block_arity[sepref_monadify_arity]: "unfiltered_list_open_block \<equiv> \<lambda>\<^sub>2x f. SP unfiltered_list_open_block$x$(\<lambda>\<^sub>2a. f$a)"
    by simp

  lemma filter_list_open_block_comb[sepref_monadify_comb]:  
    "unfiltered_list_open_block$x$f = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP unfiltered_list_open_block$x$f)"
    by simp

  lemma filter_list_open_block_mono_flat[refine_mono]: 
    "\<lbrakk>\<And>a. flat_ge (f a) (f' a)\<rbrakk> \<Longrightarrow> flat_ge (unfiltered_list_open_block x f) (unfiltered_list_open_block x f')"
    unfolding unfiltered_list_open_block_def
    apply(cases x) by simp

  lemma filter_list_SPLIT_rule[refine_vcg]:
      assumes "f (fst x) \<le> SPEC P"
      shows "unfiltered_list_open_block x f \<le> SPEC P"  
      using assms(1) unfolding unfiltered_list_open_block_def 
      apply(cases x)
      by simp

  lemma filter_list_split_refine[refine]:
      assumes "f' (fst x') \<le>\<Down>R (f (fst x))"
      shows "unfiltered_list_open_block x' f' \<le>\<Down>R (unfiltered_list_open_block x f)"
      unfolding unfiltered_list_open_block_def
      using assms
      apply(cases x; cases x')
      by auto


end

end
