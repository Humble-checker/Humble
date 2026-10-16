theory Array_Nat_Tuple_Partition
  imports "II_Modest_Base.More_B_Assn" "II_Modest_Base.More_snat" "II_Modest_Base.Bind_Const" Array_Nat_Partition
begin


section \<open>Snat Array Map\<close>

datatype tuple_list_id = LIST1 (id1: nat) | LIST2 (id2: nat)

type_synonym 'v dsmt = "'v \<Rightarrow> tuple_list_id option"

type_synonym antpar = "nat set list \<times> nat set list"

type_synonym antparc = "nat \<times> nat \<times> nat dsmt"
type_synonym antparc' = "nat \<times> nat \<times> ((nat, tuple_list_id) i_map)"

type_synonym antpari = "64 Word.word \<times> 64 Word.word \<times> 64 Word.word ptr"

locale disj_set_list_tuple_defs =
  fixes L\<^sub>1::nat \<comment> \<open>The maximal length that list 1 can have\<close>
  fixes N::nat \<comment> \<open>The largest natural number the sets can contain\<close>

  fixes li::size_t
  fixes ni::size_t
begin
 

  definition "tuple_list_id_\<alpha> i = (if i < L\<^sub>1 then LIST1 i else LIST2 (i - L\<^sub>1))"

  definition "tuple_list_id_rel = size_rel O br (tuple_list_id_\<alpha>) (\<lambda> i. True)"    
  
  abbreviation "tuple_list_id_assn \<equiv> pure tuple_list_id_rel"

  lemma tuple_list_id_assn_alt: "tuple_list_id_assn = hr_comp size_assn (br (tuple_list_id_\<alpha>) (\<lambda> i. True))"
    unfolding tuple_list_id_rel_def
    by(auto simp: hr_comp_pure)

  lemma LIST1_tuple_list_id_\<alpha>: "LIST1 i = tuple_list_id_\<alpha> j \<Longrightarrow> i = j \<and> j < L\<^sub>1" 
    unfolding tuple_list_id_\<alpha>_def
    by(auto split: if_splits)

  lemma LIST2_tuple_list_id_\<alpha>: "LIST2 i = tuple_list_id_\<alpha> j \<Longrightarrow> i = j - L\<^sub>1 \<and> j \<ge> L\<^sub>1" 
    unfolding tuple_list_id_\<alpha>_def
    by(auto split: if_splits)


  lemma m1_notin_tuple_list_id_rel: "(-1,x) \<notin> tuple_list_id_rel"
    unfolding tuple_list_id_rel_def
    apply (auto split: tuple_list_id.splits simp: m1_notin_snat_rel)
    done
  
  sublocale tuple_list_id: dflt_pure_option "-1" tuple_list_id_assn "ll_icmp_eq (-1)"
    apply unfold_locales
    subgoal
      apply (auto simp: pure_def pred_lift_extract_simps del: ext intro!: ext)
      unfolding tuple_list_id_rel_def
      apply (auto simp: snat_rel_def snat.rel_def in_br_conv snat_invar_def split: tuple_list_id.splits)
      done
    subgoal proof goal_cases
      case 1
      interpret llvm_prim_arith_setup .
      show ?case
        unfolding bool.assn_def
        apply vcg'
        done
      qed
    subgoal by simp  
    done


  definition tuple_list_id_none :: "tuple_list_id option" where "tuple_list_id_none = None"

  lemmas [sepref_fr_rules] = tuple_list_id.hn_None[folded tuple_list_id_none_def]
  sepref_register tuple_list_id_none 
  
  
  lemma [sepref_opt_simps]: "tuple_list_id.free_option (\<lambda>_. return\<^sub>M ()) (- 1) = doM {return\<^sub>M ()}"
    unfolding tuple_list_id.free_option_def by (auto simp: llc_if_def ll_icmp_eq_def op_lift_cmp_def)
 
   
  concrete_definition tuple_list_id_free_option[llvm_code,llvm_inline] is tuple_list_id.free_option_def
  concrete_definition tuple_list_id_am_empty[llvm_code,llvm_inline] is tuple_list_id.am2_empty_def
  concrete_definition tuple_list_id_am_lookup[llvm_code,llvm_inline] is tuple_list_id.am2_lookup_def
  concrete_definition tuple_list_id_am_contains_key[llvm_code,llvm_inline] is tuple_list_id.am2_contains_key_def
  concrete_definition tuple_list_id_am_update[llvm_code,llvm_inline] is tuple_list_id.am2_update_def
  concrete_definition tuple_list_id_am_delete[llvm_code,llvm_inline] is tuple_list_id.am2_delete_def

  lemmas emp[unfolded tuple_list_id_am_empty.refine,sepref_fr_rules] = tuple_list_id.am2_empty_hnr tuple_list_id.am2_empty_hnr_mop
  lemmas [unfolded tuple_list_id_am_lookup.refine,sepref_fr_rules] = tuple_list_id.am2_lookup_hnr tuple_list_id.am2_lookup_hnr_mop
  lemmas [unfolded tuple_list_id_am_contains_key.refine,sepref_fr_rules] = tuple_list_id.am2_contains_key_hnr tuple_list_id.am2_contains_key_hnr_mop
  lemmas [unfolded tuple_list_id_am_update.refine,sepref_fr_rules] = tuple_list_id.am2_update_hnr tuple_list_id.am2_update_hnr_mop
  lemmas [unfolded tuple_list_id_am_delete.refine,sepref_fr_rules] = tuple_list_id.am2_delete_hnr tuple_list_id.am2_delete_hnr_mop 

  definition tuple_list_id_am_assn :: "_ \<Rightarrow> 64 Word.word ptr \<Rightarrow> _" where "tuple_list_id_am_assn = tuple_list_id.am_assn N"

  lemma tuple_list_id_am_assn_intf[intf_of_assn]: (*Automatically converts type in sepref ID stage*)
    "intf_of_assn (tuple_list_id_am_assn) (TYPE((nat,tuple_list_id)i_map))"
    by simp

  sepref_register 
    eq_tli: "(=):: tuple_list_id \<Rightarrow> _"
    eq_tlio: "(=):: tuple_list_id option \<Rightarrow> _"
                                                              
  lemma hn_tuple_list_id_rel_icmp_op:
    "((=), (=)) \<in> tuple_list_id_rel \<rightarrow> tuple_list_id_rel \<rightarrow> bool_rel"
    unfolding tuple_list_id_rel_def
    apply (clarsimp simp: in_br_conv)
    by (auto simp: in_nres_rel_iff tuple_list_id_\<alpha>_def 
        dest:snat_rel_eq_iff split: if_splits)

  lemmas [sepref_fr_rules] = 
    hn_word_icmp_op(1)[FCOMP hn_tuple_list_id_rel_icmp_op]


  lemma hn_tuple_list_id_rel_option_icmp_op[sepref_fr_rules]:
    "(uncurry ll_icmp_eq, uncurry (RETURN \<circ>\<circ> (=))) \<in> tuple_list_id.option_assn\<^sup>k *\<^sub>a tuple_list_id.option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding tuple_list_id.option_assn_def ll_icmp_eq_def op_lift_cmp_def
    apply sepref_to_hoare
    apply vcg
    by (auto simp: sep_algebra_simps ENTAILS_def entails_def bool_to_lint_to_word_bool1_rel word_to_lint_eq tuple_list_id_rel_def in_br_conv tuple_list_id_\<alpha>_def 
      split: if_splits dest:snat_rel_eq_iff)

end


context disj_set_list_tuple_defs
begin

  abbreviation "elemt_assn \<equiv> b_assn size_assn (\<lambda> i. i < N)"
  
  abbreviation "id1_rel \<equiv> b_rel size_rel (\<lambda> i. i < L\<^sub>1)"
  
  abbreviation "id1_assn \<equiv> b_assn size_assn (\<lambda> i. i < L\<^sub>1)"
  
  abbreviation "id2_rel \<equiv> b_rel size_rel (\<lambda> i. i < max_size_t - L\<^sub>1)"
  
  abbreviation "id2_assn \<equiv> b_assn size_assn (\<lambda> i. i < max_size_t - L\<^sub>1)"
  
  definition(in disj_set_list_tuple_defs) "disj_set_list_tuple_assn_raw = size_assn \<times>\<^sub>a size_assn \<times>\<^sub>a disj_set_list_tuple_defs.tuple_list_id_am_assn L\<^sub>1 N"
  
  definition "to_LIST1 v = LIST1 v"
  
  definition "to_LIST2 v = LIST2 v"
  
  definition "in_LIST1 ns \<equiv> \<exists>v. ns = LIST1 v"
  
  definition "in_LIST2 ns \<equiv> \<exists>v. ns = LIST2 v"
  
  definition "in_SOME_LIST1 nso \<equiv> if is_None nso then False else in_LIST1 (the nso)"
  
  definition "in_SOME_LIST2 nso \<equiv> if is_None nso then False else in_LIST2 (the nso)"
  
  definition "of_LIST1 ns = id1 ns"
  
  definition "of_LIST2 ns = id2 ns"

  definition "of_tuple M = (\<lambda> v. case M v of None \<Rightarrow> None | Some v \<Rightarrow> Some (id1 v))"


  definition [llvm_inline]: "to_LIST1_impl x = x"

  definition [llvm_inline]: "to_LIST2_impl x = x + li"

  definition [llvm_inline]: "in_LIST1_impl x \<equiv> from_bool (x<li)"

  definition [llvm_inline]: "in_LIST2_impl x \<equiv> from_bool (x\<ge>li)"

  definition [llvm_inline]: "of_LIST1_impl ns = Mreturn ns"

  definition [llvm_inline]: "of_LIST2_impl ns = Mreturn (ns - li)"

end


locale disj_set_list_tuple_env = disj_set_list_tuple_defs +
  assumes l_impl: "(li,L\<^sub>1) \<in> size_rel"
  assumes n_impl: "(ni,N) \<in> size_rel"
begin

  lemmas [sepref_import_param] = n_impl
  lemmas [sepref_import_param] = l_impl

  sepref_register N
  sepref_register L\<^sub>1

  lemma L1_upper: "L\<^sub>1 < max_size_t"
    using l_impl 
    using in_snat_rel_boundsD by fastforce

  lemma N_upper: "N < max_size_t"
    using n_impl
    using in_snat_rel_boundsD by fastforce

  lemma LIST2_impl_refine_aux: "(a2,L\<^sub>1) \<in> snat_rel \<Longrightarrow> (a, a') \<in> snat_rel \<Longrightarrow> a' < max_snat LENGTH('a) - L\<^sub>1 \<Longrightarrow> (a + a2, a' + L\<^sub>1) \<in> snat_rel" for a2::"('a::len2) Word.word"
    by(auto intro!: plus_snat_refine) 

  lemma(in disj_set_list_tuple_defs) LIST1_impl_refine: "(to_LIST1_impl, to_LIST1) \<in> id1_rel \<rightarrow> tuple_list_id_rel"
    by (auto simp: tuple_list_id_rel_def br_def tuple_list_id_\<alpha>_def to_LIST1_def to_LIST1_impl_def)

  lemma LIST2_impl_refine: "(to_LIST2_impl, to_LIST2) \<in> id2_rel \<rightarrow> tuple_list_id_rel"
    apply (clarsimp simp: tuple_list_id_rel_def br_def tuple_list_id_\<alpha>_def to_LIST2_impl_def to_LIST2_def) 
    apply (rule relcompI) 
    apply (rule LIST2_impl_refine_aux)
    apply (rule l_impl)
    apply auto
    done

  lemma in_LIST1_impl_refine: "(in_LIST1_impl, in_LIST1) \<in> tuple_list_id_rel \<rightarrow> bool1_rel"
    unfolding in_LIST1_impl_def in_LIST1_def using l_impl
    apply (auto simp: in_snat_rel_snat tuple_list_id_rel_def bool1_rel_def bool.rel_def in_br_conv 
                      m1_notin_snat_rel tuple_list_id_\<alpha>_def split_ifs 
               split: tuple_list_id.splits 
                dest: lt_snat_refine ) 
    done

  lemma in_LIST2_impl_refine: "(in_LIST2_impl, in_LIST2) \<in> tuple_list_id_rel \<rightarrow> bool1_rel"
    unfolding in_LIST2_impl_def in_LIST2_def  using l_impl
    apply (auto simp: in_snat_rel_snat tuple_list_id_rel_def bool1_rel_def bool.rel_def in_br_conv 
                      m1_notin_snat_rel in_snat_rel_leq tuple_list_id_\<alpha>_def 
               split: tuple_list_id.splits 
                dest: lt_snat_refine)
    done

  lemmas [sepref_import_param] = LIST1_impl_refine LIST2_impl_refine in_LIST1_impl_refine in_LIST2_impl_refine

  (*TODO, can be stronger by using id1_assn*)
  lemma hn_dnslt_id1[sepref_fr_rules]: "(of_LIST1_impl, RETURN o of_LIST1) \<in> [\<lambda>x. \<exists>j. x = LIST1 j]\<^sub>a tuple_list_id_assn\<^sup>k \<rightarrow> size_assn" 
    apply sepref_to_hoare
    unfolding tuple_list_id_rel_def tuple_list_id_\<alpha>_def br_def of_LIST1_impl_def of_LIST1_def
    apply clarsimp
    apply vcg'
    apply (auto split: if_splits)
    done

  lemma hn_dnslt_id2[sepref_fr_rules]: "(of_LIST2_impl, RETURN o of_LIST2) \<in> [\<lambda>x. \<exists>j. x = LIST2 j]\<^sub>a tuple_list_id_assn\<^sup>k \<rightarrow> size_assn"
    apply sepref_to_hoare
    unfolding tuple_list_id_rel_def br_def of_LIST2_impl_def of_LIST2_def
    using l_impl
    apply (clarsimp simp:)
    apply vcg
    apply (drule LIST2_tuple_list_id_\<alpha>)
    apply (clarsimp simp: tuple_list_id_\<alpha>_def sep_algebra_simps minus_snat_refine) 
    apply vcg'
    done



                
  sepref_def in_SOME_LIST1_ll is "(RETURN o in_SOME_LIST1)" :: "tuple_list_id.option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding in_SOME_LIST1_def
    supply [simp] = option.split_sels(2)
    by sepref

  concrete_definition (in -) in_SOME_LIST1_ll' [llvm_code] is disj_set_list_tuple_env.in_SOME_LIST1_ll_def
  lemmas [sepref_fr_rules] = in_SOME_LIST1_ll.refine[unfolded in_SOME_LIST1_ll'.refine]
  
  
  sepref_def in_SOME_LIST2_ll is "RETURN o in_SOME_LIST2" :: "tuple_list_id.option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding in_SOME_LIST2_def
    supply [simp] = option.split_sels(2)
    by sepref

  concrete_definition (in -) in_SOME_LIST2_ll' [llvm_code] is disj_set_list_tuple_env.in_SOME_LIST2_ll_def
  lemmas [sepref_fr_rules] = in_SOME_LIST2_ll.refine[unfolded in_SOME_LIST2_ll'.refine]

end


context disj_set_list_tuple_defs
begin 
  lemmas [simp] = to_LIST1_def to_LIST2_def of_LIST1_def of_LIST2_def
  
  lemma nin_LIST1_LIST2 [simp,intro!]: "\<not>in_LIST1 (LIST2 x)"
    unfolding in_LIST1_def by blast
  
  lemma nin_LIST2_LIST1 [simp,intro!]: "\<not>in_LIST2 (LIST1 x)"
    unfolding in_LIST2_def by blast
  
  lemma in_LIST1_LIST1 [simp,intro!]: "in_LIST1 (LIST1 x)"
    unfolding in_LIST1_def by blast
  
  lemma in_LIST2_LIST2 [simp,intro!]: "in_LIST2 (LIST2 x)"
    unfolding in_LIST2_def by blast
  
  lemma in_LIST1_to_LIST1[dest!,simp]: "in_LIST1 l \<Longrightarrow> \<exists> v. l = LIST1 v" 
    unfolding in_LIST1_def .
  
  lemma in_LIST2_to_LIST2[dest!,simp]: "in_LIST2 l \<Longrightarrow> \<exists> v. l = LIST2 v" 
    unfolding in_LIST2_def .

end

  

section \<open>Abstract Disjoint Set List\<close>

subsection \<open>Abstract Operations\<close>

definition op_antpar_empty :: "antpar" where "op_antpar_empty = ([],[])"

definition op_antpar_list1_count :: "antpar \<Rightarrow> nat" where "op_antpar_list1_count = (\<lambda> (XS,YS). length XS)"

definition op_antpar_list2_count :: "antpar \<Rightarrow> nat" where "op_antpar_list2_count = (\<lambda> (XS,YS). length YS)"

definition op_antpar_list1_expand :: "antpar \<Rightarrow> nat \<Rightarrow> antpar" where "op_antpar_list1_expand = (\<lambda> (XS,YS) m. (XS @ (replicate m {}), YS))"

definition op_antpar_list2_expand :: "antpar \<Rightarrow> nat \<Rightarrow> antpar" where "op_antpar_list2_expand = (\<lambda> (XS,YS) m. (XS, YS @ (replicate m {})))"

definition op_antpar_mem_any :: "antpar \<Rightarrow> nat \<Rightarrow> bool" where "op_antpar_mem_any = (\<lambda> (XS, YS) v. (\<exists> i < length XS. v \<in> XS ! i) \<or> (\<exists> i < length YS. v \<in> YS ! i))"

definition op_antpar_mem_any1 :: "antpar \<Rightarrow> nat \<Rightarrow> bool" where "op_antpar_mem_any1 = (\<lambda> (XS, YS) v. (\<exists> i < length XS. v \<in> XS ! i))"

definition op_antpar_mem_any2 :: "antpar \<Rightarrow> nat \<Rightarrow> bool" where "op_antpar_mem_any2 = (\<lambda> (XS, YS) v. (\<exists> i < length YS. v \<in> YS ! i))"

definition op_antpar_list1_mem_of :: "antpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "op_antpar_list1_mem_of = (\<lambda> (XS,YS) v i. if i < length XS then v \<in> XS ! i else False)"

definition op_antpar_list2_mem_of :: "antpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "op_antpar_list2_mem_of = (\<lambda> (XS,YS) v i. if i < length YS then v \<in> YS ! i else False)"

definition op_antpar_eq_set_mem :: "antpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "op_antpar_eq_set_mem = (\<lambda> (XS,YS) v w. (\<forall> i < length XS. v \<in> XS ! i \<longleftrightarrow> w \<in> XS ! i) \<and> (\<forall> i < length YS. v \<in> YS ! i \<longleftrightarrow> w \<in> YS ! i))"

definition op_antpar_move_to_list1 :: "antpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> antpar" where "op_antpar_move_to_list1 = (\<lambda> (XS,YS) v i. ((map (\<lambda> X. X - {v}) XS)[i:=insert v (XS ! i)], (map (\<lambda> Y. Y - {v}) YS)))"

definition op_antpar_move_to_list2 :: "antpar \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> antpar" where "op_antpar_move_to_list2 = (\<lambda> (XS,YS) v i. ((map (\<lambda> X. X - {v}) XS), (map (\<lambda> Y. Y - {v}) YS)[i:=insert v (YS ! i)]))"

definition op_antpar_remove :: "antpar \<Rightarrow> nat \<Rightarrow> antpar" where "op_antpar_remove = (\<lambda> (XS,YS) v. (map (\<lambda> X. X - {v}) XS, map (\<lambda> Y. Y - {v}) YS))"

section \<open>Concrete Disjoint Set List\<close>


subsection \<open>Abstraction relation\<close>

definition disj_set_list_tuple_\<alpha> :: "antparc \<Rightarrow> antpar" where "disj_set_list_tuple_\<alpha> = (\<lambda> (n\<^sub>1,n\<^sub>2,M). (map (\<lambda> i. {v. M v = Some (LIST1 i)}) [0..<n\<^sub>1], map (\<lambda> i. {v. M v = Some (LIST2 i)}) [0..<n\<^sub>2]))"


context disj_set_list_tuple_defs
begin

  definition disj_set_list_tuple_invar :: "antparc \<Rightarrow> bool" where "disj_set_list_tuple_invar = (\<lambda> (n\<^sub>1,n\<^sub>2,M). n\<^sub>1 \<le> L\<^sub>1 \<and> (\<forall> v. case M v of Some lv \<Rightarrow> v < N \<and> (case lv of LIST1 i \<Rightarrow> i < n\<^sub>1 | LIST2 j \<Rightarrow> j < n\<^sub>2) | None \<Rightarrow> True))"
  
  definition "disj_set_list_tuple_rel = br disj_set_list_tuple_\<alpha> disj_set_list_tuple_invar"
  

  
  
  definition[simp]: "antpar_move1_pre = (\<lambda> (((XS,YS),v),i). i < length XS)"
  definition[simp]: "antpar_move2_pre = (\<lambda> (((XS,YS),v),i). i < length YS)"
  
  
  lemma disj_set_list_tuple_invar_geq_n1_empty: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> i \<ge> n\<^sub>1 \<Longrightarrow> {v. M v = Some (LIST1 i)} = {}" 
    by(auto simp: disj_set_list_tuple_invar_def le_def split: option.splits tuple_list_id.splits)
  
  lemma disj_set_list_tuple_invar_geq_n2_empty: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> i \<ge> n\<^sub>2 \<Longrightarrow> {v. M v = Some (LIST2 i)} = {}" 
    by(auto simp: disj_set_list_tuple_invar_def le_def split: option.splits tuple_list_id.splits)
  
  lemma disj_set_list_tuple_invarD1: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> M v = Some (LIST1 i) \<Longrightarrow> i < n\<^sub>1"
    unfolding disj_set_list_tuple_invar_def
    by(auto split: option.splits tuple_list_id.splits)
  
  lemma disj_set_list_tuple_invarD2: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> M v = Some (LIST2 i) \<Longrightarrow> i < n\<^sub>2"
    unfolding disj_set_list_tuple_invar_def
    by(auto split: option.splits tuple_list_id.splits)
  
  
  lemma disj_set_list_tuple_rel_n1_eq_len: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> n\<^sub>1 = length XS1"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv disj_set_list_tuple_\<alpha>_def)
  
  lemma disj_set_list_tuple_rel_n2_eq_len: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> n\<^sub>2 = length XS2"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv disj_set_list_tuple_\<alpha>_def)
  
  lemma disj_set_list_tuple_rel_n1_eq_len_leq: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> n\<^sub>1 + b \<le> c \<longleftrightarrow> length XS1 + b \<le> c"
    by(auto dest: disj_set_list_tuple_rel_n1_eq_len)
  
  lemma disj_set_list_tuple_rel_n2_eq_len_leq: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> n\<^sub>2 + b < c \<longleftrightarrow> length XS2 + b < c"
    by(auto dest: disj_set_list_tuple_rel_n2_eq_len)
  
  lemma disj_set_list_tuple_rel_ex_mem1_aux: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> (\<exists>i<length XS1. b \<in> XS1 ! i) = (\<exists>y. M b = Some (LIST1 y))" 
    unfolding disj_set_list_tuple_rel_def
    by(auto 0 3 simp: in_br_conv disj_set_list_tuple_\<alpha>_def dest: disj_set_list_tuple_invarD1)
  
  lemma disj_set_list_tuple_rel_ex_mem1: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> (\<exists>i<length XS1. b \<in> XS1 ! i) \<Longrightarrow> (\<exists>y. M b = Some y)"
    by(auto dest: disj_set_list_tuple_rel_ex_mem1_aux)
  
  lemma disj_set_list_rel_ex_mem2_aux: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> (\<exists>i<length XS2. b \<in> XS2 ! i) = (\<exists>y. M b = Some (LIST2 y))" 
    unfolding disj_set_list_tuple_rel_def
    by(auto 0 3 simp: in_br_conv disj_set_list_tuple_\<alpha>_def dest: disj_set_list_tuple_invarD2)
  
  lemma disj_set_list_tuple_rel_ex_mem2: "((n\<^sub>1, n\<^sub>2, M), (XS1, XS2)) \<in> disj_set_list_tuple_rel \<Longrightarrow> (\<exists>i<length XS2. b \<in> XS2 ! i) \<Longrightarrow> (\<exists>y. M b = Some y)"
    by(auto dest: disj_set_list_rel_ex_mem2_aux)

subsection \<open>Concrete Operations\<close>



  definition disj_set_list_tuple_empty :: "antparc" where "disj_set_list_tuple_empty = (let  M = op_am_custom_empty N in (0,0,M))"
  sepref_register disj_set_list_tuple_empty
  
  definition disj_set_count1 :: "antparc \<Rightarrow> nat" where "disj_set_count1 = (\<lambda> (n\<^sub>1,n\<^sub>2,M). n\<^sub>1)"
  sepref_register disj_set_count1 :: "antparc' \<Rightarrow> nat"
  
  definition disj_set_count2 :: "antparc \<Rightarrow> nat" where "disj_set_count2 = (\<lambda> (n\<^sub>1,n\<^sub>2,M). n\<^sub>2)"
  sepref_register disj_set_count2 :: "antparc' \<Rightarrow> nat"
  
  definition expand_capacity1 :: "antparc \<Rightarrow> nat \<Rightarrow> antparc" where "expand_capacity1 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) m. (n\<^sub>1 + m, n\<^sub>2, M))"
  sepref_register expand_capacity1 :: "antparc' \<Rightarrow> nat \<Rightarrow> antparc'"
  
  definition expand_capacity2 :: "antparc \<Rightarrow> nat \<Rightarrow> antparc" where "expand_capacity2 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) m. (n\<^sub>1, n\<^sub>2 + m, M))"
  sepref_register expand_capacity2 :: "antparc' \<Rightarrow> nat \<Rightarrow> antparc'"
  
  definition is_member_any_tuple :: "antparc \<Rightarrow> nat \<Rightarrow> bool" where "is_member_any_tuple = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v. \<not>is_None (op_map_lookup v M))"
  sepref_register is_member_any_tuple :: "antparc' \<Rightarrow> nat \<Rightarrow> bool"
   
  definition is_member_any_tuple1 :: "antparc \<Rightarrow> nat \<Rightarrow> bool" where "is_member_any_tuple1 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v. let vo = (op_map_lookup v M) in (if is_None vo then False else in_LIST1 (the vo) ) )"
  sepref_register is_member_any_tuple1 :: "antparc' \<Rightarrow> nat \<Rightarrow> bool"                                                            
  
  definition is_member_any_tuple2 :: "antparc \<Rightarrow> nat \<Rightarrow> bool" where "is_member_any_tuple2 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v. let vo = (op_map_lookup v M) in (if is_None vo then False else in_LIST2 (the vo) ))"
  sepref_register is_member_any_tuple2 :: "antparc' \<Rightarrow> nat \<Rightarrow> bool"
  
  definition is_member_of1 :: "antparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "is_member_of1 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v i. let vo = op_map_lookup v M in to_LIST1 i = the vo)"
  sepref_register is_member_of1 :: "antparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  
  definition is_member_of2 :: "antparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "is_member_of2 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v i. let vo = op_map_lookup v M in to_LIST2 i = the vo)"
  sepref_register is_member_of2 :: "antparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  
  definition teq_set_member :: "antparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "teq_set_member = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v w. (op_map_lookup v M) = (op_map_lookup w M))"
  sepref_register teq_set_member :: "antparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  
  definition tmove_elem1 :: "antparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> antparc" where "tmove_elem1 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v i. let n = to_LIST1 i in (n\<^sub>1,n\<^sub>2,M(v\<mapsto>n)))"
  sepref_register tmove_elem1 :: "antparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> antparc'"
  
  definition tmove_elem2 :: "antparc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> antparc" where "tmove_elem2 = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v i. let n = to_LIST2 i in (n\<^sub>1,n\<^sub>2,M(v\<mapsto>n)))"
  sepref_register tmove_elem2 :: "antparc' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> antparc'"
  
  definition tremove_elem :: "antparc \<Rightarrow> nat \<Rightarrow> antparc" where "tremove_elem = (\<lambda> (n\<^sub>1,n\<^sub>2,M) v. (n\<^sub>1,n\<^sub>2,M(v:=None)))"
  sepref_register tremove_elem :: "antparc' \<Rightarrow> nat \<Rightarrow> antparc'"

subsection \<open>Correctness of abstraction\<close>

subsubsection \<open>Abstraction correctness\<close>

  lemma(in disj_set_list_tuple_defs) disj_set_list_tuple_empty_\<alpha>: "disj_set_list_tuple_\<alpha> (disj_set_list_tuple_empty) = op_antpar_empty"
    by(auto simp: disj_set_list_tuple_\<alpha>_def op_antpar_empty_def disj_set_list_tuple_empty_def)
  
  lemma disj_set_count1_\<alpha>: "disj_set_count1 (n\<^sub>1, n\<^sub>2, M) = op_antpar_list1_count (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))"
    unfolding disj_set_list_tuple_\<alpha>_def disj_set_count1_def op_antpar_list1_count_def
    by auto
  
  lemma disj_set_count2_\<alpha>: "disj_set_count2 (n\<^sub>1, n\<^sub>2, M) = op_antpar_list2_count (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))"
    unfolding disj_set_list_tuple_\<alpha>_def disj_set_count2_def op_antpar_list2_count_def
    by auto
  
  lemma expand_capacity1_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> disj_set_list_tuple_\<alpha> (expand_capacity1 (n\<^sub>1, n\<^sub>2, M) m) = op_antpar_list1_expand (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) m"
    unfolding expand_capacity1_def op_antpar_list1_expand_def disj_set_list_tuple_invar_def
    apply(clarsimp simp: disj_set_list_tuple_\<alpha>_def split: option.splits) 
    apply(subst upt_add_eq_append)
    subgoal
      by simp
    subgoal
      apply(simp only: map_append)
      apply clarsimp
      apply(induction m)
      subgoal
        by simp
      subgoal for m
        unfolding replicate_Suc_conv_snoc
        by (auto split: tuple_list_id.splits)
      done
    done
  
  lemma expand_capacity2_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> disj_set_list_tuple_\<alpha> (expand_capacity2 (n\<^sub>1, n\<^sub>2, M) m) = op_antpar_list2_expand (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) m"
    unfolding expand_capacity2_def op_antpar_list2_expand_def disj_set_list_tuple_invar_def
    apply(clarsimp simp: disj_set_list_tuple_\<alpha>_def split: option.splits) 
    apply(subst upt_add_eq_append)
    subgoal
      by simp
    subgoal
      apply(simp only: map_append)
      apply clarsimp
      apply(induction m)
      subgoal
        by simp
      subgoal for m
        unfolding replicate_Suc_conv_snoc
        by (auto split: tuple_list_id.splits)
      done
    done
  
  lemma is_member_any_tuple_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> is_member_any_tuple (n\<^sub>1, n\<^sub>2, M) = op_antpar_mem_any (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))"
    unfolding op_antpar_mem_any_def disj_set_list_tuple_\<alpha>_def is_member_any_tuple_def
    apply clarsimp
    apply (rule ext)
    apply(rule iffI)
    subgoal for v
      apply(cases "M v")
      apply clarsimp_all
      subgoal for i
        apply(cases i)
        subgoal
          by (fastforce dest: disj_set_list_tuple_invarD1)
        subgoal
          by (blast dest: disj_set_list_tuple_invarD2)
      done
    done
    subgoal 
      by fastforce
    done
  
  lemma is_member_any_tuple1_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> is_member_any_tuple1 (n\<^sub>1, n\<^sub>2, M) = op_antpar_mem_any1 (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))"
    unfolding is_member_any_tuple1_def op_antpar_mem_any1_def disj_set_list_tuple_\<alpha>_def
    apply (rule ext)
    apply (clarsimp simp: Let_def split: if_splits option.splits)
    apply(rule iffI)
    subgoal for x l 
      using disj_set_list_tuple_invarD1 
      by fastforce
    subgoal for x l 
      by fastforce
    done
  
  
  lemma is_member_any_tuple2_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> is_member_any_tuple2 (n\<^sub>1, n\<^sub>2, M) = op_antpar_mem_any2 (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))"
    unfolding is_member_any_tuple2_def op_antpar_mem_any2_def disj_set_list_tuple_\<alpha>_def
    apply (rule ext)
    apply (clarsimp simp: Let_def split: if_splits option.splits)
    apply(rule iffI)
    subgoal for x l 
      using disj_set_list_tuple_invarD2
      by fastforce
    subgoal for x l 
      by fastforce
    done
  
  
  lemma is_member_of1_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> i < length (fst (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))) \<Longrightarrow> v \<in> fst (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) ! i \<Longrightarrow>  is_member_of1 (n\<^sub>1, n\<^sub>2, M) v = op_antpar_list1_mem_of (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) v"
    unfolding is_member_of1_def op_antpar_list1_mem_of_def disj_set_list_tuple_\<alpha>_def Let_def
    apply clarsimp
    apply(rule ext)+
    by fast
  
  lemma is_member_of2_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> i < length (snd (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))) \<Longrightarrow> v \<in> snd (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) ! i \<Longrightarrow>  is_member_of2 (n\<^sub>1, n\<^sub>2, M) v j = op_antpar_list2_mem_of (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) v j"
    unfolding is_member_of2_def op_antpar_list2_mem_of_def disj_set_list_tuple_\<alpha>_def Let_def
    apply clarsimp
    by fast
  
  
  lemma eq_set_member_\<alpha>:  "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) 
      \<Longrightarrow> teq_set_member (n\<^sub>1, n\<^sub>2, M) v w \<longleftrightarrow> op_antpar_eq_set_mem (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) v w"
    unfolding teq_set_member_def op_antpar_eq_set_mem_def disj_set_list_tuple_\<alpha>_def disj_set_list_tuple_invar_def
    apply (cases "M v"; cases "M w")
    subgoal by auto 
    subgoal for l 
      apply(cases l)
      by (auto elim: allE[where ?x=w])
    subgoal for l
      apply(cases l)
      by (auto elim: allE[where ?x=v])
    subgoal for l m
      apply(cases l; cases m)       
      by (auto elim: allE[where ?x=v] allE[where ?x=w])
    done
  
  
  lemma tmove_elem1_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> disj_set_list_tuple_\<alpha> (tmove_elem1 (n\<^sub>1, n\<^sub>2, M) v i) = op_antpar_move_to_list1 (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) v i"
    unfolding disj_set_list_tuple_\<alpha>_def op_antpar_move_to_list1_def tmove_elem1_def
    apply (clarsimp split: option.splits)
    apply(rule conjI)
    apply(rule nth_equalityI)
    subgoal
      by simp
    subgoal for j
      apply clarsimp
      apply(cases "i = j")
      subgoal
        by auto
      subgoal
        by auto
      done
    subgoal
      by blast
    done
  
  lemma tmove_elem2_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> disj_set_list_tuple_\<alpha> (tmove_elem2 (n\<^sub>1, n\<^sub>2, M) v i) = op_antpar_move_to_list2 (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) v i"
    unfolding disj_set_list_tuple_\<alpha>_def op_antpar_move_to_list2_def tmove_elem2_def
    apply (clarsimp split: option.splits)
    apply(rule conjI)
    subgoal 
      by fast
    apply(rule nth_equalityI)
    subgoal
      by simp
    subgoal for j
      apply clarsimp
      apply(cases "i = j")
      subgoal
        by auto
      subgoal
        by auto
      done
    done
  
  lemma tremove_elem_\<alpha>: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> disj_set_list_tuple_\<alpha> (tremove_elem (n\<^sub>1, n\<^sub>2, M) v) = op_antpar_remove (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M)) v"
    unfolding op_antpar_remove_def disj_set_list_tuple_\<alpha>_def tremove_elem_def
    by fastforce


subsubsection \<open>Invariant preservation\<close>
  
  lemma(in disj_set_list_tuple_defs) disj_set_list_tuple_invar_invar: "disj_set_list_tuple_invar (disj_set_list_tuple_empty)"
    by(auto simp: disj_set_list_tuple_invar_def disj_set_list_tuple_empty_def) 
  
  lemma expand_capacity1_invar: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> n\<^sub>1 + m \<le> L\<^sub>1 \<Longrightarrow> disj_set_list_tuple_invar (expand_capacity1 (n\<^sub>1, n\<^sub>2, M) m)"
    unfolding disj_set_list_tuple_invar_def expand_capacity1_def
    by (auto split: option.splits tuple_list_id.splits simp: add.commute trans_less_add2)
  
  lemma expand_capacity2_invar: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> disj_set_list_tuple_invar (expand_capacity2 (n\<^sub>1, n\<^sub>2, M) m)"
    unfolding disj_set_list_tuple_invar_def expand_capacity2_def
    by (auto split: option.splits tuple_list_id.splits simp: trans_less_add1) 
  
  lemma tmove_elem1_invar: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> v < N \<Longrightarrow> i < length (fst (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))) \<Longrightarrow> disj_set_list_tuple_invar (tmove_elem1 (n\<^sub>1, n\<^sub>2, M) v i)"
    unfolding disj_set_list_tuple_invar_def tmove_elem1_def disj_set_list_tuple_\<alpha>_def
    by(auto split: option.splits tuple_list_id.splits) 
  
  lemma tmove_elem2_invar: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> v < N \<Longrightarrow> i < length (snd (disj_set_list_tuple_\<alpha> (n\<^sub>1, n\<^sub>2, M))) \<Longrightarrow> disj_set_list_tuple_invar (tmove_elem2 (n\<^sub>1, n\<^sub>2, M) v i)"
    unfolding disj_set_list_tuple_invar_def tmove_elem2_def disj_set_list_tuple_\<alpha>_def
    by(auto split: option.splits tuple_list_id.splits)
  
  lemma tremove_elem_invar: "disj_set_list_tuple_invar (n\<^sub>1, n\<^sub>2, M) \<Longrightarrow> disj_set_list_tuple_invar (tremove_elem (n\<^sub>1, n\<^sub>2, M) v)"
    unfolding tremove_elem_def disj_set_list_tuple_invar_def
    by (auto split: option.splits) 
  
  
  
subsubsection \<open>Refinement correcness\<close>
  
  
  lemma(in disj_set_list_tuple_defs) disj_set_list_tuple_invar_correct: 
    "(uncurry0 disj_set_list_tuple_empty, uncurry0 op_antpar_empty) \<in> unit_rel \<rightarrow> disj_set_list_tuple_rel"
    by(auto intro: frefI simp: disj_set_list_tuple_rel_def in_br_conv disj_set_list_tuple_empty_\<alpha> disj_set_list_tuple_invar_invar)
  
  lemma disj_set_count1_correct: "(disj_set_count1, op_antpar_list1_count) \<in> disj_set_list_tuple_rel \<rightarrow> nat_rel"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv disj_set_count1_\<alpha>)
  
  lemma disj_set_count2_correct: "(disj_set_count2, op_antpar_list2_count) \<in> disj_set_list_tuple_rel \<rightarrow> nat_rel"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv disj_set_count2_\<alpha>)
  
  lemma expand_capacity1_correct: "(uncurry expand_capacity1, uncurry op_antpar_list1_expand) \<in> [\<lambda> ((XS,YS),m). length XS + m \<le> L\<^sub>1]\<^sub>f disj_set_list_tuple_rel \<times>\<^sub>r nat_rel \<rightarrow> disj_set_list_tuple_rel"
    apply(rule frefI)
    apply (clarsimp simp: in_br_conv)
    apply(frule disj_set_list_tuple_rel_n1_eq_len)
    by(auto simp: in_br_conv expand_capacity1_\<alpha> disj_set_list_tuple_rel_def expand_capacity1_invar) 
  
  lemma expand_capacity2_correct: "(expand_capacity2, op_antpar_list2_expand) \<in> disj_set_list_tuple_rel \<rightarrow> nat_rel \<rightarrow> disj_set_list_tuple_rel"
    apply (clarsimp simp: in_br_conv)
    apply(frule disj_set_list_tuple_rel_n2_eq_len)
    by(auto simp: in_br_conv expand_capacity2_\<alpha> disj_set_list_tuple_rel_def expand_capacity2_invar) 
  
  lemma is_member_any_correct: "(is_member_any_tuple, op_antpar_mem_any) \<in> disj_set_list_tuple_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv is_member_any_tuple_\<alpha>)
  
  lemma is_member_any1_correct: "(is_member_any_tuple1, op_antpar_mem_any1) \<in> disj_set_list_tuple_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv is_member_any_tuple1_\<alpha>)
  
  lemma is_member_any2_correct: "(is_member_any_tuple2, op_antpar_mem_any2) \<in> disj_set_list_tuple_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv is_member_any_tuple2_\<alpha>)
  
  lemma is_member_of1_correct: "(uncurry2 is_member_of1, uncurry2 op_antpar_list1_mem_of) \<in> [\<lambda> (((XS,YS),v),i). \<exists> i < length XS. v \<in> XS ! i]\<^sub>f ((disj_set_list_tuple_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> bool_rel"
    unfolding disj_set_list_tuple_rel_def
    apply(rule frefI)
    apply (clarsimp simp: in_br_conv)
    using is_member_of1_\<alpha>
    by (metis fst_conv)
  
  lemma is_member_of2_correct: "(uncurry2 is_member_of2, uncurry2 op_antpar_list2_mem_of) \<in> [\<lambda> (((XS,YS),v),i). \<exists> i < length YS. v \<in> YS ! i]\<^sub>f ((disj_set_list_tuple_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> bool_rel"
    unfolding disj_set_list_tuple_rel_def
    apply(rule frefI)
    apply (clarsimp simp: in_br_conv)
    using is_member_of2_\<alpha> 
    by (metis snd_conv)
  
  lemma teq_set_member_correct: "(uncurry2 teq_set_member, uncurry2 op_antpar_eq_set_mem) \<in> ((disj_set_list_tuple_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow>\<^sub>f bool_rel"
    unfolding disj_set_list_tuple_rel_def
    apply(clarsimp intro!: frefI simp: in_br_conv)
    apply(rule eq_set_member_\<alpha>)
    by assumption

  lemma tmove_elem1_correct: "(uncurry2 tmove_elem1, uncurry2 op_antpar_move_to_list1) \<in> [antpar_move1_pre]\<^sub>f ((disj_set_list_tuple_rel \<times>\<^sub>r b_rel nat_rel (\<lambda> i. i < N)) \<times>\<^sub>r nat_rel) \<rightarrow> disj_set_list_tuple_rel"
    unfolding disj_set_list_tuple_rel_def antpar_move1_pre_def
    apply(clarsimp intro!: frefI simp: in_br_conv tmove_elem1_\<alpha> )
    apply(rule tmove_elem1_invar)
    apply assumption+
    by (metis fstI)
  
  lemma tmove_elem2_correct: "(uncurry2 tmove_elem2, uncurry2 op_antpar_move_to_list2) \<in> [antpar_move2_pre]\<^sub>f ((disj_set_list_tuple_rel \<times>\<^sub>r b_rel nat_rel (\<lambda> i. i < N)) \<times>\<^sub>r nat_rel) \<rightarrow> disj_set_list_tuple_rel"
    unfolding disj_set_list_tuple_rel_def antpar_move2_pre_def
    apply(clarsimp intro!: frefI simp: in_br_conv tmove_elem2_\<alpha> )
    apply(rule tmove_elem2_invar)
    apply assumption+
    by (metis snd_eqD)
  
  lemma tremove_elem_correct: "(tremove_elem, op_antpar_remove) \<in> disj_set_list_tuple_rel \<rightarrow> nat_rel \<rightarrow> disj_set_list_tuple_rel"
    unfolding disj_set_list_tuple_rel_def
    by(auto simp: in_br_conv tremove_elem_\<alpha> tremove_elem_invar)

end


section \<open>Sepref Translations\<close>


lemma hfref_in_context: 
  assumes A: "(\<And> a c h. Q a c h \<Longrightarrow> (f,g) \<in> [P]\<^sub>a [C]\<^sub>c RS \<rightarrow>\<^sub>d T [CP]\<^sub>c)"
  and B: "(\<And> a c h. (fst RS) a c h \<Longrightarrow> Q a c h)"
  shows "(f,g) \<in> [P]\<^sub>a [C]\<^sub>c RS \<rightarrow>\<^sub>d T [CP]\<^sub>c"
  apply(rule hfrefI)
  apply(rule hn_refine_preI)
  apply(drule B)
  apply(rule hfrefD)
  apply(erule A)
  apply assumption+
  done

lemma hfref_in_context': 
  assumes A: "(\<And> a c h. Q a c h \<Longrightarrow> (f,g) \<in> [P]\<^sub>a [C]\<^sub>c RS \<rightarrow>\<^sub>d T [CP]\<^sub>c)"
  and B: "(\<And> a c h. (fst RS) a c h \<Longrightarrow> Q a c h)"
  shows "(f,g) \<in> [P]\<^sub>a [C]\<^sub>c RS \<rightarrow>\<^sub>d T [CP]\<^sub>c"
  apply(rule hfrefI)
  apply(rule hn_refine_preI)
  apply(drule B)
  apply(rule hfrefD)
  apply(erule A)
  apply assumption+
  done



context disj_set_list_tuple_env
begin

  definition(in disj_set_list_tuple_defs) disj_set_list_tuple_empty' :: "antparc nres" where "disj_set_list_tuple_empty' = (let N' = BCONST N N;  M = op_am_custom_empty N' in RETURN (0,0,M))"
  sepref_register(in disj_set_list_tuple_defs) disj_set_list_tuple_empty'
  

  lemma disj_set_list_tuple_empty_alt: "RETURN disj_set_list_tuple_empty = disj_set_list_tuple_empty'"
    unfolding disj_set_list_tuple_empty_def disj_set_list_tuple_empty'_def BCONST_def by presburger


  sepref_definition disj_set_list_tuple_empty_ll is "uncurry0 (RETURN disj_set_list_tuple_empty)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a (disj_set_list_tuple_assn_raw)"
    unfolding disj_set_list_tuple_empty_alt disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def disj_set_list_tuple_empty'_def

    supply [[goals_limit = 20]]

    apply (annot_snat_const "TYPE(size_T)")

    apply sepref
    done

  sepref_definition disj_set_count1_ll is "RETURN o disj_set_count1" :: "disj_set_list_tuple_assn_raw\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def disj_set_count1_def
    apply sepref
    done

  sepref_definition disj_set_count2_ll is "RETURN o disj_set_count2" :: "disj_set_list_tuple_assn_raw\<^sup>k \<rightarrow>\<^sub>a size_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def disj_set_count2_def
    apply sepref
    done

  sepref_definition expand_capacity1_ll is "uncurry (RETURN oo expand_capacity1)" :: "[\<lambda> ((n\<^sub>1,n\<^sub>2,M),m). n\<^sub>1 + m \<le> L\<^sub>1]\<^sub>a disj_set_list_tuple_assn_raw\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> disj_set_list_tuple_assn_raw"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def expand_capacity1_def
    supply [simp] = le_less_trans[OF _ L1_upper] 
    apply sepref
    done

  sepref_definition expand_capacity2_ll is "uncurry (RETURN oo expand_capacity2)" :: "[\<lambda> ((n\<^sub>1,n\<^sub>2,M),m). n\<^sub>2 + m < max_size_t - L\<^sub>1]\<^sub>a disj_set_list_tuple_assn_raw\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> disj_set_list_tuple_assn_raw"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def expand_capacity2_def
    apply sepref
    done

  sepref_definition is_member_any_ll is "(uncurry (RETURN oo is_member_any_tuple))" :: "disj_set_list_tuple_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def is_member_any_tuple_def
    apply sepref
    done

  sepref_definition is_member_any1_ll is "(uncurry (RETURN oo is_member_any_tuple1))" :: "disj_set_list_tuple_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def is_member_any_tuple1_def
    apply sepref
    done

  sepref_definition is_member_any2_ll is "(uncurry (RETURN oo is_member_any_tuple2))" :: "disj_set_list_tuple_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def is_member_any_tuple2_def
    apply sepref
    done

  sepref_definition is_member_of1_ll is "(uncurry2 (RETURN ooo is_member_of1))" :: "[\<lambda> (((n\<^sub>1,n\<^sub>2,M),v),i). M v \<noteq> None]\<^sub>a disj_set_list_tuple_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k *\<^sub>a id1_assn\<^sup>k \<rightarrow> bool1_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def is_member_of1_def
    apply sepref
    done

  sepref_definition is_member_of2_ll is "(uncurry2 (RETURN ooo is_member_of2))" :: "[\<lambda> (((n\<^sub>1,n\<^sub>2,M),v),i). M v \<noteq> None]\<^sub>a disj_set_list_tuple_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k *\<^sub>a id2_assn\<^sup>k \<rightarrow> bool1_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def is_member_of2_def
    apply sepref
    done

  sepref_definition teq_set_member_ll is "(uncurry2 (RETURN ooo teq_set_member))" :: " disj_set_list_tuple_assn_raw\<^sup>k *\<^sub>a elemt_assn\<^sup>k *\<^sub>a elemt_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def teq_set_member_def
    apply sepref
    done

  sepref_definition tmove_elem1_ll is "(uncurry2 (RETURN ooo tmove_elem1))" :: "disj_set_list_tuple_assn_raw\<^sup>d *\<^sub>a elemt_assn\<^sup>k *\<^sub>a id1_assn\<^sup>k \<rightarrow>\<^sub>a disj_set_list_tuple_assn_raw"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def tmove_elem1_def
    apply sepref
    done

  sepref_definition tmove_elem2_ll is "(uncurry2 (RETURN ooo tmove_elem2))" :: "disj_set_list_tuple_assn_raw\<^sup>d *\<^sub>a elemt_assn\<^sup>k *\<^sub>a id2_assn\<^sup>k \<rightarrow>\<^sub>a disj_set_list_tuple_assn_raw"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def tmove_elem2_def
    apply sepref
    done

  sepref_definition tremove_elem_ll is "(uncurry (RETURN oo tremove_elem))" :: "disj_set_list_tuple_assn_raw\<^sup>d *\<^sub>a elemt_assn\<^sup>k \<rightarrow>\<^sub>a disj_set_list_tuple_assn_raw"
    unfolding disj_set_list_tuple_assn_raw_def disj_set_list_tuple_defs.tuple_list_id_am_assn_def tremove_elem_def
    apply sepref
    done


  concrete_definition (in -) disj_set_list_tuple_invar_ll' [llvm_code] is disj_set_list_tuple_env.disj_set_list_tuple_empty_ll_def
  concrete_definition (in -) disj_set_count1_ll' [llvm_code] is disj_set_list_tuple_env.disj_set_count1_ll_def
  concrete_definition (in -) disj_set_count2_ll' [llvm_code] is disj_set_list_tuple_env.disj_set_count2_ll_def
  concrete_definition (in -) expand_capacity1_ll' [llvm_code] is disj_set_list_tuple_env.expand_capacity1_ll_def
  concrete_definition (in -) expand_capacity2_ll' [llvm_code] is disj_set_list_tuple_env.expand_capacity2_ll_def
  concrete_definition (in -) is_member_any_ll' [llvm_code] is disj_set_list_tuple_env.is_member_any_ll_def
  concrete_definition (in -) is_member_any1_ll' [llvm_code] is disj_set_list_tuple_env.is_member_any1_ll_def
  concrete_definition (in -) is_member_any2_ll' [llvm_code] is disj_set_list_tuple_env.is_member_any2_ll_def
  concrete_definition (in -) is_member_of1_ll' [llvm_code] is disj_set_list_tuple_env.is_member_of1_ll_def
  concrete_definition (in -) is_member_of2_ll' [llvm_code] is disj_set_list_tuple_env.is_member_of2_ll_def
  concrete_definition (in -) teq_set_member_ll' [llvm_code] is disj_set_list_tuple_env.teq_set_member_ll_def
  concrete_definition (in -) tmove_elem1_ll' [llvm_code] is disj_set_list_tuple_env.tmove_elem1_ll_def
  concrete_definition (in -) tmove_elem2_ll' [llvm_code] is disj_set_list_tuple_env.tmove_elem2_ll_def
  concrete_definition (in -) tremove_elem_ll' [llvm_code] is disj_set_list_tuple_env.tremove_elem_ll_def

  definition(in disj_set_list_tuple_defs) disj_set_list_tuple_assn :: "antpar \<Rightarrow> antpari \<Rightarrow> assn"  where
    "disj_set_list_tuple_assn = hr_comp disj_set_list_tuple_assn_raw disj_set_list_tuple_rel"



  context 
    notes [fcomp_norm_unfold] = hrr_comp_id_conv prod_rel_id_simp disj_set_list_tuple_assn_def[symmetric] 
    notes [simp] = disj_set_list_tuple_rel_ex_mem1 disj_set_list_tuple_rel_ex_mem2 
       disj_set_list_tuple_rel_n1_eq_len_leq disj_set_list_tuple_rel_n2_eq_len_leq 
  begin       

    lemmas mop_disj_set_list_tuple_invar_hnr = disj_set_list_tuple_empty_ll.refine[FCOMP disj_set_list_tuple_invar_correct]
    lemmas mop_antpar_count1_hnr = disj_set_count1_ll.refine[FCOMP disj_set_count1_correct]
    lemmas mop_antpar_count2_hnr = disj_set_count2_ll.refine[FCOMP disj_set_count2_correct]
    lemmas mop_antpar_expand1_hnr = expand_capacity1_ll.refine[FCOMP expand_capacity1_correct]
    lemmas mop_antpar_expand2_hnr = expand_capacity2_ll.refine[FCOMP expand_capacity2_correct]
    lemmas mop_antpar_mem_any_hnr = is_member_any_ll.refine[FCOMP is_member_any_correct]
    lemmas mop_antpar_mem_any1_hnr = is_member_any1_ll.refine[FCOMP is_member_any1_correct]
    lemmas mop_antpar_mem_any2_hnr = is_member_any2_ll.refine[FCOMP is_member_any2_correct]
    lemmas mop_antpar_mem_of1_hnr = is_member_of1_ll.refine[FCOMP is_member_of1_correct]
    lemmas mop_antpar_mem_of2_hnr = is_member_of2_ll.refine[FCOMP is_member_of2_correct]
    lemmas mop_eq_set_mem_hnr = teq_set_member_ll.refine[FCOMP teq_set_member_correct]
    lemmas mop_antpar_move1_hnr = tmove_elem1_ll.refine[FCOMP tmove_elem1_correct]
    lemmas mop_antpar_move2_hnr = tmove_elem2_ll.refine[FCOMP tmove_elem2_correct]
    lemmas mop_antpar_remove_hnr = tremove_elem_ll.refine[FCOMP tremove_elem_correct]
  
  end

end

end