theory SCC_map
  imports Graph "II_Modest_Base.More_B_Assn" "II_Modest_Base.More_snat" "Array_Nat_Tuple_Partition"
begin


text \<open>
  This theory implements the SCC decomposition for Gabow's algorithm. Abstractly it is a 
  topologically sorted list of sets, each set containing all states in the same SCC.
  We implement this as a map that maps each state to an SCC id.
\<close>

lemma b_assn_out_hfrefttnd:  "A \<rightarrow>\<^sub>a (b_assn B P) \<subseteq> (A \<rightarrow>\<^sub>a B)"
  apply clarsimp
  apply(erule hfref_cons)
  apply (auto simp: entails_lift_extract_simps(2))
  done

section \<open>Abstract SCC Map\<close>

type_synonym 'v sccmap = "'v set list"


subsection \<open>Basic Operations\<close>

definition mop_get_output_size :: "nat sccmap \<Rightarrow> nat nres" where 
  "mop_get_output_size S = RETURN (length S)"

definition mop_get_index :: "nat sccmap \<Rightarrow> nat \<Rightarrow> nat nres" where
  "mop_get_index S u = SPEC (\<lambda> i. i < length S \<and> u \<in> S ! i)"

definition mop_get_index_unbounded :: "nat sccmap \<Rightarrow> nat \<Rightarrow> nat nres" where
  "mop_get_index_unbounded S u = SPEC (\<lambda> i. i < length S \<and> u \<in> S ! i)"

lemma mop_get_index_unbounded_alt: "mop_get_index_unbounded = mop_get_index"
  unfolding mop_get_index_unbounded_def mop_get_index_def by argo

definition mop_get_the_val :: "nat sccmap \<Rightarrow> nat \<Rightarrow> nat set nres" where
  "mop_get_the_val S u = SPEC (\<lambda> r. (\<exists> i < length S. r = S ! i))"

definition mop_equal_set_states :: "nat sccmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where 
  "mop_equal_set_states S u v \<equiv> RETURN (\<exists>i < length S. u \<in> S!i \<and> v \<in> S!i)"

definition mop_transfer_to_antpar2 :: "nat sccmap \<Rightarrow> antpar \<Rightarrow> nat \<Rightarrow> antpar nres" where 
  "mop_transfer_to_antpar2 SM = (\<lambda> (XS,YS) u. SPEC(\<lambda> (XS',YS'). \<exists> i. i < length SM \<and> i < length YS \<and> u \<in> SM ! i \<and> XS' = (map (\<lambda> X. X - {u}) XS) \<and> YS' = (map (\<lambda> Y. Y - {u}) YS)[i:=insert u (YS ! i)]))"



section \<open>Concrete SCC Map\<close>

subsection \<open>Abstraction Relation\<close>

datatype node_state = STACK (val: nat) | DONE (data: nat)

definition "DONE0 = DONE 0"

type_synonym 'v oGS = "'v \<rightharpoonup> node_state"

definition "SCC_at I i = {v. I v = Some (DONE i)}"

definition SCC_\<alpha> :: "'v oGS \<Rightarrow> nat \<Rightarrow> 'v set list" where "SCC_\<alpha> I i \<equiv> map (SCC_at I) [0..<i]"

lemma set_SCC_\<alpha>_alt: "set (SCC_\<alpha> I i) = (SCC_at I ` {0..<i})"
  by (simp add: SCC_\<alpha>_def)

lemma SCC_at_extend_neq: "\<lbrakk>\<And>v. I v = Some (DONE j) \<Longrightarrow> \<not>Q v; j \<noteq> i\<rbrakk> \<Longrightarrow> SCC_at (\<lambda>v. if Q v then Some (DONE i) else I v) j = SCC_at I j"
  unfolding SCC_at_def
  apply auto
  done

lemma SCC_at_extend: "SCC_at (\<lambda>v. if Q v then Some (DONE i) else I v) i = Collect Q \<union> SCC_at I i"
  unfolding SCC_at_def
  apply auto
  done



locale scc_map_defs =
  fixes N::nat
  and D::nat
  and ni::size_t
begin


  definition "SCC_rel = br (\<lambda> (i, I). SCC_\<alpha> I i) (\<lambda>(i, I). i \<le> D \<and> ( \<forall> j. case I j of 
    None \<Rightarrow> True
  | Some ns \<Rightarrow> (case ns of
      STACK n \<Rightarrow> n < N
    | DONE d \<Rightarrow> d < i
  )))"
  
  lemma SCC_rel_length: "((i, I), SCC) \<in> SCC_rel \<Longrightarrow> i = length SCC"
    unfolding SCC_rel_def 
    by(auto simp: in_br_conv SCC_\<alpha>_def)


section \<open>Implementation SCC Map\<close>


  abbreviation "node_word_rel \<equiv> b_rel (snat_rel' TYPE(node_T)) (\<lambda>x. x<N)"
  abbreviation "node_word_assn \<equiv> b_assn (snat_assn' TYPE(node_T)) (\<lambda>x. x<N)"

  abbreviation "data_rel \<equiv> b_rel (snat_rel' TYPE(node_T)) (\<lambda>x. x<Suc D)"
  abbreviation "data_assn \<equiv> b_assn (snat_assn' TYPE(node_T)) (\<lambda>x. x<Suc D)"
  
  definition "\<alpha>_node_state N' i = (if i < N' then STACK i else DONE (i - N'))"
  
  definition "invar_node_state N' i = (i < N' + Suc D)"

  definition "node_state_rel_raw N' = br (\<alpha>_node_state N') (invar_node_state N')"
  definition "node_state_rel N' = size_rel O node_state_rel_raw N'"    
  
  
  abbreviation "node_state_assn N' \<equiv> pure (node_state_rel N')"
    
  lemma m1_notin_node_state_rel: "(-1,x) \<notin> node_state_rel N'"
    unfolding node_state_rel_def
    apply (auto split: node_state.splits simp: m1_notin_snat_rel)
    done
  
  sublocale node_state: dflt_pure_option "-1" "(node_state_assn N)" "ll_icmp_eq (-1)"
    apply unfold_locales
    subgoal
      apply (auto simp: pure_def pred_lift_extract_simps del: ext intro!: ext)
      unfolding node_state_rel_def
      apply (auto simp: snat_rel_def snat.rel_def in_br_conv snat_invar_def split: node_state.splits)
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

  definition node_state_none :: "node_state option" where "node_state_none = None"

  lemmas [sepref_fr_rules] =  node_state.hn_None[folded node_state_none_def]
  sepref_register node_state_none 

  concrete_definition node_state_am_empty[llvm_code,llvm_inline] is node_state.am2_empty_def
  concrete_definition node_state_am_lookup[llvm_code,llvm_inline] is node_state.am2_lookup_def
  concrete_definition node_state_am_contains_key[llvm_code,llvm_inline] is node_state.am2_contains_key_def
  concrete_definition node_state_am_update[llvm_code,llvm_inline] is node_state.am2_update_def
  concrete_definition node_state_am_delete[llvm_code,llvm_inline] is node_state.am2_delete_def


  lemmas [unfolded node_state_am_empty.refine,sepref_fr_rules] = node_state.am2_empty_hnr node_state.am2_empty_hnr_mop
  lemmas [unfolded node_state_am_lookup.refine,sepref_fr_rules] = node_state.am2_lookup_hnr node_state.am2_lookup_hnr_mop
  lemmas [unfolded node_state_am_contains_key.refine,sepref_fr_rules] = node_state.am2_contains_key_hnr node_state.am2_contains_key_hnr_mop
  lemmas [unfolded node_state_am_update.refine,sepref_fr_rules] = node_state.am2_update_hnr node_state.am2_update_hnr_mop
  lemmas [unfolded node_state_am_delete.refine,sepref_fr_rules] = node_state.am2_delete_hnr node_state.am2_delete_hnr_mop 

  definition "node_state_am_assn = node_state.am_assn"

  sepref_register 
    eq_nso: "(=):: node_state \<Rightarrow> _"
                                                              
  lemma hn_node_state_icmp_op:
    "(uncurry (RETURN oo (=)), uncurry (RETURN oo (=))) \<in> (node_state_rel N) \<times>\<^sub>r (node_state_rel N) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    unfolding node_state_rel_def node_state_rel_raw_def
    apply (clarsimp simp: in_br_conv in_nres_rel_iff )
    apply rule
    subgoal for x xi y yi
      apply(subgoal_tac "xi = yi")
      by(auto elim: snat_rel_abs_eq2)
    subgoal for x xi y yi
      apply(subgoal_tac "xi = yi")
      by(auto simp: \<alpha>_node_state_def split: if_splits elim: snat_rel_con_eq1)
    done


  lemmas [sepref_fr_rules] = hn_word_icmp_op(1)[FCOMP hn_node_state_icmp_op]

  definition "node_state_rel_alt' = {(nsi,ns)| nsi ns. case ns of STACK i \<Rightarrow> (nsi,i) \<in> node_word_rel | DONE j \<Rightarrow> (nsi-ni,j) \<in> data_rel}"
  
  
  lemma node_state_rel_alt_def_aux1: "D + N < max_snat 64 \<Longrightarrow> (ni, N) \<in> snat_rel \<Longrightarrow> b = DONE x2 \<Longrightarrow> (a - ni, x2) \<in> snat_rel \<Longrightarrow> x2 < Suc D \<Longrightarrow> ((a - ni) + ni, x2 + N) \<in> snat_rel"
    apply (rule plus_snat_refine)
    apply (drule nat_Suc_less_le_imp[of x2]) 
    apply auto 
    done
  
  lemma node_state_rel_alt_def_aux2: "D + N < max_snat 64 \<Longrightarrow> (ni, N) \<in> snat_rel \<Longrightarrow> \<forall>x1. b = STACK x1 \<longrightarrow> (a, x1) \<in> snat_rel \<and> x1 < N \<Longrightarrow> \<forall>x2. b = DONE x2 \<longrightarrow> (a - ni, x2) \<in> snat_rel \<and> x2 < Suc D \<Longrightarrow> (a, case b of STACK i \<Rightarrow> i| DONE j \<Rightarrow> j + N) \<in> snat_rel"
    using node_state_rel_alt_def_aux1 
    apply(auto split: node_state.splits)
    done
    
  
  lemma node_state_rel_alt_def: "D + N < max_snat 64 \<Longrightarrow> (ni, N) \<in> size_rel \<Longrightarrow> node_state_rel N = node_state_rel_alt'"
    unfolding node_state_rel_alt'_def node_state_rel_def node_state_rel_raw_def
    apply (auto split: node_state.splits simp: in_br_conv \<alpha>_node_state_def invar_node_state_def split_ifs)
    apply (meson leI minus_snat_refine)
    apply (rule relcompI)
    using node_state_rel_alt_def_aux2
    apply blast
    apply(auto split: node_state.splits simp: in_br_conv \<alpha>_node_state_def invar_node_state_def)
    done

  definition "is_DONE ns \<equiv> \<exists>i. ns = DONE i"
  
  definition "is_STACK_v ns \<equiv> \<exists>v. ns = STACK v"
  
  definition "is_SOME_DONE nso \<equiv> if is_None nso then False else is_DONE (the nso)"
  
  definition "is_SOME_STACK_v nso \<equiv> if is_None nso then False else is_STACK_v (the nso)"

  definition [llvm_inline]: "is_DONE_impl x \<equiv> from_bool (x\<ge>ni)"
                                                     
  definition [llvm_inline]: "is_STACK_v_impl x \<equiv> from_bool (x<ni)"


end


locale scc_map = scc_map_defs N D ni for N D ni + 
  assumes n_impl: "(ni, N) \<in> size_rel"
  assumes D_N_BOUND: "D + N < max_snat (LENGTH(size_T))"
begin

  lemmas [sepref_import_param] = n_impl

  lemma D_BOUND: "D < max_snat 64 - N" 
    using D_N_BOUND len_size_T_alt less_diff_conv by presburger

  lemma D_BOUND': "x < Suc D \<Longrightarrow> x < max_snat 64 - N"
    using D_BOUND by simp

  lemma DONE_impl_refine_aux: "(a, a') \<in> snat_rel \<Longrightarrow> a' < Suc D \<Longrightarrow> (ni + a, N + a') \<in> snat_rel"
    apply (rule plus_snat_refine)
    using D_N_BOUND apply simp
    using n_impl by simp
  
  lemma STACK_impl_refine: "(id, STACK) \<in> node_word_rel \<rightarrow> node_state_rel N"
    by (auto simp: node_state_rel_def br_def \<alpha>_node_state_def invar_node_state_def node_state_rel_raw_def)

  lemma DONE_impl_refine: "((+) ni, DONE) \<in> data_rel \<rightarrow> node_state_rel N"
    apply (clarsimp simp: node_state_rel_def br_def \<alpha>_node_state_def invar_node_state_def node_state_rel_raw_def) 
    apply (rule relcompI)
    apply (erule DONE_impl_refine_aux; assumption)
    apply auto
    done
  
  lemma is_STACK_v_impl_refine: "(is_STACK_v_impl, is_STACK_v) \<in> node_state_rel N \<rightarrow> bool1_rel"
    unfolding is_STACK_v_impl_def is_STACK_v_def
    apply clarsimp
    using n_impl
    apply (auto simp: in_snat_rel_snat node_state_rel_def bool1_rel_def bool.rel_def in_br_conv 
                      m1_notin_snat_rel \<alpha>_node_state_def split_ifs node_state_rel_raw_def
               split: node_state.splits 
                dest: lt_snat_refine) 
    done

  lemma is_DONE_impl_refine: "(is_DONE_impl, is_DONE) \<in> node_state_rel N \<rightarrow> bool1_rel"
    unfolding is_DONE_impl_def is_DONE_def
    apply clarsimp
    using n_impl
    apply (auto simp: in_snat_rel_snat node_state_rel_def bool1_rel_def bool.rel_def in_br_conv 
                      m1_notin_snat_rel in_snat_rel_leq \<alpha>_node_state_def invar_node_state_def node_state_rel_raw_def
               split: node_state.splits 
                dest: lt_snat_refine)
    
    done
  
  
  lemmas [sepref_import_param] = STACK_impl_refine is_DONE_impl_refine is_STACK_v_impl_refine DONE_impl_refine

  lemma hn_node_val[sepref_fr_rules]: "(Mreturn, RETURN o val) \<in> [\<lambda>x. \<exists>j. x = STACK j]\<^sub>a (node_state_assn N)\<^sup>k \<rightarrow> node_word_assn"
    apply sepref_to_hoare
    unfolding node_state_rel_alt_def[OF D_N_BOUND[simplified] n_impl] node_state_rel_alt'_def br_def 
    apply clarsimp
    apply vcg 
    done

  lemma hn_node_data[sepref_fr_rules]: "(Mreturn o (\<lambda> x. x - ni), RETURN o data) \<in> [\<lambda>x. \<exists>j. x = DONE j]\<^sub>a (node_state_assn N)\<^sup>k \<rightarrow> data_assn"
    apply sepref_to_hoare
    unfolding node_state_rel_alt_def[OF D_N_BOUND[simplified] n_impl] node_state_rel_alt'_def br_def 
    apply clarsimp
    apply vcg
    done
                            
  sepref_def is_SOME_DONE_impl is "RETURN o is_SOME_DONE" :: "node_state.option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding is_SOME_DONE_def
    supply [simp] = option.split_sels(2)
    by sepref

  concrete_definition (in -) is_SOME_DONE_ll' [llvm_code] is scc_map.is_SOME_DONE_impl_def
  lemmas [sepref_fr_rules] = is_SOME_DONE_impl.refine[unfolded is_SOME_DONE_ll'.refine[OF scc_map_axioms]]
  
  
  sepref_def is_SOME_STACK_v_impl is "RETURN o is_SOME_STACK_v" :: "node_state.option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding is_SOME_STACK_v_def
    supply [simp] = option.split_sels(2)
    by sepref

  concrete_definition (in -) is_SOME_STACK_v_ll' [llvm_code] is scc_map.is_SOME_STACK_v_impl_def
  lemmas [sepref_fr_rules] = is_SOME_STACK_v_impl.refine[unfolded is_SOME_STACK_v_ll'.refine[OF scc_map_axioms]]

end



context scc_map_defs
begin


  subsection \<open>Concrete operations\<close>

  definition get_output_size_impl :: "nat \<times> nat oGS \<Rightarrow> nat" where "get_output_size_impl = (\<lambda> (i,I). i)"
  sepref_register get_output_size_impl

  definition get_index_of :: "nat \<times> nat oGS \<Rightarrow> nat \<Rightarrow> nat" where 
    "get_index_of = (\<lambda> (i,I) u. data (the (I u)))"
  sepref_register get_index_of

  definition get_index_of_unbounded :: "nat \<times> nat oGS \<Rightarrow> nat \<Rightarrow> nat" where 
    "get_index_of_unbounded = (\<lambda> (i,I) u. data (the (I u)))"
  sepref_register get_index_of_unbounded

  lemma get_index_of_unbounded_alt: "get_index_of_unbounded = get_index_of"
    unfolding get_index_of_unbounded_def get_index_of_def by blast

  definition lookup_state_val :: "nat \<times> nat oGS \<Rightarrow> nat \<Rightarrow> node_state option" where "lookup_state_val = (\<lambda> (i,I) u. op_map_lookup u I)"
  sepref_register lookup_state_val

  definition lookup_state_the_val :: "nat \<times> nat oGS \<Rightarrow> nat \<Rightarrow> node_state nres" where "lookup_state_the_val = (\<lambda> (i,I) u. 
  do{
    v \<leftarrow> mop_map_lookup u I;
    RETURN (the v)
  })"
  sepref_register lookup_state_the_val

  definition "valid_map_entry = (\<lambda> (i,I) u. I u \<noteq> None)"

  definition "transfer_to_disjdlt2_pre = (\<lambda>((S,(XS,YS)), u). \<exists>j. u \<in> S ! j \<and> j < length S \<and> j < length YS)"

  lemma not_valid_map_entry_eq: "\<not>valid_map_entry (i,I) u \<longleftrightarrow> I u = None"
    unfolding valid_map_entry_def by fast

  lemma valid_map_entry_eq: "valid_map_entry (i,I) u \<longleftrightarrow> (\<exists> ya. I u = Some ya)"
    unfolding valid_map_entry_def by fast

  definition is_equal_set_states :: "nat \<times> nat oGS \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where "is_equal_set_states iI u v = 
  do{
    ASSERT (valid_map_entry iI u);
    v1 \<leftarrow> lookup_state_the_val iI u;
    ASSERT (valid_map_entry iI v);
    v2 \<leftarrow> lookup_state_the_val iI v;
    RETURN (v1 = v2)
  }"
  sepref_register is_equal_set_states


  definition transfer_to_antpar2 :: "nat \<times> nat oGS \<Rightarrow> antpar \<Rightarrow> nat \<Rightarrow> antpar nres" where
  "transfer_to_antpar2 iI DL u \<equiv> do{
    ASSERT (valid_map_entry iI u);
    ni \<leftarrow> lookup_state_the_val iI u;
    ASSERT (\<exists>i. ni = DONE i);
    let i = data ni;
    ASSERT (i < length (snd DL));
    RETURN (op_antpar_move_to_list2 DL u i)
  }"
  sepref_register transfer_to_antpar2


  lemma mop_get_output_size_refine: "((i, I), S) \<in> SCC_rel \<Longrightarrow> RETURN (get_output_size_impl (i, I)) = mop_get_output_size S"
    unfolding get_output_size_impl_def mop_get_output_size_def
    apply clarify
    apply(drule SCC_rel_length)
    apply auto
    done

  lemma get_index_of_refine: "((i, I), C) \<in> SCC_rel \<Longrightarrow> j < length C \<Longrightarrow> u \<in> C ! j \<Longrightarrow> RETURN (get_index_of (i, I) u) \<le> mop_get_index C u"
    unfolding get_index_of_def mop_get_index_def SCC_rel_def
    apply(refine_rcg)
    by(auto simp: SCC_rel_def in_br_conv SCC_\<alpha>_def SCC_at_def
      split: option.splits node_state.splits)

  lemma mop_equal_set_states_refine: "u \<in> S ! j \<Longrightarrow> v \<in> S ! k \<Longrightarrow> j < length S \<Longrightarrow> k < length S \<Longrightarrow> ((i, I), S) \<in> SCC_rel \<Longrightarrow> is_equal_set_states (i, I) u v \<le> mop_equal_set_states S u v"
    unfolding is_equal_set_states_def mop_equal_set_states_def lookup_state_the_val_def 
    apply(refine_vcg)
    by(auto simp: SCC_rel_def in_br_conv SCC_\<alpha>_def SCC_at_def valid_map_entry_eq) 

  lemma mop_transfer_to_antpar2_refine: "u \<in> S ! j \<Longrightarrow> j < length S \<Longrightarrow> j < length YS \<Longrightarrow> ((i, I), S) \<in> SCC_rel \<Longrightarrow> transfer_to_antpar2 (i, I) (XS, YS) u \<le> mop_transfer_to_antpar2 S (XS, YS) u"
    unfolding transfer_to_antpar2_def mop_transfer_to_antpar2_def lookup_state_the_val_def op_antpar_move_to_list2_def valid_map_entry_def
    apply (refine_vcg) 
    by (fastforce simp:  SCC_rel_def in_br_conv SCC_\<alpha>_def SCC_at_def)+

  lemma mop_get_output_size_correct: "(RETURN o get_output_size_impl, mop_get_output_size) \<in> SCC_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
    apply(refine_rcg)
    by(auto dest: mop_get_output_size_refine)

  lemma get_index_of_correct:  "(uncurry (RETURN oo get_index_of), uncurry mop_get_index) \<in> [\<lambda>(S,u). (\<exists> j < length S. u \<in> S ! j)]\<^sub>f SCC_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
    by (auto intro!: frefI nres_relI get_index_of_refine)

  lemma get_index_of_unbounded_correct:  "(uncurry (RETURN oo get_index_of_unbounded), uncurry mop_get_index_unbounded) \<in> [\<lambda>(S,u). (\<exists> j < length S. u \<in> S ! j)]\<^sub>f SCC_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
    using get_index_of_correct mop_get_index_unbounded_alt get_index_of_unbounded_alt by presburger

  lemma mop_equal_set_states_correct: "(uncurry2 is_equal_set_states, uncurry2 mop_equal_set_states) \<in> 
    [\<lambda>((S,u),v). (\<exists> j < length S. u \<in> S ! j) \<and> (\<exists> k < length S. v \<in> S ! k)]\<^sub>f (SCC_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    by(auto intro!: frefI nres_relI mop_equal_set_states_refine)

  lemma mop_transfer_to_antpar2_correct: "(uncurry2 transfer_to_antpar2, uncurry2 mop_transfer_to_antpar2) 
    \<in> [transfer_to_disjdlt2_pre]\<^sub>f (SCC_rel \<times>\<^sub>r Id) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
    by(auto intro!: frefI nres_relI mop_transfer_to_antpar2_refine simp: transfer_to_disjdlt2_pre_def)


end


context scc_map_defs
begin


subsection \<open>Sepref operations\<close>

  definition "output_assn_raw = data_assn \<times>\<^sub>a (node_state.am_assn N)"
  definition "output_assn \<equiv> hr_comp output_assn_raw SCC_rel"


  sepref_definition get_output_size_impl_ll is "RETURN o get_output_size_impl" :: "output_assn_raw\<^sup>k \<rightarrow>\<^sub>a data_assn"
    unfolding output_assn_raw_def get_output_size_impl_def
    apply sepref
    done

  concrete_definition (in -) get_output_size_impl_ll' [llvm_code] is scc_map_defs.get_output_size_impl_ll_def
  lemmas [sepref_fr_rules] = get_output_size_impl_ll.refine[unfolded get_output_size_impl_ll'.refine]
                                                       
  sepref_definition lookup_state_val_ll is "uncurry (RETURN oo lookup_state_val)" :: "output_assn_raw\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow>\<^sub>a node_state.option_assn"
    unfolding lookup_state_val_def output_assn_raw_def
    apply sepref
    done

  concrete_definition (in -) lookup_state_val_ll' [llvm_code] is scc_map_defs.lookup_state_val_ll_def
  lemmas [sepref_fr_rules] = lookup_state_val_ll.refine[unfolded lookup_state_val_ll'.refine]

  sepref_definition lookup_state_the_val_ll is "uncurry lookup_state_the_val" :: "[\<lambda> (iI,u). valid_map_entry iI u]\<^sub>a output_assn_raw\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow> node_state_assn N"
    unfolding lookup_state_the_val_def output_assn_raw_def valid_map_entry_def
    apply sepref
    done

  concrete_definition (in -) lookup_state_the_val_ll' [llvm_code] is scc_map_defs.lookup_state_the_val_ll_def
  lemmas [sepref_fr_rules] = lookup_state_the_val_ll.refine[unfolded lookup_state_the_val_ll'.refine]


  sepref_definition is_equal_set_states_ll is "uncurry2 is_equal_set_states" :: "output_assn_raw\<^sup>k *\<^sub>a node_word_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding  is_equal_set_states_def
    apply sepref
    done

  concrete_definition (in -) is_equal_set_states_ll'  [llvm_code] is scc_map_defs.is_equal_set_states_ll_def
  lemmas [sepref_fr_rules] = is_equal_set_states_ll.refine[unfolded is_equal_set_states_ll'.refine]

end

context scc_map
begin

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

  interpretation disj_set_list_tuple_env N N ni ni
    apply(unfold_locales)
    using n_impl .


  lemmas [unfolded disj_set_list_tuple_invar_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_disj_set_list_tuple_invar_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded disj_set_count1_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_count1_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded disj_set_count2_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_count2_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded expand_capacity1_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_expand1_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded expand_capacity2_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_expand2_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded is_member_any_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_mem_any_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded is_member_any1_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_mem_any1_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded is_member_any2_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_mem_any2_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded is_member_of1_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_mem_of1_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded is_member_of2_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_mem_of2_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded teq_set_member_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_eq_set_mem_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded tmove_elem1_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_move1_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded tmove_elem2_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_move2_hnr[OF disj_set_list_tuple_env_axioms]
  lemmas [unfolded tremove_elem_ll'.refine[OF disj_set_list_tuple_env_axioms],sepref_fr_rules] = disj_set_list_tuple_env.mop_antpar_remove_hnr[OF disj_set_list_tuple_env_axioms]
  
  

  sepref_definition get_index_of_ll is "uncurry (RETURN oo get_index_of)" :: "[\<lambda> ((i,I),u). \<exists> v. I u = Some (DONE v)]\<^sub>a output_assn_raw\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow> data_assn"
    unfolding output_assn_raw_def get_index_of_def
    apply sepref
    done

    
  sepref_definition get_index_of_unbounded_ll is "uncurry (RETURN oo get_index_of_unbounded)" :: "[\<lambda> ((i,I),u). \<exists> v. I u = Some (DONE v)]\<^sub>a output_assn_raw\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow> size_assn"
    unfolding output_assn_raw_def get_index_of_unbounded_def
    apply sepref
    done


  sepref_definition transfer_to_antpar2_ll is "uncurry2 transfer_to_antpar2" :: "output_assn_raw\<^sup>k *\<^sub>a disj_set_list_tuple_assn\<^sup>d *\<^sub>a node_word_assn\<^sup>k \<rightarrow>\<^sub>a disj_set_list_tuple_assn"
    unfolding transfer_to_antpar2_def
    supply[dest] = D_BOUND'
    apply sepref
    done
    
  concrete_definition (in -) get_index_of_unbounded_ll' [llvm_code] is scc_map.get_index_of_unbounded_ll_def
  lemmas get_index_of_unbounded_hnr'[sepref_fr_rules] = scc_map.get_index_of_unbounded_ll.refine[OF scc_map_axioms, unfolded get_index_of_unbounded_ll'.refine[OF scc_map_axioms]]
  
  concrete_definition (in -) get_index_of_ll' [llvm_code] is scc_map.get_index_of_ll_def
  lemmas get_index_of_hnr'[sepref_fr_rules] = scc_map.get_index_of_ll.refine[OF scc_map_axioms, unfolded get_index_of_ll'.refine[OF scc_map_axioms]]
    
    
  concrete_definition (in -) transfer_to_antpar2_ll' [llvm_code] is scc_map.transfer_to_antpar2_ll_def
  lemmas transfer_to_antpar2_hnr'[sepref_fr_rules] = scc_map.transfer_to_antpar2_ll.refine[OF scc_map_axioms, unfolded transfer_to_antpar2_ll'.refine[OF scc_map_axioms]]


end

context scc_map_defs
begin

  context 
    notes [fcomp_norm_unfold] = output_assn_def[symmetric]
  begin

    lemmas mop_get_output_size_hnr[sepref_fr_rules] = get_output_size_impl_ll.refine[FCOMP mop_get_output_size_correct]
    lemmas mop_equal_set_states_hnr[sepref_fr_rules] = is_equal_set_states_ll.refine[FCOMP mop_equal_set_states_correct]

  end

  lemma(in scc_map_defs) op_list_length_unbounded:  "(get_output_size_impl_ll, RETURN \<circ> op_list_length) \<in> output_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn"
    using mop_get_output_size_hnr
    unfolding mop_get_output_size_def
    by (auto simp: comp_def elim: b_assn_out_hfrefttnd[THEN set_mp])

end

context scc_map
begin

  lemma SCC_rel_pre: "((i, I), C) \<in> SCC_rel \<Longrightarrow> I u = Some (DONE j) \<longleftrightarrow> j < length C \<and> u \<in> C ! j"
    unfolding SCC_rel_def SCC_\<alpha>_def SCC_at_def
    by(auto simp: in_br_conv split: option.splits node_state.splits)

  context 
    notes [fcomp_norm_unfold] = output_assn_def[symmetric]
    notes [simp] = SCC_rel_pre
  begin
  
    lemmas transfer_to_antpar2_hnr[sepref_fr_rules] = transfer_to_antpar2_hnr'[FCOMP mop_transfer_to_antpar2_correct]    
    lemmas mop_get_index_hnr[sepref_fr_rules] = get_index_of_hnr'[FCOMP get_index_of_correct]
    lemmas mop_get_index_unbounded_hnr[sepref_fr_rules] = get_index_of_unbounded_hnr'[FCOMP get_index_of_unbounded_correct]
  end

end

end
