theory MEC_Index_List        
  imports SCC_map Filter_Index_List "../mec/MDP_MEC"
begin

  text \<open>
    To accomodate the MEC algorithm, we added some specific operations to the Filter_Index_List.
  
  \<close>
  
  lemma RETURN_comp_f: "(RETURN o f) = (\<lambda>x. RETURN (f x))"
    by fastforce
  
  context scc_map_defs
  begin
  
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using op_list_length_unbounded .
  
  end
  
  
  definition "mop_unfiltered_index_of = (\<lambda> (C,V) u. mop_get_index C u)"
  definition "mop_filtered_index_of = (\<lambda> (C,V) u. SELECT (\<lambda> i. i < length V \<and> u \<in> V ! i))"
  
  
  locale MEC_index_list_defs = fixes CV::"nat set list \<times> nat set list"
  begin
  
    definition "C = (\<lambda> (C,V). C)"
    definition "V = (\<lambda> (C,V). V)"
  
  end
  
  lemma CV_sel_simps: 
    "MEC_index_list_defs.C (C,V) = C"
    "MEC_index_list_defs.V (C,V) = V"
    unfolding MEC_index_list_defs.C_def MEC_index_list_defs.V_def
    apply auto
    done
  
  
  locale MEC_index_list_invar = MEC_index_list_defs CV for CV
  begin
  
  
  end
  
  definition "unfiltered_index_of = (\<lambda> (C,FA,c) u. mop_get_index C u)"
  sepref_register unfiltered_index_of
  
  definition "filtered_index_of = (\<lambda> CV u. do{
      i \<leftarrow> mop_unfiltered_index_of CV u;
      ASSERT(i < length (fst CV));
      mop_filter_index_select CV i
    })"
    sepref_register filtered_index_of
  
  
  definition "MEC_filter_properties \<equiv> (\<lambda> (C,V) u. (\<forall> i j. i < length C \<longrightarrow> j < length C \<longrightarrow> u \<in> C ! i \<longrightarrow> u \<in> C ! j \<longrightarrow> i = j) \<and> set V \<subseteq> set C)"
  
  lemma filtered_index_of_refine:
    assumes MP: "MEC_filter_properties (C,V) u"
    assumes IC: "i < length C" 
    assumes UCI: "u \<in> C ! i"
    shows "filtered_index_of (C, V) u \<le> mop_filtered_index_of (C, V) u"
  proof -
    
    {
      fix j k
      assume JC: "j < length C"
      and UCJ: "u \<in> C ! j"
      and NEQ: "\<forall>x<length V. V ! x \<noteq> C ! j"
      and KV: "k < length V"
      and UVK: "u \<in> V ! k"
      from MP IC UCI JC UCJ have "i = j" unfolding MEC_filter_properties_def by blast
      with MP IC KV UCI UVK have "V ! k = C ! j"
        unfolding MEC_filter_properties_def apply clarsimp 
        by (metis in_set_conv_nth subset_code(1)) 
      with NEQ KV have False by presburger
    } note AUX1 = this
  
  
    show ?thesis
      unfolding filtered_index_of_def mop_unfiltered_index_of_def mop_get_index_def mop_filter_index_select_def
        mop_filtered_index_of_def
      by(auto simp: refine_pw_simps pw_le_iff intro: AUX1)
  qed
  
  lemma unfiltered_index_of_correct: "(uncurry unfiltered_index_of, uncurry mop_unfiltered_index_of) \<in> [\<lambda> ((C, V), u). \<exists>i<length C. u \<in> C ! i]\<^sub>f filter_list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
    unfolding filter_list_rel_def unfiltered_index_of_def mop_unfiltered_index_of_def
    by(auto simp: in_br_conv filter_list_defs.\<alpha>_def intro!: frefI nres_relI)
  
  lemma filtered_index_of_correct: "(uncurry filtered_index_of, uncurry mop_filtered_index_of) 
    \<in> [\<lambda> ((C, V), u). (\<exists>i<length C. u \<in> C ! i) \<and> MEC_filter_properties (C,V) u]\<^sub>f 
      Id \<times>\<^sub>r nat_rel \<rightarrow> \<langle>\<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel"
    by (auto intro!: frefI nres_relI filtered_index_of_refine)
  
  context scc_map
  begin
  
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using mop_get_output_size_hnr
      unfolding mop_get_output_size_def
      by (auto simp: comp_def elim: b_assn_out_hfrefttnd[THEN set_mp])
  
    sepref_definition unfiltered_index_of_ll is "uncurry unfiltered_index_of" :: "[\<lambda> ((C, FA, c), u). \<exists>i<length C. u \<in> C ! i]\<^sub>a filter_list_assn_aux\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow> size_assn"
      unfolding unfiltered_index_of_def filter_list_assn_def filter_list_assn_aux_def
      by sepref
  
  
    lemma unfiltered_index_of_ll_refine_aux:  "((aa, ab, bb), a, b) \<in> filter_list_rel \<Longrightarrow>
       bc = ba \<Longrightarrow> \<exists>i<length a. ba \<in> a ! i \<Longrightarrow> \<exists>i<length aa. ba \<in> aa ! i "
      apply(drule filter_list_rel_eq_xs) by blast
  
    context
      notes [simp] = unfiltered_index_of_ll_refine_aux 
      notes[fcomp_norm_unfold] = filter_list_assn_def[symmetric] 
    begin
  
      lemmas unfiltered_index_of_hnr' = unfiltered_index_of_ll.refine[FCOMP unfiltered_index_of_correct]
  
    end
  
    concrete_definition (in -) unfiltered_index_of_ll' is scc_map.unfiltered_index_of_ll_def
    lemmas unfiltered_index_of_hnr[sepref_fr_rules] = unfiltered_index_of_hnr'[unfolded unfiltered_index_of_ll'.refine[OF scc_map_axioms]]
    
    
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using mop_get_output_size_hnr
      unfolding mop_get_output_size_def
      by (auto simp: comp_def elim: b_assn_out_hfrefttnd[THEN set_mp])
      
    sepref_definition filtered_index_of_ll is "uncurry filtered_index_of" :: "[\<lambda> ((C, V), u). \<exists>i<length C. u \<in> C ! i]\<^sub>a filter_list_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow> size_option_assn"
      unfolding filtered_index_of_def
      apply sepref
      done
  
  
    context
      notes[fcomp_norm_unfold] = filter_list_assn_def[symmetric]  option_assn_option_rel
    begin
  
      lemmas filtered_index_of_hnr' = filtered_index_of_ll.refine[FCOMP filtered_index_of_correct]
  
    end
    
    concrete_definition (in -) filtered_index_of_ll' is scc_map.filtered_index_of_ll_def
    lemmas filtered_index_of_hnr[sepref_fr_rules] = filtered_index_of_hnr'[unfolded filtered_index_of_ll'.refine[OF scc_map_axioms]]
    
    
  
  end


end