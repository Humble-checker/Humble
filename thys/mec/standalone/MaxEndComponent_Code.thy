theory MaxEndComponent_Code
  imports "Isabelle_LLVM.Proto_IICF_EOArray" "Modest_MDP_MEC" "../MaxEndComponent"
begin

  
  locale mdp_graph_mec_impl_defs =
    fixes N::nat and ni::size_t
  begin
  
    interpretation scc_map_defs N N ni .

    definition "identify_mecs_fine_impl C' = ( \<lambda> MDSKZ. do{
      ASSERT(distinct C');
      let CV = op_create_filter_set C';
      CV \<leftarrow> nfoldli [0..<N] (\<lambda>_. True) (\<lambda> u CV. 
      do { 
        ASSERT(u < N);
        if (op_deleted_state MDSKZ u) then 
          RETURN CV
        else
        do {
          ASSERT(iterate_succs_eq_pre ((MDSKZ,CV),u));
          g \<leftarrow> RETURN (\<not>op_all_succ_eq_map MDSKZ CV u);
          if g then do {
            i \<leftarrow> unfiltered_set_open_block CV (\<lambda> C. do{
              ASSERT(\<exists> i < length C. u \<in> C ! i);
              mop_get_index C u
            });
            ASSERT(i < length (fst CV));
            RETURN (op_filter_elem_id CV i)
          }
          else 
            RETURN CV
        }
      }) CV; \<^cancel>\<open>Output: filter_index_set\<close>
  
      CV \<leftarrow> mop_create_filter CV;
      RETURN CV \<^cancel>\<open>Output: filter_index_list\<close>
    })"
    sepref_register identify_mecs_fine_impl
    
    definition "cull_graph_fine_impl = (\<lambda> CV MDSKZ\<^sub>1. do {
      num \<leftarrow> unfiltered_list_open_block CV (\<lambda> C. mop_get_output_size C);
      ASSERT(num \<le> N);
      let numM = op_get_mec_num MDSKZ\<^sub>1;
      let numV = op_length_filtered CV;
      ASSERT(numM + numV \<le> N);
      let MDSKZ = op_expand_capacity MDSKZ\<^sub>1 numV;
      MLDSKZ \<leftarrow> mop_track_sccs MDSKZ CV;
  
      MLDSKZ \<leftarrow> nfoldli [0..<N] (\<lambda>_. True) (\<lambda> u MLDSKZ. 
      do {
        ASSERT(u < N);
        if (op_deleted_stateL MLDSKZ u) then 
        do {
          RETURN MLDSKZ
        }
        else do{
          ASSERT((\<exists>i<length (fst CV). u \<in> fst (CV) ! i) \<and> MEC_filter_properties CV u);
          io \<leftarrow> mop_filtered_index_of CV u;
          if (is_None io) then do{
            ASSERT (mark_as_unfinished_pre ((MLDSKZ,CV),u));
            mop_add_state_unfinished MLDSKZ CV u
          }
          else do {
            let i = the io;
            ASSERT (numM + i < N);
            let i' = op_bound_val (\<lambda>i. i < N) (numM + i);
            ASSERT(mark_as_MEC_pre N (((MLDSKZ,CV),u),i'));
            mop_add_state_to_mec MLDSKZ CV u i'
          }
        }
      }) MLDSKZ;
  
      ASSERT( mop_untrack_sccs_pre (MLDSKZ,CV));
      mop_untrack_sccs MLDSKZ CV
    })"
    sepref_register cull_graph_fine_impl
  
    definition "compute_MEC_fine_impl M\<^sub>0 \<equiv> do {
    
      MDSKZ \<leftarrow> mop_init_mdp M\<^sub>0;
  
      MDSKZ \<leftarrow> WHILEIT (compute_MEC_invar M\<^sub>0) op_states_non_empty 
      (\<lambda>MDSKZ. do {
        
        \<comment>\<open>Compute the SCCs and remove any transitions that have branches leaving an SCC\<close>
        C \<leftarrow> compute_sccs MDSKZ;
  
        ASSERT(scc_list C (compute_MEC_invar_def.S MDSKZ) (compute_MEC_invar_def.K MDSKZ) \<and> length C \<le> N);
        
        \<comment>\<open>Identify the SCCs that are MECs\<close>
        CV \<leftarrow> identify_mecs_fine_impl C MDSKZ;
  
        ASSERT(C = fst CV \<and> distinct (snd CV) \<and> set (snd CV) = {S' \<in> set C. closed_mdp S' (compute_MEC_invar_def.K MDSKZ)} \<and> length (compute_MEC_invar_def.D MDSKZ) + length (snd CV) \<le> N);
  
        \<comment>\<open>Remove the MECs from the graph and cull edges\<close>
        MDSKZ \<leftarrow> cull_graph_fine_impl CV MDSKZ;
  
        RETURN MDSKZ
      }) MDSKZ; 
    
      ASSERT(get_mec_pre MDSKZ);
      let (D,M) = op_get_mecs MDSKZ;
      unborrow M M\<^sub>0;
      RETURN D
    }"
  
  
    lemma mop_get_state_mec_id_alt: "mop_get_state_mec_id = mop_filtered_index_of"
      unfolding mop_get_state_mec_id_def mop_filtered_index_of_def by blast
  
  end
    
  
  locale mdp_graph_mec_impl_env = mdp_graph_mec_impl_defs + Finite_MDP M\<^sub>0 for M\<^sub>0::"nat mdpc" +
    assumes N_BOUND: "2*N < max_size_t"
    assumes n_impl: "(ni, N) \<in> size_rel"
    assumes M\<^sub>0_STATES: "states M\<^sub>0 = {0..<N}"
  begin

    lemma card_states_M\<^sub>0: "card (states M\<^sub>0) = N"
      unfolding M\<^sub>0_STATES by simp
  
    lemma push_bound_N_aux: "x \<le> N \<Longrightarrow> x < max_size_t"
      using n_impl in_snat_rel_boundsD by fastforce

    interpretation mec_algo M\<^sub>0
      by(unfold_locales)
  
    lemma Id_option_relI: "(x,y) \<in> Id \<Longrightarrow> (x,y) \<in> \<langle>Id\<rangle>option_rel"
      by simp
  
    lemma ref_RETURN_to_ref_SPEC: "X \<le> RETURN y \<Longrightarrow> X \<le> SPEC (\<lambda> x. (x,y) \<in> Id)"
      by (simp add: RETURN_SPEC_conv)
  
    lemma option_case_refine: "m1 \<le> \<Down>R m1' \<Longrightarrow> (\<And> i. m2 i \<le> \<Down>R (m2' i)) \<Longrightarrow> (io,io') \<in> Id \<Longrightarrow> (if is_None io then m1 else let i = the io in m2 i)
           \<le> \<Down> R (case io' of None \<Rightarrow> m1' | Some i \<Rightarrow> m2' i)"
      by auto

    lemma mop_untrack_sccs_pre_cull_alt: "mop_untrack_sccs_pre_cull = mop_untrack_sccs_pre"
      unfolding mop_untrack_sccs_pre_cull_def mop_untrack_sccs_pre_def by fast
  
    lemma get_scc_val_alt: "get_scc_val u C = mop_get_index C u"
      unfolding get_scc_val_def mop_get_index_def by presburger
  
    lemma set_to_list_alt: "set_to_list = mop_create_filter"
      unfolding set_to_list_def mop_create_filter_def by blast
  
    lemma MDSKZ_case_ref: "(s',s) \<in> Id \<Longrightarrow> (case s of (M, S, K) \<Rightarrow> m (M,S,K)) \<le> \<Down> Id (case s' of (M, S, K) \<Rightarrow> m' M S K) \<Longrightarrow> m s \<le> \<Down> Id (case s' of (M, S, K) \<Rightarrow> m' M S K)"
      by auto
  
    lemma CV_case_ref: "(s',s) \<in> Id \<Longrightarrow> (case s of (C,V) \<Rightarrow> m (C,V)) \<le> \<Down> Id (case s' of (C,V) \<Rightarrow> m' C V) \<Longrightarrow> m s \<le> \<Down> Id (case s' of (C,V) \<Rightarrow> m' C V)"
      by auto
  
    lemma MLDSKZ_case_ref: "(s',s) \<in> Id \<Longrightarrow> (case s of (L, M, S, K) \<Rightarrow> m (L,M,S,K)) \<le> \<Down> Id (case s' of (L, M, S, K) \<Rightarrow> m' L M S K) \<Longrightarrow> m s \<le> \<Down> Id (case s' of (L, M, S, K) \<Rightarrow> m' L M S K)"
      by auto
  
    lemma identify_mecs_fine_impl_refine[refine]: 
      assumes MDSKZDEF: "MDSKZ = MDSKZ'"
      assumes CDEF: "C = C'"
      shows "identify_mecs_fine_impl C MDSKZ \<le> \<Down> Id (identify_mecs_fine C' MDSKZ')"
    proof -
  
      show ?thesis
        unfolding identify_mecs_fine_def identify_mecs_fine_impl_def op_deleted_state_def op_create_filter_set_def
          unfiltered_set_open_block_def op_filter_elem_id_def ASSERT_over_prod iterate_succs_eq_pre_def
        apply(cases MDSKZ)
        apply(simp only: MDSKZDEF CDEF)
        apply clarify
        apply(refine_vcg)
        apply simp
        apply(refine_vcg LFOi_refine[where A=Id and R=Id])
          using M\<^sub>0_STATES upt_list_set_rel apply presburger
          apply simp
          using M\<^sub>0_STATES apply simp 
          apply simp
          apply force 
          apply simp
          apply(auto simp: get_scc_val_alt)[]
          apply blast
          apply blast
          apply(rule refine_IdI; simp add: set_to_list_alt)
          apply argo
        done
    qed
  
  
    lemma cull_graph_fine_impl_refine[refine]: 
      assumes MDSKZDEF: "MDSKZ=MDSKZ'"
      assumes CVDEF: "CV=CV'"
      shows "cull_graph_fine_impl CV MDSKZ \<le> \<Down> Id (cull_graph_fine CV' MDSKZ')"
    proof -
  
      show ?thesis 
        unfolding cull_graph_fine_impl_def cull_graph_fine_def unfiltered_list_open_block_def 
          mop_get_output_size_def op_length_filtered_def op_deleted_stateL_def op_get_mec_num_def
            mop_get_state_mec_id_alt op_bound_val_def track_sccs_pre_def 
              scc_map_defs.mark_as_unfinished_pre_def mark_as_MEC_pre_def
        apply(cases MDSKZ; cases CV)
        apply(simp only: MDSKZDEF CVDEF)
        apply(refine_vcg) 
          apply blast
          using M\<^sub>0_STATES apply fastforce
          apply simp using M\<^sub>0_STATES apply force 
          apply(rule refine_IdI) apply simp
          apply(rule LFOi_refine[where A=Id and R=Id])
    
            using M\<^sub>0_STATES upt_list_set_rel apply presburger
            apply(rule MLDSKZ_case_ref) (*TODO, there are multiple proglems here refining a program that uses implicit products to one that uses explicit products*)
              apply clarsimp
              apply(refine_vcg)
                using M\<^sub>0_STATES apply fastforce
                apply simp
                apply argo
                apply simp
                apply(simp add: MEC_filter_properties_def)
                apply(rule refine_IdI) apply simp
                apply(auto simp: Let_def M\<^sub>0_STATES scc_map_defs.transfer_to_disjdlt2_pre_def split!: option.splits) 
                apply(simp add: mop_untrack_sccs_pre_cull_alt)
        done
  
    qed
  


    lemma compute_MEC_fine_impl_refine: "compute_MEC_fine_impl M\<^sub>0 \<le> \<Down>Id compute_MEC_fine"
      unfolding compute_MEC_fine_impl_def compute_MEC_fine_def ASSERT_over_prod 
      apply(refine_vcg )
      apply assumption
      apply(force intro: refine_IdI simp: card_states_M\<^sub>0 unborrow_pre_def op_get_mecs_def)+
      done

    interpretation modest_init_mdp_env N ni 
      apply(unfold_locales)
      using n_impl apply simp
      using N_BOUND by simp 
  
    interpretation scc_map N N ni
      apply(unfold_locales)
      apply (simp add: n_impl)
      using N_BOUND apply simp
      done
  
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using op_list_length_unbounded .

  end

  (*TODO: Can I get rid of all this?*)
  context mdp_graph_mec_impl_env
  begin
  
    sepref_register N
    lemmas [sepref_import_param] = n_impl
  
    concrete_definition (in -) mop_modest_iterate_succs_eq_scc_ll' [llvm_code] is modest_init_mdp_env.mop_modest_iterate_succs_eq_scc_ll_def
    concrete_definition (in -) modest_init_mdp_ll' [llvm_code] is modest_init_mdp_env.modest_init_mdp_ll_def
    concrete_definition (in -) modest_states_empty_ll' [llvm_code] is modest_init_mdp_env.modest_states_nonempty_ll_def
    concrete_definition (in -) expand_capacity_MDP_ll' [llvm_code] is modest_init_mdp_env.expand_capacity_MDP_ll_def
    concrete_definition (in -) get_mec_num_MDP_ll' [llvm_code] is modest_init_mdp_env.get_mec_num_MDP_ll_def
    concrete_definition (in -) track_sccs_ll' [llvm_code] is modest_init_mdp_env.track_sccs_ll_def
    concrete_definition (in -) is_deleted_state_ll' [llvm_code] is modest_init_mdp_env.is_deleted_state_ll_def
    concrete_definition (in -) mark_as_MEC_ll' [llvm_code] is modest_init_mdp_env.mark_as_MEC_ll_def
    concrete_definition (in -) mark_as_unfinished_ll' [llvm_code] is modest_init_mdp_env.mark_as_unfinished_ll_def
    concrete_definition (in -) untrack_sccs_ll' [llvm_code] is modest_init_mdp_env.untrack_sccs_ll_def
    concrete_definition (in -) modest_get_mecs_ll' [llvm_code] is modest_init_mdp_env.modest_get_mecs_ll_def
  
    concrete_definition (in -) create_filter_set_impl_ll' [llvm_code] is filter_index_env.create_filter_set_impl_ll_def
    concrete_definition (in -) filter_elem_id_impl_ll' [llvm_code] is filter_index_env.filter_elem_id_impl_ll_def

    concrete_definition (in -) filtered_index_of_ll' [llvm_code] is scc_map.filtered_index_of_ll_def
    concrete_definition (in -) get_index_of_ll' [llvm_code] is scc_map.get_index_of_ll_def

    concrete_definition (in -) compute_sccs_cullable_impl_ll' [llvm_code] is modest_init_mdp_env.compute_sccs_cullable_impl_ll_def
    
    interpretation modest_init_mdp_env N ni 
      apply(unfold_locales)
      using n_impl apply simp
      using N_BOUND by simp 
  
  
    interpretation scc_map N N ni
      apply(unfold_locales)
      apply (simp add: n_impl)
      using N_BOUND by simp
  
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using op_list_length_unbounded .

    interpretation disj_set_list_tuple_defs N N ni ni .
  
  
  
    subsubsection \<open>Modest Data Structure Operations\<close>
    lemmas [unfolded mop_modest_iterate_succs_eq_scc_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.mop_modest_iterate_succs_eq_scc_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded modest_init_mdp_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.modest_init_mdp_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded modest_states_empty_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.modest_states_nonempty_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded is_deleted_state_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.is_deleted_state_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded expand_capacity_MDP_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.expand_capacity_MDP_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded get_mec_num_MDP_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.get_mec_num_MDP_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded track_sccs_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.track_sccs_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded is_deleted_state_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.is_deleted_stateL_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded mark_as_MEC_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.mark_as_MEC_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded mark_as_unfinished_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.mark_as_unfinished_hnr[OF modest_init_mdp_env_axioms]
    lemmas [unfolded untrack_sccs_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.untrack_sccs_hnr[OF modest_init_mdp_env_axioms]  
    lemmas [unfolded modest_get_mecs_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.modest_get_mecs_hnr[OF modest_init_mdp_env_axioms]
  
    subsubsection \<open>Filter Index Set Operations\<close>
    lemmas [unfolded create_filter_set_impl_ll'.refine[OF filter_index_env_axioms], sepref_fr_rules] = filter_index_env.create_filter_set_impl_hnr[OF filter_index_env_axioms]
    lemmas [unfolded filter_elem_id_impl_ll'.refine[OF filter_index_env_axioms], sepref_fr_rules] = filter_index_env.filter_elem_id_impl_hnr[OF filter_index_env_axioms]

    subsubsection \<open>SCC Map Operations\<close>
    lemmas [unfolded filtered_index_of_ll'.refine[OF scc_map_axioms], sepref_fr_rules] = scc_map.filtered_index_of_hnr[OF scc_map_axioms]
    lemmas [unfolded get_index_of_ll'.refine[OF scc_map_axioms], sepref_fr_rules] = scc_map.mop_get_index_hnr[OF scc_map_axioms]
    
    subsection \<open>SCC Operation\<close>
    lemmas [unfolded compute_sccs_cullable_impl_ll'.refine[OF modest_init_mdp_env_axioms], sepref_fr_rules] = modest_init_mdp_env.compute_sccs_cullable_impl_hnr[OF modest_init_mdp_env_axioms]
  
    sepref_definition identify_mecs_fine_impl_ll is "uncurry (PR_CONST identify_mecs_fine_impl)" :: "output_assn\<^sup>d *\<^sub>a modest_MDSKZ_assn\<^sup>k \<rightarrow>\<^sub>a filter_list_assn"
      unfolding identify_mecs_fine_impl_def nfoldli_upt_by_while PR_CONST_def
      apply (annot_snat_const "TYPE(size_T)")
      supply[simp] = push_bound_N_aux (*TODO Why is this necessary?*)
      apply sepref
      done
  
      
    sepref_definition cull_graph_fine_impl_ll is 
      "uncurry (PR_CONST cull_graph_fine_impl)" 
        :: "[\<lambda>_. True]\<^sub>c filter_list_assn\<^sup>k *\<^sub>a modest_MDSKZ_assn\<^sup>d \<rightarrow> modest_MDSKZ_assn
          [\<lambda>((_,_),x) x'. mdpi_peq x' x]\<^sub>c"
      unfolding cull_graph_fine_impl_def nfoldli_upt_by_while PR_CONST_def
      apply (annot_snat_const "TYPE(size_T)")
      supply[simp] = op_get_mec_num_def unfiltered_list_open_block_def mop_get_output_size_def 
        push_bound_N_aux expand_capacity_MDP_pre_def track_sccs_pre_def
      apply sepref
      done
          
  
    lemmas [sepref_bounds_dest] = modest_MDSKZ_assn_imp_closed
    
  
    schematic_goal[sepref_frame_free_rules]: "MK_FREE filter_list_assn ?A"
      unfolding filter_list_assn_def filter_list_assn_aux_def 
      unfolding output_assn_def output_assn_raw_def
      by(rule sepref_frame_free_rules | rule mk_free_pair)+
  
    concrete_definition (in -) identify_mecs_fine_impl_ll' [llvm_code] is mdp_graph_mec_impl_env.identify_mecs_fine_impl_ll_def
    lemmas [sepref_fr_rules] = identify_mecs_fine_impl_ll.refine[unfolded identify_mecs_fine_impl_ll'.refine[OF mdp_graph_mec_impl_env_axioms]]
  
    concrete_definition (in -) cull_graph_fine_impl_ll' [llvm_code] is mdp_graph_mec_impl_env.cull_graph_fine_impl_ll_def
    lemmas [sepref_fr_rules] = cull_graph_fine_impl_ll.refine[unfolded cull_graph_fine_impl_ll'.refine[OF mdp_graph_mec_impl_env_axioms]]
  
    interpretation modest_init_mdp_env N ni 
      apply(unfold_locales)
      using n_impl apply simp
      using N_BOUND by simp 
  
    interpretation disj_set_list_tuple_defs N N .

    lemma get_mec_pre_alt: "get_mec_pre = op_get_mecs_pre"
      unfolding get_mec_pre_def op_get_mecs_pre_def by fast
  
    sepref_definition compute_MEC_fine_impl_ll is "PR_CONST compute_MEC_fine_impl" 
      :: "Modest_MDP_struc_assn\<^sup>k \<rightarrow>\<^sub>a mec_map_assn"
      supply [simp] = get_mec_pre_alt
      unfolding compute_MEC_fine_impl_def PR_CONST_def                     
      apply sepref
      done
      
    concrete_definition (in -) compute_MEC_fine_impl_ll' [llvm_code] is mdp_graph_mec_impl_env.compute_MEC_fine_impl_ll_def
    lemmas compute_MEC_fine_impl_hnr [sepref_fr_rules] = compute_MEC_fine_impl_ll.refine[unfolded compute_MEC_fine_impl_ll'.refine[OF mdp_graph_mec_impl_env_axioms]]
  
    
    lemma compute_MEC_fine_impl_correct: "compute_MEC_fine_impl M\<^sub>0 \<le> mec_algo_defs.compute_MEC_spec M\<^sub>0"
    proof -
      interpret mec_algo M\<^sub>0
        by unfold_locales
    
      note compute_MEC_fine_impl_refine 
      also note compute_MEC_fine_refine 
      also note compute_MEC_refine
      finally show ?thesis .
    qed  
    

    
  end

  
  context modest_init_mdp_env
  begin

    (*TODO: Get rid of this precondition as they are inferred from the data structure*)
    lemma compute_MEC_fine_impl_ll'_hnr: "(compute_MEC_fine_impl_ll' ni, mec_algo_defs.compute_MEC_spec)
      \<in> [\<lambda>M. Finite_MDP M \<and> states M = {0..<N}]\<^sub>a (modest_init_mdp_env_defs.Modest_MDP_struc_assn N)\<^sup>k \<rightarrow> disj_set_list_tuple_defs.mec_map_assn N N"
    proof(rule hfrefI)
      fix M Mi
      assume P: "Finite_MDP M \<and> states M = {0..<N}"

      then interpret Finite_MDP M by presburger

      interpret mdp_graph_mec_impl_env N ni M
        apply(unfold_locales)
        using n_impl N_BOUND P by auto


      note R = compute_MEC_fine_impl_hnr[unfolded compute_MEC_fine_impl_ll'.refine, to_hnr, simplified, unfolded hn_ctxt_def]


      show "hn_refine (fst (Modest_MDP_struc_assn\<^sup>k) M Mi) (compute_MEC_fine_impl_ll' ni Mi)
            (snd (Modest_MDP_struc_assn\<^sup>k) M Mi) (disj_set_list_tuple_defs.mec_map_assn N N)
            (\<lambda>_. True) (mec_algo_defs.compute_MEC_spec M)"
        by(auto intro!: hn_refine_ref[OF compute_MEC_fine_impl_correct] R[of M Mi])
    qed


  end

  context mdp_graph_mec_impl_env
  begin

    lemmas compute_MEC_fine_impl_ll''_hnr = compute_MEC_fine_impl_hnr[unfolded compute_MEC_fine_impl_ll'.refine, to_hnr, simplified, THEN hn_refine_ref[OF compute_MEC_fine_impl_correct]]  

        
  end


(*TODO: remove DS from assertions in Hoare triple*)

  abbreviation "Modest_MDP_struc_assn' \<equiv> modest_init_mdp_env_defs.Modest_MDP_struc_assn"

  theorem compute_MEC_fine_impl_ll''_htriple[vcg_rules]: "llvm_htriple 
    (size_assn N ni ** Modest_MDP_struc_assn' N M\<^sub>0 mdpi 
      ** \<up>(Finite_MDP M\<^sub>0 \<and> 2 * N < max_snat 64 \<and> states M\<^sub>0={0..<N}))
    (compute_MEC_fine_impl_ll' ni mdpi)
    (\<lambda>(Di). EXS D.
        size_assn N ni ** Modest_MDP_struc_assn' N M\<^sub>0 mdpi
      ** \<up>(Finite_MDP M\<^sub>0 \<and> 2 * N < max_snat 64 \<and> states M\<^sub>0={0..<N})
      ** disj_set_list_tuple_defs.mec_map_assn N N D Di
      ** \<up>(set D = Finite_MDP_defs.mec_decomp M\<^sub>0))"
  apply (rule htriple_pure_preI)
  proof (goal_cases)
    case 1
    hence "(ni,N) \<in> size_rel" "Finite_MDP M\<^sub>0" "2*N < max_snat 64" "states M\<^sub>0={0..<N}"
      by (auto dest!: pure_part_split_conj)
    
    
    interpret Finite_MDP M\<^sub>0 by fact
        
    interpret mdp_graph_mec_impl_env N ni M\<^sub>0
      apply unfold_locales
      by fact+
      
    note [vcg_rules] = compute_MEC_fine_impl_ll''_hnr[THEN hn_refineD, unfolded hn_ctxt_def mec_algo_defs.compute_MEC_spec_def]   
      
    have [simp]: "nofail (mec_algo_defs.compute_MEC_spec M\<^sub>0)"
      unfolding mec_algo_defs.compute_MEC_spec_def by simp
    
    show ?thesis  
      by vcg
  qed
      
  
  context begin
  interpretation disj_set_list_tuple_defs N N ni ni for N ni .
  interpretation scc_map_defs N N ni for N ni .
  
  interpretation filter_index_env "output_assn N" get_output_size_impl_ll
    apply(unfold_locales)
    using op_list_length_unbounded .
  
  interpretation modest_init_mdp_env_defs N  . 
  
  interpretation llvm_prim_setup .
    
  (* TODO: Move *)
  lemmas [llvm_code] = MEC_Index_List.filtered_index_of_ll'_def MEC_Index_List.unfiltered_index_of_ll'_def
  
  
  lemmas [llvm_code] = get_output_size_impl_ll_def
  
  
  definition Modest_compute_MEC_fine_impl_ll :: "size_t \<Rightarrow> modest_input_struc_mdpi ptr \<Rightarrow> mec_mapi ptr \<Rightarrow> unit llM"
  where [llvm_code, llvm_inline]: "Modest_compute_MEC_fine_impl_ll ni Eip resp \<equiv> doM {
    Ei \<leftarrow> ll_load Eip;
    res \<leftarrow> compute_MEC_fine_impl_ll' ni Ei;
    ll_store res resp
  }"
  
  theorem Modest_compute_MEC_fine_impl_ll_htriple: "llvm_htriple 
    (   size_assn N ni 
      ** \<upharpoonleft>ll_pto mdpi p_mdpi 
      ** Modest_MDP_struc_assn' N M\<^sub>0 mdpi
      ** \<upharpoonleft>ll_pto anything resp 
      ** \<up>(Finite_MDP M\<^sub>0 \<and> 2 * N < max_snat 64 \<and> states M\<^sub>0={0..<N}))
    (Modest_compute_MEC_fine_impl_ll ni p_mdpi resp)
    (\<lambda>_. EXS D Di.
      \<upharpoonleft>ll_pto Di resp ** \<upharpoonleft>ll_pto mdpi p_mdpi 
      ** size_assn N ni ** Modest_MDP_struc_assn' N M\<^sub>0 mdpi
      ** \<up>(Finite_MDP M\<^sub>0 \<and> 2 * N < max_snat 64 \<and> states M\<^sub>0={0..<N})
      ** disj_set_list_tuple_defs.mec_map_assn N N D Di
      ** \<up>(set D = Finite_MDP_defs.mec_decomp M\<^sub>0))"
    unfolding Modest_compute_MEC_fine_impl_ll_def
    by vcg
  
  
  
  export_llvm Modest_compute_MEC_fine_impl_ll
    is "void compute_MEC(modest_size_t, modest_mdp_t *, mec_result_t *)"  
  defines \<open>
    typedef double modest_dec_t;
    typedef int64_t modest_size_t;
    typedef modest_size_t node_t;

    typedef struct {
      modest_size_t *states;
      struct {
        modest_size_t *transitions;
        struct {
          node_t *branches;
          struct {
            modest_size_t *avoid;
            modest_size_t *target;
          };
        };
      };
    } modest_mdp_t;
  
    typedef struct {
      modest_size_t num_mecs;
      modest_size_t *mec_map;
    } mec_result_t;
  
  \<close>
    file "modest_mec.ll"
  
  
  
  end


end
