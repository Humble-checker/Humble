section \<open>Code Generation for SCC-Computation \label{sec:scc_code}\<close>
theory Gabow_SCC_Code
imports 
  "../Gabow_Skeleton_Code"
  "../Gabow_SCC"
  "Modest_MDP_SCC"  
  "../../ds/SCC_map" 
  "II_Modest_Base.Bind_Const"
begin

  section \<open>General lemmas\<close>
  
  (*NOTE: Ad hoc solution*)
  lemma hfref_hrcomp_singleton_keep_simp: 
    "(\<And> x. (f,\<lambda> _::'a. g (x::'a)) \<in> [P]\<^sub>a [C]\<^sub>c (hr_comp RS {(x,x)})\<^sup>k \<rightarrow>\<^sub>d T [CP]\<^sub>c) \<Longrightarrow> (f,g) \<in> [P]\<^sub>a [C]\<^sub>c RS\<^sup>k \<rightarrow>\<^sub>d T [CP]\<^sub>c"
    by (smt (verit, ccfv_SIG) fst_conv hf_pres.simps(1) hfref_def hr_comp_b_rel_Id mem_Collect_eq prod.sel(2) prod.simps(2))
  
  section \<open>Automatic Refinement to Efficient Data Structures\<close>
  
  text \<open>
    We extend the parametric definition of operations on the graph by reusing the same locale.
  \<close>
  
  locale mdp_graph_scc_impl_def_loc = mdp_graph_impl_def_loc MG V\<^sub>i N ni D MG_assn succ_index_assn admissible_idi empty_idi init_idi get_statei succ_ati valid_idi next_idi
    for MG and V\<^sub>i and N and D and MG_assn and succ_index_assn and admissible_idi and empty_idi and init_idi and get_statei and succ_ati and valid_idi and next_idi and ni
  
  
  locale mdp_graph_scc_impl_loc = mdp_graph_impl_loc MG V\<^sub>i N D MG_assn succ_index_assn admissible_idi empty_idi init_idi get_statei succ_ati valid_idi next_idi ni + 
    mdp_graph_scc_impl_def_loc MG V\<^sub>i N D MG_assn succ_index_assn admissible_idi empty_idi init_idi get_statei succ_ati valid_idi next_idi ni
    for MG and V\<^sub>i and N and D and MG_assn and succ_index_assn and admissible_idi and empty_idi and init_idi and get_statei and succ_ati and valid_idi and next_idi and ni +
    assumes D_VAL: "D = N"
  begin
  
  
    lemma D_bound: "D < max_snat (LENGTH(size_T))"
      using D_N_BOUND
      by (simp add: D_VAL max_snat_def)
  
    lemma inc_data_ll_aux: "x < D \<Longrightarrow> Suc x < max_snat 64" using D_bound by simp
  
    definition "build_scc_impl' = (\<lambda> s i.
      do {
        ASSERT (i < card (E_\<alpha>\<^sup>* `` V0));
        s\<leftarrow>pop_impl' s i;
        RETURN (op_bound_val (\<lambda>x. x<Suc D) (Suc i), s)
      })"
    sepref_register build_scc_impl'
  
  
    lemma build_scc_impl_fr_alt_def_aux: "a < card (E_\<alpha>\<^sup>* `` V0) \<Longrightarrow> a < D"
      by (auto simp: card_reachable_bound D_VAL push_bound_aux2) 
  
    lemma build_scc_impl_fr_alt_def: "build_scc_impl_fr s i = build_scc_impl' s i"
      unfolding build_scc_impl_fr_def GSS_defs.build_scc_impl_def build_scc_impl'_def
      apply(simp add: build_scc_impl_fr_alt_def_aux pop_impl_fr_def flip: pop_impl_fr_alt)
      done
                                                                     
    sepref_definition build_scc_impl_ll is "uncurry (PR_CONST build_scc_impl')" :: "GS_assn\<^sup>d *\<^sub>a data_assn\<^sup>d \<rightarrow>\<^sub>a data_assn \<times>\<^sub>a GS_assn"
      unfolding build_scc_impl_fr_alt_def build_scc_impl'_def PR_CONST_def
      supply [simp] = inc_data_ll_aux 
      supply [dest] = build_scc_impl_fr_alt_def_aux
      apply sepref
      done
  
    concrete_definition (in -) build_scc_impl_ll' [llvm_code] is mdp_graph_scc_impl_loc.build_scc_impl_ll_def
    lemmas [sepref_fr_rules] = build_scc_impl_ll.refine[unfolded build_scc_impl_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
  
    definition open_is :: "nat \<times> nat GS \<Rightarrow> nat \<times> nat GS" where "open_is is = (case is of (i,s) \<Rightarrow> (i,s))"
    sepref_register open_is :: "nat \<times> nat list \<times> nat list \<times> (nat\<Rightarrow> node_state option) \<times> (nat \<times> nat list) list
       \<Rightarrow> nat \<times> nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> (nat \<times> nat list) list"
  
    sepref_definition open_is_ll is "RETURN o open_is" :: "(data_assn \<times>\<^sub>a GS_assn)\<^sup>d \<rightarrow>\<^sub>a data_assn \<times>\<^sub>a GS_assn"
      unfolding open_is_def
      apply sepref
      done
  
    concrete_definition (in -) open_is_ll' [llvm_code] is mdp_graph_scc_impl_loc.open_is_ll_def
    lemmas [sepref_fr_rules] = open_is_ll.refine[unfolded open_is_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
  
    definition close_is :: "nat \<Rightarrow> nat GS \<Rightarrow> nat \<times> nat GS" where "close_is i s = (i,s)"
    sepref_register close_is :: "nat \<Rightarrow> (nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> (nat \<times> nat list) list)
       \<Rightarrow> nat \<times> nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> (nat \<times> nat list) list"
  
    sepref_definition close_is_ll is "uncurry (RETURN oo close_is)" :: "data_assn\<^sup>d *\<^sub>a GS_assn\<^sup>d \<rightarrow>\<^sub>a data_assn \<times>\<^sub>a GS_assn"
      unfolding close_is_def
      apply sepref
      done
  
    concrete_definition (in -) close_is_ll' [llvm_code] is mdp_graph_scc_impl_loc.close_is_ll_def
    lemmas [sepref_fr_rules] = close_is_ll.refine[unfolded close_is_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
  
    definition "compute_SCC_inner_while_body2 MG' = (\<lambda> (i,s). 
            do {
              \<comment> \<open>Select edge from end of path\<close>
  
              (vo,s) \<leftarrow> select_edge_impl' MG' s;
  
              if (is_None vo) then \<^cancel>\<open>TODO: Handle case distinction differently\<close>
                  build_scc_impl' s i
              else do {
                  let v = the(vo);
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  ASSERT (v \<in> E_\<alpha>\<^sup>*``V0);
                  if is_on_stack_impl v s then do {
                    s\<leftarrow> collapse_impl' v s;
                    RETURN (i, s)
                  } else if \<not>is_done_impl v s then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    s \<leftarrow> push_impl' MG' v s;
                    RETURN (i, s)
                  } else do {
                    \<comment> \<open>Edge to done node. Skip\<close>
                    RETURN (i, s)
                  }
               }
            })"
    sepref_register compute_SCC_inner_while_body2 :: "nat mdpG
       \<Rightarrow> nat \<times> nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> (nat \<times> nat list) list
          \<Rightarrow> (nat \<times> (nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> (nat \<times> nat list) list)) nres"
  
  
    lemma compute_SCC_inner_while_body_alt_def: "compute_SCC_inner_while_body is = compute_SCC_inner_while_body2 MG is"
      unfolding compute_SCC_inner_while_body_def compute_SCC_inner_while_body2_def close_is_def open_is_def push_S_impl_def select_edge_S_impl_def select_edge_impl_alt_def 
      apply (cases "is")
      apply (clarsimp)
      apply (fo_rule arg_cong)
      apply (rule ext)
      apply (auto simp: push_impl_alt_def collapse_impl_fr_alt_def build_scc_impl_fr_alt_def split: option.splits)
      done
  
  
    sepref_definition compute_SCC_inner_while_body_ll is "uncurry (PR_CONST compute_SCC_inner_while_body2)" :: "MG_assn\<^sup>k *\<^sub>a (data_assn \<times>\<^sub>a GS_assn)\<^sup>d \<rightarrow>\<^sub>a data_assn \<times>\<^sub>a GS_assn"
      unfolding compute_SCC_inner_while_body2_def PR_CONST_def
      supply [simp] = option.split_sels(2)
      apply sepref
      done
  
  
    concrete_definition (in -) compute_SCC_inner_while_body_ll' [llvm_code] is mdp_graph_scc_impl_loc.compute_SCC_inner_while_body_ll_def
    lemmas [sepref_fr_rules] = compute_SCC_inner_while_body_ll.refine[unfolded compute_SCC_inner_while_body_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
  
    definition open_iI :: "nat \<times> nat oGS \<Rightarrow> nat \<times> nat oGS" where "open_iI iI = (case iI of (i,I) \<Rightarrow> (i,I))"
    sepref_register open_iI :: "nat \<times> (nat \<Rightarrow> node_state option) \<Rightarrow> nat \<times> ((nat, node_state) i_map)"
  
    sepref_definition open_iI_ll is "RETURN o open_iI" :: "output_assn_raw\<^sup>d \<rightarrow>\<^sub>a data_assn \<times>\<^sub>a (node_state.am_assn N)"
      unfolding open_iI_def output_assn_raw_def
      apply sepref
      done
  
    concrete_definition (in -) open_iI_ll' [llvm_code] is mdp_graph_scc_impl_loc.open_iI_ll_def
    lemmas [sepref_fr_rules] = open_iI_ll.refine[unfolded open_iI_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
  
  
    definition close_iI :: "nat \<Rightarrow> nat oGS \<Rightarrow> nat \<times> nat oGS" where "close_iI i I = (i,I)"
    sepref_register close_iI :: "nat \<Rightarrow> ((nat, node_state) i_map) \<Rightarrow> nat \<times> (nat \<Rightarrow> node_state option)"
  
    sepref_definition close_iI_ll is "uncurry (RETURN oo close_iI)" :: "data_assn\<^sup>d *\<^sub>a (node_state.am_assn N)\<^sup>d \<rightarrow>\<^sub>a output_assn_raw"
      unfolding close_iI_def output_assn_raw_def
      apply sepref
      done
  
    concrete_definition (in -) close_iI_ll' [llvm_code] is mdp_graph_scc_impl_loc.close_iI_ll_def
    lemmas [sepref_fr_rules] = close_iI_ll.refine[unfolded close_iI_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
  
    
  
    definition "compute_SCC_impl_nfoldli MG' \<equiv> do {
        let i = Map.empty;
        let so = close_iI 0 i;
        so \<leftarrow> nfoldli [0..<N] (\<lambda>_. True)(\<lambda>v0 (iI0 :: (nat \<times> (nat \<Rightarrow> node_state option))). do {
          v0 \<leftarrow> mop_bound_val (\<lambda> x. x < N) v0;
          ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V\<^sub>i);
          let (i0, I0) = open_iI iI0;
          adm \<leftarrow> mop_is_admissible MG' v0;
          if (adm \<and> \<not>is_done_oimpl v0 I0) then do {
            ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V0);
            s \<leftarrow> initial_impl' MG' v0 I0;
  
            (i,s)\<leftarrow> WHILEIT (\<lambda> (i,s). (\<lambda> (SCC,p,D,pE). \<exists>vE. cscc_invar v0 (oGS_\<alpha> I0) (SCC,p,D,pE,vE)) (GSS_defs.s_\<alpha> s i))
              (\<lambda> (_, s). \<not>path_is_empty_impl s) 
              (compute_SCC_inner_while_body2 MG')
              (i0,s);
            let (S,B,I,P) = open_GS s;
            RETURN (close_iI i I)
          } else
            RETURN (close_iI i0 I0)
          }) so;
        RETURN so
      }"
    sepref_register skeleton_impl_nfoldli :: "nat mdpG \<Rightarrow> ((nat, node_state) i_map) nres"
  
  
  
    lemma bounded_list_set_b_rel: "([0..<N], V\<^sub>i) \<in> \<langle>node_rel' N\<rangle>list_set_rel"
    proof -
      have "([0..<N], set [0..<N]) \<in> \<langle>node_rel' N\<rangle>list_set_rel"
        apply(rule list_to_set_b_rel'_setI)
        by (auto simp: list_all_length)
      thus ?thesis 
        by (simp add: Vi_BOUND)
    qed 
  
  
    lemma skeleton_impl_nfoldli_refine: "compute_SCC_impl_nfoldli MG \<le> \<Down> Id compute_SCC_impl"
      unfolding compute_SCC_impl_nfoldli_def compute_SCC_impl_def open_GS_def open_iI_def close_iI_def initial_S_impl_def mop_is_admissible_def
      apply (simp only: Refine_Basic.nres_monad_laws) 
      apply (simp del: conc_Id)
      apply (refine_rcg LFOi_refine[where A="node_rel' N"])
      apply refine_dref_type
      apply (vc_solve (nopre) solve: asm_rl I_to_outer 
        simp: bounded_list_set_rel compute_SCC_inner_while_body_alt_def initial_impl_alt bounded_list_set_b_rel)
      apply(auto simp add: reachable_bound) 
      done
  
    
    lemma fold_nat_am_custom_empty': "(let i = close_iI 0 Map.empty in f i) = (let N'= (BCONST N N); i = close_iI 0 (op_am_custom_empty N') in f i)"
      by simp
  
  
    sepref_definition compute_SCC_impl_ll is "PR_CONST compute_SCC_impl_nfoldli" :: "MG_assn\<^sup>k \<rightarrow>\<^sub>a output_assn_raw"
      unfolding compute_SCC_impl_nfoldli_def PR_CONST_def
      unfolding fold_am_custom_empty' nfoldli_upt_by_while
      apply (annot_snat_const "TYPE(size_T)")
      supply [simp] = reachable_bound
      apply sepref
      done
  
  
    concrete_definition (in -) compute_SCC_impl_ll' [llvm_code] is mdp_graph_scc_impl_loc.compute_SCC_impl_ll_def
    lemmas compute_SCC_impl_hnr [sepref_fr_rules] = compute_SCC_impl_ll.refine[unfolded compute_SCC_impl_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
  end
  
  
  
  context modest_init_mdp_env
  begin
  
    interpretation mdp_graph_scc_impl: mdp_graph_scc_impl_def_loc
      where N=N and D=N
      and MG_assn = "modest_mdp_succ_DS_assn DS" 
      and succ_index_assn = "modest_index_DS_assn DS"
      and admissible_idi = "mop_modest_is_admissible_ll'"
      and empty_idi = "modest_is_empty_ll'"
      and init_idi = modest_index_begin_ll'
      and get_statei = modest_get_state_ll'
      and succ_ati = modest_succ_at_ll
      and valid_idi = modest_has_successor_ll
      and next_idi = modest_next_index_ll'
      and ni=ni 
      for DS .
  
    
    concrete_definition(in -) Modest_compute_SCC_impl[llvm_code] is 
      compute_SCC_impl_ll'_def[of mop_modest_is_admissible_ll' modest_is_empty_ll' modest_index_begin_ll' modest_get_state_ll' modest_succ_at_ll' modest_has_successor_ll' modest_next_index_ll']
    
  end

  
  context
  begin
  
    interpretation disj_set_list_tuple_defs N N ni ni for N ni .
    interpretation scc_map_defs N N ni for N ni .
    interpretation modest_init_mdp_env_defs N . 
    
    type_synonym scc_resulti = "size_t \<times> size_t ptr"
    
    definition Modest_cullable_compute_SCC_impl' :: "size_t \<Rightarrow> modest_mdpi ptr \<Rightarrow> scc_resulti ptr \<Rightarrow> unit llM"
    where [llvm_code, llvm_inline]: "Modest_cullable_compute_SCC_impl' ni Eip resp \<equiv> doM {
      Ei \<leftarrow> ll_load Eip;
      res \<leftarrow> Modest_compute_SCC_impl ni Ei;
      ll_store res resp
    }"
  
    export_llvm Modest_cullable_compute_SCC_impl'  
      is "void compute_SCC(modest_size_t, modest_input_mdp_t *, scc_result_t *)"  
    defines \<open>
      typedef uint64_t modest_size_t;
      typedef modest_size_t node_t;
      typedef uint64_t shared_nat_t;
      typedef uint64_t *bitset_t;
    
      typedef struct {
        shared_nat_t *states;
        struct {
          shared_nat_t *transitions;
          struct {
            node_t *branches;
            struct {
              bitset_t avoid;
              bitset_t target;
            };
          };
        };
      } modest_input_mdp_t;
    
      typedef struct {
        modest_size_t num_sccs;
        node_t *scc_map;
      } scc_result_t;
    
    \<close>
      file "modest_scc_gabow_cullable.ll"
  
  end
  
  
  lemma hfref_case_prod: "[case_prod (\<lambda>(x,y). f (x,y))]\<^sub>a A \<rightarrow> B = [\<lambda> (a,b). f a b]\<^sub>a A \<rightarrow> B"
    by auto
  
  locale Modest_graph_impl_loc = modest_init_mdp_env N ni + mdp_graph_scc_impl_def_loc MG "{0..<N}" N N "modest_mdp_succ_DS_assn DS" 
    "modest_index_DS_assn DS" 
      mop_modest_is_admissible_ll' modest_is_empty_ll' modest_index_begin_ll' modest_get_state_ll' 
      modest_succ_at_ll modest_has_successor_ll modest_next_index_ll' ni
    for MG and N :: nat and DS and ni +
    assumes E_BOUND: "E_\<alpha> \<subseteq> {0..<N} \<times> {0..<N}"
    assumes V0_sub_it: "V0 \<subseteq> {0..<N}"
  begin
  
  
    sublocale mdp_graph_scc_impl_loc MG "{0..<N}" N "N" "modest_mdp_succ_DS_assn DS" 
    "modest_index_DS_assn DS" 
      mop_modest_is_admissible_ll' modest_is_empty_ll' modest_index_begin_ll' modest_get_state_ll' 
      modest_succ_at_ll' modest_has_successor_ll' modest_next_index_ll' ni
      apply unfold_locales
      subgoal
        apply(rule rtrancl_image_subsetI[OF E_BOUND, THEN finite_subset] ) 
        by blast
      subgoal using V0_sub_it .
      subgoal by (rule n_impl)
      subgoal using N_BOUND by simp
      subgoal by solve_constraint
      subgoal using mop_is_empty_hnr .
      subgoal using mop_is_admissible_hnr .
      subgoal using mop_index_begin_hnr .
      subgoal using mop_get_state_hnr .
      subgoal using mop_graph_succ_at_hnr .
      subgoal using mop_has_succ_hnr .
      subgoal using mop_next_id_hnr by(auto simp: hfref_case_prod)
      subgoal by (rule E_BOUND)
      subgoal by simp
      subgoal by simp
      done
  
  
    lemma SCC_rel'_to_SCC_rel: "hr_comp output_assn_raw SCC_rel' x y \<turnstile> output_assn x y"
      unfolding output_assn_def
      apply(rule hr_comp_entails)
      apply blast
      unfolding scc_map_defs.SCC_rel_def
      using card_reachable_bound
      by (fastforce simp: in_br_conv split: option.splits node_state.splits)
      
                                                                                         
    lemma Modest_graph_skeleton_impl_refines_spec: "(Modest_compute_SCC_impl ni, \<lambda>_. compute_SCC_spec) 
      \<in> (hr_comp (modest_mdp_succ_DS_assn DS) {(MG,MG)})\<^sup>k \<rightarrow>\<^sub>a output_assn"
    proof -
    
      note r1 = Modest_compute_SCC_impl.refine[of ni, folded compute_SCC_impl_ll'.refine[OF mdp_graph_scc_impl_loc_axioms]]
  
      note r2 = compute_SCC_impl_ll.refine[unfolded PR_CONST_def]  
      
      note skeleton_impl_nfoldli_refine
      also note compute_SCC_impl_refine
      also note compute_SCC_correct
      finally have "(compute_SCC_impl_nfoldli MG, compute_SCC_spec) \<in> \<langle>SCC_rel'\<rangle> nres_rel"
        by (auto simp: nres_rel_def)
      hence r3: "(compute_SCC_impl_nfoldli, (\<lambda> _. compute_SCC_spec)) \<in> {(MG,MG)} \<rightarrow> \<langle>SCC_rel'\<rangle> nres_rel"
        by auto
      
      from r2[FCOMP r3, unfolded r1, folded output_assn_def] show ?thesis
        apply(rule hfref_cons)
        by(auto simp: SCC_rel'_to_SCC_rel)
    qed
  
    lemma Modest_graph_skeleton_impl_refines_spec':
      shows "(Modest_compute_SCC_impl ni, \<lambda>_. mdp_graph_defs.compute_SCC_spec MG) 
        \<in> (hr_comp modest_mdp_succ_assn {(MG,MG)})\<^sup>k \<rightarrow>\<^sub>a scc_map_defs.output_assn N N"
    proof -
    
      have "\<forall> DS. (Modest_compute_SCC_impl ni, \<lambda>_. mdp_graph_defs.compute_SCC_spec MG)
      \<in> (hr_comp (modest_mdp_succ_DS_assn DS) {(MG,MG)})\<^sup>k \<rightarrow>\<^sub>a scc_map_defs.output_assn N N"
        using Modest_graph_impl_loc.Modest_graph_skeleton_impl_refines_spec[OF Modest_graph_impl_loc_axioms]
        by blast
    
      thus ?thesis
        apply -
        apply(drule hfref_keep_exs)
        unfolding modest_mdp_succ_assn_alt ex_hr_comp 
        by blast
     
    qed
  
  end
  
  
  definition "Modest_Gabow_SCC_pre N MG' \<equiv> mdp_graph_defs.E_\<alpha> MG' \<subseteq> {0..<N} \<times> {0..<N} \<and> mdp_graph_defs.V0 MG' \<subseteq> {0..<N}"
  
  context modest_init_mdp_env
  begin
  
    lemma hr_comp_rel_Range: "hr_comp A R x xi h \<Longrightarrow> x \<in> Range R"
      by (meson pure_partI pure_part_hr_compD)
    
    interpretation scc_map N N ni
      apply(unfold_locales)
      using n_impl apply simp
      using N_BOUND by auto
    
    
    section \<open>Refinement of the SCC algorithm\<close>
    
    text \<open>
      The following lemma allows us to implement an abstract SCC decomposition by Gabow's algorithm.
    \<close>
    
    lemma compute_SCC_DS_spec_hnr: "(Modest_compute_SCC_impl ni, mdp_graph_defs.compute_SCC_spec) \<in> [Modest_Gabow_SCC_pre N]\<^sub>a 
      (modest_mdp_succ_DS_assn DS)\<^sup>k \<rightarrow> output_assn"
    proof -
    
      {
        fix MG'
        assume "Modest_Gabow_SCC_pre N MG'"
        hence "Modest_graph_impl_loc MG' N ni"
          apply(unfold_locales)
          by (auto simp: Modest_Gabow_SCC_pre_def)
      } note AUX = this
    
      note REF = Modest_graph_impl_loc.Modest_graph_skeleton_impl_refines_spec[OF AUX]
    
      show ?thesis
        apply(rule hfref_hrcomp_singleton_keep_simp) 
        apply(rule hfrefI)
        apply(rule hn_refine_preI)
        apply (simp add: hr_comp_b_rel_Id)
        apply(drule hr_comp_rel_Range)
        apply simp
        apply(drule REF)
        apply(drule hfrefD)
        by auto
    qed
    
    
    lemma compute_SCC_spec_hnr: "(Modest_compute_SCC_impl ni, mdp_graph_defs.compute_SCC_spec) \<in> [Modest_Gabow_SCC_pre N]\<^sub>a 
      modest_mdp_succ_assn\<^sup>k \<rightarrow> output_assn"
    proof -
    
      {
        fix MG'
        assume "Modest_Gabow_SCC_pre N MG'"
        hence "Modest_graph_impl_loc MG' N ni"
          apply(unfold_locales)
          by (auto simp: Modest_Gabow_SCC_pre_def)
      } note AUX = this
    
      show ?thesis
        apply(rule hfref_hrcomp_singleton_keep_simp) 
        apply(rule hfrefI)
        apply(rule hn_refine_preI)
        apply (simp add: hr_comp_b_rel_Id)
        apply(drule hr_comp_rel_Range)
        apply(drule AUX)
        apply simp
        apply(drule Modest_graph_impl_loc.Modest_graph_skeleton_impl_refines_spec'[of _ N ni])
        apply(drule hfrefD)
        by auto
    qed

    lemma pure_part_modest_mdp_succ_assn_E: "pure_part (modest_mdp_succ_assn MG Ei) \<Longrightarrow> 
      (\<exists>DS. pure_part (modest_mdp_succ_DS_assn DS MG Ei) \<Longrightarrow> P) \<Longrightarrow> P"
      unfolding modest_mdp_succ_assn_alt pure_part_def by blast


    lemma modest_mdp_succ_DS_assn_MGD: "pure_part (modest_mdp_succ_DS_assn DS MG Ei) \<Longrightarrow> MG = modest_mdp_def.SK_\<alpha> N DS"
      unfolding modest_mdp_succ_DS_assn_def
      apply(drule pure_part_hr_compD)
      apply(clarsimp simp: Range_iff )
      apply(frule modest_mdp_succ_rel_DS_eq)
      by(auto simp: modest_mdp_succ_DS_rel_def  in_br_conv)


    lemma modest_mdp_succ_DS_assn_closedD: "pure_part (modest_mdp_succ_DS_assn DS MG Ei) \<Longrightarrow> mdp_graph_defs.E_\<alpha> MG \<subseteq> {0..<N} \<times> {0..<N}"
      apply(frule modest_mdp_succ_DS_assn_MGD)
      unfolding modest_mdp_succ_DS_assn_def
      by (auto dest!: modest_mdp_invar'.E_\<alpha>_len_St pure_part_hr_compD 
        simp: Range_iff modest_mdp_succ_DS_rel_def br_def modest_mdp_invar_def modest_mdp_def.SK_\<alpha>_def )

    lemma modest_mdp_succ_DS_assn_VD: "pure_part (modest_mdp_succ_DS_assn DS MG Ei) \<Longrightarrow> mdp_graph_defs.V0 MG \<subseteq> {0..<N}"
      by(auto simp: mdp_graph_defs.V0_def modest_mdp_def.SK_\<alpha>_def modest_mdp_def.S_\<alpha>_def dest!: modest_mdp_succ_DS_assn_MGD)
  end



  theorem Modest_graph_SCC_impl_correct_htriple: "llvm_htriple 
    ( snat_assn N ni ** \<up>(2 * N < max_snat LENGTH(64)) **
      modest_init_mdp_env_defs.modest_mdp_succ_assn N MG Mi)

    (Modest_compute_SCC_impl ni Mi) 
    (\<lambda>ri. EXS r. 
      snat_assn N ni ** \<up>(2 * N < max_snat LENGTH(64)) 
      ** modest_init_mdp_env_defs.modest_mdp_succ_assn N MG Mi
      ** scc_map_defs.output_assn N N r ri 
      ** \<up>(set r = mdp_graph_defs.scc_set MG)
      ** \<up>(mdp_graph_defs.ordered MG r))"
    apply(rule htriple_pure_preI)
    proof (goal_cases)
      case 1
  
      then interpret modest_init_mdp_env 
        apply unfold_locales 
        by (auto dest!: pure_part_split_conj)
  
      from 1 obtain St Tr Br Av Ta where "pure_part (modest_mdp_succ_DS_assn (St,Tr,Br,Av,Ta) MG Mi)"
        by(auto dest!: pure_part_split_conj elim: pure_part_modest_mdp_succ_assn_E)
  
      hence INV: "Modest_graph_impl_loc MG N ni"
        unfolding modest_mdp_def.SK_\<alpha>_def
        apply unfold_locales 
        apply (fact|clarsimp simp: modest_mdp_succ_DS_assn_closedD)+ 
        using modest_mdp_succ_DS_assn_VD by fastforce
  
      note [simp] = hr_comp_b_rel_Id
      note [simp] = mdp_graph_defs.compute_SCC_spec_def
      note [vcg_rules] = Modest_graph_impl_loc.Modest_graph_skeleton_impl_refines_spec[OF INV, to_hnr, THEN hn_refineD, unfolded hn_ctxt_def, of MG _ Mi, simplified]
  
      show ?case 
        unfolding modest_mdp_succ_assn_alt
        by vcg
    qed

end

