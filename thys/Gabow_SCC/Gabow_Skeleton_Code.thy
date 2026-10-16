section \<open>Code Generation for the Skeleton Algorithm \label{sec:skel_code}\<close>
theory Gabow_Skeleton_Code
imports 
  Gabow_Skeleton "../ds/Stack" 
  
begin


  subsection \<open>General Lemmas\<close>
  
  lemma rtrancl_image_subsetI: "E \<subseteq> B \<times> A \<Longrightarrow> E\<^sup>* `` S \<subseteq> S \<union> A"
    apply auto
    by (metis Int_absorb1 Int_iff SigmaD2 rtrancl.simps)
  
  lemma hr_comp_b_rel_Id: "hr_comp A ({(E,E)}) E Ei = A E Ei"
    unfolding hr_comp_def
    apply (auto simp: sep_algebra_simps)
    done
  
  lemma hr_comp_diff_false1: "E' \<noteq> E \<Longrightarrow> hr_comp A ({(E',E')}) E Ei = sep_false"
    unfolding hr_comp_def
    apply (auto simp: sep_algebra_simps)
    done
  
  lemma hr_comp_diff_false2: "E \<noteq> E' \<Longrightarrow> hr_comp A ({(E',E')}) E Ei = sep_false"
    unfolding hr_comp_def
    apply (auto simp: sep_algebra_simps)
    done
  
  lemma pure_part_hr_compD: "pure_part (hr_comp A R x xi) \<Longrightarrow> x \<in> Range R" 
    by (meson Range_iff rdomp_hrcomp_conv rdomp_pure_part)
  
  lemma hfref_keep_exs: "(\<forall>n. (f, g) \<in> (A n)\<^sup>k \<rightarrow>\<^sub>a B) \<Longrightarrow> (f, g) \<in> (\<lambda> c ci. EXS n. A n c ci)\<^sup>k \<rightarrow>\<^sub>a B"
    unfolding hfref_def
    apply (auto simp add: hnr_pre_ex_conv) apply(rule hn_refine_cons_post) 
    apply blast
    using entails_def by blast
  
  lemma hfref_drop_exs: "(\<forall>n. (f, g) \<in> (A n)\<^sup>d \<rightarrow>\<^sub>a B) \<Longrightarrow> (f, g) \<in> (\<lambda> c ci. EXS n. A n c ci)\<^sup>d \<rightarrow>\<^sub>a B"
    unfolding hfref_def
    apply (auto simp add: hnr_pre_ex_conv) apply(rule hn_refine_cons_post) 
    apply blast
    unfolding invalid_assn_def pure_part_def entails_def pred_lift_def
    by blast
  
  lemma ex_hr_comp: "(\<exists> x. hr_comp (A x) R c ci s) = hr_comp (\<lambda> c ci. EXS x. A x c ci) R c ci s"
      unfolding hr_comp_def IS_LEFT_UNIQUE_def single_valued_def 
      by (auto simp: sep_algebra_simps ) 
  
  
  subsection \<open>Sepref definitions\<close>
  
  text \<open>
    We define a locale in which the graph operations are parameterized. This allows us to switch the
    data structure for easy interoperability between different tools.
    For example, we generated code for Modest, but using this approach we may be able to generate 
    code for e.g. Storm or another tool. One just needs to formalize that data structure and the 
    according operations in Isabelle/HOL.
  \<close>
  
  locale mdp_graph_impl_def_loc = mdp_graph_defs MG V\<^sub>i + scc_map_defs N D ni
    for MG V\<^sub>i and N :: nat and ni :: "size_t" and D :: nat +
    fixes MG_assn :: "(nat mdpG) \<Rightarrow> 'ei::llvm_rep \<Rightarrow> assn" \<comment> \<open>The assertion for the data structure.\<close>
    fixes succ_index_assn :: "nat succ_index \<Rightarrow> 'fi::llvm_rep \<Rightarrow> assn" \<comment> \<open>The assertion for an iterator over successors of a given state.\<close>
    fixes admissible_idi :: "'ei \<Rightarrow> node_t \<Rightarrow> 1 Word.word llM" \<comment> \<open>Checks whether a state is admissible (e.g. whether the outer loop should start looking for SCC's starting in this state, usually implemented by a function that always returns "True".\<close>
    fixes empty_idi :: "'ei \<Rightarrow> node_t \<Rightarrow> 1 Word.word llM" \<comment> \<open>Checks whether the input state has any successors, for MDPs usually implemented as "True".\<close>
    fixes init_idi :: "'ei \<Rightarrow> node_t \<Rightarrow> 'fi llM" \<comment> \<open>The initial iterator for successors of a specified state.\<close>
    fixes get_statei :: "'fi \<Rightarrow> node_t llM" \<comment> \<open>Obtains the state whose successors we iterate over.\<close>
    fixes succ_ati :: "'ei \<Rightarrow> 'fi \<Rightarrow> node_t llM" \<comment> \<open>Obtains the successor that the iterator point at.\<close>
    fixes has_next_idi :: "'ei \<Rightarrow> 'fi \<Rightarrow> 1 Word.word llM" \<comment> \<open>Checks whether the iterator has a next state to iterate over.\<close>
    fixes next_idi :: "'ei \<Rightarrow> 'fi \<Rightarrow> 'fi llM" \<comment> \<open>Progress the iterator to the next element.\<close>
  begin
  
    sublocale node: dflt_pure_option "-1" node_word_assn "ll_icmp_eq (-1)" 
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
    
    definition node_none :: "nat option" where "node_none = None"
    sepref_register node_none 
  
    lemmas [sepref_fr_rules] =  node.hn_None[folded node_none_def]
  end
  
  
  
  section \<open>Sepref Refinement to LLVM\<close>
  
  locale mdp_graph_impl_loc = mdp_graph_impl_def_loc MG V\<^sub>i N ni D MG_assn succ_index_assn admissible_idi empty_idi 
      init_idi get_statei succ_ati has_next_idi next_idi + mdp_graph MG V\<^sub>i + scc_map N D ni
    for MG::"nat mdpG" and V\<^sub>i:: "nat set" and N :: nat and D::nat
    and MG_assn :: "(nat mdpG) \<Rightarrow> 'ei::llvm_rep \<Rightarrow> assn"
    and succ_index_assn :: "nat succ_index \<Rightarrow> 'fi::llvm_rep \<Rightarrow> assn"
    and admissible_idi :: "'ei \<Rightarrow> node_t \<Rightarrow> 1 Word.word llM"
    and empty_idi :: "'ei \<Rightarrow> node_t \<Rightarrow> 1 Word.word llM"
    and init_idi :: "'ei \<Rightarrow> node_t \<Rightarrow> 'fi llM"
    and get_statei :: "'fi \<Rightarrow> node_t llM"
    and succ_ati :: "'ei \<Rightarrow> 'fi \<Rightarrow> node_t llM"
    and has_next_idi :: "'ei \<Rightarrow> 'fi \<Rightarrow> 1 Word.word llM"
    and next_idi :: "'ei \<Rightarrow> 'fi \<Rightarrow> 'fi llM"
    and ni
  +
    assumes pure_succ_assn: "is_pure succ_index_assn"
    assumes empty_idi_ref [sepref_fr_rules]: "(uncurry empty_idi , uncurry mop_is_empty)
      \<in> MG_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    assumes admissible_idi_ref [sepref_fr_rules]: "(uncurry admissible_idi, uncurry mop_is_admissible)
      \<in> MG_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    assumes init_idi_ref [sepref_fr_rules]: "(uncurry init_idi, uncurry mop_index_begin)
      \<in> [\<lambda> ((S,K), v). \<not> mdp_graph_defs.is_empty (S,K) v]\<^sub>a  MG_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow> succ_index_assn"
    assumes get_statei_ref [sepref_fr_rules]: "(get_statei, mop_get_state)
      \<in> succ_index_assn\<^sup>k \<rightarrow>\<^sub>a node_word_assn"
    assumes succ_ati_ref [sepref_fr_rules]: "(uncurry succ_ati, uncurry mop_graph_succ_at) 
      \<in> MG_assn\<^sup>k *\<^sub>a succ_index_assn\<^sup>k \<rightarrow>\<^sub>a node_word_assn"
    assumes has_next_idi_ref [sepref_fr_rules]: "(uncurry has_next_idi, uncurry mop_has_succ)
      \<in> MG_assn\<^sup>k *\<^sub>a succ_index_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    assumes next_idi [sepref_fr_rules]: "(uncurry next_idi, uncurry mop_next_id)
      \<in> [\<lambda>(MG, v). mdp_graph_defs.has_next v]\<^sub>a MG_assn\<^sup>k *\<^sub>a succ_index_assn\<^sup>d \<rightarrow> succ_index_assn"
    assumes E_BOUND: "E_\<alpha> \<subseteq> {0..<N} \<times> {0..<N}"
    assumes Vi_BOUND: "V\<^sub>i = {0..<N}"
  begin
  
    lemma mk_free_succ_assn[sepref_frame_free_rules]: "MK_FREE succ_index_assn (\<lambda>_. return\<^sub>M ())"
      apply(rule mk_free_is_pure) using pure_succ_assn .
  
    lemma reachable_bound: "E_\<alpha>\<^sup>*``V\<^sub>i = {0..<N}"
    proof safe
      fix u v
      assume "(u,v) \<in> E_\<alpha>\<^sup>*" "u \<in> V\<^sub>i"
      then show "v \<in> {0..<N}"
      apply (induction rule: rtrancl_induct)
      using Vi_BOUND E_BOUND by auto
    next
      fix v
      assume "v \<in> {0..<N}"
      then show "v \<in> E_\<alpha>\<^sup>*``V\<^sub>i"
      unfolding Vi_BOUND by blast
    qed
    
  
    lemma card_reachable_bound: "card (E_\<alpha>\<^sup>*``V0) \<le> N"
      using reachable_bound subset_eq_atLeast0_lessThan_card subset_it_edges 
      by presburger
  
    definition "GS_assn = stack_assn' TYPE(size_T) node_word_assn \<times>\<^sub>a stack_assn' TYPE(size_T) size_assn \<times>\<^sub>a node_state.am_assn N 
      \<times>\<^sub>a stack_assn' TYPE(size_T) (succ_index_assn)"
  
  
    sepref_definition open_GS_ll is "RETURN o open_GS" :: "GS_assn\<^sup>d \<rightarrow>\<^sub>a stack_assn' TYPE(size_T) node_word_assn \<times>\<^sub>a stack_assn' TYPE(size_T) size_assn \<times>\<^sub>a node_state.am_assn N 
      \<times>\<^sub>a stack_assn' TYPE(size_T) (succ_index_assn)"
      unfolding GS_assn_def open_GS_def
      by sepref
  
    concrete_definition (in -) open_GS_ll' [llvm_code] is mdp_graph_impl_loc.open_GS_ll_def
    lemmas [sepref_fr_rules] = open_GS_ll.refine[unfolded open_GS_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    sepref_definition close_GS_ll is "uncurry3 (RETURN oooo close_GS)" :: "(stack_assn' TYPE(size_T) node_word_assn)\<^sup>d *\<^sub>a (stack_assn' TYPE(size_T) size_assn)\<^sup>d *\<^sub>a (node_state.am_assn N)\<^sup>d 
      *\<^sub>a (stack_assn' TYPE(size_T) (succ_index_assn))\<^sup>d \<rightarrow>\<^sub>a GS_assn"
      unfolding GS_assn_def close_GS_def
      apply sepref
      done
  
    concrete_definition (in -) close_GS_ll' [llvm_code] is mdp_graph_impl_loc.close_GS_ll_def
    lemmas [sepref_fr_rules] = close_GS_ll.refine[unfolded close_GS_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    subsection \<open>Operation: is_done_oimpl:\<close>
  
    lemma is_done_oimpl_alt: "is_done_oimpl v I = is_SOME_DONE (I v)"
      unfolding is_done_oimpl_def is_SOME_DONE_def is_DONE_def 
      using node_state.exhaust_sel by (auto split: node_state.splits option.splits) 
  
    sepref_definition is_done_oimpl_ll is "uncurry (RETURN oo is_done_oimpl)" :: "node_word_assn\<^sup>k *\<^sub>a (node_state.am_assn N)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" 
      unfolding is_done_oimpl_alt
      by sepref
  
    concrete_definition (in -) is_done_oimpl_ll' [llvm_code] is mdp_graph_impl_loc.is_done_oimpl_ll_def
    lemmas [sepref_fr_rules] = is_done_oimpl_ll.refine[unfolded is_done_oimpl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    subsection \<open>Operation: initial_impl\<close>
  
    definition initial_impl' :: "(nat mdpG) \<Rightarrow> _" where
      "initial_impl' MG' v0 I = (
        do{ 
          g \<leftarrow> mop_is_empty MG' v0;
          if g then do{
            RETURN ([v0], [0::nat], I(v0 \<mapsto> STACK 0), [])
          } else do {
            ASSERT(\<not>mdp_graph_defs.is_empty MG' v0);
            uc \<leftarrow> mop_index_begin MG' v0;
            RETURN ([v0], [0::nat], I(v0 \<mapsto> STACK 0), [uc])
          }
        })"
    sepref_register initial_impl' :: "(nat mdpG) \<Rightarrow> nat \<Rightarrow> ((nat, node_state) i_map) \<Rightarrow> (nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> (nat succ_index) list) nres"
  
  
    lemma initial_impl_alt: "initial_impl = initial_impl' MG"
      unfolding initial_impl'_def GS_initial_impl_def initial_impl_def mop_is_empty_def mop_free_def
      by (clarsimp simp: index_begin_def fun_eq_iff pw_eq_iff refine_pw_simps)
  
      
  
    sepref_definition initial_ll is "uncurry2 (initial_impl')"::"MG_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k *\<^sub>a (node_state.am_assn N)\<^sup>d \<rightarrow>\<^sub>a GS_assn"
      unfolding initial_impl_alt initial_impl'_def GS_assn_def singleton_list_append
      unfolding stack_fold_custom_empty[where 'l = size_T] 
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
  
    
    concrete_definition (in -) initial_ll' [llvm_code] is mdp_graph_impl_loc.initial_ll_def
    lemmas [sepref_fr_rules] = initial_ll.refine[unfolded initial_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    subsection \<open>Operation: path_is_empty_impl\<close>
                                                               
    sepref_definition path_is_empty_impl_ll is "RETURN o path_is_empty_impl" :: "GS_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding path_is_empty_impl_def GS_assn_def GS_defs.S_def
      unfolding prod.case_distrib[where h="\<lambda>a. a=_"]
      by sepref
  
    concrete_definition (in -) path_is_empty_impl_ll' [llvm_code] is mdp_graph_impl_loc.path_is_empty_impl_ll_def
    lemmas [sepref_fr_rules] = path_is_empty_impl_ll.refine[unfolded path_is_empty_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
  
    definition "select_edge_impl' MG' SBIP \<equiv> 
      do {
        let (S,B,I,P) = open_GS SBIP;
        if P=[] then 
          RETURN (node_none, close_GS S B I P)
        else do {
          let (vc, P') = op_list_pop_last P;
          v \<leftarrow> mop_get_state vc;
          ASSERT (\<exists>j. I v = Some (STACK j));
          j \<leftarrow> mop_map_lookup v I;
          ASSERT (length B \<ge> 1);
          if val (the j) \<ge> B ! (length B - 1) then do {
            ASSERT (succ_index_inv MG' V\<^sub>i vc);
            w \<leftarrow> mop_graph_succ_at MG' vc;
            g \<leftarrow> mop_has_succ MG' vc;
            P \<leftarrow> (if g then do{
              ASSERT(mdp_graph_defs.has_next vc);
              uc \<leftarrow> mop_next_id MG' vc; 
              mop_list_append P' uc
            } else (RETURN P'));
            RETURN (Some w, close_GS S B I P)
          } else RETURN (node_none, close_GS S B I (op_list_append P' vc))
        }
      }"
  
    sepref_register select_edge_impl'
  
  
    lemma select_edge_impl_alt_def: "select_edge_impl SBIP = select_edge_impl' MG SBIP"
      unfolding select_edge_impl_def GS_defs.sel_rem_last_def select_edge_impl'_def open_GS_def close_GS_def GS_defs.seg_start_def GS_defs.S_idx_of_def mop_get_state_def mdp_graph_defs.get_state_def
      apply(cases SBIP; simp)
      apply(simp cong: if_cong)
      apply(auto simp: node_none_def neq_Nil_conv_rev split: prod.splits)
      done
  
  
    sepref_definition select_edge_impl_ll is "uncurry (PR_CONST select_edge_impl')" :: "MG_assn\<^sup>k *\<^sub>a GS_assn\<^sup>d \<rightarrow>\<^sub>a node.option_assn \<times>\<^sub>a GS_assn"
      unfolding select_edge_impl'_def PR_CONST_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
  
  
    concrete_definition (in -) select_edge_impl_ll' [llvm_code] is mdp_graph_impl_loc.select_edge_impl_ll_def
    lemmas [sepref_fr_rules] = select_edge_impl_ll.refine[unfolded select_edge_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    subsection \<open>Operation: is_on_stack_impl\<close>
  
    lemma is_on_stack_impl_alt: "is_on_stack_impl v s = is_SOME_STACK_v (GS_defs.I s v)"
      unfolding is_on_stack_impl_def GS_defs.is_on_stack_impl_def is_SOME_STACK_v_def is_STACK_v_def
      using node_state.exhaust_sel by (auto split: node_state.splits option.splits)
  
  
    sepref_definition is_on_stack_impl_ll is "uncurry (RETURN oo is_on_stack_impl)" :: "node_word_assn\<^sup>k *\<^sub>a GS_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding GS_assn_def is_on_stack_impl_alt GS_defs.I_def
      by sepref
  
    concrete_definition (in -) is_on_stack_impl_ll' [llvm_code] is mdp_graph_impl_loc.is_on_stack_impl_ll_def
    lemmas [sepref_fr_rules] = is_on_stack_impl_ll.refine[unfolded is_on_stack_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
  subsection \<open>Operation: collapse_impl\<close>
  
  
    sepref_definition find_seg_impl_ll is "uncurry GS_defs.find_seg_impl" :: "GS_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding GS_assn_def GS_defs.find_seg_impl_def GS_defs.B_def
      unfolding prod.case_distrib[where h="length"]
      unfolding prod.case_distrib[where h="\<lambda>a. a ! _"]
      apply (annot_snat_const "TYPE(size_T)")
      by sepref
  
    concrete_definition (in -) find_seg_impl_ll' [llvm_code] is mdp_graph_impl_loc.find_seg_impl_ll_def
    lemmas [sepref_fr_rules] = find_seg_impl_ll.refine[unfolded find_seg_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    definition "S_idx_of_impl SBIP v \<equiv> 
      do {
        ASSERT (\<exists> j. GS_defs.I SBIP v = Some (STACK j));
        RETURN (val (the (GS_defs.I SBIP v)))
      }"
    
    sepref_definition S_idx_of_ll is "uncurry S_idx_of_impl" :: "GS_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding GS_assn_def S_idx_of_impl_def GS_defs.I_def
      by sepref
  
    concrete_definition (in -) S_idx_of_ll' [llvm_code] is mdp_graph_impl_loc.S_idx_of_ll_def
    lemmas [sepref_fr_rules] = S_idx_of_ll.refine[unfolded S_idx_of_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    lemma idx_of_impl_alt_def: "GS_defs.idx_of_impl SBIP = (\<lambda> v. 
        do {
          j \<leftarrow> S_idx_of_impl SBIP v;
          ASSERT (j<length (GS_defs.S SBIP));
          i \<leftarrow> GS_defs.find_seg_impl SBIP j;
          RETURN i
        })"
      unfolding GS_defs.idx_of_impl_def GS_defs.S_idx_of_def
      unfolding S_idx_of_impl_def 
      apply(auto simp: fun_eq_iff)
      by metis
  
    sepref_definition idx_of_impl_ll is "uncurry GS_defs.idx_of_impl" :: "GS_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding idx_of_impl_alt_def 
      unfolding prod.case_distrib[where h="\<lambda>a. a _"]
      unfolding prod.case_distrib[where h="\<lambda>a. val (the a)"]
      unfolding prod.case_distrib[where h="\<lambda>a. a \<noteq> None"]
      by sepref
             
    concrete_definition (in -) idx_of_impl_ll' [llvm_code] is mdp_graph_impl_loc.idx_of_impl_ll_def
    lemmas [sepref_fr_rules] = idx_of_impl_ll.refine[unfolded idx_of_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
    
    
    definition "collapse_impl' v SBIP =    
      do {                 
        i\<leftarrow>GS_defs.idx_of_impl SBIP v;
        let (S,B,I,P) = open_GS SBIP;
        ASSERT (i+1 \<le> length B);
        let B = take (i+1) B;
        RETURN (close_GS S B I P)
      }"
  
    lemma collapse_impl_fr_alt_def: "collapse_impl_fr v SBIP = collapse_impl' v SBIP"
      unfolding collapse_impl_fr_def collapse_impl'_def GS_defs.collapse_impl_def GS_defs.S_def GS_defs.B_def GS_defs.I_def GS_defs.P_def open_GS_def close_GS_def
      apply(cases SBIP)
      apply (auto split: prod.splits simp: fun_eq_iff)
      done
  
  
    sepref_definition collapse_ll is "uncurry collapse_impl'" :: "node_word_assn\<^sup>k *\<^sub>a GS_assn\<^sup>d \<rightarrow>\<^sub>a GS_assn"
      unfolding collapse_impl'_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
  
    concrete_definition (in -) collapse_ll' [llvm_code] is mdp_graph_impl_loc.collapse_ll_def 
    lemmas [sepref_fr_rules] = collapse_ll.refine[unfolded collapse_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
  
    subsection \<open>Operation: is_done_impl\<close>
  
    lemma is_done_impl_alt: "is_done_impl v s = is_SOME_DONE (GS_defs.I s v)"
      unfolding is_done_impl_def GS_defs.is_done_impl_def is_SOME_DONE_def is_DONE_def
      using node_state.exhaust_sel by (auto split: node_state.splits option.splits)
  
    sepref_definition is_done_impl_ll is "uncurry (RETURN oo is_done_impl)" :: "node_word_assn\<^sup>k *\<^sub>a GS_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding GS_assn_def is_done_impl_alt GS_defs.I_def
      by sepref
  
    concrete_definition (in -) is_done_impl_ll' [llvm_code] is mdp_graph_impl_loc.is_done_impl_ll_def 
    lemmas [sepref_fr_rules] = is_done_impl_ll.refine[unfolded is_done_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
  subsection \<open>Operation: push_impl\<close>
  
    definition push_impl' :: "(nat mdpG) \<Rightarrow> _" where 
    "push_impl' MG' v s \<equiv> 
      case s of (S, B, I, P) \<Rightarrow> do {
        ASSERT(length S < card(E_\<alpha>\<^sup>*``V0));
        ASSERT(length B < card(E_\<alpha>\<^sup>*``V0));
        ASSERT(length P < card(E_\<alpha>\<^sup>*``V0));
        let j = length S;
        let S = op_list_append S v;
        let B = op_list_append B j;
        let I = I(v \<mapsto> STACK j);
        g \<leftarrow> mop_is_empty MG' v;
        P \<leftarrow> (if g then (RETURN P) else do{ ASSERT(\<not>mdp_graph_defs.is_empty MG' v); uc \<leftarrow> mop_index_begin MG' v; mop_list_append P uc});
        RETURN (S,B,I,P) 
      }"
  
    lemma push_impl_alt_def: "push_impl_fr = push_impl' MG"
      unfolding push_impl'_def push_impl_fr_def GS_defs.push_impl_def 
        Let_def mop_is_empty_def
      apply clarsimp
      by (force simp: fun_eq_iff pw_eq_iff refine_pw_simps index_begin_def)
        
    lemma push_bound_aux: "n < card (E_\<alpha>\<^sup>* `` V0) \<Longrightarrow> Suc n < max_snat LENGTH(size_T)"
      using D_N_BOUND card_reachable_bound by linarith
  
    lemma push_bound_aux2: "n < card (E_\<alpha>\<^sup>* `` V0) \<Longrightarrow> n < N"
      using D_N_BOUND card_reachable_bound by linarith
  
    sepref_definition push_impl_ll is "uncurry2 (PR_CONST push_impl')" :: "MG_assn\<^sup>k *\<^sub>a node_word_assn\<^sup>k *\<^sub>a GS_assn\<^sup>d \<rightarrow>\<^sub>a GS_assn"
      unfolding GS_assn_def push_impl'_def singleton_list_append PR_CONST_def
      unfolding stack_fold_custom_empty[where 'l = size_T] 
      supply [simp] = push_bound_aux[simplified] push_bound_aux2
      apply sepref
      done
  
    concrete_definition (in -) push_impl_ll' [llvm_code] is mdp_graph_impl_loc.push_impl_ll_def 
    lemmas [sepref_fr_rules] = push_impl_ll.refine[unfolded push_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    subsection \<open>Operation: pop_impl\<close>
  
    
    sepref_definition mark_as_done_ll is "uncurry4 mark_as_done" :: "(stack_assn' TYPE(size_T) node_word_assn)\<^sup>k *\<^sub>a (node_state.am_assn N)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a data_assn\<^sup>k \<rightarrow>\<^sub>a (node_state.am_assn N)"
      unfolding mark_as_done_def GS_defs.S_def GS_assn_def
      by sepref
  
    concrete_definition (in -) mark_as_done_ll' [llvm_code] is mdp_graph_impl_loc.mark_as_done_ll_def 
    lemmas [sepref_fr_rules] = mark_as_done_ll.refine[unfolded mark_as_done_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    definition "pop_impl' SBIP i  \<equiv> 
      do {  
        let (S,B,I,P) = open_GS SBIP;
        ASSERT (length B \<ge> 1);
        let lsi = length B - 1;
        ASSERT (lsi<length B);
        let l = B ! lsi;
        let u = length S;
        I \<leftarrow> mark_as_done S I l u i;
        ASSERT (B\<noteq>[]);
        S \<leftarrow> mop_list_take (last B) S;
        ASSERT (B\<noteq>[]);
        let (_,B) = op_list_pop_last B;
        RETURN (close_GS S B I P)
      }"
  
      lemma pop_impl_fr_alt: "pop_impl_fr SBIP i = pop_impl' SBIP i"
        unfolding pop_impl_fr_def GS_defs.pop_impl_def pop_impl'_def GS_defs.seg_start_def GS_defs.seg_end_def open_GS_def close_GS_def
        apply(cases SBIP; simp)
        apply(auto simp: pw_eq_iff refine_pw_simps Let_def)
        done
  
  
    sepref_definition pop_impl_ll is "uncurry pop_impl'" :: "GS_assn\<^sup>d *\<^sub>a data_assn\<^sup>k \<rightarrow>\<^sub>a GS_assn"
      unfolding pop_impl'_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
  
    concrete_definition (in -) pop_impl_ll' [llvm_code] is mdp_graph_impl_loc.pop_impl_ll_def 
    lemmas [sepref_fr_rules] = pop_impl_ll.refine[unfolded pop_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    sepref_register N
    sepref_register path_is_empty_impl is_on_stack_impl collapse_impl' 
            is_done_impl push_impl' pop_impl' select_edge_impl
  
   
    lemma list_to_set_rel: "distinct xs \<Longrightarrow> (xs, set xs) \<in> \<langle>Id\<rangle>list_set_rel"
      unfolding list_set_rel_def
      apply(auto simp: br_def)
      done
      
  
    lemma bounded_list_set_rel: "([0..<N], V\<^sub>i) \<in> \<langle>Id\<rangle>list_set_rel" 
      unfolding list_set_rel_def
      apply (auto simp: br_def Vi_BOUND)
      done
  
  
    subsection \<open>Refinement to nfoldli for representation as a while loop\<close>
  
    definition "skeleton_inner_while_body2 K' s = 
            do {
              \<comment> \<open>Select edge from end of path\<close>
              (vo,s) \<leftarrow> select_edge_impl' K' s;
  
              if (is_None vo) then
                  pop_impl' s 0
              else do {
                  let v = the(vo);
                  \<comment> \<open>No more outgoing edges from current node on path\<close>
                  ASSERT (v \<in> E_\<alpha>\<^sup>*``V0);
                  if is_on_stack_impl v s then do {
                    collapse_impl' v s
                  } else if \<not>is_done_impl v s then do {
                    \<comment> \<open>Edge to new node. Append to path\<close>
                    push_impl' K' v s
                  } else do {
                    \<comment> \<open>Edge to done node. Skip\<close>
                    RETURN s
                  }
               }
            }"
    sepref_register skeleton_inner_while_body2 :: "(nat mdpG)
       \<Rightarrow> nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> ('v \<times> 'v list) list
          \<Rightarrow> (nat list \<times> nat list \<times> (nat \<Rightarrow> node_state option) \<times> ('v \<times> 'v list) list) nres"
  
  
    lemma skeleton_inner_while_body_alt_def: "skeleton_inner_while_body SBIP = skeleton_inner_while_body2 MG SBIP"
      unfolding skeleton_inner_while_body_def skeleton_inner_while_body2_def select_edge_impl_alt_def collapse_impl_fr_alt_def push_impl_alt_def pop_impl_fr_alt
      apply (fo_rule arg_cong)
      apply (rule ext)
      apply (auto split: option.splits)
      done
  
    sepref_definition skeleton_inner_while_body_ll is "uncurry (PR_CONST skeleton_inner_while_body2)" :: "MG_assn\<^sup>k *\<^sub>a GS_assn\<^sup>d \<rightarrow>\<^sub>a GS_assn"
      unfolding PR_CONST_def
      unfolding skeleton_inner_while_body2_def 
      supply [simp] = option.split_sels(2)
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
  
  
  
    concrete_definition (in -) skeleton_inner_while_body_ll' [llvm_code] is mdp_graph_impl_loc.skeleton_inner_while_body_ll_def
    lemmas [sepref_fr_rules] = skeleton_inner_while_body_ll.refine[unfolded skeleton_inner_while_body_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  
    definition skeleton_impl_nfoldli :: "nat mdpG \<Rightarrow> nat oGS nres" where
      "skeleton_impl_nfoldli MG' \<equiv> do {
        let I=Map.empty;
        r \<leftarrow> nfoldli [0..<N] (\<lambda>_. True)(\<lambda>v0 I0 :: (nat \<Rightarrow> node_state option). do {
          v0 \<leftarrow> mop_bound_val (\<lambda> x. x < N) v0;
          ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V\<^sub>i);
          adm \<leftarrow> mop_is_admissible MG' v0;
          if (adm \<and> \<not>is_done_oimpl v0 I0) then do {
            ASSERT (v0 \<in> E_\<alpha>\<^sup>*``V0);
            s \<leftarrow> initial_impl' MG' v0 I0;
  
            s\<leftarrow> WHILEIT ((\<lambda>(p,D,pE). \<exists>vE. invar v0 (oGS_\<alpha> I0) (p,D,pE,vE)) o GS_defs.\<alpha>)
              (\<lambda>s. \<not>path_is_empty_impl s) 
              (skeleton_inner_while_body2 MG') s;
            let (S,B,I,P) = open_GS s;
            RETURN I
          } else
            RETURN I0
        }) I;
        RETURN r
      }"
  
    lemma skeleton_impl_nfoldli_refine: "skeleton_impl_nfoldli MG \<le> \<Down> Id skeleton_impl"
      unfolding skeleton_impl_nfoldli_def skeleton_impl_def open_GS_def mop_bound_val_def mop_is_admissible_def
      apply (simp only: Refine_Basic.nres_monad_laws)
      apply (refine_rcg LFOi_refine[where A=Id and R=Id])
      apply refine_dref_type
      apply (vc_solve (nopre) solve: asm_rl I_to_outer 
        simp: bounded_list_set_rel skeleton_inner_while_body_alt_def initial_impl_alt)
      using reachable_bound apply simp
      done
  
    
    lemma fold_am_custom_empty': "(let i = Map.empty in f i) = (let N'= (BCONST N N); i = op_am_custom_empty N' in f i)"
      by simp
  
    sepref_definition skeleton_impl_ll is "PR_CONST skeleton_impl_nfoldli" :: "MG_assn\<^sup>k \<rightarrow>\<^sub>a node_state.am_assn N"
      unfolding skeleton_impl_nfoldli_def PR_CONST_def
      unfolding fold_am_custom_empty' nfoldli_upt_by_while
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
  
    concrete_definition (in -) skeleton_impl_ll' [llvm_code] is mdp_graph_impl_loc.skeleton_impl_ll_def
    lemmas [sepref_fr_rules] = skeleton_impl_ll.refine[unfolded skeleton_impl_ll'.refine[OF mdp_graph_impl_loc_axioms]]
  
  end

end
