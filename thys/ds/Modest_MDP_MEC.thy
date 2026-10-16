theory Modest_MDP_MEC
  imports "../Gabow_SCC/Gabow_SCC_Code" "../ds/BitSet" "../ds/MEC_map" "../ds/MEC_Index_List" "II_Modest_Base.More_B_Assn" "../mec/MDP_MEC" "../ds/SharedNat"
begin
             
  section \<open>General Lemmas\<close>

  lemma map_ls_intv[simp]: "i < cnt sn \<Longrightarrow> map f (ls_intv sn) ! i = f (i + lid sn)"
    by simp


  text \<open>
    This theory implements the operations for the Modest data structure for the MDP structure.

    The Modest data structure contains three lists respresenting States, Transitions and 
    Branches. The list of states is a tuple which respectively contains the number of transitions 
      and the starting index in the list of transitions.
    The list of transitions similarly is a tuple which contains respectively the number of branches 
      that the transition has as well as the starting index in the branch list.
    The list of branches contains a tuple (single value in this representation) with the index of 
      the successor state in the state list.\<close>

  section \<open>Modest Cullable Data Structure SCC operations\<close>

  text \<open>
    The second notion adds a map to the input data structure which determines which states and 
    transitions are removed. \<open>Mm\<close> is a tuple of lists of sets. Transitions between the same
    sets are preserved while the others are removed. By putting each set into their own set we
    automatically remove the desired transitions. The tuple construction allows us to model removed
    states. The first element of the tuple contains the MECs and the second one the unfinished SCCs
    grouped per SCC. When the algorithm is done, this list therefore also contains the MEC 
    decomposition. As an optimization we included the number of remaining states \<open>Nr\<close> which is the
    a counter that keeps track of the number of states for which we have not found a MEC. We only
    use this for the termination criterion.
  \<close>    

                    
  lemma(in modest_mdp_input_invar) K_actions_M\<^sub>0_\<alpha>: "u < N \<Longrightarrow> K_actions M\<^sub>0_\<alpha> u = succs u"
    unfolding M\<^sub>0_\<alpha>_def K_actions_def 
    by (clarsimp simp: succs_alt; transfer; simp)

  lemma(in modest_mdp_input_invar) ne_K_actions_M\<^sub>0_\<alpha>: "K_actions M\<^sub>0_\<alpha> u \<noteq> {} \<Longrightarrow> u < N"
    unfolding K_actions_def using ne_actions_M\<^sub>0_\<alpha> by blast

  lemma(in modest_mdp_input_invar) ne_K_actions_M\<^sub>0_\<alpha>': "d \<in> K_actions M\<^sub>0_\<alpha> u \<Longrightarrow> u < N"
    unfolding K_actions_def using ne_actions_M\<^sub>0_\<alpha>' by blast

  subsection \<open>Basic definition\<close>


  context modest_mdp_cullable_def
  begin 

    text\<open>
      To deal with the cullable data structure, we need to be able to reason about the activated
      transition. This part focuses purely on building an infrastructure to make it easier to
      reason about that.
    \<close>

    subsection \<open>Abstraction functions\<close>

    definition "K_\<alpha> =  (\<lambda> u. if u < N then (if u \<in> Cm then {(!) Br ` sn_intv (TrI ! t) | t.  t\<in>act_trans u} else {{u}}) else {})"

    definition "D_\<alpha> = fst Mm"

    definition "L_\<alpha> = snd Mm"

    definition "Z_\<alpha> = Av \<union> Ta"

    definition "MDSKZ_\<alpha> = (M\<^sub>0_\<alpha>,D_\<alpha>,S_\<alpha>,K_\<alpha>,Z_\<alpha>)"

    definition "MLDSKZ_\<alpha> = (M\<^sub>0_\<alpha>,L_\<alpha>,D_\<alpha>,S_\<alpha>,K_\<alpha>,Z_\<alpha>)"

    definition "SCm \<equiv> {v. v < N \<and> v \<notin> Av \<and> v \<notin> Ta \<and> (\<forall> i < length (fst Mm). v \<notin> (fst Mm) ! i)}"

    lemma SCm_alt: "SCm = Cm \<inter> S_\<alpha>"
      unfolding SCm_def Cm_def S_\<alpha>_def by fastforce

    lemma same_scc_transition:
      assumes US: "u \<in> SCm"
      assumes AKU: "a \<in> K_\<alpha> u"
      assumes EQSCC: "\<forall>t'\<in>(act_trans u). (\<forall>b\<in>sn_intv (TrI ! t'). \<forall>i<length C. (Br ! b \<in> C ! i) = (u \<in> C ! i))"
      assumes COV: "\<forall> u \<in> S_\<alpha>. (\<exists> i < length C. u \<in> C ! i)"
      shows "\<exists> i < length C. u \<in> C ! i \<and> a \<subseteq> C ! i"
    proof -

      from COV US obtain i where IC: "i < length C" and UCI: "u \<in> C ! i" 
        unfolding SCm_alt by blast

      with EQSCC AKU US show ?thesis
        unfolding K_\<alpha>_def SCm_alt US S_\<alpha>_def
        apply clarsimp
        apply(rule exI[where ?x=i])
        by force
        
    qed

    lemma diff_scc_transition:      
      assumes US: "u \<in> SCm"
      assumes SCC: "scc_list C S_\<alpha> K_\<alpha>"
      assumes INT'B: "in_intv (TrI ! t') b"
      assumes IC: "i < length C"
      assumes NEQ: "(Br ! b \<in> C ! i) = (u \<notin> C ! i)"
      assumes ACT: "is_activated_transition u t'" 
      shows "\<exists>a\<in>K_\<alpha> u. \<forall>i. u \<in> C ! i \<longrightarrow> i < length C \<longrightarrow> \<not> a \<subseteq> C ! i"
    proof -
      from US have US': "u < N"
        unfolding S_\<alpha>_def SCm_alt by blast

      define a where "a \<equiv> (!) Br ` (sn_intv (TrI ! t'))"
      with US ACT have AKU: "a \<in> K_\<alpha> u"
        unfolding K_\<alpha>_def S_\<alpha>_def SCm_alt by auto

      {
        fix j
        assume "u \<in> C ! j" "j < length C" and CC: "a \<subseteq> C ! j"
        hence "Br ! b \<notin> C ! j"
          apply(cases "i=j")
          subgoal using NEQ by auto
          subgoal using scc_list_unique_index[OF SCC] IC NEQ by blast
          done
        moreover from INT'B have "Br ! b \<in> a" by (simp add: a_def)
        ultimately have "False" using CC by blast
      } note AUX = this


      show ?thesis
        apply(rule bexI[where ?x=a])
        subgoal using AUX by presburger
        subgoal using AKU by blast
        done
    qed

    lemma act_trans_simps[simp]: "modest_mdp_cullable_def.act_trans (St, Tr, Br, Pr', Av', Ta', Mm, Nr') = act_trans"
      unfolding modest_mdp_cullable_def.act_trans_def modest_mdp_cullable_def.is_activated_transition_def
      by auto

    lemma K_\<alpha>_simps[simp]: "modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr',Av,Ta,Mm,Nr') = K_\<alpha>"
      unfolding modest_mdp_cullable_def.K_\<alpha>_def 
      apply(rule ext)
      by (auto split: if_splits)

    lemma S_\<alpha>_simps[simp]: "modest_mdp_cullable_def.S_\<alpha> N (St',Tr',Br',Pr',Av',Ta',Mm,Nr') = S_\<alpha>"
      unfolding modest_mdp_cullable_def.S_\<alpha>_def by simp

    lemma D_\<alpha>_simps[simp]: "modest_mdp_cullable_def.D_\<alpha> (St',Tr',Br',Pr',Av',Ta',Mm,Nr') = D_\<alpha>"
      unfolding modest_mdp_cullable_def.D_\<alpha>_def by simp

    lemma L_\<alpha>_simps[simp]: "modest_mdp_cullable_def.L_\<alpha> (St',Tr',Br',Pr',Av',Ta',Mm,Nr') = L_\<alpha>"
      unfolding modest_mdp_cullable_def.L_\<alpha>_def by simp

    lemma Z_\<alpha>_simps[simp]: "modest_mdp_cullable_def.Z_\<alpha> (St',Tr',Br',Pr',Av,Ta,Mm',Nr') = Z_\<alpha>"
      unfolding modest_mdp_cullable_def.Z_\<alpha>_def by simp 
  end

  context modest_mdp_cullable_invar'
  begin

    lemma Mm_state2: "x \<in> \<Union> (set (snd Mm)) \<Longrightarrow> x < N"
      using Mm2_sub atLeastLessThan_iff states_M\<^sub>0_\<alpha>
      by blast

    lemma Mm_len2: "length (snd Mm) = N"
      using Mm2_len N_DEF by blast

    lemma N_alt_snd_Mm: "N = length (snd Mm)"
      using N_DEF Mm_len2 by simp

    lemma closed_SK: "closed_mdp S_\<alpha> K_\<alpha>"
    proof(rule closed_mdpI)
      fix u a v
      assume US: "u \<in> S_\<alpha>"
      assume AK: "a \<in> K_\<alpha> u"
      assume VA: "v \<in> a"

      from US have UL: "u < N" and ADM: "(\<forall>i<length (fst Mm). u \<notin> (fst Mm) ! i)"
        unfolding S_\<alpha>_def by auto

      thus "v \<in> S_\<alpha>"
      proof(cases "u \<in> Cm")
        case True

        with AK obtain t where ACT: "is_activated_transition u t" and "a = (!) Br ` sn_intv (TrI ! t)"
          unfolding K_\<alpha>_def by (auto split: if_splits)
  
        with VA obtain b where ITB: "in_intv (TrI ! t) b" and VB: "v = Br ! b"
          by force
          
        hence VL: "v < N" 
          by(auto intro!: Br_in_bound Br_in_bound_intvD[of t] 
            simp: Tr_in_bound_intvD[OF UL is_activated_transitionD1[OF ACT]])
  
        from ACT ITB have X: "op_antpar_eq_set_mem Mm u (Br ! b)"
          unfolding is_activated_transition_def by presburger

        
        hence "(\<forall>i<length (fst Mm). v \<notin> fst Mm ! i)" 
          using Mm_disj[of v] ADM
          unfolding op_antpar_eq_set_mem_def 
          by (auto simp: VB split: prod.splits)

        then show ?thesis 
          using ADM unfolding S_\<alpha>_def by(auto simp: VL)
      next
        case False
        hence "u = v"
          using AK K_\<alpha>_def VA UL by fastforce
        with US show ?thesis by blast
      qed

    qed


    lemma E_\<alpha>_succ_N: "E_\<alpha>' `` {0..<N} \<subseteq> {0..<N}"
      unfolding MDSKZ_\<alpha>_def closed_mdp_def K_\<alpha>'_def S_\<alpha>_def
      using closed_mdpD[OF closed_SK]
      by (auto simp: mdp_graph_defs.E_\<alpha>_mem split!: if_splits 
        intro!: Br_in_bound Br_in_bound_intvD Tr_in_bound_intvD is_activated_transitionD1) 


    lemma E_\<alpha>_reach_N: "E_\<alpha>'\<^sup>* `` {0..<N} \<subseteq> {0..<N}"
      apply clarsimp
      subgoal for u v
        apply(induction rule: rtrancl_induct)
        using E_\<alpha>_succ_N
        by fastforce+
      done

    lemma mdp_impl_modest:
      shows "mdp S_\<alpha> K_\<alpha>"
      apply(unfold_locales)
      subgoal
        using finite_S_\<alpha> by presburger
      subgoal using closed_SK .
      done


  end


  \<comment> \<open>For technical purposes regarding the SCC algorithm, we need to fix the intermediary representation 
     of the state space. The SCC algorithm already implements this equivalently, but for different reasons.\<close>
  definition "modest_MDSKZ_DSC_rel N DS DSC = br (modest_mdp_cullable_def.MDSKZ_\<alpha> N) (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr). modest_mdp_cullable_invar N DSC (St,Tr,Br,Pr,Av,Ta,Mm,Nr) \<and> DS = (St,Tr,Br,Pr,Av,Ta))"

  definition "modest_MDSKZ_DS_rel N DS = br (modest_mdp_cullable_def.MDSKZ_\<alpha> N) (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr). modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,Mm,Nr) \<and> DS = (St,Tr,Br,Pr,Av,Ta))"

  definition "modest_MLDSKZ_DSC_rel N DS DSC = br (modest_mdp_cullable_def.MLDSKZ_\<alpha> N) (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr). modest_mdp_cullable_invar N DSC (St,Tr,Br,Pr,Av,Ta,Mm,Nr) \<and> DS = (St,Tr,Br,Pr,Av,Ta))"

  definition "modest_MLDSKZ_DS_rel N DS = br (modest_mdp_cullable_def.MLDSKZ_\<alpha> N) (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr). modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,Mm,Nr) \<and> DS = (St,Tr,Br,Pr,Av,Ta))"

  lemma modest_MDSKZ_DSC_rel_DS_eq: "(DSC', SK) \<in> modest_MDSKZ_DSC_rel N DS DSC \<Longrightarrow> DSC = DSC'"
    unfolding modest_MDSKZ_DSC_rel_def
    by(auto simp: in_br_conv modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def)

  lemma modest_MDSKZ_DSC_rel_DSC_eq: "((St,Tr,Br,Pr,Av,Ta,Mm,Nr), SK) \<in> modest_MDSKZ_DSC_rel N DS DSC \<Longrightarrow> DS = (St,Tr,Br,Pr,Av,Ta)"
    unfolding modest_MDSKZ_DSC_rel_def
    by(auto simp: in_br_conv)

  lemma modest_MDSKZ_DS_rel_DS_eq: "((St,Tr,Br,Pr,Av,Ta,Mm,Nr), SK) \<in> modest_MDSKZ_DS_rel N DS \<Longrightarrow> DS = (St,Tr,Br,Pr,Av,Ta)"
    unfolding modest_MDSKZ_DS_rel_def
    by(auto simp: in_br_conv)


  lemma modest_MLDSKZ_rel_DS_eq: "(DSC', SK) \<in> modest_MLDSKZ_DSC_rel N DS DSC \<Longrightarrow> DSC = DSC'"
    unfolding modest_MLDSKZ_DSC_rel_def
    by(auto simp: in_br_conv modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def)

 
  subsubsection \<open>Modest MDP\<close>

  context modest_init_mdp_env_defs
  begin

    definition "modest_MDSKZ_DSC_assn DS DSC = hr_comp modest_mdp_assn_aux (modest_MDSKZ_DSC_rel N DS DSC)"

    definition "modest_MDSKZ_DS_assn DS = hr_comp modest_mdp_assn_aux (modest_MDSKZ_DS_rel N DS)"
 
    definition "modest_MLDSKZ_DSC_assn DS DSC = hr_comp modest_mdp_assn_aux (modest_MLDSKZ_DSC_rel N DS DSC)"
  
    definition "modest_MLDSKZ_DS_assn DS = hr_comp modest_mdp_assn_aux (modest_MLDSKZ_DS_rel N DS)"
    subsubsection \<open>Modest Graph Index\<close>


    lemma modest_MDSKZ_DS_rel_alt: "modest_MDSKZ_DS_rel N DS = { (DSC,MG). (DSC,MG) \<in> modest_MDSKZ_DSC_rel N DS DSC}"
      unfolding modest_MDSKZ_DSC_rel_def modest_MDSKZ_DS_rel_def modest_mdp_cullable_invar_def
      by(auto simp: br_def modest_mdp_cullable_invar_axioms_def)

    lemma modest_MDSKZ_DS_assn_alt: "modest_MDSKZ_DS_assn DS MG Ei = (EXS DSC. modest_MDSKZ_DSC_assn DS DSC MG Ei)"
      unfolding modest_MDSKZ_DS_assn_def modest_MDSKZ_DS_rel_alt modest_MDSKZ_DSC_assn_def 
      apply(cases MG)
      apply (clarsimp simp: in_br_conv fun_eq_iff hr_comp_def sep_algebra_simps)
      by (metis modest_MDSKZ_DSC_rel_DS_eq)

  end
  



  subsection \<open>Refinement to LLVM\<close>

  context modest_init_mdp_env
  begin
  
    lemma N_BOUND2: "N < max_size_t - N"
      using N_BOUND by simp
  
    lemma N_Suc_max_size_t: "x < N \<Longrightarrow> Suc x < max_snat 64"
      using N_BOUND by simp

    lemma N_max_size_t: "x \<le> N \<Longrightarrow> x < max_size_t"
      using N_BOUND by simp
  
    lemmas [sepref_import_param] = n_impl
    sepref_register N
  
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
    
    concrete_definition (in -) t_to_mec_map_ll' [llvm_code] is disj_set_list_tuple_env.t_to_mec_map_ll_def
  
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
  
  end

  
  section \<open>Modest Graph Data Structure SCC operations\<close>
  
  
  subsection \<open>Suboperations\<close>
  
  context modest_init_mdp_env_defs 
  begin
  
    definition modest_init_mdp :: "modest_input_mdp \<Rightarrow> modest_mdp nres" where 
      "modest_init_mdp = (\<lambda>(St,Tr,Br,Pr,Av,Ta). do{
        let Mm = op_antpar_empty;
        let Mm = op_antpar_list2_expand Mm N;
        (Mm,_) \<leftarrow> WHILEIT (\<lambda>(Mm,v). v \<le> N \<and> fst Mm = [] \<and> snd Mm = (if N = 0 then [] else (replicate N {})[0:={0..<v}])) (\<lambda> (Mm,v). v < N) (\<lambda> (Mm, v). do{ 
          ASSERT(v < N);
          ASSERT(N > 0);
          mop_bound_val (\<lambda> v. v < N) v; 
          let i = 0;
          ASSERT(i < max_size_t - N);
          mop_bound_val (\<lambda> i. i < max_size_t - N) i;
          ASSERT(i < length (snd Mm));
          RETURN (op_antpar_move_to_list2 Mm v i, v+1)
        }) (Mm,0);
        RETURN (St,Tr,Br,Pr,Av,Ta,Mm,N)
      })"
  
  end
  context modest_init_mdp_env_defs
  begin
  
    definition "modest_states_nonempty = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr). Nr > 0)"
    sepref_register modest_states_nonempty
  
    definition "mop_modest_activated_transition_in_scc = (\<lambda> DS CV u t. do{
      let flag = True;
      ASSERT (t < length (modest_mdp_cullable_pre.Tr DS));
      let bl = Tr_nth DS t;
      ASSERT (Suc t < length (modest_mdp_cullable_pre.Tr DS));
      let bu = Tr_nth DS (Suc t);
      ui \<leftarrow> unfiltered_set_open_block CV (\<lambda> C. do{ 
          ASSERT(\<exists> i < length C. u \<in> C ! i); 
          mop_get_index_unbounded C u});
      (flag,b) \<leftarrow> WHILEIT (\<lambda> (flag,b). bl \<le> b \<and> b \<le> bu \<and> (flag \<longleftrightarrow> (\<forall>b' i. i < length (fst CV) \<longrightarrow> bl \<le> b' \<longrightarrow> b' < b \<longrightarrow> (modest_mdp_cullable_pre.Br DS ! b' \<in> (fst CV) ! i \<longleftrightarrow> u \<in> (fst CV) ! i )))) (\<lambda> (flag,b). b < bu \<and> flag) (\<lambda> (flag,b). do {
        v \<leftarrow> mop_modest_get_target_of_branch DS b;
        vi \<leftarrow> unfiltered_set_open_block CV (\<lambda> C. do{ 
          ASSERT(\<exists> i < length C. v \<in> C ! i); 
          mop_get_index_unbounded C v});
        ASSERT(Suc b \<le> length (modest_mdp_cullable_pre.Br DS));
        RETURN (ui = vi, Suc b)
      }) (flag,bl);
      RETURN flag
    })"
    sepref_register "mop_modest_activated_transition_in_scc"
  
    lemma modest_activated_transition_in_scc_alt: "mop_modest_activated_transition_in_scc = modest_mdp_cullable_def.modest_activated_transition_in_scc N"
      unfolding mop_modest_activated_transition_in_scc_def modest_mdp_cullable_def.modest_activated_transition_in_scc_def
        Tr_nth_alt unfiltered_set_open_block_def modest_get_target_of_branch_alt
      apply(rule ext)+
      subgoal for DS CV u t
        apply(cases CV)
        by auto
      done
  
    definition "mop_modest_iterate_succs_eq_scc = (\<lambda> DS CV u. do{
      if op_modest_is_disabled_transitions DS u then
        RETURN True
      else do{
        let flag = True;
        ASSERT(u < length (modest_mdp_cullable_pre.St DS));
        let tl = St_nth_lid DS u;
        ASSERT(Suc u < length (modest_mdp_cullable_pre.St DS));
        let tu = St_nth_uid DS u;
        (flag,t) \<leftarrow> WHILEIT (\<lambda> (flag,t). tl \<le> t \<and> t \<le> tu \<and> (flag \<longleftrightarrow> (\<forall>t' \<in> modest_mdp_cullable_def.act_trans DS u. tl \<le> t' \<longrightarrow> t' < t \<longrightarrow> (\<forall>b \<in> sn_intv (sorted_intvs (modest_mdp_cullable_pre.Tr DS) ! t'). \<forall> i < length (fst CV). (modest_mdp_cullable_pre.Br DS ! b \<in> (fst CV) ! i \<longleftrightarrow> u \<in> (fst CV) ! i))))) (\<lambda> (flag,t). t < tu \<and> flag) (\<lambda> (flag, t). do {
          g \<leftarrow> mop_modest_is_activated DS u t;
          ASSERT(Suc t \<le> length (modest_mdp_cullable_pre.Tr DS));
          if g then do {
            flag \<leftarrow> mop_modest_activated_transition_in_scc DS CV u t;
            RETURN (flag, Suc t)
          } else 
            RETURN (flag, Suc t)
        }) (flag,tl);
        RETURN flag
      }
    })"
    sepref_register "mop_modest_iterate_succs_eq_scc"
  
    lemma modest_iterate_succs_eq_scc_alt: "mop_modest_iterate_succs_eq_scc = modest_mdp_cullable_def.modest_iterate_succs_eq_scc N"
      unfolding mop_modest_iterate_succs_eq_scc_def modest_mdp_cullable_def.modest_iterate_succs_eq_scc_def
        modest_is_disabled_transitions_alt St_nth_lid_alt St_nth_uid_alt modest_is_activated_alt
        modest_activated_transition_in_scc_alt
      apply(rule ext)+
      apply auto
      done
  
  
  end


  definition "is_deleted_state = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr) u. op_antpar_mem_any1 Mm u)"

  definition "expand_capacity_MDP = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr) i. (St,Tr,Br,Pr,Av,Ta,op_antpar_list1_expand Mm i,Nr))"

  definition "get_mec_num_MDP = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr). op_antpar_list1_count Mm)"

  definition track_sccs :: "modest_mdp \<Rightarrow> nat set filter_list \<Rightarrow> modest_mdp" where 
    "track_sccs = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr) CV. (St,Tr,Br,Pr,Av,Ta,Mm,Nr))"

  definition(in modest_init_mdp_env_defs) mark_as_MEC :: "modest_mdp \<Rightarrow> nat set filter_list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> modest_mdp nres" where 
    "mark_as_MEC = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr) CV u i. do{
    ASSERT(i < N);
    mop_bound_val (\<lambda> i. i < N) i;
    ASSERT (i < length (fst Mm));
    let Mm' = op_antpar_move_to_list1 Mm u i;
    ASSERT(Nr > 0);
    RETURN (St,Tr,Br,Pr,Av,Ta,Mm',Nr - 1)
  })"

  definition(in scc_map_defs) mark_as_unfinished :: "modest_mdp \<Rightarrow> nat set filter_list \<Rightarrow> nat \<Rightarrow> modest_mdp nres" where 
    "mark_as_unfinished = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr) CV u. do{ 
    Mm' \<leftarrow> unfiltered_list_open_block CV (\<lambda> C. do{
      ASSERT (transfer_to_disjdlt2_pre ((C, Mm), u));
      mop_transfer_to_antpar2 C Mm u
    });
    RETURN (St,Tr,Br,Pr,Av,Ta,Mm',Nr)
  })"

  definition untrack_sccs :: "modest_mdp \<Rightarrow> nat set filter_list \<Rightarrow> modest_mdp" where 
    "untrack_sccs = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr) CV. (St,Tr,Br,Pr,Av,Ta,Mm,Nr))"

  definition(in modest_init_mdp_env_defs) modest_get_mecs :: "modest_mdp \<Rightarrow> (mec_map \<times> modest_input_mdp) nres" where 
    "modest_get_mecs = (\<lambda> (St,Tr,Br,Pr,Av,Ta,Mm,Nr). doN{
        ASSERT (op_antpar_to_mec_map_pre N Mm);
        RETURN ((op_antpar_to_mec_map Mm), (St,Tr,Br,Pr,Av,Ta))
    })"


  lemma eq_conj_eq: "A = B \<Longrightarrow> A \<or> C = B \<or> C"
    by blast

                                                               
  context modest_mdp_cullable_invar'
  begin                              
    interpretation disj_set_list_tuple_defs N N .

    lemma S_\<alpha>D1: "u \<in> S_\<alpha> \<Longrightarrow> u < N"
      unfolding S_\<alpha>_def by blast

    lemmas K_\<alpha>_closed_under_S_\<alpha> = mdp.K_closed_under_S[OF mdp_impl_modest, THEN closed_mdpD]

    lemma modest_closed_under_S_\<alpha>: "u \<in> SCm \<Longrightarrow> is_activated_transition u t \<Longrightarrow> in_intv (StI ! u) t \<Longrightarrow> v \<in> ((!) Br) ` (sn_intv (TrI ! t)) \<Longrightarrow> v \<in> S_\<alpha>" for u::nat and a::"nat set" and v::nat
      apply(rule K_\<alpha>_closed_under_S_\<alpha>[of _ "(!) Br ` (sn_intv (TrI ! t))"]) unfolding K_\<alpha>_def SCm_alt 
      apply clarsimp
      apply assumption
      by (auto simp: S_\<alpha>D1)

    lemma modest_activated_transition_in_scc_correct: "u \<in> SCm \<Longrightarrow> in_intv (StI!u) t \<Longrightarrow> is_activated_transition u t \<Longrightarrow> scc_list C S_\<alpha> K_\<alpha> \<Longrightarrow> modest_activated_transition_in_scc (C,V) u t \<le> RETURN ((\<forall>b \<in> sn_intv (TrI!t). \<forall> i < length C. (Br ! b \<in> C ! i \<longleftrightarrow> u \<in> C ! i)))"
      unfolding modest_activated_transition_in_scc_def mop_get_index_unbounded_def 
      apply(refine_vcg WHILEIT_rule[where ?R = "measure (\<lambda> (flag,b). uid (TrI ! t) - b)"] get_successor_of_branch_refine)
      supply [simp] = S_\<alpha>D1
      subgoal
        using S_\<alpha>D1 SCm_alt St_in_bound basic_trans_rules(19) in_intv_ubD by blast
      subgoal 
        using S_\<alpha>D1 SCm_alt Tr_in_bound_intvD less_minus_Suc_zero by blast
      subgoal 
        by (simp add: SCm_alt scc_list_states_index)
      subgoal by blast
      subgoal for C V i flag b
        by (force simp flip: lid_sorted_intvs[OF sorted_Tr]) 
      subgoal for C V i flag b 
        by (auto simp flip: lid_sorted_intvs[OF sorted_Tr] uid_sorted_intvs[OF sorted_Tr]) 
      subgoal
        by (auto simp flip: lid_sorted_intvs[OF sorted_Tr] ) 
      subgoal for C V i s flag b
        apply simp
        apply(rule Br_in_bound_intvD[where ?t=t])
        apply(rule Tr_in_bound_intvD[where ?u=u])
        by(auto simp: SCm_alt in_intvI simp flip: uid_sorted_intvs[OF sorted_Tr] lid_sorted_intvs[OF sorted_Tr])
      subgoal for C V i s flag b v 
        apply (clarsimp simp flip: lid_sorted_intvs[OF sorted_Tr] uid_sorted_intvs[OF sorted_Tr]) 
        apply(subgoal_tac "v \<in> S_\<alpha>") 
        apply (meson scc_list_states_index)
        by(auto elim!: modest_closed_under_S_\<alpha> simp: in_intv_def)
      subgoal 
        apply (clarsimp simp flip: lid_sorted_intvs[OF sorted_Tr] uid_sorted_intvs[OF sorted_Tr]) 
        using Br_in_boundD SCm_alt S_\<alpha>D1 Tr_in_bound_intvD less_eq_Suc_le by blast
      subgoal by auto
      subgoal for C V i s flag b v j flag' b' by auto
      subgoal for C V i s flag b v j flag' b' 
        apply clarsimp
        by (metis less_Suc_eq scc_list_unique_index)
      subgoal by (auto simp flip: lid_sorted_intvs[OF sorted_Tr] uid_sorted_intvs[OF sorted_Tr]) 
      subgoal for C V j s flag b 
        apply(cases flag)
        apply (clarsimp_all simp flip: lid_sorted_intvs[OF sorted_Tr] uid_sorted_intvs[OF sorted_Tr]) 
        subgoal by blast
        subgoal by(auto simp: in_intvI)
        done
      done

    lemma modest_iterate_succs_eq_scc_correct: "u \<in> S_\<alpha> \<Longrightarrow> scc_list C S_\<alpha> K_\<alpha> \<Longrightarrow> modest_iterate_succs_eq_scc (C,V) u \<le> RETURN (op_all_succ_eq_map MDSKZ_\<alpha> (C,V) u) "
      unfolding modest_iterate_succs_eq_scc_def modest_is_disabled_transitions_def
      apply(refine_vcg WHILEIT_rule[where ?R = "measure (\<lambda> (flag,t). uid (StI ! u) - t)"]
        order_trans[OF modest_is_activated_correct] order_trans[OF modest_activated_transition_in_scc_correct])
      apply(vc_solve solve: S_\<alpha>D1 S_\<alpha>D1[folded N_DEF])[20]
      subgoal 
        unfolding op_all_succ_eq_map_def MDSKZ_\<alpha>_def 
        by (auto simp: K_\<alpha>_def Av_Cm Ta_Cm scc_list_states_index)
      subgoal 
        using S_\<alpha>D1 Suc_lessD less_minus_Suc_zero N_DEF by blast
      subgoal
        using S_\<alpha>D1 less_minus_Suc_zero N_DEF by blast
      subgoal
        by (simp add: sorted_St sorted_wrt_nth_less) 
      subgoal
        using S_\<alpha>D1 in_intv_sorted_intvs sorted_St N_DEF by blast
      subgoal for fla t
        apply(clarsimp simp: Suc_le_eq dest!: S_\<alpha>D1) 
        apply(drule Tr_in_bound_intvD[of _ t])
        using in_intv_sorted_intvs less_minus_Suc_zero sorted_St apply presburger
        by linarith
      subgoal 
        by (simp add: Cm_mem SCm_alt S_\<alpha>D1)
      subgoal
        using is_activated_transition_def by blast
      subgoal using less_Suc_eq sn_intv_member
        by blast
      subgoal
        using S_\<alpha>D1 diff_less_mono2 lessI sorted_St uid_sorted_intvs by simp
      subgoal using less_Suc_eq sn_intv_member 
        by auto
      subgoal apply clarsimp
        using S_\<alpha>D1 diff_less_mono2 lessI sorted_St uid_sorted_intvs by fastforce
      subgoal for C V s flag t
        apply(cases flag)
        subgoal 
          unfolding op_all_succ_eq_map_def MDSKZ_\<alpha>_def 
          apply (clarsimp simp flip: lid_sorted_intvs[OF sorted_Tr] uid_sorted_intvs[OF sorted_Tr]) 
          apply(rule same_scc_transition)
          subgoal unfolding SCm_alt
            by (simp add: Cm_mem S_\<alpha>D1)
          subgoal by blast 
          subgoal 
            using in_intv_def is_activated_transitionD1 sn_intv_member
            by (auto simp: in_intv_def simp flip: uid_sorted_intvs[OF sorted_St] lid_sorted_intvs[OF sorted_St]) 
          subgoal using scc_list_states_index by meson
          done
        subgoal unfolding op_all_succ_eq_map_def MDSKZ_\<alpha>_def 
          by(auto simp: Cm_mem SCm_alt S_\<alpha>D1 diff_scc_transition intro: diff_scc_transition)
        done
      done

    lemma expand_capacity_MDP_\<alpha>: "op_expand_capacity MDSKZ_\<alpha> i = modest_mdp_cullable_def.MDSKZ_\<alpha> N (expand_capacity_MDP DS i)"
    proof -

      have DU: "D_\<alpha> @ replicate i {} = modest_mdp_cullable_def.D_\<alpha> (St,Tr,Br,Pr,Av,Ta,op_antpar_list1_expand Mm i,Nr)" 
        unfolding modest_mdp_cullable_def.D_\<alpha>_def op_antpar_list1_expand_def by(cases Mm) auto

      have SU: "S_\<alpha> = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,op_antpar_list1_expand Mm i,Nr)"
        unfolding modest_mdp_cullable_def.S_\<alpha>_def op_antpar_list1_expand_def
        apply (cases Mm)
        apply clarsimp
        apply(rule equalityI)
        subgoal apply clarsimp
          by (metis add.commute less_diff_conv2 linorder_le_less_linear memb_imp_not_empty nth_append nth_replicate)
        subgoal 
          apply clarsimp
          by (metis nth_append_first trans_less_add1) 
        done
       

      have "op_antpar_eq_set_mem Mm u (Br ! b) \<longleftrightarrow> op_antpar_eq_set_mem (op_antpar_list1_expand Mm i) u (Br ! b)" for u b
        unfolding op_antpar_eq_set_mem_def op_antpar_list1_expand_def
        apply (cases Mm)
        apply clarsimp
        apply(rule iffI)
        subgoal by (simp add: nth_append)
        subgoal by (metis nth_append_left trans_less_add1)
        done
      hence KU: "K_\<alpha> = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,op_antpar_list1_expand Mm i,Nr)" 
        unfolding modest_mdp_cullable_def.K_\<alpha>_def modest_mdp_cullable_def.act_trans_def modest_mdp_cullable_def.is_activated_transition_def
        by (fastforce split: if_splits)

      have ZU: "Z_\<alpha> = modest_mdp_cullable_def.Z_\<alpha> (St, Tr, Br, Pr, Av, Ta, op_antpar_list1_expand Mm i, Nr)"
        by auto

      show ?thesis
        unfolding modest_mdp_cullable_def.MDSKZ_\<alpha>_def op_expand_capacity_def expand_capacity_MDP_def 
        apply(cases DS)
        using DU SU KU ZU 
        by force
    qed

    lemma expand_capacity_S_\<alpha>: "modest_mdp_cullable_def.S_\<alpha> N (expand_capacity_MDP (St',Tr',Br',Pr',Av',Ta',Mm',Nr') i) = modest_mdp_cullable_def.S_\<alpha> N (St',Tr',Br',Pr',Av',Ta',Mm',Nr')"
      unfolding modest_mdp_cullable_def.S_\<alpha>_def expand_capacity_MDP_def op_antpar_list1_expand_def 
      apply(rule equalityI)
      apply clarsimp_all
      apply (metis nth_append_first trans_less_add1)
      by (metis add_diff_inverse_nat memb_imp_not_empty nat_add_left_cancel_less nth_append nth_replicate)

    lemma expand_capacity_MDP_invar: 
      assumes MN: "length D_\<alpha> + i \<le> N" 
      and DSD: "DS = (St',Tr',Br',Pr',Av',Ta',Mm',Nr')"
      shows "modest_mdp_cullable_invar' N (expand_capacity_MDP (St',Tr',Br',Pr',Av',Ta',Mm',Nr') i)"
      unfolding expand_capacity_MDP_def op_antpar_list1_expand_def using DSD
      apply(unfold_locales) 
      subgoal using N_DEF by force
      subgoal using N0 by blast
      subgoal using AN by simp
      subgoal using TN by simp
      subgoal using AT by force
      subgoal using St_dom by simp
      subgoal using Tr_dom by force
      subgoal using Br_dom by fastforce
      subgoal using Sorted_St by force
      subgoal using Sorted_Tr by force
      subgoal using Pr_lt_one by force
      subgoal using Pr_gt_zero by auto
      subgoal using Len_Pr_Br by force
      subgoal using expand_capacity_S_\<alpha> Nr_S 
        unfolding expand_capacity_MDP_def op_antpar_list1_expand_def 
        by (simp add: expand_capacity_S_\<alpha>)
      subgoal for u using Mm_all_states[of u]  
        by (auto simp: nth_append split: prod.splits)
      subgoal for u using Mm_disj[of u]
        apply(cases Mm')
        apply clarsimp 
        by (metis add_diff_inverse_nat empty_iff nat_add_left_cancel_less nth_append nth_replicate)
      subgoal 
        apply(cases Mm')
        by (auto simp: nth_append Mm1_disj split: if_splits)
      subgoal
        apply(cases Mm')
        by (auto simp: Mm2_disj)
      subgoal
        apply(cases Mm')
        using MN unfolding D_\<alpha>_def by simp
      subgoal
        apply(cases Mm')
        using Mm2_len by simp
      subgoal apply(cases Mm') using Mm1_sub by force
      subgoal apply(cases Mm') using Mm2_sub by force
      done

    lemma S_\<alpha>_sub_S0_\<alpha>: "S_\<alpha> \<subseteq> states M\<^sub>0_\<alpha>"
      unfolding S_\<alpha>_def states_M\<^sub>0_\<alpha> by force

    lemma K_\<alpha>_sub_K0_\<alpha>: "\<forall>u\<in>S_\<alpha>. K_\<alpha> u \<subseteq> K_actions M\<^sub>0_\<alpha> u"
      unfolding K_\<alpha>_def S_\<alpha>_def
      by (auto simp: actions_M\<^sub>0_\<alpha> K_actions_M\<^sub>0_\<alpha> Cm_mem is_activated_transitionD1 succs_def dest: is_activated_transitionD1) 


    lemma culled_edges_K_\<alpha>: 
      assumes SC: "S = \<Union>(set C)"
      assumes SCA: "\<Union>(set C) - \<Union>(set V) \<subseteq> S_\<alpha>"
      assumes SCC: "scc_list C S K"
      assumes SUB: "sub_struc_of M\<^sub>0_\<alpha> S K"
      assumes VDEF: "set V = {S' \<in> set C. closed_mdp S' K}"
      assumes Mm2_Upp: "\<And>i. i < length (snd Mm) \<Longrightarrow> length C \<le> i \<Longrightarrow> snd Mm ! i = {}"
      assumes Mm2_Low: "\<And>i. i < length C \<Longrightarrow> snd Mm ! i = (if C ! i \<in> set V then {} else C ! i)"
      shows "culled_edges C V (K_actions M\<^sub>0_\<alpha>) K_\<alpha>"
    proof(rule culled_edgesI; safe)
      fix u X a
      assume "u \<notin> \<Union> (set V)" "u \<in> X" "X \<in> set C" "a \<in> K_\<alpha> u"
      moreover have "u \<in> S_\<alpha>"
        using SCA calculation by auto
      ultimately show "a \<in> K_actions M\<^sub>0_\<alpha> u"
        using K_\<alpha>_sub_K0_\<alpha> SC by fast
    next
      fix u X a
      assume UV: "u \<notin> \<Union> (set V)" 
      and UX: "u \<in> X" 
      and XC: "X \<in> set C" 
      and AKU: "a \<in> K_\<alpha> u"
      hence US: "u \<in> S_\<alpha>"
        using assms by auto
      then obtain i where UM2: "u \<in> snd (Mm) ! i" and IM2: "i < length (snd Mm)" and NMEM: "\<forall> X \<in> set (fst (Mm)). u \<notin> X"
        unfolding S_\<alpha>_def apply clarsimp
        by (metis Mm_all_states fst_conv in_set_conv_nth snd_conv)
      hence IL: "i < length C"
        using Mm2_Upp by fastforce
      hence "u \<in> C ! i"
        using Mm2_Low UM2 by (auto simp: if_splits)
      hence XDEF: "X = C ! i"
        by (meson IL SCC UX XC nth_mem scc_list_unique_C)

      show "\<exists>X'\<in>set C - set V. u \<in> X' \<and> (\<forall>v\<in> a. v \<in> X')"
      proof(cases "u \<in> Cm")
        case True

        with AKU obtain t where UST: "u \<in> Cm" 
          and ADEF: "a = (!) Br ` (sn_intv (TrI ! t))" 
          and ACT: "is_activated_transition u t" 
          by(auto simp: K_\<alpha>_def split: if_splits)
  
  
        from ACT have A: "in_intv (TrI ! t) b \<Longrightarrow> (\<exists>i<length (snd Mm). u \<in> (snd Mm) ! i \<and> (Br ! b) \<in> (snd Mm) ! i)" for b
          unfolding is_activated_transition_def op_antpar_eq_set_mem_def using IM2 UM2 by (auto split: prod.splits)

        have "(\<forall>v\<in>a. v \<in> X)"
        proof
          fix v
          assume "v \<in> a"
          with ADEF obtain b where VDEF: "v = Br ! b" and ITRB: "in_intv (TrI ! t) b" by force
          from A[OF ITRB] IM2 UM2 have "Br ! b \<in> C ! i" using Mm2_disj[OF IM2 _ UM2] 
            using IL Mm2_Low
            by (metis empty_iff)
  
          with VDEF XDEF show "v \<in> X" by presburger
        qed

        with XDEF UV UX XC show ?thesis
          by blast 
      next
        case False
        then show ?thesis
          using AKU UV XC  \<open>u \<in> C ! i\<close> S_\<alpha>D1[OF US] 
          by (auto simp: K_\<alpha>_def XDEF)
      qed
    next
      fix u X a X'
      assume USV: "u \<notin> \<Union> (set V)" 
      and UX:"u \<in> X" 
      and XC: "X \<in> set C" 
      and AK0U: "a \<in> K_actions M\<^sub>0_\<alpha> u" 
      and "X' \<in> set C" 
      and "X' \<notin> set V" 
      and "u \<in> X'" 
      and ALX: "\<forall>v\<in>a. v \<in> X'"
      hence XEQ: "X' = X"
        using scc_list_unique_C[OF SCC]
        by presburger

      have US: "u \<in> S_\<alpha>"
        using assms XC UX  \<open>u \<notin> \<Union> (set V)\<close> by blast
      then obtain i where UM2: "u \<in> snd (Mm) ! i" and IM2: "i < length (snd Mm)" and NMEM: "\<forall> X \<in> set (fst (Mm)). u \<notin> X"
        unfolding S_\<alpha>_def apply clarsimp
        by (metis Mm_all_states in_set_conv_nth prod.sel(1,2))
      hence IL: "i < length C"
        using Mm2_Upp by fastforce
      hence "u \<in> C ! i"
        using Mm2_Low UM2 by(auto split: if_splits)
      hence XDEF: "X = C ! i"
        by (meson IL SCC UX XC nth_mem scc_list_unique_C)

      have AK0U': "a \<in> succs u"
        using AK0U K_actions_M\<^sub>0_\<alpha> S_\<alpha>D1 US by blast
      (*
        This is a bit of a workaround that arises from the incompatibility between the representation
        in the SCC algorithm (which represents Av and Ta states as having no edges) and the MDP representation
        (which necessarily represents these states as having a self-loop). Rewriting the SCC algorithm
        to make these states have a self-loop would lead to redundancies in that proof.
        Luckily, we are able to proof that Av and Ta states that are in C must necessarily be in V,
        which saves this proof, but feels ad hoc.
      *)

      thus "a \<in> K_\<alpha> u" 
      proof(cases "u \<in> Cm")
        case True

        then obtain t 
          where ADEF: "a = (!) Br ` sn_intv (TrI ! t)"
          and INST:"in_intv (StI ! u) t"
          using AK0U' unfolding succs_def   
          by(clarsimp split: if_splits)
  
        have "is_activated_transition u t"
          apply(rule is_activated_transitionI)
          subgoal using INST .
          subgoal
            unfolding op_antpar_eq_set_mem_def
            using ADEF ALX IM2 Mm2_Low[OF IL] UM2 XDEF XEQ \<open>X' \<notin> set V\<close> Mm2_disj Mm_disj
            apply (clarsimp simp: NMEM split: prod.splits simp del: sn_intv_member simp flip: sn_intv_member) 
            apply (smt (verit, best))
            done
          done
        hence "t \<in> act_trans u"
          by (simp add: INST)
        hence "a \<in> (\<lambda>i. (!) Br ` (sn_intv (TrI ! i))) ` act_trans u"
          using ADEF by blast

        then show ?thesis unfolding K_\<alpha>_def
          by(auto simp: K_\<alpha>_def US True S_\<alpha>D1[OF US])
      next
        case False
        then show ?thesis
          using AK0U' K_\<alpha>_def modest_mdp_input_struc_def.succs_def S_\<alpha>D1[OF US] by metis
      qed
    qed
        

  end

  lemma replicate_upd_same: "i < n \<Longrightarrow> (replicate n x)[i:=x] = replicate n x"
    by (simp add: list_update_same_conv)


  lemma(in modest_init_mdp_env_defs) modest_iterate_succs_eq_scc_correct:
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr),M,D,S,K,Z) \<in> modest_MDSKZ_DS_rel N DS"
    assumes US: "u \<in> S"
    assumes SCC: "scc_list C S K"
    shows "mop_modest_iterate_succs_eq_scc (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) (C,V) u \<le> RETURN (op_all_succ_eq_map (M,D,S,K,Z) (C,V) u)"
  proof -
    from REL 
      have DP[simp]: "D = modest_mdp_cullable_def.D_\<alpha> (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  ZP[simp]: "Z = modest_mdp_cullable_def.Z_\<alpha> (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def
      by(auto simp: in_br_conv modest_mdp_cullable_def.MDSKZ_\<alpha>_def 
        modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    from REL have MP: "M = M\<^sub>0_\<alpha>"
      unfolding modest_MDSKZ_DSC_rel_def modest_MDSKZ_DS_rel_def 
      by(auto simp: in_br_conv modest_mdp_cullable_def.MDSKZ_\<alpha>_def) 

    show ?thesis
      using US SCC apply clarsimp
      unfolding MP modest_iterate_succs_eq_scc_alt MDSKZ_\<alpha>_def[symmetric]
      using modest_iterate_succs_eq_scc_correct .
  qed


  lemma(in modest_init_mdp_env) modest_init_mdp_correct:
    assumes REL: "((St,Tr,Br,Pr,Av,Ta), M\<^sub>0) \<in> modest_mdp_input_DS_rel N DS"
    shows "modest_init_mdp (St,Tr,Br,Pr,Av,Ta) \<le> \<Down>(modest_MDSKZ_DS_rel N DS) (mop_init_mdp M\<^sub>0)"
  proof - 

    from REL interpret modest_mdp_input_invar N St Tr Br Pr Av Ta
      unfolding modest_mdp_input_DS_rel_def
      by(auto simp: in_br_conv)

    from REL have MP: "M\<^sub>0 = M\<^sub>0_\<alpha>" and DDEF: "DS = (St, Tr, Br, Pr, Av, Ta)"
      unfolding modest_mdp_input_DS_rel_def
      by(auto simp: in_br_conv)


    obtain nat where SUC: "Suc nat = N" 
      using N0 apply(cases N) by blast+

    hence STEQ: "length St = Suc (Suc nat)"
      using N_DEF by linarith

    have SD: "states M\<^sub>0 = modest_mdp_cullable_def.S_\<alpha> N (St, Tr, Br, Pr, Av, Ta, ([], insert nat {0..<nat} # replicate nat {}), N)"
      unfolding modest_mdp_cullable_def.S_\<alpha>_def states_M\<^sub>0_\<alpha> MP 
      by auto

    have AUX1: "x \<in> ({0..<N} # replicate nat {}) ! i \<Longrightarrow> i < N \<Longrightarrow> i = 0 \<and> x < N" for x i
      using SUC[symmetric]
      apply(induction N)
      using less_Suc_eq_0_disj by fastforce+

    have "modest_mdp_cullable_def.is_activated_transition (St,Tr,Br,Pr,Av,Ta, ([], {0..<N} # replicate nat {}), N) u t" 
      if "u < N" and "in_intv (StI ! u) t" for u t
      unfolding modest_mdp_cullable_def.is_activated_transition_def op_antpar_eq_set_mem_def
      by (auto dest!: AUX1 simp add: that Suc SUC intro!: Br_in_bound Br_in_bound Br_in_boundD[OF Tr_in_bound_intvD[OF that]]) 

    hence ACTT: "(modest_mdp_cullable_def.act_trans (St,Tr,Br,Pr,Av,Ta, ([], {0..<N} # replicate nat {}), N) u) = sn_intv (StI ! u)" 
      if "u < N" for u
      unfolding modest_mdp_cullable_def.act_trans_def modest_mdp_cullable_def.is_activated_transition_def
      using that by auto

    have KD: "K_actions M\<^sub>0 = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta, ([], {0..<N} # replicate nat {}), N)"
      apply(rule ext)
      using ACTT unfolding modest_mdp_cullable_def.K_\<alpha>_def states_M\<^sub>0_\<alpha> MP atLeast0_lessThan_Suc[symmetric]
      by(auto simp: Cm_mem K_actions_M\<^sub>0_\<alpha> succs_def atLeast0_lessThan_Suc dest!: ne_K_actions_M\<^sub>0_\<alpha>')   

    have INV': "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta, ([], insert nat {0..<nat} # replicate nat {}), N)"
      apply(unfold_locales)
      subgoal by (auto simp: N_DEF)
      subgoal by (auto simp: N0)
      subgoal using AN by auto
      subgoal using TN by auto
      subgoal using AT by auto
      subgoal 
        by (simp add: St_dom)
      subgoal 
        by (simp add: Tr_dom)
      subgoal 
        by (simp add: Br_dom)
      subgoal 
        using Sorted_St by force
      subgoal 
        using Sorted_Tr by auto
      subgoal
        by (simp add: Pr_lt_one)
      subgoal
        by (simp add: Pr_gt_zero)
      subgoal 
        by auto
      subgoal using N_card SD MP by auto
      subgoal
        apply clarsimp
        apply(rule exI[where ?x=0]) 
        using SUC by (auto simp: STEQ)
      subgoal 
        by auto
      subgoal using STEQ by simp
      subgoal for i j u 
        apply clarsimp
        apply(subgoal_tac "i=0")
        using less_Suc_eq_0_disj apply force 
        using not_empty_eq by fastforce
      subgoal by auto
      subgoal by (auto simp: SUC)
      subgoal by simp
      subgoal
        using SUC states_M\<^sub>0_\<alpha> by force
      done

    show ?thesis 
      unfolding modest_init_mdp_def mop_init_mdp_def op_antpar_list2_expand_def
        op_antpar_empty_def op_antpar_move_to_list2_def modest_mdp_cullable_def.MDSKZ_\<alpha>_def 
        modest_mdp_cullable_def.D_\<alpha>_def modest_mdp_cullable_def.S_\<alpha>_def mop_bound_val_def
        modest_MDSKZ_DS_rel_def build_rel_SPEC_conv
      apply(refine_vcg WHILEIT_rule[where ?R="measure (\<lambda>(_,i). N - i)"])
      subgoal by blast
      subgoal by blast
      subgoal by fastforce 
      subgoal by(auto simp: replicate_upd_same split: if_splits)
      subgoal by blast
      subgoal by linarith
      subgoal 
        using N_BOUND2 by linarith 
      subgoal by auto
      subgoal by auto
      subgoal by fastforce
      subgoal 
        by (force simp: atLeast0_lessThan_Suc map_update) 
      subgoal by auto
      subgoal for St X1 Tr X2 Br X3 Pr X4 Av X5 Mm Mm1 Mm2
        apply(cases Mm)
        using INV' SUC apply clarsimp
        using atLeast0_lessThan_Suc by presburger
      subgoal using DDEF by fast
      subgoal for St X1 Tr X2 Br X3 Pr X4 Av X5 Mm Mm1 Mm2
        apply(cases Mm)
        using INV' by (auto simp: KD MP)
      subgoal for St X1 Tr X2 Br X3 Pr X4 Av X5 Mm Mm1 Mm2
        apply(cases Mm) by auto
      subgoal for St X1 Tr X2 Br X3 Pr X4 Av X5 Mm Mm1 Mm2
        apply(cases Mm) 
        unfolding MP states_M\<^sub>0_\<alpha>
        using SUC by force
      subgoal for St X1 Tr X2 Br X3 Pr X4 Av X5 Mm Mm1 Mm2
        apply(cases Mm)
        using SUC KD by fastforce
      done

  qed

  lemma(in modest_init_mdp_env_defs) modest_states_nonempty_correct: 
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr), M,D,S,K,Z) \<in> modest_MDSKZ_DS_rel N DS"
    shows "modest_states_nonempty (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) \<longleftrightarrow> op_states_non_empty (M,D,S,K,Z)"
  proof -

    from REL 
      have DP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def
      by(auto simp: in_br_conv modest_mdp_cullable_def.MDSKZ_\<alpha>_def 
        modest_mdp_cullable_def.D_\<alpha>_def modest_mdp_cullable_invar'_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    show ?thesis
      unfolding modest_states_nonempty_def op_antpar_mem_any1_def op_states_non_empty_def
      using Nr_0_empty_iff by auto
  qed

  lemma is_deleted_state_correct:
    assumes IN: "u < N"
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr), M,D,S,K,Z) \<in> modest_MDSKZ_DS_rel N DS"
    shows "is_deleted_state (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) u \<longleftrightarrow> op_deleted_state (M,D,S,K,Z) u"
  proof -
    from REL 
      have DP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def 
      by(auto simp: in_br_conv modest_mdp_cullable_def.MDSKZ_\<alpha>_def 
        modest_mdp_cullable_def.D_\<alpha>_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    show ?thesis 
      unfolding is_deleted_state_def op_deleted_state_def op_antpar_mem_any1_def
      by (auto simp: S_\<alpha>_def IN)
  qed

  lemma expand_capacity_MDP_correct:
    assumes A: "length D + i \<le> N"
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr), M,D,S,K,Z) \<in> modest_MDSKZ_DS_rel N DS"
    shows "RETURN (expand_capacity_MDP (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) i) \<le> \<Down>(modest_MDSKZ_DS_rel N DS) (RETURN (op_expand_capacity (M,D,S,K,Z) i))"
  proof -

    from REL 
      have MP[simp]: "M = modest_mdp_input_def.M\<^sub>0_\<alpha> N St Tr Br Av Ta Pr"
      and  DP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  ZP[simp]: "Z = Av \<union> Ta"
      and DDEF: "DS = (St, Tr, Br, Pr, Av, Ta)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def 
      by(auto simp: in_br_conv modest_mdp_cullable_def.MDSKZ_\<alpha>_def 
        modest_mdp_cullable_def.D_\<alpha>_def modest_mdp_cullable_def.Z_\<alpha>_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    have "S_\<alpha> = modest_mdp_cullable_def.S_\<alpha> N (St, Tr, Br, Pr, Av, Ta, (MmM @ replicate i {}, MmU), Nr)"
      unfolding modest_mdp_cullable_def.S_\<alpha>_def by (auto simp: nth_append) 

    moreover have "K_\<alpha> = modest_mdp_cullable_def.K_\<alpha> N (St, Tr, Br, Pr, Av, Ta, (MmM @ replicate i {}, MmU), Nr)" 
      unfolding modest_mdp_cullable_def.K_\<alpha>_def
      apply(rule ext)
      by (auto simp: nth_append op_antpar_eq_set_mem_def modest_mdp_cullable_def.act_trans_def modest_mdp_cullable_def.is_activated_transition_def 
        split: if_splits)
    moreover have "modest_mdp_cullable_def.Z_\<alpha> (St, Tr, Br, Pr, Av, Ta, (MmM @ replicate i {}, MmU), Nr) = Av \<union> Ta"
      unfolding modest_mdp_cullable_def.Z_\<alpha>_def by auto
    ultimately have AUX: "op_expand_capacity (M, D, S, K, Z) i =
    modest_mdp_cullable_def.MDSKZ_\<alpha> N
     (St, Tr, Br, Pr, Av, Ta, op_antpar_list1_expand (MmM, MmU) i, Nr)"
      unfolding op_expand_capacity_def modest_mdp_cullable_def.MDSKZ_\<alpha>_def
        modest_mdp_cullable_def.D_\<alpha>_def op_antpar_list1_expand_def
      by auto

    show ?thesis
      apply refine_vcg
      unfolding modest_MDSKZ_DS_rel_def
      using A AUX by(auto simp: DDEF D_\<alpha>_def in_br_conv expand_capacity_MDP_def intro!: expand_capacity_MDP_invar [unfolded expand_capacity_MDP_def, simplified])
  qed

  lemma track_sccs_correct:
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr), M,D,S,K,Z) \<in> modest_MDSKZ_DS_rel N DS"
    assumes CN: "length C \<le> N"
    shows "RETURN (track_sccs (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) (C, V)) \<le> \<Down> (modest_MLDSKZ_DS_rel N DS) (mop_track_sccs (M,D,S,K,Z) (C, V))"
  proof -

    from REL 
      have DP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  ZP[simp]: "Z = modest_mdp_cullable_def.Z_\<alpha> (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def 
      by(auto simp: in_br_conv modest_mdp_cullable_def.MDSKZ_\<alpha>_def 
        modest_mdp_cullable_def.D_\<alpha>_def modest_mdp_cullable_invar'_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    from REL have MP: "M = M\<^sub>0_\<alpha>" and DDEF: "DS = (St, Tr, Br, Pr, Av, Ta)"
      unfolding modest_MDSKZ_DS_rel_def by(auto simp: MDSKZ_\<alpha>_def in_br_conv)

    have [simp]: "L_\<alpha> = MmU"
      unfolding L_\<alpha>_def by simp

    have [simp]: "length C \<le> length MmU"
      using CN Mm_len2 N_DEF by auto

    have A: "x \<in> X \<Longrightarrow> X \<in> set MmU \<Longrightarrow> i < length MmM \<Longrightarrow> x \<in> MmM ! i \<Longrightarrow> False" for x X i
      by (metis DS_sel_simps(7) in_set_conv_nth Mm_disj prod.sel)

    have B: "x \<in> X \<Longrightarrow> X \<in> set MmU \<Longrightarrow> x < N" for x X
      using Mm_state2 by auto

    show ?thesis
      unfolding track_sccs_def mop_track_sccs_def modest_mdp_cullable_def.MLDSKZ_\<alpha>_def modest_MLDSKZ_DS_rel_def
      apply refine_vcg
      by(auto simp: DDEF MP pw_le_iff refine_pw_simps in_br_conv INV D_\<alpha>_def S_\<alpha>_def Mm_state2[simplified] intro: A B) 
  qed

  lemma is_deleted_stateL_correct:
    assumes IN: "u < N"
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr),M,L,D,S,K,Z) \<in> modest_MLDSKZ_DS_rel N DS"
    shows "is_deleted_state (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) u \<longleftrightarrow> op_deleted_stateL (M,L,D,S,K,Z) u"
  proof -
    from REL 
      have LP[simp]: "L = MmU" 
      and  MP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv modest_mdp_cullable_def.MLDSKZ_\<alpha>_def modest_mdp_cullable_def.D_\<alpha>_def modest_mdp_cullable_def.L_\<alpha>_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    from REL have "M = M\<^sub>0_\<alpha>"
      unfolding modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv MLDSKZ_\<alpha>_def)

    thus ?thesis 
      unfolding is_deleted_state_def op_deleted_stateL_def op_antpar_mem_any1_def
      by (auto simp: S_\<alpha>_def IN)
  qed

  lemma(in modest_init_mdp_env_defs) mark_as_MEC_correct:
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr), (M,L,D,S,K,Z)) \<in> modest_MLDSKZ_DS_rel N DS"
    assumes US: "u < N"
    assumes IM: "i < length D"
    assumes MN: "length D \<le> N"
    assumes UNM: "u \<notin> \<Union>(set D)"
    shows "mark_as_MEC (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) (C, V) u i \<le> \<Down> (modest_MLDSKZ_DS_rel N DS) (mop_add_state_to_mec (M,L,D,S,K,Z) (C, V) u i)"
  proof -

    from REL 
      have LP[simp]: "L = MmU" 
      and  DP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  ZP[simp]: "Z = modest_mdp_cullable_def.Z_\<alpha> (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv modest_mdp_cullable_def.MLDSKZ_\<alpha>_def modest_mdp_cullable_def.D_\<alpha>_def modest_mdp_cullable_def.L_\<alpha>_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    from REL have MP: "M = M\<^sub>0_\<alpha>" and DDEF: "DS = (St, Tr, Br, Pr, Av, Ta)"
      unfolding modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv MLDSKZ_\<alpha>_def)

    have AUX1: "modest_mdp_cullable_def.D_\<alpha> (St,Tr,Br,Pr,Av,Ta, ((map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)], map (\<lambda>Y. Y - {u}) MmU), Nr - Suc 0)
      = (map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)]"
      by(auto simp: modest_mdp_cullable_def.D_\<alpha>_def)

    have AUX2: "modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta, ((map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)], map (\<lambda>Y. Y - {u}) MmU), Nr - Suc 0)
      = S_\<alpha> - {u}"
      unfolding modest_mdp_cullable_def.S_\<alpha>_def
      using IM by (auto simp: nth_list_update' )

    have AUX3: "modest_mdp_cullable_def.L_\<alpha> (St,Tr,Br,Pr,Av,Ta, ((map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)], map (\<lambda>Y. Y - {u}) MmU), Nr - 1) = map (\<lambda>Y. Y - {u}) L"
      unfolding modest_mdp_cullable_def.L_\<alpha>_def by auto 

    have AUX4: "i < N"
      using IM MN by simp

    have AUXZ: "modest_mdp_cullable_def.Z_\<alpha> (St, Tr, Br, Pr, Av, Ta, ((map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)], map (\<lambda>Y. Y - {u}) MmU), Nr - Suc 0) = Z_\<alpha>"
      unfolding modest_mdp_cullable_def.Z_\<alpha>_def by auto 

    have US0: "u \<in> states M\<^sub>0_\<alpha>"
      using N_DEF states_M\<^sub>0_\<alpha> US by force

    have "\<Union> (set ((map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)])) \<subseteq> \<Union> (set (map (\<lambda>X. X - {u}) MmM)) \<union> insert u (MmM ! i) "
      using set_update_subset_insert by fastforce
    also have "... \<subseteq> insert u (\<Union> (set MmM))"
      using IM nth_mem by auto
    also have "... \<subseteq> states M\<^sub>0_\<alpha>" using Mm1_sub US0 by simp
    finally have AUX5: "\<Union> (set ((map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)])) \<subseteq> states M\<^sub>0_\<alpha>" .

    have USA:"u \<in> S_\<alpha>"
      unfolding S_\<alpha>_def using US apply (auto simp: N_DEF)
      using UNM by force
    hence AUX6: "card (S_\<alpha> - {u}) = Nr - 1" 
      using Nr_S by(simp add: card_Diff_singleton )

    from USA have NR0: "Nr > 0"
      using Nr_0_empty_iff by auto

    have INV': "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta, ((map (\<lambda>X. X - {u}) MmM)[i := insert u (MmM ! i)], map (\<lambda>Y. Y - {u}) MmU), Nr - Suc 0)"
      apply(unfold_locales)
      apply simp_all
      subgoal by (simp add: N_DEF)
      subgoal by (simp add: N0)
      subgoal using AN by simp
      subgoal using TN by simp
      subgoal using AT by simp
      subgoal using St_dom by auto
      subgoal using Tr_dom le_def by auto
      subgoal using Br_dom by auto
      subgoal using Sorted_St by force
      subgoal using Sorted_Tr by force
      subgoal 
        using Pr_lt_one by auto
      subgoal 
        using Pr_gt_zero by simp
      subgoal
        using Len_Pr_Br by simp
      subgoal by (auto simp: AUX2 AUX6)
      subgoal for v using Mm_all_states[of v]
        using IM  
        apply (clarsimp simp: nth_list_update') 
        by (metis DiffI empty_iff insert_iff nth_map)
      subgoal for v using Mm_disj[of v]
        by(auto simp: nth_list_update') 
      subgoal for i j v 
        by (auto simp: nth_list_update' Mm1_disj split: if_splits)
      subgoal for i j v
        using Mm2_disj by force
      subgoal 
        using Mm1_len by auto
      subgoal 
        using Mm2_len by auto
      subgoal using AUX5 by simp
      subgoal 
        using Mm2_sub by auto
      done

    show ?thesis
      unfolding mark_as_MEC_def mop_add_state_to_mec_def op_antpar_move_to_list1_def
        modest_mdp_cullable_def.MLDSKZ_\<alpha>_def modest_MLDSKZ_DS_rel_def
      apply refine_vcg
      using AUX4 apply blast
      using IM by (fastforce simp: DDEF MP NR0 pw_le_iff refine_pw_simps in_br_conv AUX1 AUX2 AUX3 AUXZ INV' modest_mdp_cullable_def.L_\<alpha>_def)
  qed

  lemma(in scc_map_defs) mark_as_unfinished_correct: 
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr), (M,L,D',S,K,Z)) \<in> modest_MLDSKZ_DS_rel N DS"
    assumes US: "u < N"
    and UNM: "u \<notin> \<Union>(set D')"
    and TR: "transfer_to_disjdlt2_pre ((C,D',L), u)"
    shows "mark_as_unfinished (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) (C, V) u \<le> \<Down> (modest_MLDSKZ_DS_rel N DS) (mop_add_state_unfinished (M,L,D',S,K,Z) (C,V) u)"
  proof -
    from REL 
      have LP[simp]: "L = MmU" 
      and  DP[simp]: "D' = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  ZP[simp]: "Z = modest_mdp_cullable_def.Z_\<alpha> (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv modest_mdp_cullable_def.MLDSKZ_\<alpha>_def modest_mdp_cullable_def.D_\<alpha>_def modest_mdp_cullable_def.L_\<alpha>_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    from REL have MP: "M = M\<^sub>0_\<alpha>" and DDEF: "DS = (St, Tr, Br, Pr, Av, Ta)"
      unfolding modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv MLDSKZ_\<alpha>_def)

    hence UMU: "u \<in> \<Union>(set MmU)"
      using Mm_all_states US N_DEF UNM
      by fastforce

    have AUX0: "S_\<alpha> = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta, (map (\<lambda>X. X - {u}) MmM, (map (\<lambda>Y. Y - {u}) MmU)[j := insert u (MmU ! j)]), Nr)"
      for j using UNM by(auto simp: modest_mdp_cullable_def.S_\<alpha>_def)

    have US0: "u \<in> states M\<^sub>0_\<alpha>"
      using N_DEF US states_M\<^sub>0_\<alpha> by force

    {
      fix i
      assume IM: "i < length MmU"
      have "\<Union> (set ((map (\<lambda>X. X - {u}) MmU)[i := insert u (MmU ! i)])) \<subseteq> \<Union> (set (map (\<lambda>X. X - {u}) MmU)) \<union> insert u (MmU ! i) "
        using set_update_subset_insert by fastforce
      also have "... \<subseteq> insert u (\<Union> (set MmU))"
        using IM nth_mem by auto
      also have "... \<subseteq> states M\<^sub>0_\<alpha>" using Mm2_sub US0 by simp
      finally have "\<Union> (set ((map (\<lambda>X. X - {u}) MmU)[i := insert u (MmU ! i)])) \<subseteq> states M\<^sub>0_\<alpha>" .
    } note AUXI = this

    have INV': "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta, (map (\<lambda>X. X - {u}) MmM, (map (\<lambda>Y. Y - {u}) MmU)[j := insert u (MmU ! j)]), Nr)" 
      if "j < length C" "j < length MmU" "u \<in> C ! j" for j
      apply(unfold_locales)
      subgoal by (simp add: N_DEF)
      subgoal by (simp add: N0)
      subgoal using AN by simp
      subgoal using TN by simp
      subgoal using AT by simp
      subgoal using St_dom by auto
      subgoal using Tr_dom le_def by auto
      subgoal using Br_dom by auto
      subgoal using Sorted_St by force
      subgoal using Sorted_Tr by force
      subgoal using Pr_lt_one by simp
      subgoal using Pr_gt_zero by auto
      subgoal using Len_Pr_Br by force 
      subgoal by(auto simp flip: AUX0 Nr_S) 
      subgoal for v 
        using Mm_all_states[of v]
        apply clarsimp
        subgoal
          apply(cases "u=v")
          subgoal
            using that by (auto)
          subgoal
            by(auto simp: nth_list_update' split: if_splits)
          done
        done
      subgoal for v using Mm_disj[of v] by (auto simp: nth_list_update')
      subgoal
        by (auto simp: Mm1_disj)
      subgoal
        by (auto simp: nth_list_update' Mm2_disj split: if_splits)
      subgoal 
        using Mm1_len by auto
      subgoal 
        using Mm2_len by auto
      subgoal using Mm1_sub by auto
      subgoal using AUXI that(2) by simp
      done
      

    have AUX1: "modest_mdp_cullable_def.D_\<alpha> (St,Tr,Br,Pr,Av,Ta, (map (\<lambda>X. X - {u}) MmM, (map (\<lambda>Y. Y - {u}) MmU)[j := insert u (MmU ! j)]), Nr) = map (\<lambda>X. X - {u}) MmM" for j
      by(auto simp: modest_mdp_cullable_def.D_\<alpha>_def)
      
    have AUX2: "modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta, (map (\<lambda>X. X - {u}) MmM, (map (\<lambda>Y. Y - {u}) MmU)[j := insert u (MmU ! j)]), Nr) = S_\<alpha>" for j
      unfolding modest_mdp_cullable_def.S_\<alpha>_def
      using UNM by auto 

    have AUX3: "modest_mdp_cullable_def.L_\<alpha> (St,Tr,Br,Pr,Av,Ta, (map (\<lambda>X. X - {u}) MmM, (map (\<lambda>Y. Y - {u}) MmU)[j := insert u (MmU ! j)]), Nr) 
      = (map (\<lambda>X. X - {u}) MmU)[j := insert u (MmU ! j)]" for j
      unfolding modest_mdp_cullable_def.L_\<alpha>_def
      by auto

    have AUX4: "modest_mdp_cullable_def.Z_\<alpha> (St, Tr, Br, Pr, Av, Ta, (map (\<lambda>X. X - {u}) MmM, (map (\<lambda>Y. Y - {u}) MmU)[i := insert u (MmU ! i)]), Nr)
      = Z_\<alpha>" for i
      unfolding modest_mdp_cullable_def.Z_\<alpha>_def
      by force

    show ?thesis
      unfolding mark_as_unfinished_def mop_add_state_unfinished_def mop_transfer_to_antpar2_def
        modest_MLDSKZ_DS_rel_def modest_mdp_cullable_def.MLDSKZ_\<alpha>_def unfiltered_list_open_block_def
      apply refine_vcg
      using TR
      by (fastforce simp: DDEF MP pw_le_iff refine_pw_simps in_br_conv INV' AUX1 AUX2 AUX3 AUX4)

  qed

  definition "mop_untrack_sccs_pre \<equiv> (\<lambda> ((M,L,D,S,K,Z),(C,V)). \<exists> S\<^sub>1 K\<^sub>1. (S\<^sub>1 = \<Union> (set C)) \<and> scc_list C S\<^sub>1 K\<^sub>1 \<and> set V = {S' \<in> set C. closed_mdp S' K\<^sub>1} \<and> sub_struc_of M S\<^sub>1 K\<^sub>1 \<and> \<Union>(set C) - \<Union>(set V) \<subseteq> S \<and> (\<forall>i < length L. length C \<le> i \<longrightarrow> L ! i = {}) \<and> (\<forall>i < length C. if C ! i \<in> set V then L ! i = {} else L ! i = C ! i))"

  lemma untrack_sccs_correct:
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr),M,L,D,S,K,Z) \<in> modest_MLDSKZ_DS_rel N DS"
    assumes PRE: "mop_untrack_sccs_pre ((M,L,D,S,K,Z),(C,V))"
    shows "RETURN (untrack_sccs (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) (C, V)) \<le> \<Down>(modest_MDSKZ_DS_rel N DS) (mop_untrack_sccs (M,L,D,S,K,Z) (C, V))"
  proof - 
    from PRE obtain S\<^sub>1 K\<^sub>1 
      where SC: "S\<^sub>1 = \<Union> (set C)"
      and SCC: "scc_list C S\<^sub>1 K\<^sub>1"
      and VDEF: "set V = {S' \<in> set C. closed_mdp S' K\<^sub>1}"
      and SUB: "sub_struc_of M S\<^sub>1 K\<^sub>1"
      and SUBO: "\<Union>(set C) - \<Union>(set V) \<subseteq> S"
      and C1: "\<And>i. i < length L \<Longrightarrow> length C \<le> i \<Longrightarrow> L ! i = {}"
      and C2: "\<And>i. i < length C \<Longrightarrow> if C ! i \<in> set V then L ! i = {} else L ! i = C ! i"
    unfolding mop_untrack_sccs_pre_def by auto  

    from REL 
      have LP[simp]: "L = MmU" 
      and  DP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St, Tr, Br, Pr, Av, Ta, (MmM, MmU), Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St, Tr, Br, Pr, Av, Ta, (MmM, MmU), Nr)"
      and  ZP[simp]: "Z = modest_mdp_cullable_def.Z_\<alpha> (St, Tr, Br, Pr, Av, Ta, (MmM, MmU), Nr)"
      and INV: "modest_mdp_cullable_invar' N (St, Tr, Br, Pr, Av, Ta, (MmM, MmU), Nr)"
      unfolding modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv modest_mdp_cullable_def.MLDSKZ_\<alpha>_def modest_mdp_cullable_def.D_\<alpha>_def 
        modest_mdp_cullable_def.L_\<alpha>_def)

    from INV interpret modest_mdp_cullable_invar' N "(St, Tr, Br, Pr, Av, Ta, (MmM, MmU), Nr)" .

    from REL have MP: "M = M\<^sub>0_\<alpha>" and DDEF: "DS = (St, Tr, Br, Pr, Av, Ta)"
      unfolding modest_MLDSKZ_DS_rel_def
      by(auto simp: in_br_conv MLDSKZ_\<alpha>_def)

    have X: "culled_edges C V (K_actions M) K_\<alpha>"
      unfolding MP
      apply(rule culled_edges_K_\<alpha>)
      using SC apply blast 
      subgoal using SUBO by simp
      using SCC apply blast
      using SUB MP apply blast
      using VDEF apply blast
      subgoal using C1 by auto
      subgoal by (auto split: if_splits dest: C2)
      done

    show ?thesis
      unfolding untrack_sccs_def mop_untrack_sccs_def modest_MDSKZ_DS_rel_def
      apply refine_vcg
      using MP X
      by(fastforce simp: DDEF pw_le_iff refine_pw_simps in_br_conv MDSKZ_\<alpha>_def D_\<alpha>_def INV)
  qed

  lemma(in modest_init_mdp_env_defs) modest_get_mecs_correct: 
    assumes REL: "((St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr), M,D,S,K,Z) \<in> modest_MDSKZ_DS_rel N DS"
    assumes MS0: "states M = \<Union> (set D)" 
    assumes NED: "{} \<notin> set D"                                  
    shows "modest_get_mecs (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr) \<le> \<Down>(Id \<times>\<^sub>r modest_mdp_input_DS_rel N DS) (RETURN (op_get_mecs (M,D,S,K,Z)))"
  proof -
    from REL 
      have DP[simp]: "D = MmM"
      and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"

      and INV: "modest_mdp_cullable_invar' N (St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)"
      unfolding modest_MDSKZ_DS_rel_def 
      by(auto simp: in_br_conv modest_mdp_cullable_def.MDSKZ_\<alpha>_def modest_mdp_cullable_def.D_\<alpha>_def)

    from INV interpret modest_mdp_cullable_invar' N "(St,Tr,Br,Pr,Av,Ta,(MmM,MmU),Nr)" .

    from REL have MP: "M = M\<^sub>0_\<alpha>" and DDEF: "DS = (St, Tr, Br, Pr, Av, Ta)"
      unfolding modest_MDSKZ_DS_rel_def
      by(auto simp: in_br_conv MDSKZ_\<alpha>_def)

    have  "\<Union>(set MmM) = {0..<N}"
      using DP MP MS0 states_M\<^sub>0_\<alpha> by argo

    moreover have "{} \<notin> set MmM"
      using NED by auto

    ultimately have AUX1: "op_antpar_to_mec_map_pre N (MmM, MmU)"
      unfolding op_antpar_to_mec_map_pre_def by blast

    have R': "((St,Tr,Br,Pr,Av,Ta), M\<^sub>0_\<alpha>) \<in> modest_mdp_input_DS_rel N DS"
      unfolding modest_mdp_input_DS_rel_def using INV
      by(auto simp: DDEF in_br_conv modest_mdp_cullable_invar'_def)      

    show ?thesis
      unfolding modest_get_mecs_def op_get_mecs_def
      apply(refine_vcg)
      subgoal using AUX1 by blast
      subgoal unfolding op_antpar_to_mec_map_def
        using R' MP by auto 
      done
  qed

  lemma(in modest_init_mdp_env_defs) mop_modest_iterate_succs_eq_scc_refine: "(uncurry2 mop_modest_iterate_succs_eq_scc, uncurry2 (RETURN ooo op_all_succ_eq_map)) \<in> [\<lambda> (((M,D,S,K,Z),(C,V)), u). u \<in> S \<and> scc_list C S K]\<^sub>f (modest_MDSKZ_DS_rel N DS \<times>\<^sub>r Id) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    by(auto intro!: frefI nres_relI modest_iterate_succs_eq_scc_correct)

  lemma(in modest_init_mdp_env) modest_init_mdp_refine: "(modest_init_mdp, mop_init_mdp) \<in> modest_mdp_input_DS_rel N DS \<rightarrow> \<langle>modest_MDSKZ_DS_rel N DS\<rangle>nres_rel"
    by(auto intro!: frefI nres_relI modest_init_mdp_correct)

  lemma(in modest_init_mdp_env_defs) modest_states_nonempty_refine: "((RETURN o modest_states_nonempty), (RETURN o op_states_non_empty)) \<in> modest_MDSKZ_DS_rel N DS \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    apply refine_vcg
    apply auto
    using modest_states_nonempty_correct
    by auto

  lemma is_deleted_state_refine: "(uncurry (RETURN oo is_deleted_state), uncurry (RETURN oo op_deleted_state)) \<in> [\<lambda> ((M,S,K),i). i < N]\<^sub>f modest_MDSKZ_DS_rel N DS \<times>\<^sub>r nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    apply(rule frefI)
    apply refine_vcg
    by(auto simp: in_br_conv is_deleted_state_correct)


  definition "expand_capacity_MDP_pre N = (\<lambda> ((M,D,S,K,Z),i). length D + i \<le> N)"
  lemma expand_capacity_MDP_refine: 
    "(uncurry expand_capacity_MDP, uncurry op_expand_capacity) \<in> [expand_capacity_MDP_pre N]\<^sub>f modest_MDSKZ_DS_rel N DS \<times>\<^sub>r nat_rel \<rightarrow> modest_MDSKZ_DS_rel N DS"
    apply(rule frefI)
    unfolding expand_capacity_MDP_pre_def
    using expand_capacity_MDP_correct
    apply clarsimp
    by (metis modest_MDSKZ_DS_rel_DS_eq)


  lemma get_mec_num_MDP_refine: "(get_mec_num_MDP, op_get_mec_num) \<in> modest_MDSKZ_DS_rel N DS \<rightarrow> nat_rel"
    unfolding modest_MDSKZ_DS_rel_def get_mec_num_MDP_def op_get_mec_num_def
    apply refine_vcg
    by(auto simp: in_br_conv op_antpar_list1_count_def modest_mdp_cullable_def.MDSKZ_\<alpha>_def modest_mdp_cullable_def.D_\<alpha>_def)

  lemma is_deleted_stateL_refine: "(uncurry (RETURN oo is_deleted_state), uncurry (RETURN oo op_deleted_stateL)) \<in> [\<lambda> ((L,M,S,K),i). i < N]\<^sub>f modest_MLDSKZ_DS_rel N DS \<times>\<^sub>r nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    apply(rule frefI)
    apply refine_vcg
    by(auto simp: in_br_conv is_deleted_stateL_correct)

  lemma track_sccs_refine: "(uncurry (RETURN oo track_sccs), uncurry mop_track_sccs) \<in> [\<lambda> ((M,S,K),C,V). length C \<le> N]\<^sub>f (modest_MDSKZ_DS_rel N DS \<times>\<^sub>r Id) \<rightarrow> \<langle>modest_MLDSKZ_DS_rel N DS\<rangle>nres_rel"
    apply (rule frefI)
    apply refine_vcg
    by (auto intro!: track_sccs_correct)
                                                                                                                                                              
  lemma(in modest_init_mdp_env_defs) mark_as_MEC_refine: "(uncurry3 mark_as_MEC, uncurry3 mop_add_state_to_mec) \<in> [\<lambda> ((((M,L,D,S,K,Z),(C,V)),u),i). u < N \<and> u \<notin> \<Union>(set D) \<and> i < length D \<and> length D \<le> N]\<^sub>f ((modest_MLDSKZ_DS_rel N DS \<times>\<^sub>r Id) \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>modest_MLDSKZ_DS_rel N DS\<rangle>nres_rel"
    apply (rule frefI)
    apply refine_vcg
    by (force intro!: mark_as_MEC_correct)

  lemma(in scc_map_defs) mark_as_unfinished_refine: "(uncurry2 mark_as_unfinished, uncurry2 mop_add_state_unfinished) \<in> [\<lambda> (((M,L,D,S,K,Z),(C,V)),u). u < N \<and> u \<notin> \<Union>(set D) \<and> transfer_to_disjdlt2_pre ((C,D,L), u)]\<^sub>f (modest_MLDSKZ_DS_rel N DS \<times>\<^sub>r Id) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>modest_MLDSKZ_DS_rel N DS\<rangle>nres_rel"
    apply (rule frefI)                                    
    apply(refine_vcg)
    by (force intro!: mark_as_unfinished_correct)

  lemma untrack_sccs_refine: "(uncurry (RETURN oo untrack_sccs), uncurry mop_untrack_sccs) \<in> [mop_untrack_sccs_pre]\<^sub>f (modest_MLDSKZ_DS_rel N DS \<times>\<^sub>r Id) \<rightarrow> \<langle>modest_MDSKZ_DS_rel N DS\<rangle>nres_rel"
    apply (rule frefI)                                    
    apply(refine_vcg)
    by (auto intro!: untrack_sccs_correct)

  definition "op_get_mecs_pre = (\<lambda> (M,D,S,K,Z). \<Union>(set D) = states M \<and> {} \<notin> set D)"
  lemma(in modest_init_mdp_env_defs) modest_get_mecs_refine: "(modest_get_mecs, RETURN o op_get_mecs) \<in> [op_get_mecs_pre]\<^sub>f modest_MDSKZ_DS_rel N DS \<rightarrow> \<langle>Id \<times>\<^sub>r modest_mdp_input_DS_rel N DS\<rangle>nres_rel"
    by(auto intro!: nres_relI frefI simp: in_br_conv modest_get_mecs_correct op_get_mecs_pre_def)


  context modest_init_mdp_env
  begin
  
    interpretation scc_map N N ni
      apply(unfold_locales)
      apply (simp add: n_impl)
      using N_BOUND apply simp
      done
  
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using op_list_length_unbounded .
  
    lemma modest_init_mdp_ll_aux1: "[] = (replicate N {})[0 := {0..<x}] \<Longrightarrow> N = 0"
      by (metis list_update_nonempty replicate_empty)

    sepref_definition mop_modest_activated_transition_in_scc_ll is "uncurry3 (PR_CONST mop_modest_activated_transition_in_scc)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a filter_set_assn\<^sup>k *\<^sub>a node_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_activated_transition_in_scc_def PR_CONST_def
      supply[elim] = modest_mdp_assn_boundsD(1)[THEN less_trans[rotated]]
      apply sepref
      done
  
    concrete_definition (in -) mop_modest_activated_transition_in_scc_ll' [llvm_code] is modest_init_mdp_env.mop_modest_activated_transition_in_scc_ll_def
    lemmas [sepref_fr_rules] = mop_modest_activated_transition_in_scc_ll.refine[unfolded mop_modest_activated_transition_in_scc_ll'.refine[OF modest_init_mdp_env_axioms]]
  
    interpretation scc_map N N ni
      apply(unfold_locales)
      apply (simp add: n_impl)
      using N_BOUND apply simp
      done
  
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using op_list_length_unbounded .
  
    sepref_definition mop_modest_iterate_succs_eq_scc_ll is "uncurry2 mop_modest_iterate_succs_eq_scc" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a filter_set_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding mop_modest_iterate_succs_eq_scc_def
      supply [dest] = modest_mdp_assn_boundsD (*NOTE this should work without adding it as a dest rule*)
      by sepref
  
    definition "expand_capacity_MDP_ll_pre = (\<lambda>((St,Tr,Br,Pr,Av,Ta,Mm,Nr),i). length (fst Mm) + i \<le> N)"

    abbreviation "mdpi_peq \<equiv> \<lambda>(St',Tr',Br',Pr',Av',Ta',_) (St,Tr,Br,Pr,Av,Ta, _). 
      St'=St \<and> Tr'=Tr \<and> Br'=Br \<and> Pr'=Pr \<and> Av'=Av \<and> Ta' = Ta"  
      
    abbreviation "mdp_peq_imdp \<equiv> \<lambda>(St',Tr',Br',Pr',Av',Ta', _) (St,Tr,Br,Pr,Av,Ta).
      St'=St \<and> Tr'=Tr \<and> Br'=Br \<and> Pr'=Pr \<and> Av'=Av \<and> Ta'=Ta"  
  
    abbreviation "imdp_peq_mdp \<equiv> \<lambda>(St',Tr',Br',Pr',Av',Ta') (St,Tr,Br,Pr,Av,Ta, _).
      St'=St \<and> Tr'=Tr \<and> Br'=Br \<and> Pr'=Pr \<and> Av'=Av \<and> Ta'=Ta"  
          
    sepref_definition modest_init_mdp_ll is modest_init_mdp :: 
      "[\<lambda>_. True]\<^sub>c Modest_mdp_assn_aux\<^sup>d \<rightarrow> modest_mdp_assn_aux [\<lambda>x x'. mdp_peq_imdp x' x]\<^sub>c"
      unfolding modest_init_mdp_def Modest_mdp_assn_aux_def modest_mdp_assn_aux_def
      apply (annot_snat_const "TYPE(size_T)")
      supply [simp] = op_antpar_empty_def N_BOUND2
      supply[dest] = modest_init_mdp_ll_aux1
      apply sepref
      done
  
    sepref_definition modest_states_nonempty_ll is "(RETURN o modest_states_nonempty)" :: "modest_mdp_assn_aux\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding modest_states_nonempty_def modest_mdp_assn_aux_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref
      done
  
    
    sepref_definition expand_capacity_MDP_ll is "uncurry (RETURN oo expand_capacity_MDP)" 
      :: "[expand_capacity_MDP_ll_pre]\<^sub>a [\<lambda>_. True]\<^sub>c modest_mdp_assn_aux\<^sup>d *\<^sub>a size_assn\<^sup>k 
        \<rightarrow>\<^sub>d (\<lambda>_. modest_mdp_assn_aux) [\<lambda>(x,_) x'. mdpi_peq x' x]\<^sub>c"
      unfolding expand_capacity_MDP_def modest_mdp_assn_aux_def expand_capacity_MDP_ll_pre_def
      apply sepref
      done
  
    sepref_definition get_mec_num_MDP_ll is "RETURN o get_mec_num_MDP" :: "modest_mdp_assn_aux\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding get_mec_num_MDP_def modest_mdp_assn_aux_def
      apply sepref
      done
  
    sepref_definition track_sccs_ll is "uncurry (RETURN oo track_sccs)" 
      :: "[\<lambda>_. True]\<^sub>c modest_mdp_assn_aux\<^sup>d *\<^sub>a filter_list_assn\<^sup>k \<rightarrow> modest_mdp_assn_aux [\<lambda>(x,_) x'. mdpi_peq x' x]\<^sub>c"
      unfolding track_sccs_def modest_mdp_assn_aux_def filter_list_assn_def
      apply sepref
      done
  
    sepref_definition is_deleted_state_ll is "uncurry (RETURN oo is_deleted_state)" :: "modest_mdp_assn_aux\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding is_deleted_state_def modest_mdp_assn_aux_def
      apply sepref
      done
  
    
    sepref_definition mark_as_MEC_ll is "uncurry3 mark_as_MEC" 
      :: "[\<lambda>_. True]\<^sub>c modest_mdp_assn_aux\<^sup>d *\<^sub>a filter_list_assn\<^sup>k *\<^sub>a node_assn\<^sup>k *\<^sub>a (b_assn size_assn (\<lambda> i. i < N))\<^sup>k 
          \<rightarrow> modest_mdp_assn_aux [\<lambda>(((x,_),_),_) x'. mdpi_peq x' x]\<^sub>c"
      unfolding mark_as_MEC_def modest_mdp_assn_aux_def
      apply (annot_snat_const "TYPE(size_T)")
      apply sepref    
      done
  
    sepref_definition mark_as_unfinished_ll is "uncurry2 mark_as_unfinished" 
      :: "[\<lambda>_. True]\<^sub>c modest_mdp_assn_aux\<^sup>d *\<^sub>a filter_list_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow> modest_mdp_assn_aux [\<lambda>((x,_),_) x'. mdpi_peq x' x]\<^sub>c"
      unfolding mark_as_unfinished_def modest_mdp_assn_aux_def
      apply sepref
      done
  
    sepref_definition untrack_sccs_ll is "uncurry (RETURN oo untrack_sccs)" 
      :: "[\<lambda>_. True]\<^sub>c modest_mdp_assn_aux\<^sup>d *\<^sub>a filter_list_assn\<^sup>k \<rightarrow> modest_mdp_assn_aux [\<lambda>(x,_) x'. mdpi_peq x' x]\<^sub>c"
      unfolding untrack_sccs_def modest_mdp_assn_aux_def filter_list_assn_def
      apply sepref
      done
  
    interpretation disj_set_list_tuple_env N N ni ni
      apply(unfold_locales)
      using n_impl by presburger
  
  
    sepref_definition modest_get_mecs_ll is "modest_get_mecs" 
      :: "[\<lambda>_. True]\<^sub>c modest_mdp_assn_aux\<^sup>d \<rightarrow> mec_map_assn \<times>\<^sub>a Modest_mdp_assn_aux [\<lambda>x (_,x'). imdp_peq_mdp x' x]\<^sub>c"
      unfolding modest_get_mecs_def modest_mdp_assn_aux_def Modest_mdp_assn_aux_def
      apply sepref
      done
  
    lemma fcomp_aux1: "tcomp_pre (\<lambda>((M,D,S,K,Z), C, V). f M D S K C V) (modest_MDSKZ_DS_rel N DS \<times>\<^sub>r Id) (\<lambda>_. True) = (\<lambda>((M,D,S,K,Z),C,V). f M D S K C V)"
      unfolding tcomp_pre_def by auto
    lemma fcomp_aux2: "tcomp_pre (\<lambda>(((M,D,S,K,Z), C, V), u). f M D S K C V u) ((modest_MDSKZ_DS_rel N DS \<times>\<^sub>r Id) \<times>\<^sub>r nat_rel) (\<lambda>_. True) = (\<lambda>(((M,D,S,K,Z), C, V), u). f M D S K C V u)"
      unfolding tcomp_pre_def by auto
    lemma fcomp_aux3: "tcomp_pre (\<lambda>((((M,L,D,S,K,Z), C, V),u),i). f L M D S K C V u i) (((modest_MLDSKZ_rel N DS \<times>\<^sub>r Id) \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) (\<lambda>_. True) = (\<lambda>((((M,L,D,S,K,Z), C, V),u),i). f L M D S K C V u i)"
      unfolding tcomp_pre_def by auto
    lemma fcomp_aux4: "tcomp_pre (\<lambda>(((M,L,D,S,K,Z), C, V),u). f L M D S K C V u) ((modest_MLDSKZ_rel N DS \<times>\<^sub>r Id) \<times>\<^sub>r nat_rel) (\<lambda>_. True) = (\<lambda>(((M,L,D,S,K,Z), C, V),u). f L M D S K C V u )"
      unfolding tcomp_pre_def by auto
    lemma fcomp_aux5: "tcomp_pre (\<lambda>((M,L,D,S,K,Z), C, V). f L M D S K C V) (modest_MLDSKZ_rel N DS \<times>\<^sub>r Id) (\<lambda>_. True) = (\<lambda>((M,L,D,S,K,Z), C, V). f L M D S K C V)"
      unfolding tcomp_pre_def by auto
    
    lemma expand_capacity_MDP_aux: "\<And>ac ad ae af ag ah ai bb bc bd.
           ((ac, ad, ae, af, ag, ah, (ai, bb), bc), a, aa, ab, b,c) \<in> modest_MDSKZ_DS_rel N DS \<Longrightarrow>
           bd = ba \<Longrightarrow>
           expand_capacity_MDP_pre N ((a, aa, ab, b,c), ba) \<Longrightarrow>
           expand_capacity_MDP_ll_pre ((ac, ad, ae, af, ag, ah, (ai, bb), bc), ba) "
      unfolding expand_capacity_MDP_pre_def expand_capacity_MDP_ll_pre_def
      by(auto simp: modest_MDSKZ_DS_rel_def br_def modest_mdp_cullable_def.MDSKZ_\<alpha>_def modest_mdp_cullable_def.D_\<alpha>_def)

  
    context
      notes[simp] = expand_capacity_MDP_aux
      notes [fcomp_norm_unfold] = modest_MDSKZ_DS_assn_def[symmetric] modest_MLDSKZ_DS_assn_def[symmetric] Modest_MDP_assn_def[symmetric] Modest_MDP_DS_assn_def[symmetric]
    begin
  
      lemmas modest_init_mdp_hnr =  modest_init_mdp_ll.refine[FCOMP modest_init_mdp_refine]
      lemmas modest_states_nonempty_hnr = modest_states_nonempty_ll.refine[FCOMP modest_states_nonempty_refine]
      lemmas is_deleted_state_hnr = is_deleted_state_ll.refine[FCOMP is_deleted_state_refine[where ?N=N]]
      lemmas expand_capacity_MDP_hnr = expand_capacity_MDP_ll.refine[FCOMP expand_capacity_MDP_refine[where ?N=N]]
      lemmas get_mec_num_MDP_hnr =  get_mec_num_MDP_ll.refine[FCOMP get_mec_num_MDP_refine[where?N = N]]
      lemmas is_deleted_stateL_hnr = is_deleted_state_ll.refine[FCOMP is_deleted_stateL_refine[where ?N=N]]
    
      (*TODO: Make this work with FCOMP by making dedicated precondition predicates*)
      lemmas mop_modest_iterate_succs_eq_scc_hnr = hfcomp_tcomp_pre[OF mop_modest_iterate_succs_eq_scc_refine mop_modest_iterate_succs_eq_scc_ll.refine, unfolded hrp_comp_dest hrp_comp_keep prod_hrp_comp hrr_comp_nondep fcomp_aux2 hr_comp_Id2, folded modest_MDSKZ_DS_assn_def modest_MLDSKZ_DS_assn_def] 
      lemmas track_sccs_hnr = hfcomp_tcomp_pre[OF track_sccs_refine[where ?N=N] track_sccs_ll.refine, unfolded hrp_comp_dest hrp_comp_keep prod_hrp_comp hrr_comp_nondep fcomp_aux1 hr_comp_Id2, folded modest_MDSKZ_DS_assn_def modest_MLDSKZ_DS_assn_def] 
      lemmas mark_as_MEC_hnr = hfcomp_tcomp_pre[OF mark_as_MEC_refine mark_as_MEC_ll.refine, unfolded hrp_comp_dest hrp_comp_keep prod_hrp_comp hrr_comp_nondep fcomp_aux3 hr_comp_Id2, folded modest_MDSKZ_DS_assn_def modest_MLDSKZ_DS_assn_def] 
      lemmas mark_as_unfinished_hnr = hfcomp_tcomp_pre[OF mark_as_unfinished_refine mark_as_unfinished_ll.refine, unfolded hrp_comp_dest hrp_comp_keep prod_hrp_comp hrr_comp_nondep fcomp_aux4 hr_comp_Id2, folded modest_MDSKZ_DS_assn_def modest_MLDSKZ_DS_assn_def] 
    
    end                                                                             
  
  end
  
 
  context modest_init_mdp_env
  begin
  
    interpretation scc_map N N ni
      apply(unfold_locales)
      apply (simp add: n_impl)
      using N_BOUND apply simp
      done
  
    interpretation filter_index_env output_assn get_output_size_impl_ll
      apply(unfold_locales)
      using op_list_length_unbounded .
  
    interpretation disj_set_list_tuple_defs N N ni ni .
  
    context
      notes [simp] = expand_capacity_MDP_aux
      notes [fcomp_norm_unfold] = modest_MDSKZ_DS_assn_def[symmetric] modest_MLDSKZ_DS_assn_def[symmetric] Modest_MDP_DS_assn_def[symmetric]
    begin
      (*TODO: same problem here*)
      lemmas untrack_sccs_hnr = hfcomp_tcomp_pre[OF untrack_sccs_refine[where ?N=N] untrack_sccs_ll.refine, unfolded hrp_comp_dest hrp_comp_keep prod_hrp_comp hrr_comp_nondep fcomp_aux5 hr_comp_Id2, folded modest_MDSKZ_DS_assn_def modest_MLDSKZ_DS_assn_def] 
      lemmas modest_get_mecs_hnr = modest_get_mecs_ll.refine[FCOMP modest_get_mecs_refine]
  
    end
  
  end


  section \<open>Strongly Connected Components\<close>


  subsection \<open>Sepref Abstract Conversion\<close>

  definition "K_to_Succ K = (\<lambda>u. \<Union>(K u))"

  definition "K_deadlock Z K = (\<lambda>u. if u \<in> Z then {} else K u)"

  
  lemma K_deadlock_eq_edges: "(\<And>u. u \<in> Z \<Longrightarrow> K u \<subseteq> {u}) \<Longrightarrow> (mdp_graph_defs.E_\<alpha> (S, K_deadlock Z K))\<^sup>* = (mdp_graph_defs.E_\<alpha> (S, K))\<^sup>*"
  proof(safe)
    fix u v
    assume "(u, v) \<in> (mdp_graph_defs.E_\<alpha> (S, K_deadlock Z K))\<^sup>*"
    thus "(u, v) \<in> (mdp_graph_defs.E_\<alpha> (S, K))\<^sup>*"
      apply(induction rule: rtrancl.induct) 
      apply (fastforce simp: K_deadlock_def mdp_graph_defs.E_\<alpha>_def elim!: rtrancl.rtrancl_into_rtrancl split: if_splits)+
      done
  next
    fix u v
    assume A: "(\<And>u. u \<in> Z \<Longrightarrow> K u \<subseteq> {u})" and B: "(u, v) \<in> (mdp_graph_defs.E_\<alpha> (S, K))\<^sup>*"

    show "(u, v) \<in> (mdp_graph_defs.E_\<alpha> (S, K_deadlock Z K))\<^sup>*"
    using B
    proof(induction rule: rtrancl.induct)
      case (rtrancl_refl a)
      then show ?case by auto
    next
      case (rtrancl_into_rtrancl u v w)
      then show ?case 
      proof(cases "v \<in> Z")
        case True
        with A have "v = w"
          using rtrancl_into_rtrancl.hyps(2)
          unfolding mdp_graph_defs.E_\<alpha>_def by auto
        then show ?thesis using rtrancl_into_rtrancl 
          by auto
      next
        case False
        then show ?thesis 
          using rtrancl_into_rtrancl 
          by (force simp: K_deadlock_def mdp_graph_defs.E_\<alpha>_def elim!: rtrancl.intros(2) split: if_splits)
      qed
    qed 
  qed


  definition "rem_K_sinks K K' \<equiv> (\<forall>u. K' u \<subseteq> K u) \<and> (\<forall>u. K u \<noteq> {u} \<longrightarrow> K' u = K u)"
  

  lemma rem_K_sinksI: "(\<And>u a. a \<in> K' u \<Longrightarrow> a \<in> K u) \<Longrightarrow> (\<And>u. K u \<noteq> {u} \<Longrightarrow> K' u = K u) \<Longrightarrow> rem_K_sinks K K'"
    unfolding rem_K_sinks_def by blast

  lemma rem_K_sinks_eq: "rem_K_sinks K K' \<Longrightarrow> K u \<noteq> {u} \<Longrightarrow> K' u = K u"
    unfolding rem_K_sinks_def by presburger

  lemma rem_K_sinks_self_loop_cases: "rem_K_sinks K K' \<Longrightarrow> K u = {u} \<Longrightarrow> (K' u = {} \<Longrightarrow> P) \<Longrightarrow> (K' u = {u} \<Longrightarrow> P) \<Longrightarrow> P"
    unfolding rem_K_sinks_def by fast


  definition "rem_E_loops E E' \<equiv> E' \<subseteq> E \<and> (\<forall> (u,v) \<in> E. u \<noteq> v \<longrightarrow> (u,v) \<in> E')"
  
  lemma rem_E_loopsI: "(\<And>u v. (u,v) \<in> E' \<Longrightarrow> (u,v) \<in> E) \<Longrightarrow> (\<And>u v. (u,v) \<in> E \<Longrightarrow> u \<noteq> v \<Longrightarrow> (u,v) \<in> E') \<Longrightarrow> rem_E_loops E E'"
    unfolding rem_E_loops_def by fast

  lemma rem_E_loops_sub: "rem_E_loops E E' \<Longrightarrow> (u,v) \<in> E' \<Longrightarrow> (u,v) \<in> E"
    unfolding rem_E_loops_def
    by blast

  lemma rem_E_loops_eq: "rem_E_loops E E' \<Longrightarrow> (u,v) \<in> E \<Longrightarrow> u \<noteq> v \<Longrightarrow> (u,v) \<in> E'"
    unfolding rem_E_loops_def by fast

  lemma rem_E_loops_self_loop_cases: "rem_E_loops E E' \<Longrightarrow> E `` {u} = {u} \<Longrightarrow> (E' `` {u} = {} \<Longrightarrow> P) \<Longrightarrow> (E' `` {u} = {u} \<Longrightarrow> P) \<Longrightarrow> P"
    unfolding rem_E_loops_def by fast

  lemma rem_K_sinks_E_loops: "rem_K_sinks K K' \<Longrightarrow> rem_E_loops (mdp_graph_defs.E_\<alpha> (S',K)) (mdp_graph_defs.E_\<alpha> (S',K'))"
    unfolding rem_K_sinks_def rem_E_loops_def mdp_graph_defs.E_\<alpha>_def 
    subgoal
      apply(rule conjI)
      apply fastforce
      apply clarsimp_all 
      apply rotate_tac
      subgoal for u v
        apply(erule allE[where x=u])
        by fast
      done
    done

  lemma rem_E_loops_rtrancl_eq: "rem_E_loops E E' \<Longrightarrow> E\<^sup>* = E'\<^sup>*"
    unfolding rem_E_loops_def
    apply(safe)
    subgoal for u v
      apply(rotate_tac 2)
      by(induction rule: rtrancl.induct; auto)
    subgoal for u v
      apply(rotate_tac 2)
      by(induction rule: rtrancl.induct; auto)
    done      

  lemmas rem_E_loops_eq_scc = rem_E_loops_rtrancl_eq[THEN rtrancl_eq_scc]

  lemma rem_K_sinks_K_to_succ: "rem_K_sinks (K_to_Succ (modest_mdp_cullable_def.K_\<alpha> N DS)) (modest_mdp_cullable_def.K_\<alpha>' N DS)"
    apply(rule rem_K_sinksI)
    subgoal 
      unfolding K_to_Succ_def modest_mdp_cullable_def.K_\<alpha>_def modest_mdp_cullable_def.K_\<alpha>'_def
      by (auto simp: modest_mdp_input_struc_def.Cm_def split: if_splits)
    subgoal
      unfolding K_to_Succ_def modest_mdp_cullable_def.K_\<alpha>_def modest_mdp_cullable_def.K_\<alpha>'_def
      by (auto simp: modest_mdp_input_struc_def.Cm_def)
    done



  context modest_mdp_cullable_def begin

    abbreviation "E_\<alpha>m \<equiv> mdp_graph_defs.E_\<alpha> (S_\<alpha>,K_\<alpha>')"


    lemma(in modest_mdp_cullable_invar') E_\<alpha>_closed: "u \<in> S_\<alpha> \<Longrightarrow> (u,v) \<in> E_\<alpha>m \<Longrightarrow> v \<in> S_\<alpha>"
      unfolding mdp_graph_defs.E_\<alpha>_def S_\<alpha>_def
      apply clarsimp
      apply(rule conjI)
      subgoal 
        apply (auto simp: K_\<alpha>'_def split: if_splits dest: is_activated_transitionD1 intro!: Br_in_bound Br_in_bound_intvD Tr_in_bound_intvD)
        done
      subgoal for Mm1 Mm2
        apply(clarsimp simp: K_\<alpha>'_def split: if_splits)
        subgoal for t b i
          apply(erule is_activated_transitionE)
          unfolding op_antpar_eq_set_mem_def
          by simp
        done
      done

    lemma(in modest_mdp_cullable_invar') Modest_Gabow_SCC_pre_MDSKZ: 
      "Modest_Gabow_SCC_pre N SK_\<alpha>"
      unfolding Modest_Gabow_SCC_pre_def SK_\<alpha>_def
      by (clarsimp split: prod.splits simp: S_\<alpha>D1)
  
  end

  lemma hr_comp_alt_rel: "(\<And>x. (x, x1) \<in> R1 \<Longrightarrow> (x, x2) \<in> R2) \<Longrightarrow> hr_comp A R1 x1 y \<turnstile> hr_comp A R2 x2 y"
    unfolding hr_comp_def entails_def 
    by (auto simp: sep_algebra_simps) 


  lemma hr_comp_alt_rel_exs: 
    assumes A: "(\<And>x. (x, x1) \<in> R1 \<Longrightarrow> \<exists>x2. (x, x2) \<in> R2)"
    shows "hr_comp A R1 x1 y \<turnstile> (EXS x2. hr_comp A R2 x2 y)"
    unfolding hr_comp_def entails_def 
    by (auto simp: sep_algebra_simps dest!: A)  

  lemma pure_part_mono: "pure_part P \<Longrightarrow> P \<turnstile> Q \<Longrightarrow> pure_part Q"
    unfolding pure_part_def entails_def
    by auto

  lemma pure_part_hr_comp_eq: "pure_part (hr_comp A R x xi) \<longleftrightarrow> (\<exists>s x'. (x', x) \<in> R \<and> A x' xi s)"
    unfolding pure_part_def hr_comp_def by(auto simp: sep_algebra_simps)

  \<comment> \<open>This is a workaround for composed assertions. When changing the assertion on the abstract level
    but not on the concrete level, it is necessary to keep track of the intermediate representation,
    which otherwise gets lost. The workaround fixes the relations to one specific arbitrary intermediate
    representation which can later be converted to an assertion on all intermediate representations.\<close>
  lemma hr_comp_entails_unique_dom: "pure_part (hr_comp A R\<^sub>1 a\<^sub>1 c) \<Longrightarrow> (\<And> a b. a \<in> Domain R\<^sub>1 \<Longrightarrow> b \<in> Domain R\<^sub>2 \<Longrightarrow> a = b) \<Longrightarrow> hr_comp A R\<^sub>2 a\<^sub>2 c \<turnstile> hr_comp A R\<^sub>1 a\<^sub>1 c"
    unfolding hr_comp_def
    apply (rule entails_exE2)
    by (force simp: sep_algebra_simps entails_def pure_part_def hr_comp_def)

  (*TODO, move these lemmas to general theory file*)
  lemma Domain_br [simp]: "x \<in> Domain (br \<alpha> I) = I x"
    unfolding br_def by auto

  lemma Domain_modest_MDSKZ_DS_rel_eq_invar: "(St, Tr, Br, Pr, Av, Ta, Mm, Nr) \<in> Domain (modest_MDSKZ_DSC_rel N DS DSC) \<longleftrightarrow> modest_mdp_cullable_invar N DSC (St, Tr, Br, Pr, Av, Ta, Mm, Nr) \<and> DS = (St, Tr, Br, Pr, Av, Ta)"
    unfolding modest_MDSKZ_DSC_rel_def by auto

  lemma Domain_modest_MDSKZ_DS_rel_alt: "modest_mdp_cullable_invar N DS' DS \<Longrightarrow> Domain (modest_mdp_succ_DS_rel N DS') = {DS}"
    by (auto simp: in_br_conv modest_mdp_succ_rel_alt modest_mdp_succ_DS_rel_def
      modest_mdp_cullable_invar_def modest_mdp_cullable_invar_axioms_def)

  lemmas conj_entails_mono1 = conj_entails_mono[OF entails_refl]
  lemmas conj_entails_mono2 = conj_entails_mono[OF _ entails_refl]

  lemma hn_refine_cons_post':
    assumes R: "hn_refine P c Q R CP m"
    assumes I: "pure_part P \<Longrightarrow> Q\<turnstile>Q'"
    shows "hn_refine P c Q' R CP m"
    apply(cases "Ex P")
    subgoal
      using assms
      apply (rule hn_refine_cons[OF entails_refl _ _ entails_refl])
      unfolding pure_part_def by blast
    subgoal
      by(auto intro: hn_refine_preI)
    done

  context modest_init_mdp_env_defs
  begin

    definition "mec_to_scc_block = (\<lambda>(M,D,S,K,Z) f. f (S,K_deadlock Z (K_to_Succ K)))"


    lemma pure_part_hr_comp_eq: "pure_part (hr_comp A R x xi) \<longleftrightarrow> (\<exists>s x'. (x', x) \<in> R \<and> A x' xi s)"
      unfolding pure_part_def hr_comp_def by(auto simp: sep_algebra_simps)


    lemma modest_MDSKZ_to_succ_rel: 
      assumes REL: "(DSC', M, D, S, K, Z) \<in> modest_MDSKZ_DSC_rel N DS DSC"
      shows "(DSC', S, K_deadlock Z (K_to_Succ K)) \<in> modest_mdp_succ_DS_rel N DSC"
    proof -

      from REL 
        have DP[simp]: "D = modest_mdp_cullable_def.D_\<alpha> DSC"
        and  SP[simp]: "S = modest_mdp_cullable_def.S_\<alpha> N DSC"
        and  KP[simp]: "K = modest_mdp_cullable_def.K_\<alpha> N DSC"
        and  ZP[simp]: "Z = modest_mdp_cullable_def.Z_\<alpha> DSC"
        and INV: "modest_mdp_cullable_invar N DSC DSC'"
        using modest_MDSKZ_DSC_rel_DS_eq[OF REL]
        unfolding modest_MDSKZ_DSC_rel_def modest_mdp_cullable_def.MDSKZ_\<alpha>_def
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_cullable_invar N DSC DSC' .

      note [simp] = DS_DEF

      have "K_deadlock Z_\<alpha> (K_to_Succ K_\<alpha>) = K_\<alpha>'"
        unfolding K_deadlock_def Z_\<alpha>_def K_to_Succ_def K_\<alpha>'_def K_\<alpha>_def
        apply(rule ext)
        by (auto simp: Cm_def)


      thus ?thesis
        unfolding modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def
        using INV by (auto simp: in_br_conv)
    qed


    lemma mdp_succ_ent_MDSKZ: "pure_part (modest_MDSKZ_DSC_assn DS DSC (M,D,S,K,Z) ss) 
      \<Longrightarrow> modest_mdp_succ_DS_assn DSC (S, K_deadlock Z (K_to_Succ K)) ss 
      \<turnstile> modest_MDSKZ_DSC_assn DS DSC (M,D,S,K,Z) ss"
      unfolding modest_MDSKZ_DSC_assn_def modest_mdp_succ_DS_assn_def
        modest_MDSKZ_DSC_rel_def
      apply(erule hr_comp_entails_unique_dom) 
      unfolding Domain_modest_MDSKZ_DS_rel_eq_invar
      apply(subst(asm) Domain_modest_MDSKZ_DS_rel_alt)
      by auto

    lemma MDSKZ_ent_mdp_succ: "modest_MDSKZ_DSC_assn DS DSC (M,D,S,K,Z) ss \<turnstile> modest_mdp_succ_DS_assn DSC (S, K_deadlock Z (K_to_Succ K)) ss"
      unfolding modest_MDSKZ_DSC_assn_def modest_mdp_succ_DS_assn_def
      apply(rule hr_comp_alt_rel)
      by(erule modest_MDSKZ_to_succ_rel)

  
    lemma hn_mec_to_scc_block:
      assumes FR: "\<Gamma> \<turnstile> hn_ctxt (modest_MDSKZ_DSC_assn DS DSC) p' p ** \<Gamma>1"
      assumes Pair: "\<And> a1' a1. hn_refine (hn_ctxt (modest_mdp_succ_DS_assn DSC) a1' a1 \<and>* \<Gamma>1) (f a1) (\<Gamma>1' a1' a1) R CP (f' a1')"
      assumes FR2: "\<And>a1' a1. \<Gamma>1' a1' a1 \<turnstile> hn_ctxt (modest_mdp_succ_DS_assn DSC) a1' a1 ** \<Gamma>2'"  
      shows "hn_refine \<Gamma> (f p) (hn_ctxt (modest_MDSKZ_DSC_assn DS DSC) p' p ** \<Gamma>2')
        R CP (mec_to_scc_block$p'$(\<lambda>\<^sub>2 x. f' x))"
        apply(rule hn_refine_cons_pre[OF FR])
        unfolding autoref_tag_defs PROTECT2_def hr_comp_def 
        apply(cases p')
        apply (clarsimp simp:  mec_to_scc_block_def hn_ctxt_def sep_conj_exists hnr_pre_ex_conv)
        apply(sepref_to_hoare)
        apply(rule htriple_pure_preI)
        apply(drule pure_part_split_conj, clarify)+
        supply [vcg_rules] = Pair[THEN hn_refineD, unfolded hn_ctxt_def, THEN htriple_ent_pre[OF conj_entails_mono2[OF MDSKZ_ent_mdp_succ]]]
        apply vcg
        apply(rule ENTAILS_trans_pre)  
        apply(sep_drule FR2)
        unfolding hn_ctxt_def
        apply(erule conj_entails_mono2[OF conj_entails_mono2[OF mdp_succ_ent_MDSKZ]])
        apply vcg'
        done
  
    lemma mec_to_scc_block_mono: 
      "\<lbrakk>\<And>a. f a \<le> f' a\<rbrakk> \<Longrightarrow> mec_to_scc_block x f \<le> mec_to_scc_block x f'"
      unfolding mec_to_scc_block_def
      apply(cases x)
      by auto
  
    lemma mec_to_scc_block_arity: "mec_to_scc_block \<equiv> \<lambda>\<^sub>2x f. SP mec_to_scc_block$x$(\<lambda>\<^sub>2a. f$a)"
      by simp
  
    lemma mec_to_scc_block_comb:  
      "mec_to_scc_block$x$f = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP mec_to_scc_block$x$f)"
      by simp
  
    lemma mec_to_scc_block_mono_flat: 
      "\<lbrakk>\<And>a. flat_ge (f a) (f' a)\<rbrakk> \<Longrightarrow> flat_ge (mec_to_scc_block x f) (mec_to_scc_block x f')"
      unfolding mec_to_scc_block_def
      apply(cases x) by simp
  
    lemma mec_to_scc_block_SPLIT_rule:
        assumes "f (S,K_deadlock Z (K_to_Succ K)) \<le> SPEC P"
        shows "mec_to_scc_block (M,D,S,K,Z) f \<le> SPEC P"  
        using assms(1) unfolding mec_to_scc_block_def 
        by simp
  
    lemma filter_list_split_refine:
        assumes "f' (S',K_deadlock Z' (K_to_Succ K')) \<le>\<Down>R (f (S,K_deadlock Z (K_to_Succ K)))"
        shows "mec_to_scc_block (M',D',S',K',Z') f' \<le>\<Down>R (mec_to_scc_block (M,D,S,K,Z) f)"
        unfolding mec_to_scc_block_def
        using assms
        by auto

  end

  subsection \<open>Theory Conversion\<close>

  definition "E\<alpha>_closed \<equiv> \<lambda>(S,K). mdp_graph_defs.E_\<alpha> (S,K) `` S \<subseteq> S"

  lemma rtrancl_closed_aux: "u\<in>S \<Longrightarrow> R``S \<subseteq> S \<Longrightarrow> (u,v)\<in>(R\<inter>(S\<times>UNIV))\<^sup>* \<longleftrightarrow> (u,v)\<in>R\<^sup>*"
    apply rule
    subgoal by (meson inf_le1 rtrancl_mono_mp)
    apply (rotate_tac -1)
    apply (induction rule: converse_rtrancl_induct)
    by (auto simp add: ImageI converse_rtrancl_into_rtrancl subsetD)

  
  lemma(in modest_init_mdp_env_defs) modest_MDSKZ_assn_imp_closed:
    assumes "rdomp (modest_mdp_succ_DS_assn DS) (S,K)"
    shows "E\<alpha>_closed (S,K)" and "Modest_Gabow_SCC_pre N (S,K)"
    subgoal
      using assms
      unfolding modest_init_mdp_env_defs.modest_mdp_succ_DS_assn_def modest_mdp_succ_DS_rel_def modest_mdp_cullable_def.SK_\<alpha>_def
        E\<alpha>_closed_def
      apply (clarsimp simp: in_br_conv )
      using modest_mdp_cullable_invar'.E_\<alpha>_closed modest_mdp_cullable_invar.DS_DEF modest_mdp_cullable_invar_alt by blast
    subgoal
      using assms
      unfolding modest_init_mdp_env_defs.modest_mdp_succ_DS_assn_def modest_mdp_succ_DS_rel_def 
        E\<alpha>_closed_def modest_mdp_cullable_def.MDSKZ_\<alpha>_def
      apply (clarsimp simp: in_br_conv modest_mdp_cullable_def.SK_\<alpha>_def 
        dest!: modest_mdp_cullable_invar'.Modest_Gabow_SCC_pre_MDSKZ)
      by (metis modest_mdp_cullable_def.SK_\<alpha>_def modest_mdp_cullable_invar'.Modest_Gabow_SCC_pre_MDSKZ modest_mdp_cullable_invar.DS_DEF modest_mdp_cullable_invar.axioms(1))
    done

  lemma Et_\<alpha>_as_E: "mdp_def.Et_\<alpha> S K = mdp_graph_defs.E_\<alpha> (S, K_to_Succ K) \<inter> S \<times> UNIV"
    unfolding mdp_def.Et_\<alpha>_def mdp_graph_defs.E_\<alpha>_def mdp_graph_defs.K_def K_to_Succ_def
    by auto
  
  lemma Et_\<alpha>_ss: "mdp_def.Et_\<alpha> S K \<subseteq> mdp_graph_defs.E_\<alpha> (S, K_to_Succ K)"  
    unfolding Et_\<alpha>_as_E by blast

    
  lemma ordered_eq: 
    assumes "E\<alpha>_closed (S,K_to_Succ K)"
    assumes "\<Union>(set r) \<subseteq> S"
    shows "ordered r S K = mdp_graph_defs.ordered (S,K_to_Succ K) r"
    unfolding ordered_def Et_\<alpha>_as_E
    unfolding mdp_graph_defs.ordered_def
    using assms
    apply (auto simp: E\<alpha>_closed_def)
    apply (subst (asm) rtrancl_closed_aux[symmetric, where S=S])
    apply force
    apply blast
    apply blast
    apply (subst (asm) rtrancl_closed_aux)
    apply force
    apply blast
    by blast


  definition "Z_Deadlock \<equiv> (\<lambda>(M,D,S,K,Z). \<forall>u \<in> Z. K_to_Succ K u \<subseteq> {u})"

  lemma(in modest_init_mdp_env_defs) modest_MDSKZ_DS_assn_Z_Deadlock: "rdomp (modest_MDSKZ_DSC_assn DS DSC) (M,D,S,K,Z) \<Longrightarrow> Z_Deadlock (M,D,S,K,Z)"
    unfolding modest_MDSKZ_DSC_assn_def Z_Deadlock_def modest_MDSKZ_DSC_rel_def modest_mdp_cullable_def.MDSKZ_\<alpha>_def
      K_to_Succ_def modest_mdp_cullable_def.K_\<alpha>_def modest_mdp_input_struc_def.Cm_def modest_mdp_cullable_def.Z_\<alpha>_def
    by (fastforce simp: in_br_conv split: if_splits) 

  lemma scc_ordered_consD1: "mdp_graph_defs.ordered (S,K) (x # xs) \<Longrightarrow> mdp_graph_defs.ordered (S,K) xs"
    unfolding mdp_graph_defs.ordered_def
    by (metis Suc_less_eq length_Cons nth_Cons_Suc)

  lemma scc_ordered_distinct: "{} \<notin> set l \<Longrightarrow> mdp_graph_defs.ordered (S,K) l \<Longrightarrow> distinct l"
  proof(induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons a l)
    {
      fix u
      assume O: "mdp_graph_defs.ordered (S,K) (a # l)"
      and "a \<in> set l"
      and UA: "u \<in> a"
  
      then obtain i where ADEF: "a = l!i" and IB: "i < length l"
        by (metis in_set_conv_nth)
      
      have "0 < Suc i" by simp
      moreover from IB have "Suc i < Suc (length l)" by blast
      ultimately have CC: "a \<times> l!i \<inter> (mdp_graph_defs.E_\<alpha> (S,K))\<^sup>* = {}"
        using O unfolding mdp_graph_defs.ordered_def by fastforce
      moreover from UA ADEF have "(u,u) \<in> a \<times> l!i \<inter> (mdp_graph_defs.E_\<alpha> (S,K))\<^sup>*" by blast
      ultimately have False by fast
    } note AUX = this
  
    from Cons.prems Cons.IH show ?case 
      by (auto intro: AUX dest: scc_ordered_consD1) 
  qed

  lemma ordered_impl_distinct: 
    assumes C: "mdp_graph_defs.ordered (S,K) r"
    assumes D: "set r = {scc. is_scc (mdp_graph_defs.E_\<alpha> (S,K)) scc \<and> scc \<subseteq> S}"
    shows "distinct r"
    apply(rule scc_ordered_distinct[of _ S K])
    using C D
    unfolding mdp_graph_defs.ordered_def
    apply simp
    using C mdp_graph_defs.ordered_def by blast

  lemma(in mdp) mdp_reach_sub_S: "mdp S K \<Longrightarrow> (mdp_def.Et_\<alpha> S K)\<^sup>* `` S \<subseteq> S"
    using Et_\<alpha>_subset_states
    by (metis Image_closed_trancl Image_iff mdp.edge_connects_states(2) subsetI)

  lemma closed_E_\<alpha>_reachable_eq: "E\<alpha>_closed (S,K) \<Longrightarrow> (mdp_graph_defs.E_\<alpha> (S, K))\<^sup>* `` S = S"  
    unfolding E\<alpha>_closed_def
    by (auto dest: Image_closed_trancl)
    
  lemma E\<alpha>_closed_transcl_iff: "E\<alpha>_closed (S,K_to_Succ K) \<Longrightarrow> u\<in>S \<Longrightarrow> (u,v)\<in>(mdp_graph_defs.E_\<alpha> (S, K_to_Succ K))\<^sup>* \<longleftrightarrow> (u,v)\<in>(mdp_def.Et_\<alpha> S K)\<^sup>*"
    apply safe
    subgoal
      unfolding Et_\<alpha>_as_E E\<alpha>_closed_def 
      using rtrancl_closed_aux by force
    using Et_\<alpha>_ss
    using rtrancl_mono_mp by metis
   
        
  lemma closed_E_\<alpha>_is_scc_eq:
    assumes CL: "E\<alpha>_closed (S,(K_to_Succ K))" and SUB: "scc\<subseteq>S" and DL: "(\<And>u. u \<in> Z \<Longrightarrow> K_to_Succ K u \<subseteq> {u})"
    shows "is_scc (mdp_def.Et_\<alpha> S K) scc \<longleftrightarrow> is_scc (mdp_graph_defs.E_\<alpha> (S,K_deadlock Z (K_to_Succ K))) scc"
    apply(rule rtrancl_eq_scc'[of _ S])
    using CL unfolding E\<alpha>_closed_def using Et_\<alpha>_ss apply blast
    apply (metis K_deadlock_eq_edges assms(1) assms(3) closed_E_\<alpha>_reachable_eq rtrancl_image_unfold_right)
    apply(subst K_deadlock_eq_edges)
    subgoal using DL by presburger
    subgoal by (auto simp: CL E\<alpha>_closed_transcl_iff)
    using SUB by presburger

  lemma E\<alpha>_closed_compute_sccs_eq': "E\<alpha>_closed (S,K_to_Succ K) \<Longrightarrow> (\<And>u. u \<in> Z \<Longrightarrow> K_to_Succ K u \<subseteq> {u}) \<Longrightarrow> mdp_graph_defs.compute_SCC_spec (S,K_deadlock Z (K_to_Succ K)) \<le> compute_sccs (M,D,S,K,Z)"
    unfolding compute_sccs_def mdp_graph_defs.compute_SCC_spec_def scc_list_def mdp_graph_defs.scc_set_def
    apply (simp add: closed_E_\<alpha>_reachable_eq)
    using ordered_impl_distinct[of S "K_to_Succ K"] closed_E_\<alpha>_is_scc_eq[of S K _ Z] 
    by (smt (verit, best) Collect_cong K_deadlock_eq_edges closed_E_\<alpha>_reachable_eq mem_Collect_eq ordered_impl_distinct subsetI)

  lemma E\<alpha>_closed_compute_sccs_eq: "E\<alpha>_closed (S,K_to_Succ K) \<Longrightarrow> Z_Deadlock (M,D,S,K,Z) \<Longrightarrow> mdp_graph_defs.compute_SCC_spec (S,K_deadlock Z (K_to_Succ K)) \<le> compute_sccs (M,D,S,K,Z)"
    using E\<alpha>_closed_compute_sccs_eq' unfolding Z_Deadlock_def by fast

  lemma E\<alpha>_closed_deadlock: "E\<alpha>_closed (S, K_deadlock Z (K_to_Succ K)) \<Longrightarrow> Z_Deadlock (M,D,S,K,Z) \<Longrightarrow> E\<alpha>_closed (S, K_to_Succ K)"
    unfolding E\<alpha>_closed_def K_deadlock_def Z_Deadlock_def K_to_Succ_def mdp_graph_defs.E_\<alpha>_def
    apply clarsimp 
    by (smt (verit, best) UnionI insert_iff mem_Collect_eq subsetD)

  context modest_init_mdp_env_defs
  begin

    definition "compute_sccs_cullable \<equiv> (\<lambda> MDSKZ. do{ ASSUME (Z_Deadlock MDSKZ); mec_to_scc_block MDSKZ (\<lambda> SK'. do { ASSUME (E\<alpha>_closed SK'); mdp_graph_defs.compute_SCC_spec SK'})})"
  
    lemma compute_sccs_cullable_refines: "(compute_sccs_cullable, compute_sccs) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
      unfolding compute_sccs_cullable_def mec_to_scc_block_def 
      apply refine_rcg
      by (auto intro!: E\<alpha>_closed_compute_sccs_eq E\<alpha>_closed_deadlock)


    concrete_definition (in -) compute_SCC_impl_mec_ll' [llvm_code] is Modest_compute_SCC_impl_def[of ni' for ni']

  end

  context modest_init_mdp_env
  begin

    lemmas [unfolded compute_SCC_impl_mec_ll'.refine, sepref_fr_rules] 
      = modest_init_mdp_env.compute_SCC_DS_spec_hnr[OF modest_init_mdp_env_axioms]
  
    interpretation scc_map N N ni
      apply(unfold_locales)
      apply (simp add: n_impl)
      using N_BOUND apply simp
      done

    context
      notes [sepref_comb_rules] = hn_mec_to_scc_block
      and [sepref_monadify_arity] = mec_to_scc_block_arity
      and [sepref_monadify_comb] = mec_to_scc_block_comb
    begin
      
      sepref_definition compute_sccs_cullable_impl_ll is "compute_sccs_cullable" :: "(modest_MDSKZ_DSC_assn DS DSC)\<^sup>k \<rightarrow>\<^sub>a output_assn"
        unfolding compute_sccs_cullable_def 
        supply[elim] = modest_MDSKZ_assn_imp_closed modest_MDSKZ_DS_assn_Z_Deadlock
        apply sepref
        done

    end


    lemma compute_sccs_cullable_impl_hnr: "(compute_sccs_cullable_impl_ll, compute_sccs) \<in> (modest_MDSKZ_DS_assn DS)\<^sup>k \<rightarrow>\<^sub>a output_assn"
    proof -

      note REF = compute_sccs_cullable_impl_ll.refine[FCOMP compute_sccs_cullable_refines, to_hnr]

      show ?thesis
        apply(rule hfrefI)
        apply simp
        unfolding modest_MDSKZ_DS_assn_alt hnr_pre_ex_conv
        apply (rule allI)
        apply(sepref_to_hoare)
        supply [vcg_rules] = REF[THEN hn_refineD, unfolded hn_ctxt_def, simplified]
        by vcg

    qed

  end


end
