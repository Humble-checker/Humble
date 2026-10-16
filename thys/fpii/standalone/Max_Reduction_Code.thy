theory Max_Reduction_Code
  imports "../Interval_Iteration_Tool_GS_Maxred_Impl"
begin

text \<open>Standalone export of the \<^emph>\<open>max reduction\<close> alone: given a Modest MDP, compute a sorted MEC
  decomposition, collapse the MDP along it and re-index the collapsed space, yielding the indexed
  \<^const>\<open>Max_red\<close>. No interval iteration --- the caller gets all three state-space components back
  (the preserved input MDP, the decomposition that relates them, and the reduced MDP) and may do
  what it likes with them.

  This is \<^const>\<open>modest_init_mdp_env_defs.tool_pmax_impl\<close> stopped one step early: the same MEC
  computation and the same builder, without the final \<^const>\<open>ii_max_out\<close>. Every sub-operation is
  already registered, so the synthesis is a bare \<^theory_text>\<open>sepref\<close> and the result assertion is the
  \<open>M\<close>-free \<^const>\<open>Modest_build_assn_t\<close> that the pipeline already uses.\<close>

  context modest_init_mdp_env_defs
  begin

    definition "tool_maxred_impl \<M> = do {
      ASSERT (compute_mecs_pre \<M>);
      D \<leftarrow> compute_MEC_sorted \<M>;
      let M = op_mec_map_length D;
      ASSERT (M \<le> N);
      ASSERT (reinterpret_pre (\<M>,D) \<and> M = length D);
      op_build_reindex_t M (\<M>, D) }"

  end

  context interval_iteration_sup_env
  begin

    interpretation modest_init_mdp_env N ni
      apply unfold_locales using n_impl by auto

    interpretation disj_set_list_tuple_defs N N ni ni .
    interpretation disj_set_list_tuple_env N N ni ni
      unfolding disj_set_list_tuple_env_def using n_impl by satx

    lemmas build_reindex_hnr_arg_t'[sepref_fr_rules] =
      build_reindex_hnr_arg_t[OF interval_iteration_env_axioms]

    sepref_definition tool_maxred_impl_ll is "tool_maxred_impl"
      :: "(Modest_mdp_sup_assn N)\<^sup>d \<rightarrow>\<^sub>a Modest_build_assn_t N"
      unfolding tool_maxred_impl_def compute_MEC_sorted_def
      supply [elim] = M_bound_Suc M_bound_2
      supply [simp] = bind_ref_tag_def op_mec_map_length_def
      by sepref

    concrete_definition (in -) tool_maxred_impl_ll' [llvm_code] is
      interval_iteration_sup_env.tool_maxred_impl_ll_def

    lemmas tool_maxred_impl_hnr_raw =
      tool_maxred_impl_ll.refine[unfolded
        tool_maxred_impl_ll'.refine[OF interval_iteration_sup_env_axioms]]

  end

  section \<open>The reduction meets its specification\<close>

  text \<open>What the caller gets back: the untouched input MDP, a MEC decomposition of it, and the
    reduced MDP --- which is \<^emph>\<open>the\<close> max reduction \<^const>\<open>Max_red\<close>, relabelled by the index each MEC
    got in the decomposition. Stating all three components is what makes the relabelling \<open>idx_of D\<close>
    pinned down rather than merely existentially quantified.\<close>

  definition tool_maxred_spec ::
    "nat mdptc \<Rightarrow> (nat mdptc \<times> nat set list \<times> nat mdptc) nres" where
    "tool_maxred_spec \<M> = SPEC (\<lambda>(\<M>\<^sub>0, D, \<M>').
        \<M>\<^sub>0 = \<M>
        \<and> set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D
        \<and> \<M>' = map_mdptc (idx_of D) (Max_red \<M>))"

  text \<open>The three \<^const>\<open>ASSERT\<close>s discharge exactly as in \<open>tool_pmax_impl_correct\<close> --- via
    @{thm [source] mec_count_le} and \<^const>\<open>reinterpret_pre\<close> --- and \<^const>\<open>op_build_reindex_t\<close> is a
    \<^const>\<open>RETURN\<close>, so nothing is left but rewriting \<^const>\<open>to_index\<close> into \<^const>\<open>Max_red\<close>.\<close>

  lemma (in modest_init_mdp_env_defs) tool_maxred_impl_correct:
    assumes WF: "MDPC_Reach_Avoid_Sup \<M>"
      and ST: "states (to_mdpc \<M>) = {0..<N}"
    shows "tool_maxred_impl \<M> \<le> tool_maxred_spec \<M>"
  proof -
    have WFa: "MDPC_Reach_Avoid \<M>" using WF by (simp add: MDPC_Reach_Avoid_Sup_def)
    interpret M: MDPC_Reach_Avoid \<M> by (rule WFa)
    have FM: "Finite_MDP (to_mdpc \<M>)" using WFa by (simp add: MDPC_Reach_Avoid_def)
    have PRE: "compute_mecs_pre \<M>"
      unfolding compute_mecs_pre_def using ST FM by simp
    have SORT: "compute_MEC_sorted \<M>
                  \<le> SPEC (\<lambda>D. set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D)"
      unfolding compute_MEC_sorted_def op_compute_mecs_def mec_algo_defs.compute_MEC_spec_def
        op_sort_by_inf_def
      apply refine_vcg by auto
    show ?thesis
      unfolding tool_maxred_impl_def Let_def tool_maxred_spec_def
      apply (rule ASSERT_leI[OF PRE])
      apply (refine_vcg SORT[THEN order_trans])
      subgoal by (auto simp: op_mec_map_length_def intro!: mec_count_le[OF WFa _ _ ST])
      subgoal by (simp add: reinterpret_pre_def)
      subgoal by (simp add: op_mec_map_length_def)
      subgoal
        unfolding op_build_reindex_t_def op_build_reindex_tp_def op_build_reindex_def
          op_build_index_def op_to_index_def op_reinterpret_def
        by (simp add: to_index_map_mdptc M.reduce_M_mec)
      done
  qed

  section \<open>Hoare triples\<close>

  context interval_iteration_sup_code
  begin

    lemma WF_sup': "MDPC_Reach_Avoid_Sup \<M>"
      by (simp add: MDPC_Reach_Avoid_Sup_def MDPC_Reach_Avoid_axioms)

    lemma max_red_hnr: "hn_refine
      (Modest_mdp_sup_assn N \<M> \<M>i)
      (tool_maxred_impl_ll' ni \<M>i)
      (hn_invalid (Modest_mdp_sup_assn N) \<M> \<M>i)
      (Modest_build_assn_t N) (\<lambda>_. True)
      (tool_maxred_spec \<M>)"
    proof -
      note R = tool_maxred_impl_hnr_raw[to_hnr, simplified]
      show ?thesis
        apply (rule hn_refine_ref)
         apply (rule tool_maxred_impl_correct[OF WF_sup' states_M])
        apply (rule hn_refine_cons[OF _ R])
        unfolding hn_ctxt_def apply blast+
        done
    qed

  end

  text \<open>Main correctness theorem. \<^const>\<open>Modest_build_assn_t\<close> is the \<open>M\<close>-free bundle of all three
    state-space components, so the MEC count never escapes into the interface.\<close>

  theorem compute_max_red_ll_htriple[vcg_rules]: "llvm_htriple
    (size_assn N ni ** Modest_mdp_sup_assn N \<M> \<M>i ** \<up>(2 * N < max_size_t)
       ** \<up>((\<epsilon>i::double, \<epsilon>::real) \<in> nn_real_lb_double_rel))

    (tool_maxred_impl_ll' ni \<M>i)

    (\<lambda>resi. EXS D \<M>'. size_assn N ni ** hn_invalid (Modest_mdp_sup_assn N) \<M> \<M>i
       ** \<up>(2 * N < max_size_t)
       ** Modest_build_assn_t N (\<M>, D, \<M>') resi
       ** \<up>(set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D
            \<and> \<M>' = map_mdptc (idx_of D) (Max_red \<M>)))"
  proof (rule htriple_pure_preI; goal_cases)
    have AUX: "(DS, \<M>) \<in> modest_mdp_sup_rel N \<Longrightarrow> states (to_mdpc \<M>) = {0..<N}" for DS \<M>
      unfolding modest_mdp_sup_rel_def modest_mdp_input_def.\<M>_\<alpha>_def modest_mdp_input_def.M\<^sub>0_\<alpha>_def
      by (auto simp: in_br_conv to_mdpc.abs_eq states.abs_eq split: if_splits)

    have AUX2: "(DS, \<M>) \<in> modest_mdp_sup_rel N \<Longrightarrow> MDPC_Reach_Avoid \<M>" for DS \<M>
      unfolding modest_mdp_sup_rel_def
      by (auto simp: in_br_conv modest_mdp_ii_invar_sup_def
        dest: modest_mdp_input_invar.MDPC_Reach_Avoid_\<M>_\<alpha>)

    case 1
    then interpret MDPC_Reach_Avoid_Sup \<M>
      by (auto simp: Modest_mdp_sup_assn_def pure_part_hr_comp_eq MDPC_Reach_Avoid_Sup_def AUX2
        dest!: pure_part_split_conj)

    from 1 have "(ni,N) \<in> size_rel" "(\<epsilon>i, \<epsilon>) \<in> nn_real_lb_double_rel" "2 * N < max_snat 64"
      "states (to_mdpc \<M>) = {0..<N}"
      by (auto simp: Modest_mdp_sup_assn_def pure_part_hr_comp_eq MDPC_Reach_Avoid_Sup_def AUX AUX2
        dest!: pure_part_split_conj)

    then interpret interval_iteration_sup_code
      apply unfold_locales
      subgoal by (simp add: closed_M)
      subgoal by (simp add: actions_finite')
      subgoal by blast
      done

    note [vcg_rules] = max_red_hnr[THEN hn_refineD, unfolded tool_maxred_spec_def]

    show ?thesis
      apply vcg
      done
  qed

  type_synonym modest_maxred_res = "(modest_mdpi \<times> modest_mdpi) \<times> mec_mapi"

  definition Modest_compute_max_red_ll ::
    "size_t \<Rightarrow> modest_mdpi ptr \<Rightarrow> modest_maxred_res ptr \<Rightarrow> unit llM"
  where [llvm_code, llvm_inline]: "Modest_compute_max_red_ll ni \<M>ip resp \<equiv> doM {
    \<M>i \<leftarrow> ll_load \<M>ip;
    res \<leftarrow> tool_maxred_impl_ll' ni \<M>i;
    ll_store res resp
  }"

  text \<open>\<dots> and the same including the pointer import/export done by the wrapper.\<close>

  context
  begin

    interpretation llvm_prim_setup . \<comment> \<open>For \<open>ll_load\<close>/\<open>ll_store\<close>\<close>

    corollary Modest_compute_max_red_ll_htriple: "llvm_htriple
      ( \<upharpoonleft>ll_pto \<M>i Mip ** \<upharpoonleft>ll_pto alloc resip
      ** size_assn N ni ** Modest_mdp_sup_assn N \<M> \<M>i ** \<up>(2 * N < max_size_t)
      ** \<up>((\<epsilon>i::double, \<epsilon>::real) \<in> nn_real_lb_double_rel))

      (Modest_compute_max_red_ll ni Mip resip)

      (\<lambda>_. EXS D \<M>' resi. \<upharpoonleft>ll_pto resi resip ** \<upharpoonleft>ll_pto \<M>i Mip
        ** size_assn N ni ** hn_invalid (Modest_mdp_sup_assn N) \<M> \<M>i
        ** \<up>(2 * N < max_size_t)
        ** Modest_build_assn_t N (\<M>, D, \<M>') resi
        ** \<up>(set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D
             \<and> \<M>' = map_mdptc (idx_of D) (Max_red \<M>)))"
      unfolding Modest_compute_max_red_ll_def
      apply vcg
      done

  end

  export_llvm Modest_compute_max_red_ll
    is "void compute_max_red(modest_size_t, modest_mdp_t *, modest_max_red_t *)"
  defines \<open>
    typedef double modest_dec_t;
    typedef int64_t modest_size_t;
    typedef modest_size_t node_t;

    typedef struct {
      modest_dec_t lb;
      modest_dec_t ub;
    } modest_interval_t;

    typedef struct {
      node_t *states;
      struct {
        node_t *transitions;
        struct {
          node_t *branches;
          struct {
            modest_interval_t *probabilities;
            struct {
              modest_size_t *avoid;
              modest_size_t *target;
            };
          };
        };
      };
    } modest_mdp_t;

    typedef struct {
      modest_mdp_t input;
      modest_mdp_t reduced;
    } modest_mdp_pair_t;

    typedef struct {
      modest_size_t mec_count;
      node_t *mec_of;
    } modest_mec_map_t;

    typedef struct {
      modest_mdp_pair_t mdps;
      modest_mec_map_t mecs;
    } modest_max_red_t;
  \<close>
    file "modest_max_red.ll"

end
