theory MaxEndComponent_Sorted_Code
  imports "../Interval_Iteration_Tool_GS_Minred_Code"
begin

text \<open>Standalone export of the \<^emph>\<open>sorted\<close> MEC decomposition: \<^const>\<open>compute_MEC_sorted\<close>, i.e. the
  MEC decomposition of \<^file>\<open>../../mec/MaxEndComponent_Code.thy\<close> followed by \<^const>\<open>op_sort_by_inf\<close>, so the
  classes come back ordered by their least element. The sorted order is what the max-reduction
  builder relies on to index MECs deterministically.

  The loop is not re-synthesised. It is the one from
  \<^file>\<open>../../ds/Impl/Modest_MDP_II_Minred_Impl.thy\<close>
  (@{thm [source] modest_init_mdp_env.compute_MEC_sorted_ll.refine}); it is only ever used there from
  inside the locale, so the setup this theory adds is the \<^theory_text>\<open>concrete_definition\<close> that turns it into
  a global constant with an unconditional code equation --- without which \<open>export_llvm\<close> stops at
  \<open>No code equation for modest_init_mdp_env.compute_MEC_sorted_ll\<close> --- plus the pointer-passing
  wrapper.\<close>

  concrete_definition compute_MEC_sorted_ll' [llvm_code] is
    modest_init_mdp_env.compute_MEC_sorted_ll_def

  definition Modest_compute_MEC_sorted_ll ::
    "size_t \<Rightarrow> modest_mdpi ptr \<Rightarrow> mec_mapi ptr \<Rightarrow> unit llM"
  where [llvm_code, llvm_inline]: "Modest_compute_MEC_sorted_ll ni \<M>ip resp \<equiv> doM {
    \<M>i \<leftarrow> ll_load \<M>ip;
    res \<leftarrow> compute_MEC_sorted_ll' ni \<M>i;
    ll_store res resp
  }"

  section \<open>Hoare triple\<close>

  text \<open>Stated inside \<^locale>\<open>interval_iteration_inf_code\<close>, which is the code locale the min
    pipeline already uses: it fixes a reach-avoid \<^term>\<open>\<M>\<close> with \<open>states (to_mdpc \<M>) = {0..<N}\<close>, and
    that plus finiteness is exactly \<^const>\<open>modest_init_mdp_env_defs.compute_mecs_pre\<close>, the
    precondition of the synthesised loop. The MDP is a \<^emph>\<open>kept\<close> argument.\<close>

  context interval_iteration_inf_code
  begin

    lemma modest_init_mdp_env_this: "modest_init_mdp_env N ni"
      apply unfold_locales using n_impl by auto

    lemma compute_mecs_pre_this: "compute_mecs_pre \<M>"
      unfolding compute_mecs_pre_def using states_M MDPC_Reach_Avoid_axioms
      by (simp add: MDPC_Reach_Avoid_def)

    lemma mec_sorted_hnr: "hn_refine
      (Modest_mdp_inf_assn N \<M> \<M>i)
      (compute_MEC_sorted_ll' ni \<M>i)
      (Modest_mdp_inf_assn N \<M> \<M>i)
      (disj_set_list_tuple_defs.mec_map_assn N N) (\<lambda>_. True)
      (op_compute_mec_sorted (to_mdpc \<M>))"
    proof -
      note R = modest_init_mdp_env.compute_MEC_sorted_ll.refine[OF modest_init_mdp_env_this,
        unfolded compute_MEC_sorted_ll'.refine[OF modest_init_mdp_env_this], to_hnr]
      show ?thesis
        apply (rule hn_refine_ref)
         apply (rule compute_MEC_sorted_correct)
        apply (rule hn_refine_cons[OF _ R[THEN hn_refine_preI, of \<M> \<M>i, simplified]])
        unfolding hn_ctxt_def
        apply (simp_all add: compute_mecs_pre_this entails_refl)
        done
    qed

  end

  text \<open>Main correctness theorem: the returned list is a MEC decomposition of the input, without
    repetitions, sorted strictly by least element.\<close>

  theorem compute_MEC_sorted_ll_htriple[vcg_rules]: "llvm_htriple
    (size_assn N ni ** Modest_mdp_inf_assn N \<M> \<M>i ** \<up>(2 * N < max_size_t)
       ** \<up>((\<epsilon>i::double, \<epsilon>::real) \<in> nn_real_lb_double_rel))

    (compute_MEC_sorted_ll' ni \<M>i)

    (\<lambda>resi. EXS D. size_assn N ni ** Modest_mdp_inf_assn N \<M> \<M>i
       ** \<up>(2 * N < max_size_t)
       ** disj_set_list_tuple_defs.mec_map_assn N N D resi
       ** \<up>(set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D
            \<and> sorted_wrt (\<lambda>x y. Inf x < Inf y) D))"
  proof (rule htriple_pure_preI; goal_cases)
    have AUX: "(DS, \<M>) \<in> modest_mdp_inf_rel N \<Longrightarrow> states (to_mdpc \<M>) = {0..<N}" for DS \<M>
      unfolding modest_mdp_inf_rel_def modest_mdp_input_def.\<M>_\<alpha>_def modest_mdp_input_def.M\<^sub>0_\<alpha>_def
      by (auto simp: in_br_conv to_mdpc.abs_eq states.abs_eq split: if_splits)

    have AUX2: "(DS, \<M>) \<in> modest_mdp_inf_rel N \<Longrightarrow> MDPC_Reach_Avoid \<M>" for DS \<M>
      unfolding modest_mdp_inf_rel_def
      by (auto simp: in_br_conv modest_mdp_ii_invar_inf_def
        dest: modest_mdp_input_invar.MDPC_Reach_Avoid_\<M>_\<alpha>)

    case 1
    then interpret MDPC_Reach_Avoid_Inf \<M>
      by (auto simp: Modest_mdp_inf_assn_def pure_part_hr_comp_eq MDPC_Reach_Avoid_Inf_def AUX2
        dest!: pure_part_split_conj)

    from 1 have "(ni,N) \<in> size_rel" "(\<epsilon>i, \<epsilon>) \<in> nn_real_lb_double_rel" "2 * N < max_snat 64"
      "states (to_mdpc \<M>) = {0..<N}"
      by (auto simp: Modest_mdp_inf_assn_def pure_part_hr_comp_eq MDPC_Reach_Avoid_Inf_def AUX AUX2
        dest!: pure_part_split_conj)

    then interpret interval_iteration_inf_code
      apply unfold_locales
      subgoal by (simp add: closed_M)
      subgoal by (simp add: actions_finite')
      subgoal by blast
      done

    note [vcg_rules] = mec_sorted_hnr[THEN hn_refineD, unfolded op_compute_mec_sorted_def]

    show ?thesis
      apply vcg
      done
  qed

  text \<open>\<dots> and the same including the pointer import/export done by the wrapper.\<close>

  context
  begin

    interpretation llvm_prim_setup . \<comment> \<open>For \<open>ll_load\<close>/\<open>ll_store\<close>\<close>

    corollary Modest_compute_MEC_sorted_ll_htriple: "llvm_htriple
      ( \<upharpoonleft>ll_pto \<M>i Mip ** \<upharpoonleft>ll_pto alloc resip
      ** size_assn N ni ** Modest_mdp_inf_assn N \<M> \<M>i ** \<up>(2 * N < max_size_t)
      ** \<up>((\<epsilon>i::double, \<epsilon>::real) \<in> nn_real_lb_double_rel))

      (Modest_compute_MEC_sorted_ll ni Mip resip)

      (\<lambda>_. EXS D resi. \<upharpoonleft>ll_pto resi resip ** \<upharpoonleft>ll_pto \<M>i Mip
        ** size_assn N ni ** Modest_mdp_inf_assn N \<M> \<M>i
        ** \<up>(2 * N < max_size_t)
        ** disj_set_list_tuple_defs.mec_map_assn N N D resi
        ** \<up>(set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D
             \<and> sorted_wrt (\<lambda>x y. Inf x < Inf y) D))"
      unfolding Modest_compute_MEC_sorted_ll_def
      apply vcg
      done

  end

  text \<open>\<^const>\<open>op_sort_by_inf\<close> reads the MEC classes back out of the tuple-list map, which the min
    pipeline never does, so these two accessors have no code equation yet.\<close>
  lemmas [llvm_inline] = disj_set_list_tuple_defs.of_LIST1_impl_def
    disj_set_list_tuple_defs.of_LIST2_impl_def

  export_llvm Modest_compute_MEC_sorted_ll
    is "void compute_MEC_sorted(modest_size_t, modest_mdp_t *, mec_result_t *)"
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
      modest_size_t num_mecs;
      modest_size_t *mec_map;
    } mec_result_t;
  \<close>
    file "modest_mec_sorted.ll"

end
