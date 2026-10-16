theory Interval_Iteration_Min_GS_Code
  imports "../Interval_Iteration_Tool_GS_Minred_Code"
begin

text \<open>Standalone export of \<^emph>\<open>minimal\<close> reach-avoid interval iteration (Gauss-Seidel), without the
  \<^const>\<open>Min_red\<close> reduction: the \<open>Inf\<close> Bellman sweep run directly on the input Modest MDP. The
  counterpart of \<^file>\<open>Interval_Iteration_Max_GS_Code.thy\<close> on the min side.

  The loop is not re-synthesised. \<^const>\<open>mop_interval_iteration_gs_ll'\<close> is the one synthesised in
  \<^file>\<open>../Interval_Iteration_Tool_GS_Minred_Code.thy\<close> (refinement
  @{thm [source] interval_iteration_inf_env.mop_interval_iteration_gs_hnr_raw}); the pipeline theory
  exports it only as part of \<open>compute_II\<close>, so the sole addition is the pointer-passing wrapper that
  \<open>export_llvm\<close> needs --- exactly the one \<open>Modest_compute_ii_max_ll\<close> has on the max side.\<close>

  definition Modest_compute_ii_min_ll ::
    "size_t \<Rightarrow> size_t \<Rightarrow> double \<Rightarrow> modest_mdpi ptr \<Rightarrow> (double ptr \<times> double ptr \<times> size_t) ptr \<Rightarrow> unit llM"
  where [llvm_code, llvm_inline]: "Modest_compute_ii_min_ll Li ni \<epsilon>i Mip resp \<equiv> doM {
    Mi \<leftarrow> ll_load Mip;
    res \<leftarrow> mop_interval_iteration_gs_ll' ni \<epsilon>i Mi Li;
    ll_store res resp
  }"

  section \<open>Hoare triples\<close>

  text \<open>The loop's \<open>hn_refine\<close> against the abstract specification, inside
    \<^locale>\<open>interval_iteration_inf_code\<close> --- the same code locale the min pipeline uses, which
    already fixes a reach-avoid \<^term>\<open>\<M>\<close>, its size \<open>N\<close>/\<open>ni\<close>, the tolerance \<open>\<epsilon>\<close>/\<open>\<epsilon>i\<close> and
    \<open>states (to_mdpc \<M>) = {0..<N}\<close>. The MDP is a \<^emph>\<open>kept\<close> argument, so unlike \<open>compute_II\<close> (which
    reduces in place) it survives the call unchanged.\<close>

  context interval_iteration_inf_code
  begin

    lemma ii_min_hnr: "hn_refine
      (Modest_mdp_inf_assn N \<M> \<M>i ** snat_assn L Li)
      (mop_interval_iteration_gs_ll' ni \<epsilon>i \<M>i Li)
      (Modest_mdp_inf_assn N \<M> \<M>i ** snat_assn L Li)
      (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (\<lambda>_. True)
      (mop_interval_iteration \<M> L)"
    proof -
      note R = mop_interval_iteration_gs_hnr_raw[to_hnr, simplified]
      show ?thesis
        apply (rule hn_refine_ref)
         apply (rule interval_iteration_impl_inf_correct)
        apply (rule hn_refine_cons[OF _ R])
        unfolding hn_ctxt_def apply blast+
        done
    qed

  end

  text \<open>Main correctness theorem: the two returned arrays bracket the \<^emph>\<open>minimal\<close> reach-avoid
    probability at every state of the input MDP.\<close>

  theorem compute_ii_min_ll_htriple[vcg_rules]: "llvm_htriple
    (size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** Modest_mdp_inf_assn N \<M> \<M>i ** snat_assn L Li
       ** \<up>(2 * N < max_size_t))

    (mop_interval_iteration_gs_ll' ni \<epsilon>i \<M>i Li)

    (\<lambda>resi. EXS x y i. size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i
       ** Modest_mdp_inf_assn N \<M> \<M>i ** snat_assn L Li
       ** \<up>(2 * N < max_size_t)
       ** (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (x,y,i) resi
       ** \<up>(\<forall>u \<in> states (to_mdpc \<M>). x u \<le> n_real' \<M> u \<and> n_real' \<M> u \<le> y u))"
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

    note [vcg_rules] = ii_min_hnr[THEN hn_refineD,
      unfolded mop_interval_iteration_def interval_iteration_defs.interval_iteration_spec_def]

    show ?thesis
      apply vcg
      done
  qed

  text \<open>\<dots> and the same including the pointer import/export done by the wrapper.\<close>

  context
  begin

    interpretation llvm_prim_setup . \<comment> \<open>For \<open>ll_load\<close>/\<open>ll_store\<close>\<close>

    corollary Modest_compute_ii_min_ll_htriple: "llvm_htriple
      ( \<upharpoonleft>ll_pto \<M>i Mip ** \<upharpoonleft>ll_pto alloc resip
      ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** Modest_mdp_inf_assn N \<M> \<M>i ** snat_assn L Li
      ** \<up>(2 * N < max_size_t))

      (Modest_compute_ii_min_ll Li ni \<epsilon>i Mip resip)

      (\<lambda>_. EXS x y i resi. \<upharpoonleft>ll_pto resi resip ** \<upharpoonleft>ll_pto \<M>i Mip
        ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i
        ** Modest_mdp_inf_assn N \<M> \<M>i ** snat_assn L Li
        ** \<up>(2 * N < max_size_t)
        ** (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (x,y,i) resi
        ** \<up>(\<forall>u \<in> states (to_mdpc \<M>). x u \<le> n_real' \<M> u \<and> n_real' \<M> u \<le> y u))"
      unfolding Modest_compute_ii_min_ll_def
      apply vcg
      done

  end


  export_llvm Modest_compute_ii_min_ll
    is "void compute_II_min(modest_size_t, modest_size_t, modest_dec_t, modest_mdp_t *, modest_ii_vals_t *)"
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
      modest_dec_t *lbs;
      struct {
        modest_dec_t *ubs;
        modest_size_t iterations;
      };
    } modest_ii_vals_t;
  \<close>
    file "modest_ii_min.ll"

end
