theory Interval_Iteration_Max_GS_Code
  imports "../Interval_Iteration_Max_Code"
begin

text \<open>Standalone export of \<^emph>\<open>maximal\<close> reach-avoid interval iteration (Gauss-Seidel), without any
  MEC reduction: the \<open>Sup\<close> Bellman sweep run directly on the input Modest MDP.

  The loop and its refinement are those of \<^file>\<open>../Interval_Iteration_Max_Code.thy\<close>; this theory
  re-emits that one verified function as a self-contained LLVM module, so Modest can link the
  interval-iteration loop on its own, and packages its correctness as a Hoare triple.\<close>

  no_notation Finite_Cartesian_Product.matrix_matrix_mult (infixl "**" 70)

  section \<open>Hoare triples\<close>

  text \<open>The loop's \<open>hn_refine\<close> against the abstract specification, inside the code locale that
    already fixes everything needed: a reach-avoid \<^term>\<open>\<M>\<close>, its size \<open>N\<close>/\<open>ni\<close>, the tolerance
    \<open>\<epsilon>\<close>/\<open>\<epsilon>i\<close> and \<open>states (to_mdpc \<M>) = {0..<N}\<close>. The MDP is a \<^emph>\<open>kept\<close> argument, so it survives the
    call unchanged.\<close>

  context interval_iteration_sup_code
  begin

    lemma ii_max_hnr: "hn_refine
      (Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li)
      (ii_max_impl_ll' ni \<epsilon>i \<M>i Li)
      (Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li)
      (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (\<lambda>_. True)
      (mop_interval_iteration_sup \<M> L)"
    proof -
      note R = ii_max_impl_hnr_raw[to_hnr, simplified]
      show ?thesis
        apply (rule hn_refine_ref)
         apply (rule ii_max_impl_correct)
        apply (rule hn_refine_cons[OF _ R])
        unfolding hn_ctxt_def apply blast+
        done
    qed

  end

  abbreviation "p_real'' \<equiv> MDPC_Reach_Avoid.p_real"

  text \<open>Main correctness theorem: the two returned arrays bracket the \<^emph>\<open>maximal\<close> reach-avoid
    probability at every state of the input MDP.\<close>

  theorem compute_ii_max_ll_htriple[vcg_rules]: "llvm_htriple
    (size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li
       ** \<up>(2 * N < max_size_t))

    (ii_max_impl_ll' ni \<epsilon>i \<M>i Li)

    (\<lambda>resi. EXS x y i. size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i
       ** Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li
       ** \<up>(2 * N < max_size_t)
       ** (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (x,y,i) resi
       ** \<up>(\<forall>u \<in> states (to_mdpc \<M>). x u \<le> p_real'' \<M> u \<and> p_real'' \<M> u \<le> y u))"
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

    note [vcg_rules] = ii_max_hnr[THEN hn_refineD,
      unfolded mop_interval_iteration_sup_def interval_iteration_defs.interval_iteration_spec_def]

    show ?thesis
      apply vcg
      done
  qed

  text \<open>\<dots> and the same including the pointer import/export done by the wrapper.\<close>

  context
  begin

    interpretation llvm_prim_setup . \<comment> \<open>For \<open>ll_load\<close>/\<open>ll_store\<close>\<close>

    corollary Modest_compute_ii_max_ll_htriple: "llvm_htriple
      ( \<upharpoonleft>ll_pto \<M>i Mip ** \<upharpoonleft>ll_pto alloc resip
      ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li
      ** \<up>(2 * N < max_size_t))

      (Modest_compute_ii_max_ll Li ni \<epsilon>i Mip resip)

      (\<lambda>_. EXS x y i resi. \<upharpoonleft>ll_pto resi resip ** \<upharpoonleft>ll_pto \<M>i Mip
        ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i
        ** Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li
        ** \<up>(2 * N < max_size_t)
        ** (output_lb_assn N \<times>\<^sub>a output_ub_assn N \<times>\<^sub>a size_assn) (x,y,i) resi
        ** \<up>(\<forall>u \<in> states (to_mdpc \<M>). x u \<le> p_real'' \<M> u \<and> p_real'' \<M> u \<le> y u))"
      unfolding Modest_compute_ii_max_ll_def
      apply vcg
      done

  end


  export_llvm Modest_compute_ii_max_ll
    is "void compute_II_max(modest_size_t, modest_size_t, modest_dec_t, modest_mdp_t *, modest_ii_vals_t *)"
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
    file "modest_ii_max.ll"

end
