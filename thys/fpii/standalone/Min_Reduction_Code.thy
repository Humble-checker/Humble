theory Min_Reduction_Code
  imports "../Interval_Iteration_Tool_GS_Minred_Code"
begin

text \<open>Standalone export of the \<^emph>\<open>min reduction\<close> alone: given a Modest MDP, compute its MEC
  decomposition and turn every non-trivial, non-target, non-avoid state into an avoid sink, yielding
  \<^const>\<open>Min_red\<close>. No interval iteration --- the caller gets the reduced MDP back and may do what it
  likes with it.

  The function is not re-synthesised. \<^const>\<open>mop_min_red_impl_ll'\<close> is the one synthesised in
  \<^file>\<open>../Interval_Iteration_Tool_GS_Minred_Code.thy\<close>, where it is used as the first half of
  \<open>compute_II\<close>; the additions are the pointer-passing wrapper and the Hoare triple, both obtained by
  specialising what the pipeline already proves.

  Note the reduction needs no tolerance: unlike the interval-iteration entry points, this one takes
  no \<open>\<epsilon>\<close>.\<close>

  definition Modest_compute_min_red_ll :: "size_t \<Rightarrow> modest_mdpi ptr \<Rightarrow> modest_mdpi ptr \<Rightarrow> unit llM"
  where [llvm_code, llvm_inline]: "Modest_compute_min_red_ll ni \<M>ip resp \<equiv> doM {
    \<M>i \<leftarrow> ll_load \<M>ip;
    res \<leftarrow> mop_min_red_impl_ll' ni \<M>i;
    ll_store res resp
  }"

  section \<open>Hoare triples\<close>

  text \<open>The reduction's \<open>hn_refine\<close> against \<^const>\<open>op_min_red\<close>, inside
    \<^locale>\<open>interval_iteration_inf_code\<close> --- the code locale the min pipeline already uses. The MDP
    is a \<^emph>\<open>destroyed\<close> argument: the reduction rewrites it in place and hands the result back, so the
    input assertion is invalidated.\<close>

  context interval_iteration_inf_code
  begin

    lemma min_red_hnr: "hn_refine
      (Modest_mdp_inf_assn N \<M> \<M>i)
      (mop_min_red_impl_ll' ni \<M>i)
      (hn_invalid (Modest_mdp_inf_assn N) \<M> \<M>i)
      (Modest_mdp_inf_assn N) (\<lambda>_. True)
      (RETURN (op_min_red \<M>))"
    proof -
      note R = mop_min_red_impl_hnr_raw[to_hnr, simplified]
      show ?thesis
        apply (rule hn_refine_ref)
         apply (rule mop_min_red_impl_correct)
        apply (rule hn_refine_cons[OF _ R])
        unfolding hn_ctxt_def apply blast+
        done
    qed

  end

  text \<open>Main correctness theorem: what comes back is exactly \<^const>\<open>Min_red\<close> of the input.\<close>

  theorem compute_min_red_ll_htriple[vcg_rules]: "llvm_htriple
    (size_assn N ni ** Modest_mdp_inf_assn N \<M> \<M>i ** \<up>(2 * N < max_size_t)
       ** \<up>((\<epsilon>i::double, \<epsilon>::real) \<in> nn_real_lb_double_rel))

    (mop_min_red_impl_ll' ni \<M>i)

    (\<lambda>resi. EXS \<M>'. size_assn N ni ** hn_invalid (Modest_mdp_inf_assn N) \<M> \<M>i
       ** \<up>(2 * N < max_size_t)
       ** Modest_mdp_inf_assn N \<M>' resi
       ** \<up>(\<M>' = Min_red \<M>))"
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

    note [vcg_rules] = min_red_hnr[THEN hn_refineD, unfolded op_min_red_def]

    show ?thesis
      apply vcg
      done
  qed

  text \<open>\<dots> and the same including the pointer import/export done by the wrapper.\<close>

  context
  begin

    interpretation llvm_prim_setup . \<comment> \<open>For \<open>ll_load\<close>/\<open>ll_store\<close>\<close>

    corollary Modest_compute_min_red_ll_htriple: "llvm_htriple
      ( \<upharpoonleft>ll_pto \<M>i Mip ** \<upharpoonleft>ll_pto alloc resip
      ** size_assn N ni ** Modest_mdp_inf_assn N \<M> \<M>i ** \<up>(2 * N < max_size_t)
      ** \<up>((\<epsilon>i::double, \<epsilon>::real) \<in> nn_real_lb_double_rel))

      (Modest_compute_min_red_ll ni Mip resip)

      (\<lambda>_. EXS \<M>' resi. \<upharpoonleft>ll_pto resi resip ** \<upharpoonleft>ll_pto \<M>i Mip
        ** size_assn N ni ** hn_invalid (Modest_mdp_inf_assn N) \<M> \<M>i
        ** \<up>(2 * N < max_size_t)
        ** Modest_mdp_inf_assn N \<M>' resi
        ** \<up>(\<M>' = Min_red \<M>))"
      unfolding Modest_compute_min_red_ll_def
      apply vcg
      done

  end


  export_llvm Modest_compute_min_red_ll
    is "void compute_min_red(modest_size_t, modest_mdp_t *, modest_mdp_t *)"
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
  \<close>
    file "modest_min_red.ll"

end
