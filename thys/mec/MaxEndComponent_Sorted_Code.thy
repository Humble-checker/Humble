theory MaxEndComponent_Sorted_Code
  imports "MaxEndComponent_Code"
begin


  lemma sorted_wrt_sort_key_le:"(\<And> a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> g a \<le> g b \<Longrightarrow> f a b) \<Longrightarrow> sorted_wrt f (sort_key g xs)"
    apply(rule sorted_wrt_mono_rel[where ?P = "\<lambda> x y. g x \<le> g y"])
    by(auto simp flip: sorted_map[of g])

  lemma sorted_wrt_sort_key_lt:"(\<And> a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> g a < g b \<Longrightarrow> f a b) \<Longrightarrow> distinct xs \<Longrightarrow> inj_on g (set xs) \<Longrightarrow> sorted_wrt f (sort_key g xs)"
    apply(rule sorted_wrt_mono_rel[where ?P = "\<lambda> x y. g x < g y"])
    by(auto simp flip: sorted_wrt_map[of _ g] simp: strict_sorted_iff distinct_map)

  definition "compute_MEC_sorted_spec M \<equiv> SPEC (\<lambda>D. set D = Finite_MDP_defs.mec_decomp M \<and> distinct D \<and> sorted_wrt (\<lambda> x y. Inf x < Inf y) D)"
    

  definition "compute_MEC_sorted M = do {
    D \<leftarrow> mec_algo_defs.compute_MEC_spec M;
    RETURN (op_sort_by_inf D)
  }"

  lemma "Finite_MDP M \<Longrightarrow> compute_MEC_sorted M \<le> compute_MEC_sorted_spec M"
    unfolding compute_MEC_sorted_def compute_MEC_sorted_spec_def mec_algo_defs.compute_MEC_spec_def
    apply(refine_vcg)
    subgoal unfolding op_sort_by_inf_def Finite_MDP_defs.mec_decomp_def by auto
    subgoal unfolding op_sort_by_inf_def by simp
    subgoal unfolding op_sort_by_inf_def 
      by(auto 0 3 intro!: inj_on_nat_Inf sorted_wrt_sort_key_lt 
        simp: eq_bot_iff_states Finite_MDP_defs.mec_decomp_def 
        dest: mec_unique_state mec_imp_bot_eq_bot Finite_MDP.M_neq_bot) 
    done
  

  context mdp_graph_mec_impl_env
  begin

    interpretation disj_set_list_tuple_defs N N .

    interpretation modest_init_mdp_env N ni 
      apply(unfold_locales)
      using n_impl apply simp
      using N_BOUND by simp 
  

    sepref_definition compute_MEC_sorted_ll is "compute_MEC_sorted" :: "(Modest_MDP_DS_assn DS)\<^sup>k \<rightarrow>\<^sub>a mec_map_assn"
      unfolding compute_MEC_sorted_def


  end

end