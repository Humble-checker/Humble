theory Interval_Iteration_Tool_GS_Maxred_Impl
  imports "Interval_Iteration_Tool_GS_Maxred_Code" "../ds/Impl/Modest_MDP_II_Build_Sup"
begin

no_notation Finite_Cartesian_Product.matrix_matrix_mult (infixl "**" 70)

text \<open>Step 8, operational: the max-reduction pipeline as an \<open>nres\<close> program over the Modest data
  structure, and its refinement to LLVM.

  Kept in its own theory rather than added to \<^file>\<open>Interval_Iteration_Tool_GS_Maxred_Code.thy\<close>:
  importing the \<open>Impl\<close> layer there disturbs the \<^type>\<open>mdptc\<close> coercion (\<open>declare [[coercion to_mdpc]]\<close>,
  \<^file>\<open>../II/II_Def.thy\<close>) and breaks that theory's own proofs --- the same trap recorded in
  \<open>Modest_MDP_II_Minred_Impl\<close>'s header. Downstream of both, we simply write \<^const>\<open>to_mdpc\<close>
  explicitly wherever it is needed.\<close>

text \<open>Interval iteration \<^emph>\<open>bundled with the state space it ran on\<close>. This is not cosmetic: the two
  value arrays are refined by \<^const>\<open>output_lb_assn\<close>/\<^const>\<open>output_ub_assn\<close>, which mention \<open>M\<close>, and
  \<open>M\<close> may not escape into an exposed assertion. \<^const>\<open>Modest_build_out_assn\<close> is the \<open>M\<close>-free
  bundle of all four components, and it exists only for a value that \<^emph>\<open>contains\<close> the built MDP ---
  which is what fixes \<open>M\<close> internally.

  What it bundles is the \<^emph>\<open>triple\<close> \<^term>\<open>(\<MM>\<^sub>0,D,\<MM>')\<close> of \<^const>\<open>modest_build_rel_t\<close>: the input
  state space, its MEC decomposition, and the reduced state space built from them. All three are
  physically present in what the caller receives --- the builder allocates fresh arrays and never
  overwrites its input --- so the specification can name them all and say how they are related,
  instead of handing back only the reduced one.\<close>
definition ii_max_out ::
  "nat \<Rightarrow> (nat mdptc \<times> nat set list \<times> nat mdptc) \<Rightarrow> nat
     \<Rightarrow> ((nat mdptc \<times> nat set list \<times> nat mdptc) \<times> (nat \<Rightarrow> real) \<times> (nat \<Rightarrow> real) \<times> nat) nres" where
  "ii_max_out M t L = do {
     R \<leftarrow> ii_max_impl_x M (snd (snd t)) L;
     Refine_Basic.RETURN (t, R) }"

sepref_register ii_max_out

text \<open>The pipeline. Every \<^const>\<open>ASSERT\<close> is abstract or \<^emph>\<open>relative\<close> (\<open>M \<le> N\<close>) --- never a
  machine-word bound, per the hard rule in \<open>CLAUDE.md\<close>. The sepref layer cashes
  \<open>Suc M < max_size_t\<close> and \<open>2 * M < max_size_t\<close> from \<open>M \<le> N\<close> together with the locale's own
  \<open>n_impl\<close>. The MEC count is read off the decomposition at run time with
  \<^const>\<open>op_mec_map_length\<close>, which is why it can be an input parameter of the builder.\<close>

context modest_init_mdp_env_defs
begin

  definition "tool_pmax_impl \<M> L = do {
    ASSERT (compute_mecs_pre \<M>);
    D \<leftarrow> compute_MEC_sorted \<M>;
    let M = op_mec_map_length D;
    ASSERT (M \<le> N);
    ASSERT (reinterpret_pre (\<M>,D) \<and> M = length D);
    t \<leftarrow> op_build_reindex_t M (\<M>, D);
    ASSERT (states (to_mdpc (snd (snd t))) = {0..<M});
    ii_max_out M t L }"

end

text \<open>Towards \<open>tool_pmax_impl \<M> L \<le> tool_pmax \<M> L\<close>. The steps line up as follows:
  \<^const>\<open>op_sort_by_inf\<close> is \<^const>\<open>sort_key\<close>, so it preserves \<open>set\<close> and \<open>distinct\<close> and the sorted
  decomposition still meets \<^const>\<open>tool_pmax\<close>'s \<^const>\<open>SPEC\<close>; \<^const>\<open>op_build_reindex'\<close> unfolds to
  \<^term>\<open>Refine_Basic.RETURN (op_to_index (op_reinterpret (\<M>, D)))\<close>, matching \<^const>\<open>tool_pmax\<close>'s
  \<open>let\<close>; and the interval-iteration step is
  @{thm [source] interval_iteration_sup_code.ii_max_impl_correct}, which is why the refinement has to
  live in a code locale carrying \<open>n_impl\<close>/\<open>\<epsilon>_impl\<close> --- exactly as \<open>tool_pmin_impl_correct\<close> does on
  the min side.

  The one step that needed new work is the \<^const>\<open>ASSERT\<close> \<open>states (to_mdpc new) = {0..<M}\<close>, proved
  next.\<close>

subsection \<open>The one abstract fact: the re-indexed MDP's states are exactly \<open>{0..<length D}\<close>\<close>

text \<open>@{thm [source] to_index_states} proves this for a \<^emph>\<open>Modest-represented\<close> MDP; here \<^term>\<open>\<M>\<close> is
  an abstract \<^typ>\<open>nat mdptc\<close>, so it is redone from @{thm [source] idx_of_wd}. The \<open>\<subseteq>\<close> half is
  immediate; the \<open>\<supseteq>\<close> half needs that every element of \<^term>\<open>set D\<close> is \<^term>\<open>states m\<close> for some MEC
  \<open>m\<close> reachable as \<^term>\<open>the_mec\<close> of one of its own states --- which is where non-emptiness of a MEC
  comes in.\<close>

lemma states_to_index_img: "states (to_mdpc (to_index \<M>c D)) = idx_of D ` states \<M>c"
  unfolding to_index_to_mdpc by (simp add: states_map_mdpc states_reduce)

lemma states_to_index_abs:
  assumes WF: "MDPC_Reach_Avoid \<M>"
    and setD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>)" and dist: "distinct D"
  shows "states (to_mdpc (to_index (M_mec \<M>) D)) = {0..<length D}"
proof -
  interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
  have ST: "states (to_mdpc (to_index (M_mec \<M>) D)) = idx_of D ` states (M_mec \<M>)"
    by (rule states_to_index_img)
  have SD: "states m \<in> set D" if "m \<in> states (M_mec \<M>)" for m
  proof -
    from that obtain u where u: "u \<in> states (to_mdpc \<M>)" and mu: "m = the_mec (to_mdpc \<M>) u"
      by (auto simp: states_M_mec)
    have "mec (to_mdpc \<M>) m" unfolding mu using u by (rule the_mec)
    thus ?thesis unfolding setD Finite_MDP_defs.mec_decomp_def by auto
  qed
  have SUR: "\<exists>m \<in> states (M_mec \<M>). states m = X" if "X \<in> set D" for X
  proof -
    from that obtain m where mm: "mec (to_mdpc \<M>) m" and sm: "states m = X"
      unfolding setD Finite_MDP_defs.mec_decomp_def by auto
    have ne: "states m \<noteq> {}"
      using mm M.M_neq_bot by (metis mec_bot_imp_bot eq_bot_iff_states)
    then obtain s where s: "s \<in> states m" by auto
    have sM: "s \<in> states (to_mdpc \<M>)" using s mm by (meson mec_le states_mono subsetD)
    have "the_mec (to_mdpc \<M>) s = m" using mm s by (rule the_mec_eqI)
    hence "m \<in> states (M_mec \<M>)" using sM by (auto simp: states_M_mec)
    thus ?thesis using sm by auto
  qed
  show ?thesis
    unfolding ST
  proof (rule set_eqI, rule iffI)
    fix i assume "i \<in> idx_of D ` states (M_mec \<M>)"
    then obtain m where m: "m \<in> states (M_mec \<M>)" and im: "i = idx_of D m" by auto
    show "i \<in> {0..<length D}" using idx_of_wd(1)[OF dist SD[OF m]] im by simp
  next
    fix i assume i: "i \<in> {0..<length D}"
    hence iD: "D ! i \<in> set D" by auto
    from SUR[OF iD] obtain m where m: "m \<in> states (M_mec \<M>)" and sm: "states m = D ! i" by auto
    have "idx_of D m = i"
      using idx_of_wd[OF dist SD[OF m]] sm i dist
      by (metis atLeastLessThan_iff nth_eq_iff_index_eq)
    thus "i \<in> idx_of D ` states (M_mec \<M>)" using m by auto
  qed
qed

subsection \<open>\<dots> and there are no more of them than there are states\<close>

text \<open>The counterpart of @{thm [source] to_index_card} for an abstract \<^typ>\<open>nat mdptc\<close>: the MEC
  count is bounded by the state count, so the sepref layer can cash \<open>Suc M < max_size_t\<close> and
  \<open>2 * M < max_size_t\<close> from the locale's own \<open>n_impl\<close>. The MECs of a finite MDP are the image of its
  states under \<^const>\<open>the_mec\<close>, and the re-indexing is onto \<open>{0..<length D}\<close>, so two applications of
  @{thm [source] card_image_le} suffice.\<close>

lemma mec_count_le:
  assumes WF: "MDPC_Reach_Avoid \<M>"
    and setD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>)" and dist: "distinct D"
    and ST: "states (to_mdpc \<M>) = {0..<N}"
  shows "length D \<le> N"
proof -
  have FIN: "finite (states (to_mdpc \<M>))" using ST by simp
  have FM: "finite (states (M_mec \<M>))" unfolding states_M_mec using FIN by simp
  have "length D = card {0..<length D}" by simp
  also have "\<dots> = card (idx_of D ` states (M_mec \<M>))"
    using states_to_index_abs[OF WF setD dist] states_to_index_img by simp
  also have "\<dots> \<le> card (states (M_mec \<M>))" using FM by (rule card_image_le)
  also have "\<dots> \<le> card (states (to_mdpc \<M>))"
    unfolding states_M_mec using FIN by (rule card_image_le)
  also have "\<dots> = N" using ST by simp
  finally show ?thesis .
qed

subsection \<open>Interval iteration, freed from the code locale\<close>

text \<open>@{thm [source] interval_iteration_sup_code.ii_max_impl_correct} is stated inside a locale that
  also fixes the \<^emph>\<open>concrete\<close> parameters \<open>ni\<close>/\<open>\<epsilon>i\<close>. Its proof uses none of them ---
  \<^const>\<open>interval_iteration_sup_env_defs.ii_max_impl\<close> mentions no locale parameter at all --- so the
  same chain goes through from the abstract assumption alone, which is what the pipeline can supply
  about the \<^emph>\<open>built\<close> state space.\<close>

lemma ii_max_impl_correct_abs:
  assumes WF: "MDPC_Reach_Avoid_Sup m"
  shows "ii_max_impl_x M m L \<le> mop_interval_iteration_sup m L"
proof -
  interpret M: MDPC_Reach_Avoid_Sup m by (rule WF)
  have "ii_max_impl_x M m L = M.mop_interval_iteration_gs L"
    unfolding ii_max_impl_x_def interval_iteration_sup_env_defs.ii_max_impl_def
      M.mop_interval_iteration_gs_def interval_iteration_sup_env_defs.mop_state_vals_gs_sup_def
      next_iter_max_def
    by blast
  also note M.mop_interval_iteration_gs_correct
  also have "M.interval_iteration_pspec = mop_interval_iteration_sup m L"
    unfolding mop_interval_iteration_sup_def by presburger
  finally show ?thesis .
qed

subsection \<open>The re-indexed MDP is itself a reach-avoid \<open>Sup\<close> problem\<close>

text \<open>\<^const>\<open>to_index\<close> is the relabelling of \<^const>\<open>Max_red\<close> by \<^const>\<open>idx_of\<close>
  (@{thm [source] to_index_map_mdptc}), and @{thm [source] idx_of_inj} says that relabelling is
  injective, so @{thm [source] map_mdptc_reach_avoid} applies. \<^locale>\<open>MDPC_Reach_Avoid_Sup\<close> adds no
  assumption over \<^locale>\<open>MDPC_Reach_Avoid\<close> --- it only selects the \<open>Sup\<close> mode --- so this is all
  that is needed to run interval iteration on the collapsed space.\<close>

lemma reach_avoid_sup_to_index:
  assumes WF: "MDPC_Reach_Avoid \<M>"
    and setD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>)" and dist: "distinct D"
  shows "MDPC_Reach_Avoid_Sup (to_index (M_mec \<M>) D)"
proof -
  interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
  have inj: "inj_on (idx_of D) (states (Max_red \<M>))"
    using idx_of_inj[OF WF setD dist] by (simp add: states_Max_red)
  have EQ: "to_index (M_mec \<M>) D = map_mdptc (idx_of D) (Max_red \<M>)"
    by (simp add: to_index_map_mdptc M.reduce_M_mec)
  show ?thesis
    unfolding MDPC_Reach_Avoid_Sup_def EQ
    by (rule map_mdptc_reach_avoid[OF M.MDPC_Reach_Avoid_max_red inj])
qed


section \<open>The pipeline's specification, naming both state spaces\<close>

text \<open>Because the result carries the whole triple, the specification can name every component and
  say how they are related: \<^term>\<open>\<MM>\<^sub>0\<close> is the state space that was handed in, \<^term>\<open>D\<close> is a MEC
  decomposition of it, and the reduced state space \<^term>\<open>\<MM>'\<close> is \<^emph>\<open>the\<close> max reduction
  \<^const>\<open>Max_red\<close> of \<^term>\<open>\<MM>\<^sub>0\<close>, relabelled by \<open>idx_of D\<close> --- the injection that sends a MEC
  to its position in \<^term>\<open>D\<close>. Together with \<^term>\<open>states (to_mdpc \<MM>') = {0..<length D}\<close> that pins
  the relabelling down: \<^term>\<open>\<MM>'\<close> is \<^const>\<open>Max_red\<close> with its states numbered consecutively in the
  order \<^term>\<open>D\<close> lists their MECs.

  \<^const>\<open>tool_pmax_spec\<close> says only that \<^emph>\<open>some\<close> relabelling of \<^const>\<open>Max_red\<close> comes back, and
  mentions neither the input nor the decomposition; it is recovered by projection
  (\<open>tool_pmax_spec_t_proj\<close>).\<close>

definition tool_pmax_spec_at
  :: "nat mdptc \<Rightarrow> nat set list \<Rightarrow> nat
       \<Rightarrow> ((nat mdptc \<times> nat set list \<times> nat mdptc) \<times> (nat \<Rightarrow> real) \<times> (nat \<Rightarrow> real) \<times> nat) nres" where
  "tool_pmax_spec_at \<MM> D L =
     SPEC (\<lambda>((\<MM>\<^sub>0, D', \<MM>'), lb, ub, i).
        \<MM>\<^sub>0 = \<MM> \<and> D' = D
        \<and> \<MM>' = map_mdptc (idx_of D) (Max_red \<MM>)
        \<and> inj_on (idx_of D) (states (Max_red \<MM>))
        \<and> states (to_mdpc \<MM>') = {0..<length D}
        \<and> (\<forall>u \<in> states (to_mdpc \<MM>).
             lb (idx_of D (the_mec (to_mdpc \<MM>) u)) \<le> MDPC_Reach_Avoid.p_real \<MM> u
             \<and> MDPC_Reach_Avoid.p_real \<MM> u \<le> ub (idx_of D (the_mec (to_mdpc \<MM>) u))))"

definition tool_pmax_spec_t
  :: "nat mdptc \<Rightarrow> nat
       \<Rightarrow> ((nat mdptc \<times> nat set list \<times> nat mdptc) \<times> (nat \<Rightarrow> real) \<times> (nat \<Rightarrow> real) \<times> nat) nres" where
  "tool_pmax_spec_t \<MM> L =
     SPEC (\<lambda>((\<MM>\<^sub>0, D, \<MM>'), lb, ub, i).
        \<MM>\<^sub>0 = \<MM>
        \<and> set D = Finite_MDP_defs.mec_decomp (to_mdpc \<MM>) \<and> distinct D
        \<and> \<MM>' = map_mdptc (idx_of D) (Max_red \<MM>)
        \<and> inj_on (idx_of D) (states (Max_red \<MM>))
        \<and> states (to_mdpc \<MM>') = {0..<length D}
        \<and> (\<forall>u \<in> states (to_mdpc \<MM>).
             lb (idx_of D (the_mec (to_mdpc \<MM>) u)) \<le> MDPC_Reach_Avoid.p_real \<MM> u
             \<and> MDPC_Reach_Avoid.p_real \<MM> u \<le> ub (idx_of D (the_mec (to_mdpc \<MM>) u))))"

lemma tool_pmax_spec_at_le:
  assumes setD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<MM>)" and dist: "distinct D"
  shows "tool_pmax_spec_at \<MM> D L \<le> tool_pmax_spec_t \<MM> L"
  unfolding tool_pmax_spec_at_def tool_pmax_spec_t_def
  using setD dist by (auto simp: pw_le_iff refine_pw_simps split: prod.splits)

text \<open>Forgetting the input and the decomposition gives back the original specification.\<close>
lemma tool_pmax_spec_t_proj:
  "do { r \<leftarrow> tool_pmax_spec_t \<MM> L; Refine_Basic.RETURN (snd (snd (fst r)), snd r) }
     \<le> tool_pmax_spec \<MM> L"
  unfolding tool_pmax_spec_t_def tool_pmax_spec_def
  by (auto simp: pw_le_iff refine_pw_simps split: prod.splits)


section \<open>The pipeline refines it\<close>

text \<open>Everything downstream of the decomposition, in one step. The three \<^const>\<open>ASSERT\<close>s discharge
  against @{thm [source] mec_count_le}, @{thm [source] states_to_index_abs} and
  @{thm [source] reach_avoid_sup_to_index}; \<^const>\<open>op_build_reindex_t\<close> is a \<^const>\<open>RETURN\<close>, so what
  remains is the interval-iteration step, whose bounds transfer back to the \<^emph>\<open>original\<close> nodes by
  @{thm [source] p_real_new}.\<close>

lemma (in modest_init_mdp_env_defs) tool_pmax_impl_step:
  assumes WF: "MDPC_Reach_Avoid \<M>"
    and ST: "states (to_mdpc \<M>) = {0..<N}"
    and setD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>)" and dist: "distinct D"
  shows "do { ASSERT (op_mec_map_length D \<le> N);
              ASSERT (reinterpret_pre (\<M>,D) \<and> op_mec_map_length D = length D);
              t \<leftarrow> op_build_reindex_t (op_mec_map_length D) (\<M>, D);
              ASSERT (states (to_mdpc (snd (snd t))) = {0..<op_mec_map_length D});
              ii_max_out (op_mec_map_length D) t L }
         \<le> tool_pmax_spec_at \<M> D L"
proof -
  have NEW: "op_to_index (op_reinterpret (\<M>, D)) = to_index (M_mec \<M>) D"
    unfolding op_to_index_def op_reinterpret_def by simp
  have MLEN: "op_mec_map_length D = length D" unfolding op_mec_map_length_def by (rule refl)
  have MLE: "length D \<le> N" by (rule mec_count_le[OF WF setD dist ST])
  have RP: "reinterpret_pre (\<M>,D)"
    unfolding reinterpret_pre_def using setD dist by simp
  have STN: "states (to_mdpc (to_index (M_mec \<M>) D)) = {0..<length D}"
    by (rule states_to_index_abs[OF WF setD dist])
  have SUP: "MDPC_Reach_Avoid_Sup (to_index (M_mec \<M>) D)"
    by (rule reach_avoid_sup_to_index[OF WF setD dist])
  have INJ: "inj_on (idx_of D) (states (Max_red \<M>))"
    using idx_of_inj[OF WF setD dist] by (simp add: states_Max_red)
  have EQ: "to_index (M_mec \<M>) D = map_mdptc (idx_of D) (Max_red \<M>)"
    by (simp add: to_index_map_mdptc MDPC_Reach_Avoid.reduce_M_mec[OF WF])

  have MEM: "idx_of D (the_mec (to_mdpc \<M>) u) \<in> states (to_mdpc (to_index (M_mec \<M>) D))"
    if "u \<in> states (to_mdpc \<M>)" for u
    using that unfolding states_to_index_img by (auto simp: states_M_mec)
  have PV: "MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) (idx_of D (the_mec (to_mdpc \<M>) u))
              = MDPC_Reach_Avoid.p_real \<M> u"
    if "u \<in> states (to_mdpc \<M>)" for u
    by (rule p_real_new[OF WF setD dist that])

  text \<open>Bounds proved on the \<^emph>\<open>re-indexed\<close> space transfer back to the original nodes: a node's own
    probability is the value its MEC's index carries (@{thm [source] p_real_new}), and that index is
    a state of the re-indexed space, so the bracket the loop established there is a bracket here.\<close>
  have TRANSFER: "\<forall>u \<in> states (to_mdpc \<M>).
        lb (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> MDPC_Reach_Avoid.p_real \<M> u
        \<and> MDPC_Reach_Avoid.p_real \<M> u \<le> ub (idx_of D (the_mec (to_mdpc \<M>) u))"
    if B: "\<forall>v \<in> states (to_mdpc (to_index (M_mec \<M>) D)).
             lb v \<le> MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) v
             \<and> MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) v \<le> ub v"
    for lb ub :: "nat \<Rightarrow> real"
  proof
    fix u assume u: "u \<in> states (to_mdpc \<M>)"
    have "lb (idx_of D (the_mec (to_mdpc \<M>) u))
            \<le> MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) (idx_of D (the_mec (to_mdpc \<M>) u))
          \<and> MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) (idx_of D (the_mec (to_mdpc \<M>) u))
            \<le> ub (idx_of D (the_mec (to_mdpc \<M>) u))"
      using B MEM[OF u] by blast
    thus "lb (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> MDPC_Reach_Avoid.p_real \<M> u
          \<and> MDPC_Reach_Avoid.p_real \<M> u \<le> ub (idx_of D (the_mec (to_mdpc \<M>) u))"
      unfolding PV[OF u] .
  qed

  have BOUNDS: "ii_max_impl_x (length D) (to_index (M_mec \<M>) D) L
      \<le> SPEC (\<lambda>(lb,ub,i). \<forall>u \<in> states (to_mdpc \<M>).
            lb (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> MDPC_Reach_Avoid.p_real \<M> u
            \<and> MDPC_Reach_Avoid.p_real \<M> u \<le> ub (idx_of D (the_mec (to_mdpc \<M>) u)))"
  proof -
    note ii_max_impl_correct_abs[OF SUP, of "length D" L]
    also have "mop_interval_iteration_sup (to_index (M_mec \<M>) D) L
      \<le> SPEC (\<lambda>(lb,ub,i). \<forall>u \<in> states (to_mdpc \<M>).
            lb (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> MDPC_Reach_Avoid.p_real \<M> u
            \<and> MDPC_Reach_Avoid.p_real \<M> u \<le> ub (idx_of D (the_mec (to_mdpc \<M>) u)))"
      unfolding mop_interval_iteration_sup_def
        interval_iteration_defs.interval_iteration_spec_def
      using TRANSFER by (auto simp: pw_le_iff refine_pw_simps split: prod.splits)
    finally show ?thesis .
  qed

  show ?thesis
    unfolding op_build_reindex_t_def op_build_reindex_tp_def op_build_reindex_def
      op_build_index_def ii_max_out_def tool_pmax_spec_at_def MLEN NEW
    apply (simp add: RP MLE STN)
    using BOUNDS INJ EQ STN
    by (auto simp: pw_le_iff refine_pw_simps split: prod.splits)
qed

lemma (in modest_init_mdp_env_defs) tool_pmax_impl_correct:
  assumes WF: "MDPC_Reach_Avoid_Sup \<M>"
    and ST: "states (to_mdpc \<M>) = {0..<N}"
  shows "tool_pmax_impl \<M> L \<le> tool_pmax_spec_t \<M> L"
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
  have SORTD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D"
    if "Refine_Basic.RETURN D \<le> compute_MEC_sorted \<M>" for D
    using order_trans[OF that SORT] by simp
  have STEP: "tool_pmax_impl \<M> L
        \<le> do { D \<leftarrow> SPEC (\<lambda>D. set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D);
               tool_pmax_spec_at \<M> D L }"
    unfolding tool_pmax_impl_def Let_def
    apply (rule ASSERT_leI[OF PRE])
    apply (rule bind_mono(1)[OF SORT])
    subgoal for D
      using tool_pmax_impl_step[OF WFa ST, of D L] SORTD[of D] by simp
    done
  also have "do { D \<leftarrow> SPEC (\<lambda>D. set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D);
                  tool_pmax_spec_at \<M> D L }
             \<le> tool_pmax_spec_t \<M> L"
    unfolding tool_pmax_spec_at_def tool_pmax_spec_t_def
    by (auto simp: pw_le_iff refine_pw_simps split: prod.splits)
  finally show ?thesis .
qed

text \<open>Step 9 for the Modest pipeline: the operational program meets the specification outright, and
  \<^emph>\<open>a fortiori\<close> the original \<^const>\<open>tool_pmax_spec\<close> once the extra components are projected away.\<close>

lemma (in modest_init_mdp_env_defs) tool_pmax_impl_spec:
  assumes WF: "MDPC_Reach_Avoid_Sup \<M>"
    and ST: "states (to_mdpc \<M>) = {0..<N}"
  shows "tool_pmax_impl \<M> L \<le> tool_pmax_spec_t \<M> L"
  by (rule tool_pmax_impl_correct[OF WF ST])

lemma (in modest_init_mdp_env_defs) tool_pmax_impl_spec_proj:
  assumes WF: "MDPC_Reach_Avoid_Sup \<M>"
    and ST: "states (to_mdpc \<M>) = {0..<N}"
  shows "do { r \<leftarrow> tool_pmax_impl \<M> L; Refine_Basic.RETURN (snd (snd (fst r)), snd r) }
         \<le> tool_pmax_spec \<M> L"
  using order_trans[OF bind_mono(1)[OF tool_pmax_impl_correct[OF WF ST] order_refl]
                       tool_pmax_spec_t_proj] .
section \<open>LLVM synthesis\<close>

subsection \<open>\<^const>\<open>ii_max_out\<close>: the loop, then the bundle\<close>

text \<open>This step is done by hand rather than by \<^theory_text>\<open>sepref\<close>. The reason is a genuine limitation:
  @{thm [source] ii_max_built_x_hnr} is a \<^emph>\<open>dependent-result\<close> rule (\<open>\<rightarrow>\<^sub>d\<close>), so the assertion
  \<^theory_text>\<open>sepref\<close> installs for its result, \<^term>\<open>output_lb_assn M \<times>\<^sub>a output_ub_assn M \<times>\<^sub>a snat_assn\<close>,
  mentions the \<^emph>\<open>goal's own bound variable\<close> \<open>M\<close>. Every subsequent translation step then has to
  instantiate a rule's assertion schematic with a term containing that bound variable, and the
  translation phase fails --- \<^theory_text>\<open>sepref\<close>'s \<open>Apply rule\<close> phase refuses even the plain
  \<^const>\<open>Pair\<close> rule @{thm [source] hn_Pair}. (Verified: the very same \<^theory_text>\<open>sepref_definition\<close> goes
  through when the inner rule's result assertion is closed.) So the pairing is done here instead,
  and what \<^theory_text>\<open>sepref\<close> sees downstream is the \<open>M\<close>-free \<open>ii_max_out_hnr\<close> below.

  Note the limitation is about a result assertion that \<^emph>\<open>genuinely depends\<close> on the new argument.
  A \<open>\<rightarrow>\<^sub>d\<close> whose result does not mention it is not a case of this: collapse it to a plain \<open>\<rightarrow>\<close> first,
  as @{thm [source] build_reindex_hnr_arg_t} does, and the question never arises.\<close>

text \<open>The generic step: a call that keeps its whole precondition, followed by returning a pure
  function of its result. The \<open>PACK\<close> premise is where the result assertion is rebuilt --- for us,
  @{thm [source] build_out_bundle}.\<close>

lemma hn_refine_bind_pack:
  assumes INNER: "hn_refine \<Gamma> c \<Gamma> R CP m"
  assumes PACK: "\<And>v vi. \<Gamma> ** R v vi \<turnstile> \<Gamma>' ** S (f v) (g vi)"
  shows "hn_refine \<Gamma> (doM { v \<leftarrow> c; Mreturn (g v) }) \<Gamma>' S (\<lambda>_. True)
           (m \<bind> (\<lambda>v. Refine_Basic.RETURN (f v)))"
proof (rule hn_refineI)
  assume NF: "nofail (m \<bind> (\<lambda>v. Refine_Basic.RETURN (f v)))"
  hence NFm: "nofail m" by (auto simp: refine_pw_simps)
  note H = hn_refineD[OF INNER NFm]
  show "llvm_htriple \<Gamma> (doM { v \<leftarrow> c; Mreturn (g v) })
          (\<lambda>r. \<Gamma>' ** \<up>True
               ** (EXS y. S y r ** \<up>(Refine_Basic.RETURN y \<le> m \<bind> (\<lambda>v. Refine_Basic.RETURN (f v)))))"
    supply [vcg_rules] = H
    apply vcg
    subgoal premises prems for asf r sa x
    proof -
      have LE: "Refine_Basic.RETURN (f x) \<le> m \<bind> (\<lambda>v. Refine_Basic.RETURN (f v))"
        using prems by (auto simp: pw_le_iff refine_pw_simps)
      have "\<Gamma> ** R x r \<turnstile> \<Gamma>' ** S (f x) (g r)" by (rule PACK)
      also have "\<dots> \<turnstile> \<Gamma>' ** \<up>True ** (EXS y. S y (g r)
                      ** \<up>(Refine_Basic.RETURN y \<le> m \<bind> (\<lambda>v. Refine_Basic.RETURN (f v))))"
        using LE by (auto simp: entails_def sep_conj_def pred_lift_extract_simps)
      finally show ?thesis unfolding ENTAILS_def .
    qed
    done
qed

text \<open>The emitted function: the loop, then two \<open>insertvalue\<close>s that put the built MDP in front of
  the value triple.\<close>

definition ii_max_out_ll where [llvm_code]:
  "ii_max_out_ll Mi \<epsilon>i mi (Li::size_t) = doM {
     R \<leftarrow> ii_max_built_ll' Mi \<epsilon>i mi Li;
     s \<leftarrow> prod_insert_fst init mi;
     s \<leftarrow> prod_insert_snd s (R :: double ptr \<times> double ptr \<times> size_t);
     Mreturn s }"

lemma ii_max_out_ll_alt:
  "ii_max_out_ll Mi \<epsilon>i mi Li = doM { R \<leftarrow> ii_max_built_ll' Mi \<epsilon>i mi Li; Mreturn (mi, R) }"
  unfolding ii_max_out_ll_def by (simp add: prod_ops_simp)

lemma ii_max_out_hnr_aux:
  assumes EPS: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
  assumes MREL: "(Mi,M) \<in> snat_rel"
  assumes MB: "2*M < max_size_t"
  assumes ST: "states (to_mdpc (snd (snd t))) = {0..<M}"
  shows "hn_refine (snat_assn M Mi ** Modest_build_assn_t N\<^sub>0 t mi ** snat_assn L Li)
           (ii_max_out_ll Mi \<epsilon>i mi Li)
           (snat_assn M Mi ** invalid_assn (Modest_build_assn_t N\<^sub>0) t mi ** snat_assn L Li)
           (Modest_build_out_assn N\<^sub>0) (\<lambda>_. True)
           (ii_max_out M t L)"
proof -
  have DUP: "Modest_build_assn_t N\<^sub>0 t mi
    = (invalid_assn (Modest_build_assn_t N\<^sub>0) t mi ** Modest_build_assn_t N\<^sub>0 t mi)"
    by (rule invalidate_clone)
  have PACK: "(snat_assn M Mi ** Modest_build_assn_t N\<^sub>0 t mi ** snat_assn L Li)
      ** (output_lb_assn M \<times>\<^sub>a output_ub_assn M \<times>\<^sub>a snat_assn) v vi
      \<turnstile> (snat_assn M Mi ** invalid_assn (Modest_build_assn_t N\<^sub>0) t mi ** snat_assn L Li)
        ** Modest_build_out_assn N\<^sub>0 (t,v) (mi,vi)" for v vi
  proof -
    obtain lb ub i where V: "v = (lb,ub,i)" by (cases v; cases "snd v") auto
    obtain lbi ubi ii where VI: "vi = (lbi,ubi,ii)" by (cases vi; cases "snd vi") auto
    show ?thesis
      unfolding V VI prod_assn_pair_conv
      apply (rule entails_trans[OF _ conj_entails_mono[OF entails_refl build_out_bundle[OF ST]]])
      apply (subst DUP)
      by (simp add: sep_conj_ac entails_refl)
  qed
  show ?thesis
    unfolding ii_max_out_ll_alt ii_max_out_def
    by (rule hn_refine_bind_pack[where f = "\<lambda>v. (t,v)" and g = "\<lambda>vi. (mi,vi)",
          OF ii_max_built_t_hnr_aux2[OF EPS MREL MB ST] PACK])
qed

text \<open>\<dots> and as a rule \<^theory_text>\<open>sepref\<close> can use: every assertion, argument and result alike, is \<open>M\<close>-free.\<close>

lemma ii_max_out_hnr:
  assumes EPS: "(\<epsilon>i,\<epsilon>) \<in> nn_real_lb_double_rel"
  shows "(uncurry2 (\<lambda>Mi t L. ii_max_out_ll Mi \<epsilon>i t L), uncurry2 ii_max_out)
    \<in> [\<lambda>((M,t),L). 2*M < max_size_t \<and> states (to_mdpc (snd (snd t))) = {0..<M}]\<^sub>a
        size_assn\<^sup>k *\<^sub>a (Modest_build_assn_t N\<^sub>0)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> Modest_build_out_assn N\<^sub>0"
  apply (rule hfrefI)
  apply (clarsimp split: prod.splits)
  apply (rule hn_refine_preI)
  apply (rule ii_max_out_hnr_aux[OF EPS])
    apply (auto simp: sep_conj_def pure_def pred_lift_extract_simps)
  done

subsection \<open>The whole pipeline, synthesised\<close>

text \<open>With both pipeline rules stated at \<open>M\<close>-free assertions the synthesis is bare: the MEC
  decomposition, its length, the builder and the interval iteration are all registered operations.
  The only side conditions are the two machine-word bounds, and both are cashed --- as the hard rule
  in \<open>CLAUDE.md\<close> prescribes --- from the \<^emph>\<open>relative\<close> \<^term>\<open>M \<le> N\<close> that the program asserts,
  together with the locale's own \<open>n_impl\<close>.\<close>

context interval_iteration_sup_env
begin

  text \<open>The two machine-word bounds, from the \<^emph>\<open>relative\<close> \<^term>\<open>M \<le> N\<close> alone. Stated before the
    \<^theory_text>\<open>interpretation\<close> below, which would otherwise shadow \<^locale>\<open>interval_iteration_env\<close>'s \<open>n_impl\<close>
    with \<^locale>\<open>modest_init_mdp_env\<close>'s weaker one.\<close>
  lemma M_bound_2: "M \<le> N \<Longrightarrow> 2 * M < max_size_t" using n_impl by auto
  lemma M_bound_Suc: "M \<le> N \<Longrightarrow> Suc M < max_size_t" using n_impl by (auto simp: max_snat_def)

  interpretation modest_init_mdp_env N ni
    apply unfold_locales using n_impl by auto

  interpretation disj_set_list_tuple_defs N N ni ni .
  interpretation disj_set_list_tuple_env N N ni ni
    unfolding disj_set_list_tuple_env_def using n_impl by satx

  lemmas ii_max_out_hnr'[sepref_fr_rules] = ii_max_out_hnr[OF \<epsilon>_impl, where N\<^sub>0 = N]
  lemmas build_reindex_hnr_arg_t'[sepref_fr_rules] =
    build_reindex_hnr_arg_t[OF interval_iteration_env_axioms]

  sepref_definition tool_pmax_impl_ll is "uncurry tool_pmax_impl"
    :: "(Modest_mdp_sup_assn N)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a Modest_build_out_assn N"
    unfolding tool_pmax_impl_def compute_MEC_sorted_def
    supply [elim] = M_bound_Suc M_bound_2
    supply [simp] = bind_ref_tag_def op_mec_map_length_def
    by sepref

  text \<open>The emitted pipeline function, and the rule at the exposed assertion. Deliberately \<^emph>\<open>not\<close>
    \<^theory_text>\<open>[sepref_fr_rules]\<close>, matching the min side.\<close>
  concrete_definition (in -) tool_pmax_impl_ll' [llvm_code] is
    interval_iteration_sup_env.tool_pmax_impl_ll_def

  lemmas tool_pmax_impl_hnr_raw =
    tool_pmax_impl_ll.refine[unfolded tool_pmax_impl_ll'.refine[OF interval_iteration_sup_env_axioms]]

end


section \<open>Step 9: the Hoare triple\<close>

text \<open>\<^locale>\<open>interval_iteration_sup_code\<close> already fixes exactly what is needed --- a reach-avoid
  \<^term>\<open>\<M>\<close>, its size \<open>N\<close>/\<open>ni\<close>, the tolerance \<open>\<epsilon>\<close>/\<open>\<epsilon>i\<close>, and \<open>states (to_mdpc \<M>) = {0..<N}\<close> --- so no
  new code locale is needed; this mirrors \<open>interval_iteration_inf_hnr\<close> on the min side.\<close>

context interval_iteration_sup_code
begin

  lemma WF_sup: "MDPC_Reach_Avoid_Sup \<M>"
    by (simp add: MDPC_Reach_Avoid_Sup_def MDPC_Reach_Avoid_axioms)

  lemma tool_pmax_hnr: "hn_refine
    (Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li)
    (tool_pmax_impl_ll' ni \<epsilon>i \<M>i Li)
    (hn_invalid (Modest_mdp_sup_assn N) \<M> \<M>i ** snat_assn L Li)
    (Modest_build_out_assn N) (\<lambda>_. True)
    (tool_pmax_spec_t \<M> L)"
  proof -
    note R = tool_pmax_impl_hnr_raw[to_hnr, simplified]
    show ?thesis
      apply (rule hn_refine_ref)
       apply (rule tool_pmax_impl_spec[OF WF_sup states_M, of L])
      apply (rule hn_refine_cons[OF _ R])
      unfolding hn_ctxt_def apply blast+
      done
  qed

end

abbreviation "p_real' \<equiv> MDPC_Reach_Avoid.p_real"


text \<open>Main correctness theorem, mirroring \<open>interval_iteration_inf_ll_htriple\<close>. What the caller gets
  back holds \<^emph>\<open>both\<close> state spaces and the decomposition that relates them:

    \<^item> \<^term>\<open>\<M>\<^sub>0\<close> is the state space that was passed in --- unchanged, \<^term>\<open>\<M>\<^sub>0 = \<M>\<close>;
    \<^item> \<^term>\<open>D\<close> is a MEC decomposition of it (a duplicate-free enumeration of \<^term>\<open>mec_decomp\<close>);
    \<^item> \<^term>\<open>\<M>'\<close> is \<^emph>\<open>the max reduction of\<close> \<^term>\<open>\<M>\<close>: literally \<^const>\<open>Max_red\<close> relabelled by the
      injection \<open>idx_of D\<close>, whose states are exactly \<^term>\<open>{0..<length D}\<close>.

  and the two value arrays bracket each original node's reach-avoid probability at the index its own
  MEC received. \<open>M\<close> never appears --- \<^const>\<open>Modest_build_out_assn\<close> bundles it away.\<close>

theorem tool_pmax_ll_htriple[vcg_rules]: "llvm_htriple
  (size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li
     ** \<up>(2 * N < max_size_t))

  (tool_pmax_impl_ll' ni \<epsilon>i \<M>i Li)

  (\<lambda>resi. EXS \<M>\<^sub>0 D \<M>' x y i. size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i
     ** hn_invalid (Modest_mdp_sup_assn N) \<M> \<M>i ** snat_assn L Li
     ** \<up>(2 * N < max_size_t)
     ** Modest_build_out_assn N ((\<M>\<^sub>0,D,\<M>'),x,y,i) resi
     ** \<up>(\<M>\<^sub>0 = \<M>
          \<and> set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D
          \<and> \<M>' = map_mdptc (idx_of D) (Max_red \<M>)
          \<and> inj_on (idx_of D) (states (Max_red \<M>))
          \<and> states (to_mdpc \<M>') = {0..<length D}
          \<and> (\<forall>u \<in> states (to_mdpc \<M>). x (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> p_real' \<M> u
                \<and> p_real' \<M> u \<le> y (idx_of D (the_mec (to_mdpc \<M>) u)))))"
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

  note [vcg_rules] = tool_pmax_hnr[THEN hn_refineD, unfolded tool_pmax_spec_t_def]

  show ?thesis
    apply vcg
    done
qed


section \<open>The C entry point\<close>

text \<open>The result the caller gets back is the whole bundle \<^const>\<open>Modest_build_out_assn\<close> describes:
  the input MDP and the re-indexed reduced one, the MEC decomposition that relates them, and the two
  value arrays with the iteration count.\<close>

type_synonym modest_pmax_res =
  "((modest_mdpi \<times> modest_mdpi) \<times> mec_mapi) \<times> double ptr \<times> double ptr \<times> size_t"

definition Modest_tool_pmax_impl_ll ::
  "size_t \<Rightarrow> size_t \<Rightarrow> double \<Rightarrow> modest_mdpi ptr \<Rightarrow> modest_pmax_res ptr \<Rightarrow> unit llM"
where [llvm_code, llvm_inline]: "Modest_tool_pmax_impl_ll Li ni \<epsilon>i Eip resp \<equiv> doM {
  Ei \<leftarrow> ll_load Eip;
  res \<leftarrow> tool_pmax_impl_ll' ni \<epsilon>i Ei Li;
  ll_store res resp
}"


subsection \<open>Correctness Theorems\<close>

  lemma mec_bot: "mec \<bottom> m \<longleftrightarrow> m=\<bottom>"
    unfolding mec_def by auto

  (* TODO Move: List D is a partitioning of set S, assigning each partition an index *)
  definition "is_partitioning D S \<equiv> distinct D \<and> S = \<Union>(set D) \<and> (\<forall>m\<^sub>1\<in>set D. \<forall>m\<^sub>2\<in>set D. m\<^sub>1\<noteq>m\<^sub>2 \<longrightarrow> m\<^sub>1\<inter>m\<^sub>2 = {})"
  definition "idx_of' D u \<equiv> THE i. i<length D \<and> u\<in>D!i"  
    
  (* TODO Move: Additions for map_mdptc *)  
  lemma map_mdptc_id: "map_mdptc id = id"
    unfolding map_mdptc_def 
    apply transfer
    by (auto simp: map_mdpc_id)
    
  lemma map_mdptc_compose: "map_mdptc f (map_mdptc g m) = map_mdptc (f o g) m"  
    unfolding map_mdptc_def 
    apply transfer
    apply (auto simp: map_mdpc_compose)
    done
  
  lemma map_mdptc_cong: "\<lbrakk>closed_mdpc (to_mdpc \<M>); \<And>x. x \<in> states (to_mdpc \<M>) \<union> avoids \<M> \<union> targets \<M> \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> map_mdptc f \<M> = map_mdptc g \<M>"  
    unfolding map_mdptc_def 
    apply transfer
    apply (auto cong: map_mdpc_cong_states)
    done
    
  corollary map_mdptcRA_cong:
    assumes "MDPC_Reach_Avoid \<M>"  
    assumes "\<And>x. x \<in> states (to_mdpc \<M>) \<Longrightarrow> f x = g x"
    shows "map_mdptc f \<M> = map_mdptc g \<M>"
  proof - 
    interpret MDPC_Reach_Avoid \<M> by fact
    
    show ?thesis
      apply (rule map_mdptc_cong)
      apply (rule closed_M)
      using assms(2) by auto
  qed    
    
  (* TODO: Move *)
  lemma Modest_mdp_sup_assn_pure_part_Reach_Avoid: "pure_part (Modest_mdp_sup_assn N \<M> \<M>i) \<Longrightarrow> MDPC_Reach_Avoid \<M>"
    unfolding Modest_mdp_sup_assn_def
    apply (clarsimp simp: pure_part_hr_comp_eq modest_mdp_sup_rel_def in_br_conv)
    subgoal for _ St Tr Br Pr Av Ta 
    proof -
      assume "modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta"
      then interpret modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta .
      show "MDPC_Reach_Avoid \<M>_\<alpha>" 
        by (metis MDPC_Reach_Avoid_\<M>_\<alpha>)
    qed
    done      
  
  
    


context
  fixes A_sz A_lb A_lbf A_ubf A_MDP and states' :: "nat mdptc \<Rightarrow> _" and mec_decomp' :: "nat mdptc \<Rightarrow> _"
  defines "A_sz \<equiv> size_assn"
  defines "A_lb \<equiv> nn_real_lb_assn"
  defines "A_lbf \<equiv> output_lb_assn"
  defines "A_ubf \<equiv> output_ub_assn"
  defines "A_MDP \<equiv> Modest_mdp_sup_assn"
  defines "states' \<equiv> states o to_mdpc"
  defines "mec_decomp' \<equiv> Finite_MDP_defs.mec_decomp o to_mdpc"

  
  notes A_defs = A_sz_def A_lb_def A_lbf_def A_ubf_def A_MDP_def states'_def mec_decomp'_def
begin

  interpretation llvm_prim_setup . \<comment> \<open>For \<open>ll_load\<close>/\<open>ll_store\<close>\<close>

  \<comment> \<open>For completeness, the full Hoare triple including importing pointers.\<close>
  corollary Modest_tool_pmax_ll_htriple_aux1: "llvm_htriple
    ( \<upharpoonleft>ll_pto \<M>i Mip ** \<upharpoonleft>ll_pto alloc resip
    ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i ** Modest_mdp_sup_assn N \<M> \<M>i ** snat_assn L Li
    ** \<up>(2 * N < max_size_t))

    (Modest_tool_pmax_impl_ll Li ni \<epsilon>i Mip resip)

    (\<lambda>_. EXS \<M>\<^sub>0 D \<M>' x y i resi. \<upharpoonleft>ll_pto resi resip
      ** size_assn N ni ** nn_real_lb_assn \<epsilon> \<epsilon>i
      ** hn_invalid (Modest_mdp_sup_assn N) \<M> \<M>i ** snat_assn L Li
      ** \<up>(2 * N < max_size_t)
      ** Modest_build_out_assn N ((\<M>\<^sub>0,D,\<M>'),x,y,i) resi
      ** \<upharpoonleft>ll_pto \<M>i Mip
      ** \<up>(\<M>\<^sub>0 = \<M>
           \<and> set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D
           \<and> \<M>' = map_mdptc (idx_of D) (Max_red \<M>)
           \<and> inj_on (idx_of D) (states (Max_red \<M>))
           \<and> states (to_mdpc \<M>') = {0..<length D}
           \<and> (\<forall>u \<in> states (to_mdpc \<M>). x (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> p_real' \<M> u
                 \<and> p_real' \<M> u \<le> y (idx_of D (the_mec (to_mdpc \<M>) u)))))"
    unfolding Modest_tool_pmax_impl_ll_def
    apply vcg
    done

    
  corollary Modest_tool_pmax_ll_htriple_aux2: "llvm_htriple
    ( A_sz L Li ** A_sz N ni ** A_lb \<epsilon> \<epsilon>i ** \<upharpoonleft>ll_pto \<M>i Mip ** A_MDP N \<M> \<M>i ** \<upharpoonleft>ll_pto xx resip
    ** \<up>(2 * N < max_size_t))

    (Modest_tool_pmax_impl_ll Li ni \<epsilon>i Mip resip)

    (\<lambda>_. EXS \<M>\<^sub>0 D \<M>' x y i resi. \<upharpoonleft>ll_pto resi resip
      ** Modest_build_out_assn N ((\<M>\<^sub>0,D,\<M>'),x,y,i) resi
      ** \<upharpoonleft>ll_pto \<M>i Mip
      ** \<up>(\<M>\<^sub>0 = \<M>
           \<and> set D = mec_decomp' \<M> \<and> distinct D
           \<and> \<M>' = map_mdptc (idx_of D) (Max_red \<M>)
           \<and> inj_on (idx_of D) (states (Max_red \<M>))
           \<and> states' \<M>' = {0..<length D}
           \<and> (\<forall>u \<in> states' \<M>. x (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> p_real' \<M> u
                 \<and> p_real' \<M> u \<le> y (idx_of D (the_mec (to_mdpc \<M>) u)))))"
    unfolding Modest_tool_pmax_impl_ll_def A_defs
    apply vcg
    \<comment> \<open>Purge leftover pure assertions\<close>
    unfolding pure_def hn_ctxt_def invalid_assn_def
    by fri
    
  lemma Modest_tool_pmax_ll_htriple_beautify:
    assumes RA: "MDPC_Reach_Avoid \<M>"
    assumes 
      SETD: "set D = mec_decomp' \<M>" 
      and "distinct D"
      "\<M>' = map_mdptc (idx_of D) (Max_red \<M>)"
      "inj_on (idx_of D) (states (Max_red \<M>))"
      "states' \<M>' = {0..<length D}"
      "(\<forall>u \<in> states' \<M>. x (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> p_real' \<M> u
                 \<and> p_real' \<M> u \<le> y (idx_of D (the_mec (to_mdpc \<M>) u)))"
    shows 
      "is_partitioning D (states' \<M>) 
        \<and> map_mdptc (nth D) \<M>' = map_mdptc states (Max_red \<M>) 
        \<and> (\<forall>u\<in>states' \<M>. p_real' \<M> u \<in> {x (idx_of' D u) .. y (idx_of' D u)})"
  proof - 
    have 1: "\<Union>(set D) = states (to_mdpc \<M>)"
      unfolding SETD states_Max_red states_M_mec mec_decomp'_def
      apply safe
      subgoal
        apply (auto simp: states_Max_red Finite_MDP_defs.mec_decomp_def states_M_mec)
        by (meson le_mdpc_iff mec_le subsetD)
      subgoal
        by (simp add: Finite_MDP_defs.states_in_decomp)  
      done

    have 2: "\<forall>m\<^sub>1\<in>set D. \<forall>m\<^sub>2\<in>set D. m\<^sub>1\<noteq>m\<^sub>2 \<longrightarrow> m\<^sub>1\<inter>m\<^sub>2 = {}"  
      apply (clarsimp simp: SETD mec_decomp'_def)
      using Finite_MDP_defs.unique_in_mec_decomp[where M=\<M>] by blast
      
    have 3: "idx_of D (the_mec (to_mdpc \<M>) u) = idx_of' D u" if "u\<in>states (to_mdpc \<M>)" for u  
      unfolding idx_of_def idx_of'_def
      apply (rule arg_cong[where f=The]; intro ext)
      subgoal for i
        apply (cases "i<length D"; simp)
        apply (subgoal_tac "D!i \<in> Finite_MDP_defs.mec_decomp (to_mdpc \<M>)")
        subgoal by (smt (verit, ccfv_threshold) Finite_MDP_defs.mec_decomp_def mem_Collect_eq states_the_mec that the_mec_eqI)
        subgoal using SETD nth_mem unfolding mec_decomp'_def by auto
        done
      done
      
    have 4: "map_mdptc (nth D) \<M>' = map_mdptc states (Max_red \<M>)"
      unfolding \<open>\<M>' = _\<close>
      apply (auto simp: map_mdptc_compose comp_def)
      apply (rule map_mdptcRA_cong[OF MDPC_Reach_Avoid.MDPC_Reach_Avoid_max_red[OF RA]])
      using assms(2,3) unfolding mec_decomp'_def  Finite_MDP_defs.mec_decomp_def
      apply clarsimp
      by (smt (verit, ccfv_SIG) idx_of_wd(2) image_iff mem_Collect_eq states_M_mec states_Max_red the_mec)
      
    show ?thesis unfolding is_partitioning_def using assms 1 2 3 4 unfolding states'_def by auto
  qed
    
  theorem Modest_tool_pmax_ll_htriple: "llvm_htriple
    (A_sz L Li ** A_sz N ni ** A_lb \<epsilon> \<epsilon>i ** \<upharpoonleft>ll_pto \<M>i Mip ** A_MDP N \<M> \<M>i ** \<upharpoonleft>ll_pto xx resip
    ** \<up>(2 * N < max_size_t))

    (Modest_tool_pmax_impl_ll Li ni \<epsilon>i Mip resip)

    (\<lambda>_. EXS D \<M>' x y i resi. \<upharpoonleft>ll_pto resi resip
      ** Modest_build_out_assn N ((\<M>,D,\<M>'),x,y,i) resi
      ** \<upharpoonleft>ll_pto \<M>i Mip
      ** \<up>( is_partitioning D (states' \<M>) \<and> set D = mec_decomp' \<M>
            \<and> states' \<M>' = {0..<length D}
            \<and> map_mdptc (nth D) \<M>' = map_mdptc states (Max_red \<M>)
            \<and> (\<forall>u\<in>states' \<M>. p_real' \<M> u \<in> {x (idx_of' D u) .. y (idx_of' D u)})))"
            
    (*supply [vcg_prep_ext_rules] = Modest_mdp_sup_assn_pure_part_Reach_Avoid*)
            
    apply (rule htriple_pure_preI)
    
    apply (rule htriple_ent_post[OF _ Modest_tool_pmax_ll_htriple_aux2])
    unfolding A_MDP_def
    apply (clarsimp intro!: entails_exE2)
    apply (rule entails_pureI)
    apply (drule vcg_prep_ext_rules Modest_mdp_sup_assn_pure_part_Reach_Avoid|erule conjE)+
    apply (drule (6) Modest_tool_pmax_ll_htriple_beautify)
    by fri
  
  
end

subsection \<open>Code export\<close>

lemmas [llvm_code] = disj_set_list_tuple_defs.tuple_list_id_am_lookup_def
  disj_set_list_tuple_defs.tuple_list_id_am_update_def
  scc_map_defs.node_state_am_lookup_def
  scc_map_defs.node_state_am_update_def
  scc_map_defs.node_state_am_empty_def
  disj_set_list_tuple_defs.tuple_list_id_am_empty_def

lemmas [llvm_inline] = disj_set_list_tuple_defs.to_LIST1_impl_def
  disj_set_list_tuple_defs.to_LIST2_impl_def
  scc_map_defs.is_DONE_impl_def
  scc_map_defs.is_STACK_v_impl_def
  disj_set_list_tuple_defs.in_LIST1_impl_def
  disj_set_list_tuple_defs.in_LIST2_impl_def
  disj_set_list_tuple_defs.of_LIST1_impl_def
  disj_set_list_tuple_defs.of_LIST2_impl_def

export_llvm Modest_tool_pmax_impl_ll
  is "void compute_pmax(modest_size_t, modest_size_t, modest_dec_t, modest_mdp_t *, modest_pmax_res_t *)"
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
  } modest_build_t;

  typedef struct {
    modest_build_t build;
    struct {
      modest_dec_t *lbs;
      struct {
        modest_dec_t *ubs;
        modest_size_t iterations;
      };
    };
  } modest_pmax_res_t;
\<close>
  file "modest_pmax_gs.ll"

end
