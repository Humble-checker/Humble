theory Modest_MDP_II_Maxred
  imports "../Modest_MDP_input" "../Modest_MDP_MEC" "Modest_MDP_II_Ops" "./Iterators" "../../II/Max_Reduction" "./Modest_MDP_II_Reach"
begin

  text \<open>This theory refines the collapsed MDP (of @{typ \<open>nat mdpc mdptc\<close>}, the MEC quotient
    @{const M_mec}) to the Modest sparse-matrix data structure for MDPs together with a MEC
    decomposition. It is the analogue, for the max-reduction pipeline, of the theory
    \<^file>\<open>Modest_MDP_II_Minred.thy\<close> (which handles min-reduction and interval iteration). Note that
    the further abstract reduction \<^const>\<open>Max_red\<close> (bottom MECs become avoid states, self-loops
    removed) is not part of this data refinement; only the (M_mec \<M>_\<alpha>) \<^const>\<open>M_mec\<close> is refined
    here.\<close>


  section \<open>Refinement Relation for the Collapsed MDP\<close>

  subsection \<open>General: relabelling agrees on states\<close>

  text \<open>If two relabellings agree on the states of a closed MDP, they produce the same collapsed
    MDP. Used to convert the concrete (M_mec \<M>_\<alpha>) map to the abstract \<^const>\<open>the_mec\<close>.\<close>
  lemma map_mdpc_cong_states:
    assumes cl: "closed_mdpc M"
      and fg: "\<And>u. u \<in> states M \<Longrightarrow> f u = g u"
    shows "map_mdpc f M = map_mdpc g M"
  proof (rule mdpc_eqI)
    show "states (map_mdpc f M) = states (map_mdpc g M)"
      using fg by (auto simp: states_map_mdpc)
  next
    fix s
    have inS: "u \<in> states M" if "a \<in> actions M u" for a u
      using that by (metis empty_iff in_states)
    have U: "\<Union> (actions M ` (f -` {s})) = \<Union> (actions M ` (g -` {s}))"
      using fg inS by (fastforce simp: vimage_def)
    have map_eq: "map_pmf f a = map_pmf g a" if a: "a \<in> \<Union> (actions M ` (g -` {s}))" for a
    proof -
      from a obtain u where u: "a \<in> actions M u" by auto
      then have "set_pmf a \<subseteq> states M" using cl by (blast intro: closed_mdpcD)
      then show ?thesis using fg by (auto intro!: map_pmf_cong)
    qed
    show "actions (map_mdpc f M) s = actions (map_mdpc g M) s"
      unfolding actions_map_mdpc U by (rule image_cong[OF refl map_eq])
  qed

  text \<open>A collapsed MDP @{typ \<open>nat mdpc mdptc\<close>} is represented concretely by a Modest MDP together
    with a MEC decomposition \<open>D\<close> of it: a distinct list whose set is the MEC decomposition
    \<open>mec_decomp'\<close> of the MDP that the Modest data structure encodes. The abstraction is the
    MEC (M_mec \<M>_\<alpha>) \<^const>\<open>M_mec\<close> of that MDP. This is a reinterpretation of the data already
    present (no new state space is materialised here; that is the state-space-building step).

    The MEC decomposition is kept as an abstract @{typ \<open>nat set list\<close>} at this interface layer,
    matching how the min-reduction chain keeps it abstract before refining to the concrete
    @{typ \<open>nat set list\<close>} array partition at the implementation/Sepref layer.\<close>

  type_synonym modest_collapse = "modest_input_mdp \<times> nat set list"

  subsection \<open>The Balanced Abstraction: a Locale over the Concrete Data\<close>

  text \<open>Following the meaning-first style of \<^const>\<open>modest_mdp_input_def.\<M>_\<alpha>\<close>, we fix the concrete
    Modest data together with a MEC decomposition \<^term>\<open>D\<close> and give each component its meaning:
    \<^term>\<open>mec_of u\<close> is the index of the MEC containing state \<^term>\<open>u\<close>, and its defining property is
    the bridge \<^prop>\<open>D ! mec_of u = states (the_mec \<M>_\<alpha> u)\<close> connecting the concrete decomposition to
    the abstract MEC. From these the structure of the collapsed MDP \<^const>\<open>M_mec\<close> is characterised
    component-wise (states, avoids, targets, and -- in the (M_mec \<M>_\<alpha>) operation -- leaving-actions).\<close>

  locale modest_collapse_invar = modest_mdp_input_invar N St Tr Br Pr Av Ta
    for N St Tr Br Pr Av Ta +
    fixes D :: "nat set list"
    assumes distinct_D: "distinct D"
      and set_D: "set D = mec_decomp' \<M>_\<alpha>"
  begin

    \<comment> \<open>\<^locale>\<open>MDPC_Reach_Avoid\<close> for \<^const>\<open>\<M>_\<alpha>\<close> (with lemma \<open>MDPC_Reach_Avoid_\<M>_\<alpha>\<close>) is already
      established, unprefixed, via \<^locale>\<open>modest_mdp_input_invar\<close> in \<open>Modest_MDP_II_Reach\<close>; we reuse
      those inherited (unprefixed) names rather than re-proving it and adding a redundant \<open>M:\<close>
      sublocale.\<close>

    lemma states_\<M>_\<alpha>[simp]: "states \<M>_\<alpha> = {0..<N}"
      by (simp add: states_M\<^sub>0_\<alpha>)

    lemma mec_decomp_\<M>_\<alpha>: "mec_decomp = mec_decomp' \<M>_\<alpha>"
      by simp

    subsubsection \<open>MEC index of a state\<close>

    definition "mec_of u = (THE i. i < length D \<and> u \<in> D ! i)"

    lemma mec_decomp_D: "X \<in> set D \<longleftrightarrow> X \<in> mec_decomp' \<M>_\<alpha>"
      using set_D by blast

    lemma the_mec_in_decomp: "u < N \<Longrightarrow> states (the_mec \<M>_\<alpha> u) \<in> mec_decomp' \<M>_\<alpha>"
      using the_mec[of u \<M>_\<alpha>]
      by (fastforce simp: states_M\<^sub>0_\<alpha> Finite_MDP_defs.mec_decomp_def)

    lemma mec_of_unique: "u < N \<Longrightarrow> \<exists>!i. i < length D \<and> u \<in> D ! i"
    proof (rule ex_ex1I)
      assume "u < N"
      then have "u \<in> states M\<^sub>0_\<alpha>" by (simp add: states_M\<^sub>0_\<alpha>)
      then obtain X where "X \<in> mec_decomp' \<M>_\<alpha>" "u \<in> X"
        using states_in_decomp[of u] mec_decomp_\<M>_\<alpha> by auto
      then show "\<exists>i. i < length D \<and> u \<in> D ! i"
        using set_D by (metis in_set_conv_nth)
    next
      fix i j
      assume "i < length D \<and> u \<in> D ! i" "j < length D \<and> u \<in> D ! j"
      then show "i = j"
        using set_D distinct_D Finite_MDP_defs.unique_in_mec_decomp nth_mem
        by (metis nth_eq_iff_index_eq)
    qed

    lemma mec_of_lt: "u < N \<Longrightarrow> mec_of u < length D"
      unfolding mec_of_def using mec_of_unique by (metis (no_types, lifting) theI')

    lemma u_in_mec_of: "u < N \<Longrightarrow> u \<in> D ! mec_of u"
      unfolding mec_of_def using mec_of_unique by (metis (no_types, lifting) theI')

    lemma mec_of_bridge: "u < N \<Longrightarrow> D ! mec_of u = states (the_mec \<M>_\<alpha> u)"
    proof -
      assume u: "u < N"
      have "u \<in> D ! mec_of u" using u by (rule u_in_mec_of)
      moreover have "D ! mec_of u \<in> mec_decomp' \<M>_\<alpha>"
        using u mec_of_lt set_D nth_mem by metis
      moreover have "u \<in> states (the_mec \<M>_\<alpha> u)"
        using u states_\<M>_\<alpha> by (auto simp: states_the_mec)
      moreover have "states (the_mec \<M>_\<alpha> u) \<in> mec_decomp' \<M>_\<alpha>"
        using u by (rule the_mec_in_decomp)
      ultimately show ?thesis
        by (metis Finite_MDP_defs.unique_in_mec_decomp)
    qed

    text \<open>The build/count code indexes MECs via the LLVM-refined \<^const>\<open>op_mec_index_of\<close>; the abstraction
      side uses \<^const>\<open>mec_of\<close>. They are definitionally the same \<open>THE\<close>-description, so this bridge lets
      build-side indices meet abstraction-side ones.\<close>
    lemma mec_of_op_index: "op_mec_index_of D u = mec_of u"
      by (simp add: op_mec_index_of_def mec_of_def)

    text \<open>The MEC decomposition is nonempty: the source MDP has at least one state (\<open>N > 0\<close>), which lies
      in some class of the decomposition \<open>= set D\<close>.\<close>
    lemma length_D_pos: "0 < length D"
    proof (rule ccontr)
      assume "\<not> 0 < length D"
      then have "mec_decomp' \<M>_\<alpha> = {}" using set_D by simp
      moreover have "states (the_mec \<M>_\<alpha> 0) \<in> mec_decomp' \<M>_\<alpha>"
        using N0 the_mec_in_decomp by blast
      ultimately show False by simp
    qed

    text \<open>Every MEC class is nonempty, hence \<^const>\<open>mec_of\<close> is onto the index set \<open>{0..<length D}\<close>.\<close>
    lemma in_D_iff_mec_of: "u < N \<Longrightarrow> i < length D \<Longrightarrow> (u \<in> D ! i) = (mec_of u = i)"
      using u_in_mec_of mec_of_unique unfolding mec_of_def
      by (metis (mono_tags, lifting) the_equality)

    text \<open>Every MEC class is nonempty. A class is \<^term>\<open>states \<phi>\<close> for some \<^term>\<open>mec (to_mdpc \<M>_\<alpha>) \<phi>\<close>;
      if it were empty then \<^term>\<open>\<phi> = \<bottom>\<close> (\<open>eq_bot_iff_states\<close>), and a MEC equal to \<open>\<bottom>\<close> forces the
      ambient MDP \<^term>\<open>to_mdpc \<M>_\<alpha>\<close> to be \<open>\<bottom>\<close> (\<open>mec_bot_imp_bot\<close>) -- impossible since it has \<open>N > 0\<close>
      states. Everything stays at the \<^typ>\<open>_ mdpc\<close> level (\<^term>\<open>to_mdpc \<M>_\<alpha>\<close>); the outer \<^typ>\<open>_ mdptc\<close>
      \<^term>\<open>\<M>_\<alpha>\<close> has no \<open>\<bottom>\<close>, so the facts must be applied to \<^term>\<open>to_mdpc \<M>_\<alpha>\<close>, not \<^term>\<open>\<M>_\<alpha>\<close>.\<close>
    lemma mec_class_ne: "X \<in> mec_decomp' \<M>_\<alpha> \<Longrightarrow> X \<noteq> {}"
    proof -
      assume "X \<in> mec_decomp' \<M>_\<alpha>"
      then have "X \<in> mec_decomp" using mec_decomp_\<M>_\<alpha> by simp
      then obtain \<phi> where \<phi>: "mec \<M>_\<alpha> \<phi>" and X: "X = states \<phi>"
        unfolding mec_decomp_def by auto
      have "to_mdpc \<M>_\<alpha> \<noteq> \<bottom>"
        using N0 by (simp add: eq_bot_iff_states states_M\<^sub>0_\<alpha>)
      with \<phi> have "\<phi> \<noteq> \<bottom>" by (metis mec_bot_imp_bot)
      then show "X \<noteq> {}" using X by (simp add: eq_bot_iff_states)
    qed

    text \<open>Each MEC class is a subset of the state space \<open>{0..<N}\<close>: a MEC is a sub-MDP
      (\<open>mec_le\<close>), and sub-MDPs have fewer states (\<open>states_mono\<close>).\<close>
    lemma mec_class_sub: "X \<in> mec_decomp' \<M>_\<alpha> \<Longrightarrow> X \<subseteq> {0..<N}"
    proof -
      assume "X \<in> mec_decomp' \<M>_\<alpha>"
      then have "X \<in> mec_decomp" using mec_decomp_\<M>_\<alpha> by simp
      then obtain \<phi> where \<phi>: "mec \<M>_\<alpha> \<phi>" and X: "X = states \<phi>"
        unfolding mec_decomp_def by auto
      have "states \<phi> \<subseteq> states (to_mdpc \<M>_\<alpha>)"
        using \<phi> by (rule states_mono[OF mec_le])
      with X show "X \<subseteq> {0..<N}" by (simp add: states_M\<^sub>0_\<alpha>)
    qed

    lemma mec_of_surj: "j < length D \<Longrightarrow> \<exists>u<N. mec_of u = j"
    proof -
      assume j: "j < length D"
      then have "D ! j \<in> mec_decomp' \<M>_\<alpha>" using set_D nth_mem by metis
      then have ne: "D ! j \<noteq> {}" and sub: "D ! j \<subseteq> {0..<N}"
        using mec_class_ne mec_class_sub by auto
      from ne obtain u where u: "u \<in> D ! j" by blast
      then have uN: "u < N" using sub by auto
      have "mec_of u = j" using u uN j mec_of_unique unfolding mec_of_def
        by (metis (mono_tags, lifting) the_equality)
      then show ?thesis using uN by blast
    qed

    lemma mec_of_image: "mec_of ` {0..<N} = {0..<length D}"
    proof (intro Set.equalityI subsetI)
      fix j assume "j \<in> mec_of ` {0..<N}"
      then show "j \<in> {0..<length D}" by (auto simp: mec_of_lt)
    next
      fix j assume "j \<in> {0..<length D}"
      then show "j \<in> mec_of ` {0..<N}" using mec_of_surj by fastforce
    qed

    text \<open>The MEC decomposition read off \<^term>\<open>M_mec \<M>_\<alpha>\<close>: its states are the MEC-MDPs,
      whose state sets are exactly the classes of \<^term>\<open>mec_decomp' \<M>_\<alpha>\<close>. Used by the step-7
      \<open>fref\<close> precondition to recover "\<open>D\<close> is a valid decomposition list" from the abstract collapsed MDP.\<close>
    lemma states_M_mec_decomp: "(\<lambda>m. states m) ` states (M_mec \<M>_\<alpha>) = mec_decomp' \<M>_\<alpha>"
    proof -
      have "(\<lambda>m. states m) ` states (M_mec \<M>_\<alpha>) = (\<lambda>u. states (the_mec \<M>_\<alpha> u)) ` {0..<N}"
        by (simp add: states_M_mec states_M\<^sub>0_\<alpha> image_image)
      also have "\<dots> = mec_decomp' \<M>_\<alpha>"
      proof (intro Set.equalityI subsetI)
        fix X assume "X \<in> (\<lambda>u. states (the_mec \<M>_\<alpha> u)) ` {0..<N}"
        then obtain u where uN: "u < N" and XU: "X = states (the_mec \<M>_\<alpha> u)" by auto
        show "X \<in> mec_decomp' \<M>_\<alpha>" using the_mec_in_decomp[OF uN] XU by simp
      next
        fix X assume X: "X \<in> mec_decomp' \<M>_\<alpha>"
        then obtain i where i: "i < length D" and XD: "X = D ! i"
          using mec_decomp_D by (metis in_set_conv_nth)
        have "X \<noteq> {}" using X mec_class_ne by simp
        then obtain u where u: "u \<in> X" by blast
        then have uN: "u < N" using mec_class_sub[OF X] by auto
        have "mec_of u = i" using u uN i XD in_D_iff_mec_of by auto
        then have "X = states (the_mec \<M>_\<alpha> u)" using XD uN mec_of_bridge by auto
        then show "X \<in> (\<lambda>u. states (the_mec \<M>_\<alpha> u)) ` {0..<N}" using uN by auto
      qed
      finally show ?thesis .
    qed

    subsubsection \<open>The inner MDP of a MEC\<close>

    text \<open>The MDP living on MEC \<^term>\<open>i\<close>: its states are the class \<^term>\<open>D!i\<close>, and its actions are
      those of the member states that stay inside the MEC.\<close>
    definition mec_mdp :: "nat \<Rightarrow> nat mdpc" where
      "mec_mdp i = Abs_mdpc (\<lambda>s. if s \<in> D ! i then Some {a \<in> St_to_pmfs s. set_pmf a \<subseteq> D ! i} else None)"

    lemma states_mec_mdp: "states (mec_mdp i) = D ! i"
      unfolding mec_mdp_def by (auto simp: states.abs_eq split: if_splits)

    lemma actions_mec_mdp: "s \<in> D ! i \<Longrightarrow> actions (mec_mdp i) s = {a \<in> St_to_pmfs s. set_pmf a \<subseteq> D ! i}"
      unfolding mec_mdp_def by (auto simp: actions.abs_eq)

    subsubsection \<open>The (M_mec \<M>_\<alpha>) map and the abstraction function\<close>

    text \<open>\<^term>\<open>col u\<close> is the collapsed state of \<^term>\<open>u\<close> (the inner MDP of its MEC). The MEC quotient
      \<^term>\<open>M_mec \<M>_\<alpha>\<close> relabels the Modest MDP by \<^term>\<open>col\<close> (branches inside a MEC become self-loops
      on the collapsed state) and maps the avoid/target states.\<close>
    definition col :: "nat \<Rightarrow> nat mdpc" where "col u = mec_mdp (mec_of u)"

    subsubsection \<open>Bridge: the (M_mec \<M>_\<alpha>) map is the MEC map, and the conversion to \<^const>\<open>M_mec\<close>\<close>

    text \<open>The key bridge: the concrete MEC map equals the abstract MEC map. From it every
      abstract \<^const>\<open>M_mec\<close> fact transfers to the concrete data.\<close>
    lemma col_eq_the_mec:
      assumes u: "u < N" shows "col u = the_mec M\<^sub>0_\<alpha> u"
    proof (rule mdpc_eqI)
      have uS: "u \<in> states M\<^sub>0_\<alpha>" using u by (simp add: states_M\<^sub>0_\<alpha>)
      have mec: "mec M\<^sub>0_\<alpha> (the_mec M\<^sub>0_\<alpha> u)" using uS by (rule the_mec)
      have br: "D ! mec_of u = states (the_mec M\<^sub>0_\<alpha> u)" using u by (simp add: mec_of_bridge)
      show "states (col u) = states (the_mec M\<^sub>0_\<alpha> u)"
        unfolding col_def states_mec_mdp using br .
      fix s assume "s \<in> states (col u)"
      then have sD: "s \<in> D ! mec_of u" unfolding col_def states_mec_mdp .
      then have sS: "s \<in> states (the_mec M\<^sub>0_\<alpha> u)" using br by simp
      then have sN: "s < N" using states_the_mec_subs[OF uS] states_M\<^sub>0_\<alpha> by auto
      have "actions (col u) s = {a \<in> St_to_pmfs s. set_pmf a \<subseteq> D ! mec_of u}"
        unfolding col_def using sD by (rule actions_mec_mdp)
      also have "\<dots> = {a \<in> actions M\<^sub>0_\<alpha> s. set_pmf a \<subseteq> states (the_mec M\<^sub>0_\<alpha> u)}"
        using sN br by (simp add: actions_M\<^sub>0_\<alpha>)
      also have "\<dots> = actions (the_mec M\<^sub>0_\<alpha> u) s"
        using mec_actions[OF mec sS] by simp
      finally show "actions (col u) s = actions (the_mec M\<^sub>0_\<alpha> u) s" .
    qed

    text \<open>The MEC quotient \<^term>\<open>M_mec \<M>_\<alpha>\<close> read off the concrete data: it is \<^term>\<open>M\<^sub>0_\<alpha>\<close>
      relabelled by \<^term>\<open>col\<close> (genuine content, resting on the bridge).\<close>
    lemma Mmec_unfold: "M_mec \<M>_\<alpha> = Abs_mdptc (map_mdpc col M\<^sub>0_\<alpha>, col ` Av, col ` Ta)"
    proof -
      have "map_mdpc col M\<^sub>0_\<alpha> = map_mdpc (the_mec \<M>_\<alpha>) M\<^sub>0_\<alpha>"
        by (rule map_mdpc_cong_states[OF closed_mdpc_M\<^sub>0_\<alpha>]) (simp add: states_M\<^sub>0_\<alpha> col_eq_the_mec)
      moreover have "col ` Av = the_mec \<M>_\<alpha> ` Av"
        using AvN by (auto simp: col_eq_the_mec)
      moreover have "col ` Ta = the_mec \<M>_\<alpha> ` Ta"
        using TaN by (auto simp: col_eq_the_mec)
      ultimately show ?thesis
        unfolding M_mec_def by simp
    qed

    lemma states_collapse: "states (M_mec \<M>_\<alpha>) = col ` {0..<N}"
      unfolding Mmec_unfold by (simp add: to_mdpc.abs_eq states_map_mdpc states_M\<^sub>0_\<alpha>)

    lemma avoids_collapse: "avoids (M_mec \<M>_\<alpha>) = col ` Av"
      unfolding Mmec_unfold by (simp add: avoids.abs_eq)

    lemma targets_collapse: "targets (M_mec \<M>_\<alpha>) = col ` Ta"
      unfolding Mmec_unfold by (simp add: targets.abs_eq)

  end

  subsection \<open>The Refinement Relation\<close>

  text \<open>The abstraction is the MEC quotient \<^const>\<open>M_mec\<close> of the abstract MDP
    \<^const>\<open>modest_mdp_input_def.\<M>_\<alpha>\<close> that the concrete data encodes.\<close>
  abbreviation "collapse_\<alpha> N \<equiv>
    (\<lambda>((St,Tr,Br,Pr,Av,Ta), D). (M_mec (modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr), D))"

  abbreviation "collapse_inv N \<equiv>
    (\<lambda>((St,Tr,Br,Pr,Av,Ta), D). modest_collapse_invar N St Tr Br Pr Av Ta D)"

  definition modest_collapse_rel :: "nat \<Rightarrow> ((modest_input_mdp \<times> nat set list) \<times> (nat mdpc mdptc \<times> nat set list)) set" where
    "modest_collapse_rel N = br (collapse_\<alpha> N) (collapse_inv N)"

  lemma modest_collapse_rel_iff:
    "(((St,Tr,Br,Pr,Av,Ta), D), (\<M>c, D2)) \<in> modest_collapse_rel N \<longleftrightarrow>
       \<M>c = M_mec (modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr) \<and> D2 = D
       \<and> modest_collapse_invar N St Tr Br Pr Av Ta D"
    by (auto simp: modest_collapse_rel_def in_br_conv)

  lemma modest_collapse_rel_sv[simp, intro!]: "single_valued (modest_collapse_rel N)"
    unfolding modest_collapse_rel_def by (rule br_sv)

  text \<open>The MDP related to the concrete data is exactly its abstract MEC quotient \<^const>\<open>M_mec\<close>.\<close>
  lemma modest_collapse_rel_M_mec:
    assumes "(((St,Tr,Br,Pr,Av,Ta), D), (\<M>c, D2)) \<in> modest_collapse_rel N"
    shows "\<M>c = M_mec (modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr)"
    using assms by (simp add: modest_collapse_rel_iff)


  section \<open>The Reinterpretation Operation (step 3)\<close>

  text \<open>The (mode-neutral) refinement relation between a Modest MDP and the abstract MDP
    \<^const>\<open>modest_mdp_input_def.\<M>_\<alpha>\<close> it encodes.\<close>
  abbreviation "modest_mdp_\<alpha> N \<equiv> (\<lambda>(St,Tr,Br,Pr,Av,Ta). modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr)"
  abbreviation "modest_mdp_inv N \<equiv> (\<lambda>(St,Tr,Br,Pr,Av,Ta). modest_mdp_input_invar N St Tr Br Pr Av Ta)"

  definition modest_mdp_rel :: "nat \<Rightarrow> (modest_input_mdp \<times> nat mdptc) set" where
    "modest_mdp_rel N = br (modest_mdp_\<alpha> N) (modest_mdp_inv N)"

  text \<open>The reinterpretation of a Modest MDP together with its MEC decomposition as the collapsed
    MDP. Concretely it is the identity (a noop): the collapsed MDP is represented by the same data.
    Abstractly it produces the MEC (M_mec \<M>_\<alpha>) \<^const>\<open>M_mec\<close>.\<close>
  definition reinterpret :: "(modest_input_mdp \<times> nat set list) \<Rightarrow> (modest_input_mdp \<times> nat set list)" where
    "reinterpret = id"

  definition op_reinterpret :: "(nat mdptc \<times> nat set list) \<Rightarrow> (nat mdpc mdptc \<times> nat set list)" where
    "op_reinterpret = (\<lambda>(\<M>, D). (M_mec \<M>, D))"

  definition "reinterpret_pre = (\<lambda>(\<M>::nat mdptc, D). distinct D \<and> set D = mec_decomp' \<M>)"

  lemma reinterpret_refine:
    assumes REL: "(DS, \<M>) \<in> modest_mdp_rel N"
    assumes DEC: "distinct D" "set D = mec_decomp' \<M>"
    shows "(reinterpret (DS, D), op_reinterpret (\<M>, D)) \<in> modest_collapse_rel N"
  proof -
    obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)" by (cases DS)
    from REL have INV: "modest_mdp_input_invar N St Tr Br Pr Av Ta"
      and MA: "\<M> = modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr"
      unfolding DDEF modest_mdp_rel_def by (auto simp: in_br_conv)
    have LOC: "modest_collapse_invar N St Tr Br Pr Av Ta D"
      using INV DEC MA
      by (simp add: modest_collapse_invar_def modest_collapse_invar_axioms_def)
    have "op_reinterpret (\<M>, D) = (M_mec (modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr), D)"
      unfolding op_reinterpret_def using MA by simp
    then show ?thesis
      unfolding reinterpret_def DDEF id_apply
      using LOC by (simp add: modest_collapse_rel_iff)
  qed

  lemma reinterpret_correct:
    "(reinterpret, op_reinterpret) \<in> [reinterpret_pre]\<^sub>f (modest_mdp_rel N \<times>\<^sub>r Id) \<rightarrow> modest_collapse_rel N"
    by (rule frefI; auto simp: reinterpret_refine reinterpret_pre_def)


  section \<open>Indexing the Collapsed MDP (step 5)\<close>

  text \<open>The abstract operation that converts a collapsed MDP \<^typ>\<open>nat mdpc mdptc\<close> to an ordinary
    \<^typ>\<open>nat mdptc\<close>, by replacing each state (an inner MDP / MEC) with its index in the MEC
    decomposition \<^term>\<open>D\<close>, and performing the \<^const>\<open>Max_red\<close> cleanup: a collapsed computes-state
    with no leaving action (its only action is the self-loop \<^term>\<open>return_pmf m\<close>) is a bottom MEC and
    becomes an avoid state (self-loop only); every other computes-state loses its self-loop.\<close>

  definition idx_of :: "nat set list \<Rightarrow> nat mdpc \<Rightarrow> nat" where
    "idx_of D m = (THE i. i < length D \<and> states m = D ! i)"

  text \<open>The bottom MECs of a collapsed MDP: computes-states with no leaving action.\<close>
  definition bots :: "'a mdpc mdptc \<Rightarrow> 'a mdpc set" where
    "bots \<M>c = {m \<in> computes \<M>c. actions \<M>c m = {return_pmf m}}"

  text \<open>The \<^const>\<open>Max_red\<close> cleanup on a collapsed MDP: drop self-loops on non-bottom computes-states,
    turn bottom MECs into avoid states.\<close>
  definition reduce :: "'a mdpc mdptc \<Rightarrow> 'a mdpc mdptc" where
    "reduce \<M>c = Abs_mdptc
       (map_actions (\<lambda>m a. if m \<in> computes \<M>c - bots \<M>c then a - {return_pmf m} else {return_pmf m})
          (to_mdpc \<M>c),
        avoids \<M>c \<union> bots \<M>c - targets \<M>c,
        targets \<M>c)"

  lemma states_reduce: "states (reduce \<M>c) = states \<M>c"
    unfolding reduce_def by (simp add: to_mdpc.abs_eq state_map_actions)

  lemma avoids_reduce: "avoids (reduce \<M>c) = avoids \<M>c \<union> bots \<M>c - targets \<M>c"
    unfolding reduce_def by (simp add: avoids.abs_eq)

  lemma targets_reduce: "targets (reduce \<M>c) = targets \<M>c"
    unfolding reduce_def by (simp add: targets.abs_eq)

  definition to_index :: "nat mdpc mdptc \<Rightarrow> nat set list \<Rightarrow> nat mdptc" where
    "to_index \<M>c D =
       Abs_mdptc (map_mdpc (idx_of D) (to_mdpc (reduce \<M>c)),
                  idx_of D ` avoids (reduce \<M>c), idx_of D ` targets (reduce \<M>c))"

  text \<open>The abstract operation of step 5, packaged for composition in the step-8 pipeline: index the
    collapsed MDP by its MEC decomposition. Its concrete implementation \<open>build_statespace\<close> (step 6) and
    the step-7 refinement relating them live in \<open>Modest_MDP_II_Maxred_Build\<close>.\<close>
  definition op_to_index :: "(nat mdpc mdptc \<times> nat set list) \<Rightarrow> nat mdptc" where
    "op_to_index = (\<lambda>(\<M>c, D). to_index \<M>c D)"

  text \<open>\<^type>\<open>mdptc\<close> is a plain triple typedef, so equality is componentwise, and the three projections
    of \<^const>\<open>to_index\<close> read off its definition.\<close>
  lemma mdptc_eqI:
    "to_mdpc x = to_mdpc y \<Longrightarrow> avoids x = avoids y \<Longrightarrow> targets x = targets y \<Longrightarrow> x = y"
    by transfer (auto simp: prod_eq_iff)

  lemma to_index_to_mdpc: "to_mdpc (to_index \<M>c D) = map_mdpc (idx_of D) (to_mdpc (reduce \<M>c))"
    unfolding to_index_def by (simp add: to_mdpc.abs_eq)
  lemma to_index_avoids: "avoids (to_index \<M>c D) = idx_of D ` avoids (reduce \<M>c)"
    unfolding to_index_def by (simp add: avoids.abs_eq)
  lemma to_index_targets: "targets (to_index \<M>c D) = idx_of D ` targets (reduce \<M>c)"
    unfolding to_index_def by (simp add: targets.abs_eq)

  text \<open>Relabelling the support of a \<^const>\<open>pmf_of_list\<close> distribution: pushing \<open>f\<close> through the values
    (keeping the probabilities) is the same as mapping the whole distribution by \<open>f\<close>. The linchpin for
    matching the built \<open>Tr_to_pmf\<close> readback against the relabelled abstract action.\<close>
  lemma map_pmf_of_list:
    assumes wf: "pmf_of_list_wf xs"
    shows "map_pmf f (pmf_of_list xs) = pmf_of_list (map (\<lambda>(v, p). (f v, p)) xs)"
  proof (rule pmf_eqI)
    fix y
    have snd_eq: "map snd (map (\<lambda>(v, p). (f v, p)) xs) = map snd xs"
      by (simp add: case_prod_beta)
    have wf2: "pmf_of_list_wf (map (\<lambda>(v, p). (f v, p)) xs)"
    proof -
      \<comment> \<open>\<open>pmf_of_list_wf\<close> depends only on \<open>map snd\<close>, and \<open>snd_eq\<close> makes that equal for the two
        lists (\<open>simp only\<close> avoids \<open>map_map\<close> firing first and hiding the match).\<close>
      have "pmf_of_list_wf (map (\<lambda>(v, p). (f v, p)) xs) = pmf_of_list_wf xs"
        unfolding pmf_of_list_wf_def by (simp only: snd_eq)
      then show ?thesis using wf by simp
    qed
    have "pmf (map_pmf f (pmf_of_list xs)) y = measure (pmf_of_list xs) (f -` {y})"
      by (rule pmf_map)
    also have "\<dots> = sum_list (map snd (filter (\<lambda>x. fst x \<in> f -` {y}) xs))"
      by (rule measure_pmf_of_list[OF wf])
    also have "\<dots> = sum_list (map snd (filter (\<lambda>z. fst z = y) (map (\<lambda>(v, p). (f v, p)) xs)))"
      by (simp add: filter_map o_def case_prod_beta)
    also have "\<dots> = pmf (pmf_of_list (map (\<lambda>(v, p). (f v, p)) xs)) y"
      by (rule pmf_pmf_of_list[OF wf2, symmetric])
    finally show "pmf (map_pmf f (pmf_of_list xs)) y
        = pmf (pmf_of_list (map (\<lambda>(v, p). (f v, p)) xs)) y" .
  qed

  text \<open>\<^const>\<open>pmf_of_list\<close> depends only on the multiset of value/probability pairs, so a segment read
    as a list in any order yields the same distribution.\<close>
  lemma pmf_of_list_cong_mset:
    assumes wf: "pmf_of_list_wf xs" and m: "mset xs = mset ys"
    shows "pmf_of_list xs = pmf_of_list ys"
  proof -
    have setxy: "set xs = set ys" using m by (metis set_mset_mset)
    have sumxy: "sum_list (map snd xs) = sum_list (map snd ys)"
      using m by (metis mset_map sum_mset_sum_list)
    have wfy: "pmf_of_list_wf ys"
      using wf setxy sumxy unfolding pmf_of_list_wf_def by simp
    show ?thesis
    proof (rule pmf_eqI)
      fix x
      have "pmf (pmf_of_list xs) x = sum_list (map snd (filter (\<lambda>z. fst z = x) xs))"
        by (rule pmf_pmf_of_list[OF wf])
      also have "\<dots> = sum_list (map snd (filter (\<lambda>z. fst z = x) ys))"
      proof -
        have "mset (filter (\<lambda>z. fst z = x) xs) = mset (filter (\<lambda>z. fst z = x) ys)"
          using m by (metis mset_filter)
        hence "mset (map snd (filter (\<lambda>z. fst z = x) xs))
               = mset (map snd (filter (\<lambda>z. fst z = x) ys))" by (metis mset_map)
        thus ?thesis by (metis sum_mset_sum_list)
      qed
      also have "\<dots> = pmf (pmf_of_list ys) x"
        by (rule pmf_pmf_of_list[OF wfy, symmetric])
      finally show "pmf (pmf_of_list xs) x = pmf (pmf_of_list ys) x" .
    qed
  qed

  text \<open>The structural bottom test coincides with the abstract \<^const>\<open>bmecs\<close> on computes-states, hence
    the cleanup \<^const>\<open>reduce\<close> applied to the (M_mec \<M>_\<alpha>) \<^const>\<open>M_mec\<close> is exactly \<^const>\<open>Max_red\<close>.\<close>
  context MDPC_Reach_Avoid
  begin

    lemma bots_M_mec: "bots (M_mec \<M>) = bmecs \<M> \<inter> computes (M_mec \<M>)"
    proof (intro Set.equalityI subsetI)
      fix m assume "m \<in> bots (M_mec \<M>)"
      then have C: "m \<in> computes (M_mec \<M>)" and A: "actions (M_mec \<M>) m = {return_pmf m}"
        unfolding bots_def by auto
      from C have MS: "m \<in> states (M_mec \<M>)" by simp
      then obtain u where u: "u \<in> states \<M>" and mu: "m = the_mec \<M> u"
        unfolding states_M_mec by auto
      have MEC: "mec \<M> m" using mu the_mec[OF u] by simp
      have "bmec \<M> m"
      proof (rule ccontr)
        assume NB: "\<not> bmec \<M> m"
        obtain a s where s: "s \<in> states m" and a: "a \<in> actions \<M> s"
          and nsub: "\<not> set_pmf a \<subseteq> states m"
          using NB MEC by (rule nbmec_exit)
        from nsub obtain v where v: "v \<in> set_pmf a" and vnm: "v \<notin> states m" by blast
        have vS: "v \<in> states \<M>" using v a closed_M by (blast dest: closed_mdpcD)
        have ne: "the_mec \<M> v \<noteq> m"
          using vnm vS states_the_mec'[OF u] by (auto simp: mu)
        have "map_pmf (the_mec \<M>) a \<in> actions (M_mec \<M>) m"
          using s a by (subst actions_M_mec'[OF MS]) auto
        then have "map_pmf (the_mec \<M>) a = return_pmf m" using A by simp
        then have "\<forall>x\<in>set_pmf a. the_mec \<M> x = m" by (simp add: map_pmf_eq_return_pmf_iff)
        then show False using v ne by blast
      qed
      then show "m \<in> bmecs \<M> \<inter> computes (M_mec \<M>)" using C by simp
    next
      fix m assume "m \<in> bmecs \<M> \<inter> computes (M_mec \<M>)"
      then have B: "bmec \<M> m" and C: "m \<in> computes (M_mec \<M>)" by auto
      have "actions (M_mec \<M>) m = {return_pmf m}"
        using B C actions_M_mec_bot by simp
      then show "m \<in> bots (M_mec \<M>)" unfolding bots_def using C by simp
    qed

    lemma reduce_M_mec: "reduce (M_mec \<M>) = Max_red \<M>"
    proof -
      have BC: "computes (M_mec \<M>) - bots (M_mec \<M>) = computes (M_mec \<M>) - bmecs \<M>"
        using bots_M_mec by blast
      have BS: "bmecs \<M> \<subseteq> states (M_mec \<M>)"
        using bmec_states_mec by auto
      have AV: "avoids (M_mec \<M>) \<union> bots (M_mec \<M>) - targets (M_mec \<M>)
              = avoids (M_mec \<M>) \<union> bmecs \<M> - targets (M_mec \<M>)"
      proof -
        have "avoids (M_mec \<M>) \<union> bots (M_mec \<M>) - targets (M_mec \<M>)
            = avoids (M_mec \<M>) \<union> (bmecs \<M> \<inter> computes (M_mec \<M>)) - targets (M_mec \<M>)"
          by (simp add: bots_M_mec)
        also have "\<dots> = avoids (M_mec \<M>) \<union> bmecs \<M> - targets (M_mec \<M>)"
          using BS by (auto simp: computes_def)
        finally show ?thesis .
      qed
      show ?thesis
        unfolding reduce_def Max_red_def Let_def by (simp add: BC AV)
    qed

  end



  section \<open>Abstract Sup interval-iteration layer\<close>

  text \<open>The \<open>Sup\<close> instance of the mode-generic interval-iteration layer. The concrete
    \<open>get_state_val_opt\<close>/\<open>updated_state_val_gs\<close> keep their own names (so the code layer can
    unfold them) but are definitionally the \<open>Sup\<close>-instance of the generic backup, so their
    refinements transfer directly from \<open>modest_mdp_ii_mode_invar.get_state_val_opt_refine\<close>.\<close>

  locale modest_mdp_ii_sup_def = modest_mdp_input_def N St Tr Br Av Ta Pr for N St Tr Br Pr Av Ta
  begin

    sublocale reachability_opt_mode_defs Sup sup "(\<ge>)" 1 0 .

    definition "get_state_val_opt xs u = do {
      let xopt = 0;
      xopt \<leftarrow> FOREACH (sn_intv (StI ! u)) (\<lambda> t xopt. do{

        ASSERT (t < length Tr - Suc 0);
        val \<leftarrow> get_trans_val xs t;
        RETURN (sup val xopt)

      }) xopt;
      RETURN xopt
    }"

    definition "updated_state_val_gs = (\<lambda> xs ys. do {
      nfoldli (rev [0..<N]) (\<lambda>_. True) (\<lambda> u (xs,ys). do {
        ASSERT (u < N \<and> N_len xs \<and> N_len ys);
        let u' = op_bound_val (\<lambda>i. i < N) u;
        if is_avoid_state u' then RETURN (xs,ys)
        else if is_target_state u' then RETURN (xs,ys)
        else do {
          xmin \<leftarrow> get_state_val_opt xs u';
          ymin \<leftarrow> get_state_val_opt ys u';
          RETURN (xs[u:=xmin],ys[u:=ymin])
        }
      }) (xs,ys)
    })"

  end

  locale modest_mdp_ii_invar_sup = modest_mdp_input_invar + modest_mdp_ii_sup_def +
    assumes vDom_alt: "vDom = {0..1}"
  begin

    sublocale reachability_opt_mode Sup sup "(\<ge>)" 1 0
      using reachability_opt_mode_sup .

    sublocale G: modest_mdp_ii_mode_invar N St Tr Br Pr Av Ta Sup sup "(\<ge>)" 1 0
      by unfold_locales (rule vDom_alt)

    lemma get_state_val_opt_eq: "get_state_val_opt = G.get_state_val_opt"
      unfolding get_state_val_opt_def G.get_state_val_opt_def by simp

    lemma updated_state_val_gs_eq: "updated_state_val_gs = G.updated_state_val_gs"
      unfolding updated_state_val_gs_def G.updated_state_val_gs_def get_state_val_opt_eq by simp

    lemma get_state_val_opt_refine:
      assumes UREL: "(ui,u) \<in> node_rel' N"
      assumes LFR: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes UB: "u \<in> states M\<^sub>0_\<alpha>"
      assumes UNA: "\<not>op_is_avoid \<M>_\<alpha> u"
      assumes UNT: "\<not>op_is_target \<M>_\<alpha> u"
      assumes XB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> x v \<in> vDom"
      shows "get_state_val_opt xs ui \<le> RETURN (op_state_val \<M>_\<alpha> x u)"
      unfolding get_state_val_opt_eq by (rule G.get_state_val_opt_refine[OF assms])

    lemma MDPC_Reach_Avoid_Sup_M_\<alpha>: "MDPC_Reach_Avoid_Sup \<M>_\<alpha>"
      by(unfold_locales)

    sublocale MDPC_Reach_Avoid_Sup \<M>_\<alpha> using MDPC_Reach_Avoid_Sup_M_\<alpha> .

    lemma updated_state_val_max_gs_refine:
      assumes XB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> x v \<le> 1"
      assumes YB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> y v \<le> 1"
      assumes XSX: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YSY: "(ys,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      shows "updated_state_val_gs xs ys \<le> \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_state_vals_gs \<M>_\<alpha> x y)"
      unfolding updated_state_val_gs_eq by (rule G.updated_state_val_gs_refine[OF assms])

  end

  subsection \<open>State & MDP relation\<close>

  abbreviation "\<M>_\<alpha>_sup' N \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr)"
  abbreviation "\<M>_sup_inv N \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). modest_mdp_ii_invar_sup N St Tr Br Pr Av Ta)"

  definition modest_mdp_sup_rel :: "nat \<Rightarrow> (modest_mdp \<times> (nat mdptc)) set" where
    "modest_mdp_sup_rel N = br (\<M>_\<alpha>_sup' N) (\<M>_sup_inv N)"

end
