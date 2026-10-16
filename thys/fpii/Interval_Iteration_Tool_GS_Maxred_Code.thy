theory Interval_Iteration_Tool_GS_Maxred_Code
  imports "../ds/Intf/Modest_MDP_II_Maxred" "Interval_Iteration_Tool"
begin

text \<open>Step 8: the max-reduction pipeline over the Modest data structure, mirroring the min-side
  \<^file>\<open>Interval_Iteration_Tool_GS_Minred_Code.thy\<close>. Unlike the min case (in-place avoid-sinks), the
  max case genuinely collapses and re-indexes: compute MECs, reinterpret as the collapsed MDP
  (step 3), re-index the reduced MDP (step 5/6), then run interval iteration on the smaller
  state space.\<close>

  text \<open>The combined max-reduction pipeline, making the procedure explicit (CLAUDE.md step 8):
    (a) compute a MEC decomposition, (b) reinterpret as the collapsed MDP \<^const>\<open>op_reinterpret\<close>,
    (c) re-index the reduced MDP \<^const>\<open>op_to_index\<close>, (d) run interval iteration on the smaller
    state space.\<close>
  definition tool_pmax
    :: "nat mdptc \<Rightarrow> nat \<Rightarrow> (nat mdptc \<times> (nat \<Rightarrow> real) \<times> (nat \<Rightarrow> real) \<times> nat) nres" where
    "tool_pmax \<M> L = do {
       D \<leftarrow> SPEC (\<lambda>D. set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>) \<and> distinct D);
       let new = op_to_index (op_reinterpret (\<M>, D));
       R \<leftarrow> mop_interval_iteration_sup new L;
       RETURN (new, R)
     }"

  subsection \<open>Relabelling of a collapsed MDP\<close>

  text \<open>State relabelling of an \<^type>\<open>mdptc\<close> by a function \<open>f\<close> (the \<^type>\<open>mdptc\<close> analogue of
    \<^const>\<open>map_mdpc\<close>). The re-indexing \<^const>\<open>to_index\<close> is exactly the relabelling of the reduced
    collapse by \<^const>\<open>idx_of\<close>, so a re-indexed MDP is precisely \<open>\<exists>f. map_mdptc f (Max_red \<M>) = M\<close>.\<close>
  definition map_mdptc :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mdptc \<Rightarrow> 'b mdptc" where
    "map_mdptc f \<M> = Abs_mdptc (map_mdpc f (to_mdpc \<M>), f ` avoids \<M>, f ` targets \<M>)"

  lemma to_index_map_mdptc: "to_index \<M>c D = map_mdptc (idx_of D) (reduce \<M>c)"
    unfolding to_index_def map_mdptc_def by (rule refl)

  lemma to_mdpc_map_mdptc[simp]: "to_mdpc (map_mdptc f \<M>) = map_mdpc f (to_mdpc \<M>)"
    unfolding map_mdptc_def by (simp add: to_mdpc.abs_eq)
  lemma avoids_map_mdptc[simp]: "avoids (map_mdptc f \<M>) = f ` avoids \<M>"
    unfolding map_mdptc_def by (simp add: avoids.abs_eq)
  lemma targets_map_mdptc[simp]: "targets (map_mdptc f \<M>) = f ` targets \<M>"
    unfolding map_mdptc_def by (simp add: targets.abs_eq)
  lemma states_map_mdptc[simp]: "states (map_mdptc f \<M>) = f ` states \<M>"
    by (simp add: states_map_mdpc)
  text \<open>\<^const>\<open>computes\<close> is \<open>states - avoids - targets\<close>; commuting it with an injective relabelling
    needs \<open>avoids, targets \<subseteq> states\<close>, i.e. a reach-avoid \<^term>\<open>\<M>\<close>.\<close>
  lemma computes_map_mdptc:
    assumes WF: "MDPC_Reach_Avoid \<M>" and INJ: "inj_on f (states \<M>)"
    shows "computes (map_mdptc f \<M>) = f ` computes \<M>"
  proof -
    interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
    show ?thesis unfolding computes_def
      using INJ M.Avd_states M.Tgt_states by (auto simp: states_map_mdptc dest: inj_onD)
  qed

  text \<open>The reach-avoid structure is preserved under an injective state relabelling.\<close>
  lemma map_mdptc_reach_avoid:
    assumes WF: "MDPC_Reach_Avoid \<M>" and INJ: "inj_on f (states \<M>)"
    shows "MDPC_Reach_Avoid (map_mdptc f \<M>)"
  proof -
    interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
    have act: "\<And>t. t \<in> states \<M> \<Longrightarrow> actions (map_mdptc f \<M>) (f t) = map_pmf f ` actions \<M> t"
    proof -
      fix t assume t: "t \<in> states \<M>"
      have "actions (map_mdpc f (to_mdpc \<M>)) (f t) = map_pmf f ` (\<Union>u\<in>f -` {f t}. actions (to_mdpc \<M>) u)"
        by (rule actions_map_mdpc)
      also have "(\<Union>u\<in>f -` {f t}. actions (to_mdpc \<M>) u) = actions \<M> t"
      proof (intro Set.equalityI subsetI)
        fix a assume "a \<in> (\<Union>u\<in>f -` {f t}. actions (to_mdpc \<M>) u)"
        then obtain u where u: "f u = f t" and a: "a \<in> actions \<M> u" by auto
        have "u \<in> states \<M>" using a by (auto intro: in_states)
        with u t INJ have "u = t" by (auto dest: inj_onD)
        with a show "a \<in> actions \<M> t" by simp
      qed auto
      finally show "actions (map_mdptc f \<M>) (f t) = map_pmf f ` actions \<M> t" by simp
    qed
    show ?thesis
    proof unfold_locales
      show "closed_mdpc (to_mdpc (map_mdptc f \<M>))"
        by (simp add: closed_mdpc_map M.closed_M)
      show "to_mdpc (map_mdptc f \<M>) \<noteq> bot"
        using M.M_neq_bot by (simp add: eq_bot_iff_states states_map_mdpc)
      show "\<And>s. s \<in> states (to_mdpc (map_mdptc f \<M>)) \<Longrightarrow> actions (map_mdptc f \<M>) s \<noteq> {}"
        using act M.actions_neq_empty_M by (auto simp: states_map_mdpc)
      show "finite (states (to_mdpc (map_mdptc f \<M>)))"
        using M.finite_states_M by (simp add: states_map_mdpc)
      show "\<And>s. finite (actions (map_mdptc f \<M>) s)"
      proof -
        fix s
        have eq: "actions (map_mdptc f \<M>) s = map_pmf f ` (\<Union>u\<in>f -` {s}. actions (to_mdpc \<M>) u)"
          by (simp add: actions_map_mdpc)
        have "(\<Union>u\<in>f -` {s}. actions (to_mdpc \<M>) u) \<subseteq> (\<Union>u\<in>states (to_mdpc \<M>). actions (to_mdpc \<M>) u)"
          by (auto intro: in_states)
        moreover have "finite (\<Union>u\<in>states (to_mdpc \<M>). actions (to_mdpc \<M>) u)"
          using M.finite_states_M M.finite_actions_M by blast
        ultimately have "finite (\<Union>u\<in>f -` {s}. actions (to_mdpc \<M>) u)" by (rule finite_subset)
        thus "finite (actions (map_mdptc f \<M>) s)"
          by (simp add: actions_map_mdpc finite_imageI)
      qed
      show "avoids (map_mdptc f \<M>) \<subseteq> states (map_mdptc f \<M>)"
        using M.Avd_states by (auto simp: states_map_mdpc)
      show "targets (map_mdptc f \<M>) \<subseteq> states (map_mdptc f \<M>)"
        using M.Tgt_states by (auto simp: states_map_mdpc)
      show "targets (map_mdptc f \<M>) \<inter> avoids (map_mdptc f \<M>) = {}"
        using M.AT_disj M.Avd_states M.Tgt_states INJ by (auto dest: inj_onD)
      show "\<And>u. u \<in> targets (map_mdptc f \<M>) \<Longrightarrow> actions (map_mdptc f \<M>) u = {return_pmf u}"
        using M.Tgt_loop M.Tgt_states act by (auto simp: pmf.map_comp o_def)
      show "\<And>u. u \<in> avoids (map_mdptc f \<M>) \<Longrightarrow> actions (map_mdptc f \<M>) u = {return_pmf u}"
        using M.Avd_loop M.Avd_states act by (auto simp: pmf.map_comp o_def)
    qed
  qed

  subsection \<open>Specification\<close>

  lemma actions_map_mdptc_f:
    assumes WF: "MDPC_Reach_Avoid \<M>" and INJ: "inj_on f (states \<M>)" and t: "t \<in> states \<M>"
    shows "actions (map_mdptc f \<M>) (f t) = map_pmf f ` actions \<M> t"
  proof -
    interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
    have "actions (map_mdpc f (to_mdpc \<M>)) (f t) = map_pmf f ` (\<Union>u\<in>f -` {f t}. actions (to_mdpc \<M>) u)"
      by (rule actions_map_mdpc)
    also have "(\<Union>u\<in>f -` {f t}. actions (to_mdpc \<M>) u) = actions \<M> t"
    proof (intro Set.equalityI subsetI)
      fix a assume "a \<in> (\<Union>u\<in>f -` {f t}. actions (to_mdpc \<M>) u)"
      then obtain u where u: "f u = f t" and a: "a \<in> actions \<M> u" by auto
      have "u \<in> states \<M>" using a by (auto intro: in_states)
      with u t INJ have "u = t" by (auto dest: inj_onD)
      with a show "a \<in> actions \<M> t" by simp
    qed auto
    finally show ?thesis by simp
  qed

  text \<open>State-relabelling invariance of the reach-avoid probability: renaming the states of a
    well-formed reach-avoid MDP along an injection leaves \<^const>\<open>MDPC_Reach_Avoid.p_real\<close> unchanged
    (proved by a \<^const>\<open>Reachability_Problem.p_fin\<close> induction with an \<^const>\<open>nn_integral\<close>
    change-of-variables). This is the last piece of deep math for the max pipeline.\<close>
  lemma p_real_map_mdptc:
    assumes WF: "MDPC_Reach_Avoid \<M>" and INJ: "inj_on f (states \<M>)" and s0: "s0 \<in> states \<M>"
    shows "MDPC_Reach_Avoid.p_real (map_mdptc f \<M>) (f s0) = MDPC_Reach_Avoid.p_real \<M> s0"
  proof -
    interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
    interpret M': MDPC_Reach_Avoid "map_mdptc f \<M>" by (rule map_mdptc_reach_avoid[OF WF INJ])

    have Kf: "actions' (map_mdptc f \<M>) (f t) = map_pmf f ` actions' \<M> t" if t: "t \<in> states \<M>" for t
    proof -
      have ft: "f t \<in> states (map_mdptc f \<M>)" using t by (simp add: states_map_mdptc)
      have "actions' (map_mdptc f \<M>) (f t) = actions (map_mdptc f \<M>) (f t)"
        using ft by (rule M'.actions'_states)
      also have "\<dots> = map_pmf f ` actions \<M> t" using WF INJ t by (rule actions_map_mdptc_f)
      also have "\<dots> = map_pmf f ` actions' \<M> t" using t by (simp add: M.actions'_states)
      finally show ?thesis .
    qed

    have clsd: "set_pmf a \<subseteq> states \<M>" if "s \<in> states \<M>" "a \<in> actions' \<M> s" for s a
      using that M.set_pmf_closed' by (auto simp: M.actions'_states)

    have pf: "M'.R.p_fin i (f s) = M.R.p_fin i s" if "s \<in> states \<M>" for i s
      using that
    proof (induction i arbitrary: s)
      case 0
      show ?case
      proof (cases "s \<in> targets \<M>")
        case True
        have fsT: "f s \<in> targets (map_mdptc f \<M>)" using True by (auto simp: targets_map_mdptc)
        show ?thesis using M'.R.p_fin_S2[OF fsT] M.R.p_fin_S2[OF True] by simp
      next
        case False
        have fsnT: "f s \<notin> targets (map_mdptc f \<M>)"
          using False 0 INJ M.Tgt_states by (auto simp: targets_map_mdptc dest: inj_onD)
        have fsSt: "f s \<in> states (map_mdptc f \<M>)" using 0 by (simp add: states_map_mdptc)
        have "M'.R.p_fin 0 (f s) = 0" by (rule M'.R.p_fin_0) (use fsSt fsnT in simp)
        moreover have "M.R.p_fin 0 s = 0" by (rule M.R.p_fin_0) (use 0 False in simp)
        ultimately show ?thesis by simp
      qed
    next
      case (Suc i)
      note IH = Suc.IH
      show ?case
      proof (cases "s \<in> targets \<M>")
        case True
        have fsT: "f s \<in> targets (map_mdptc f \<M>)" using True by (auto simp: targets_map_mdptc)
        show ?thesis using M'.R.p_fin_S2[OF fsT] M.R.p_fin_S2[OF True] by simp
      next
        case nT: False
        show ?thesis
        proof (cases "s \<in> computes \<M>")
          case False
          have m1: "s \<in> states \<M> - computes \<M> - targets \<M>" using Suc nT False by simp
          have m2: "f s \<in> states (map_mdptc f \<M>) - computes (map_mdptc f \<M>) - targets (map_mdptc f \<M>)"
            using False nT Suc INJ by (auto simp: states_map_mdptc computes_map_mdptc[OF WF INJ] dest: inj_onD)
          have "M'.R.p_fin (Suc i) (f s) = 0" by (rule M'.R.p_fin_nS12) (use m2 in simp)
          moreover have "M.R.p_fin (Suc i) s = 0" by (rule M.R.p_fin_nS12) (use m1 in simp)
          ultimately show ?thesis by simp
        next
          case True
          have sSt: "s \<in> states \<M>" using Suc by simp
          have fsC: "f s \<in> computes (map_mdptc f \<M>)"
            using True by (simp add: computes_map_mdptc[OF WF INJ])
          have "M'.R.p_fin (Suc i) (f s)
              = (\<Squnion>a'\<in>actions' (map_mdptc f \<M>) (f s). \<integral>\<^sup>+s'. M'.R.p_fin i s' \<partial>measure_pmf a')"
            using fsC by (rule M'.R.p_fin_Suc_S1)
          also have "\<dots> = (\<Squnion>a\<in>actions' \<M> s. \<integral>\<^sup>+s'. M'.R.p_fin i s' \<partial>measure_pmf (map_pmf f a))"
            using Kf[OF sSt] by (simp add: image_image)
          also have "\<dots> = (\<Squnion>a\<in>actions' \<M> s. \<integral>\<^sup>+s'. M.R.p_fin i s' \<partial>measure_pmf a)"
          proof (rule SUP_cong[OF refl])
            fix a assume a: "a \<in> actions' \<M> s"
            have "(\<integral>\<^sup>+s'. M'.R.p_fin i s' \<partial>measure_pmf (map_pmf f a))
                = (\<integral>\<^sup>+s'. M'.R.p_fin i (f s') \<partial>measure_pmf a)"
              by (rule nn_integral_measure_map_pmf[symmetric]) simp
            also have "\<dots> = (\<integral>\<^sup>+s'. M.R.p_fin i s' \<partial>measure_pmf a)"
            proof (intro nn_integral_cong_AE)
              have "\<forall>y\<in>set_pmf a. M'.R.p_fin i (f y) = M.R.p_fin i y"
              proof
                fix y assume "y \<in> set_pmf a"
                hence "y \<in> states \<M>" using clsd[OF sSt a] by blast
                thus "M'.R.p_fin i (f y) = M.R.p_fin i y" by (rule IH)
              qed
              thus "AE s' in measure_pmf a. M'.R.p_fin i (f s') = M.R.p_fin i s'"
                by (simp add: AE_measure_pmf_iff)
            qed
            finally show "(\<integral>\<^sup>+s'. M'.R.p_fin i s' \<partial>measure_pmf (map_pmf f a))
                        = (\<integral>\<^sup>+s'. M.R.p_fin i s' \<partial>measure_pmf a)" .
          qed
          also have "\<dots> = M.R.p_fin (Suc i) s"
            using True by (rule M.R.p_fin_Suc_S1[symmetric])
          finally show ?thesis .
        qed
      qed
    qed

    have "M'.R.p (f s0) = M.R.p s0"
    proof -
      have "M'.R.p (f s0) = (\<Squnion>i. M'.R.p_fin i (f s0))"
        unfolding M'.R.p_eq_Sup_p_fin by (rule SUP_apply)
      also have "\<dots> = (\<Squnion>i. M.R.p_fin i s0)" by (simp only: pf[OF s0])
      also have "\<dots> = M.R.p s0"
        unfolding M.R.p_eq_Sup_p_fin by (rule SUP_apply[symmetric])
      finally show ?thesis .
    qed
    thus ?thesis
      using s0 by (simp add: M.p_real_def M'.p_real_def states_map_mdptc)
  qed

  text \<open>For a distinct MEC-decomposition list, \<^const>\<open>idx_of\<close> is well defined and injective on the
    collapsed states, so it is an admissible relabelling for \<open>p_real_map_mdptc\<close>.\<close>
  lemma idx_of_wd:
    assumes dist: "distinct D" and mem: "states m \<in> set D"
    shows "idx_of D m < length D" and "D ! idx_of D m = states m"
  proof -
    have ex1: "\<exists>!i. i < length D \<and> states m = D ! i"
      using dist mem distinct_Ex1[of D "states m"] by metis
    have "idx_of D m < length D \<and> states m = D ! idx_of D m"
      unfolding idx_of_def by (rule theI'[OF ex1])
    thus "idx_of D m < length D" "D ! idx_of D m = states m" by auto
  qed

  lemma idx_of_inj:
    assumes WF: "MDPC_Reach_Avoid \<M>"
      and setD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>)" and dist: "distinct D"
    shows "inj_on (idx_of D) (states (M_mec \<M>))"
  proof -
    interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
    have sd: "states m \<in> set D" if "m \<in> states (M_mec \<M>)" for m
    proof -
      from that obtain u where u: "u \<in> states \<M>" and mu: "m = the_mec (to_mdpc \<M>) u"
        by (auto simp: states_M_mec)
      have "mec (to_mdpc \<M>) m" unfolding mu using u by (rule the_mec)
      thus ?thesis unfolding setD Finite_MDP_defs.mec_decomp_def by auto
    qed
    have detm: "m1 = m2" if "m1 \<in> states (M_mec \<M>)" "m2 \<in> states (M_mec \<M>)" "states m1 = states m2" for m1 m2
    proof -
      from that(1) obtain u1 where u1: "u1 \<in> states \<M>" and m1: "m1 = the_mec (to_mdpc \<M>) u1"
        by (auto simp: states_M_mec)
      from that(2) obtain u2 where u2: "u2 \<in> states \<M>" and m2: "m2 = the_mec (to_mdpc \<M>) u2"
        by (auto simp: states_M_mec)
      have "u1 \<in> states m1" unfolding m1 using u1 by (rule states_the_mec)
      hence "u1 \<in> states m2" using that(3) by simp
      hence "the_mec (to_mdpc \<M>) u1 = the_mec (to_mdpc \<M>) u2"
        unfolding m2 using u2 by (rule M.the_mec_eq)
      thus "m1 = m2" unfolding m1 m2 .
    qed
    show ?thesis
    proof (rule inj_onI)
      fix m1 m2 assume m1: "m1 \<in> states (M_mec \<M>)" and m2: "m2 \<in> states (M_mec \<M>)"
        and eq: "idx_of D m1 = idx_of D m2"
      have "states m1 = D ! idx_of D m1" using idx_of_wd(2)[OF dist sd[OF m1]] by simp
      also have "\<dots> = D ! idx_of D m2" using eq by simp
      also have "\<dots> = states m2" using idx_of_wd(2)[OF dist sd[OF m2]] by simp
      finally show "m1 = m2" using detm[OF m1 m2] by simp
    qed
  qed

  text \<open>The collapse half (reused from \<open>MDPC_Reach_Avoid.p_eq_max\<close>): the reduced MDP's value
    at a node's MEC equals the node's own reach-avoid probability.\<close>
  lemma p_real_Max_red:
    assumes WF: "MDPC_Reach_Avoid \<M>" and u: "u \<in> states \<M>"
    shows "MDPC_Reach_Avoid.p_real (Max_red \<M>) (the_mec (to_mdpc \<M>) u) = MDPC_Reach_Avoid.p_real \<M> u"
  proof -
    interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
    interpret MR: MDPC_Reach_Avoid "Max_red \<M>" by (rule M.MDPC_Reach_Avoid_max_red)
    have tm: "the_mec (to_mdpc \<M>) u \<in> states (Max_red \<M>)"
      using u by (simp add: states_Max_red states_M_mec)
    \<comment> \<open>\<open>interpret MR: MDPC_Reach_Avoid "Max_red \<M>"\<close> aliases the existing \<open>M.max_red\<close>
      sublocale (which is itself a \<open>Reachability_Problem\<close>), so its value is \<open>M.max_red.p\<close>
      -- there is no nested \<open>MR.R\<close>.\<close>
    have "MR.p_real (the_mec (to_mdpc \<M>) u) = enn2real (M.max_red.p (the_mec (to_mdpc \<M>) u))"
      using tm by (simp add: MR.p_real_def)
    also have "enn2real (M.max_red.p (the_mec (to_mdpc \<M>) u)) = enn2real (M.R.p u)"
      by (simp add: M.p_eq_max[OF u])
    also have "\<dots> = M.p_real u" using u by (simp add: M.p_real_def)
    finally show ?thesis .
  qed

  text \<open>The full chain: the interval-iteration value of the re-indexed reduced MDP \<^term>\<open>to_index (M_mec \<M>) D\<close>
    at a node's MEC index equals the node's original probability (relabelling invariance + collapse).\<close>
  lemma p_real_new:
    assumes WF: "MDPC_Reach_Avoid \<M>"
      and setD: "set D = Finite_MDP_defs.mec_decomp (to_mdpc \<M>)" and dist: "distinct D" and u: "u \<in> states \<M>"
    shows "MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) (idx_of D (the_mec (to_mdpc \<M>) u))
         = MDPC_Reach_Avoid.p_real \<M> u"
  proof -
    interpret M: MDPC_Reach_Avoid \<M> by (rule WF)
    have inj: "inj_on (idx_of D) (states (Max_red \<M>))"
      using idx_of_inj[OF WF setD dist] by (simp add: states_Max_red)
    have tm: "the_mec (to_mdpc \<M>) u \<in> states (Max_red \<M>)"
      using u by (simp add: states_Max_red states_M_mec)
    have "to_index (M_mec \<M>) D = map_mdptc (idx_of D) (Max_red \<M>)"
      by (simp add: to_index_map_mdptc M.reduce_M_mec)
    hence "MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) (idx_of D (the_mec (to_mdpc \<M>) u))
         = MDPC_Reach_Avoid.p_real (map_mdptc (idx_of D) (Max_red \<M>)) (idx_of D (the_mec (to_mdpc \<M>) u))"
      by simp
    also have "\<dots> = MDPC_Reach_Avoid.p_real (Max_red \<M>) (the_mec (to_mdpc \<M>) u)"
      by (rule p_real_map_mdptc[OF M.MDPC_Reach_Avoid_max_red inj tm])
    also have "\<dots> = MDPC_Reach_Avoid.p_real \<M> u"
      by (rule p_real_Max_red[OF WF u])
    finally show ?thesis .
  qed

  text \<open>Step 9 specification, mirroring the min-side \<^const>\<open>ii_tool_nspec\<close> / \<open>tool_pmin_impl_correct\<close>.
    Unlike the min case, max-reduction \<^emph>\<open>collapses\<close> the state space (\<open>states (Max_red \<M>) = the_mec \<M> \` states \<M>\<close>),
    so the value bounds can't sit on \<^term>\<open>\<M>\<close>'s states directly; instead we quantify over every original
    node \<open>u \<in> states \<M>\<close> and read its bound at the index \<open>f (the_mec \<M> u)\<close> of the MEC it belongs to. The
    single relabelling \<open>f\<close> (shared between the MDP and the values) makes the spec decomposition-agnostic —
    \<^emph>\<open>some\<close> relabelling of the canonical reduced MDP \<^term>\<open>Max_red \<M>\<close> — and the value-preservation
    \<open>p_eq_max\<close> (\<open>Max_Reduction\<close>: \<open>R.p s = max_red.p (the_mec \<M> s)\<close>) is what makes the
    bound at the MEC's index a bound on the original node's probability \<^term>\<open>MDPC_Reach_Avoid.p_real \<M>\<close>.\<close>
  definition tool_pmax_spec
    :: "nat mdptc \<Rightarrow> nat \<Rightarrow> (nat mdptc \<times> (nat \<Rightarrow> real) \<times> (nat \<Rightarrow> real) \<times> nat) nres" where
    "tool_pmax_spec \<M> L =
       SPEC (\<lambda>(M, lb, ub, i). \<exists>f.
          map_mdptc f (Max_red \<M>) = M \<and>
          (\<forall>u \<in> states (to_mdpc \<M>).
             lb (f (the_mec \<M> u)) \<le> MDPC_Reach_Avoid.p_real \<M> u \<and>
             MDPC_Reach_Avoid.p_real \<M> u \<le> ub (f (the_mec \<M> u))))"

  text \<open>Step 9: the max-reduction pipeline refines the specification (for a well-formed reach-avoid MDP).\<close>
  theorem tool_pmax_correct:
    assumes WF: "MDPC_Reach_Avoid_Sup \<M>"
    shows "tool_pmax \<M> L \<le> tool_pmax_spec \<M> L"
  proof -
    have WFa: "MDPC_Reach_Avoid \<M>" using WF by (simp add: MDPC_Reach_Avoid_Sup_def)
    have new_eq: "to_index (M_mec \<M>) D = map_mdptc (idx_of D) (Max_red \<M>)" for D
      by (simp add: to_index_map_mdptc MDPC_Reach_Avoid.reduce_M_mec[OF WFa])
    have mem: "idx_of D (the_mec (to_mdpc \<M>) u) \<in> states (to_index (M_mec \<M>) D)"
      if "u \<in> states (to_mdpc \<M>)" for D u
      using that by (auto simp: new_eq states_map_mdptc states_Max_red states_M_mec)
    show ?thesis
      unfolding tool_pmax_def tool_pmax_spec_def op_reinterpret_def op_to_index_def
        mop_interval_iteration_sup_def interval_iteration_defs.interval_iteration_spec_def
      apply refine_vcg
      apply clarsimp
      subgoal premises prems for D x y
        apply (rule exI[where x="idx_of D"], rule conjI)
        subgoal by (simp add: new_eq)
        subgoal
        proof (intro ballI)
          fix u assume u: "u \<in> states (to_mdpc \<M>)"
          have vm: "idx_of D (the_mec (to_mdpc \<M>) u) \<in> states (to_index (M_mec \<M>) D)"
            using mem[OF u] .
          have pv: "MDPC_Reach_Avoid.p_real (to_index (M_mec \<M>) D) (idx_of D (the_mec (to_mdpc \<M>) u))
                  = MDPC_Reach_Avoid.p_real \<M> u"
            using prems by (intro p_real_new[OF WFa _ _ u]) auto
          show "x (idx_of D (the_mec (to_mdpc \<M>) u)) \<le> MDPC_Reach_Avoid.p_real \<M> u \<and>
                MDPC_Reach_Avoid.p_real \<M> u \<le> y (idx_of D (the_mec (to_mdpc \<M>) u))"
            using prems vm pv by auto
        qed
        done
      done
  qed

end
