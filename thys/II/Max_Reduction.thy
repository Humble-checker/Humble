theory Max_Reduction
  imports II_Def (*MDP Target may be superfluous after reworking*)
begin

  section \<open>Max-Reduction\<close>
  
  lemma states_the_mec_subs: \<open>s \<in> states M \<Longrightarrow> states (the_mec M s) \<subseteq> states M\<close>
    using the_mec le_mdpc_iff mec_le 
    by fastforce
  
  lemma states_the_mec': \<open>s \<in> states M \<Longrightarrow> states (the_mec M s) = {s' \<in> states M. the_mec M s' = the_mec M s}\<close>
    using the_mec states_the_mec_subs[of s] states_the_mec
    by force
  
  lemmas states_map_mdpc[simp]
  
  lemma eq_loop_state: "(loop u = loop v) \<longleftrightarrow> u = v"
    by (metis actions_loop_neq actions_loop_self empty_not_insert)
  
  lemma (in Finite_MDP) en_scD2: \<open>sc m \<Longrightarrow> m \<le> M \<Longrightarrow> s \<in> m \<Longrightarrow> s' \<in> m \<Longrightarrow> (s, s') \<in> (en M)\<^sup>*\<close>
    using scD
    by (metis Set.basic_monos(7) en_mono rtrancl_mono)
  
  lemma nbmec_exit:
    assumes \<open>\<not>bmec M m\<close> \<open>mec M m\<close>
    obtains a s where \<open>s \<in> m\<close> \<open>a \<in> actions M s\<close> \<open>\<not>a \<subseteq> m\<close>
  proof atomize_elim
    {
      assume closed: \<open>\<forall>s \<in> m. \<forall>a \<in> actions M s. a \<subseteq> m\<close>
      let ?m = \<open>(restrict_states (states m) M)\<close>
      have le: \<open>m \<le> ?m\<close>
        using assms mec_le in_states
        by (fastforce simp: le_mdpc_iff)
  
      have \<open>ec ?m\<close>
      proof -
        have \<open>sc ?m\<close>
          using en_mono[OF le] mec_ec[OF \<open>mec M m\<close>]  
          by (intro scI) (auto dest: scD rtrancl_mono simp: ec_def)
        moreover have \<open>closed_mdpc ?m\<close>
          unfolding closed_mdpc_def
          using closed  assms(2)[THEN mec_le, THEN states_mono]
          by (auto intro: in_states simp: en_def  dest: closed_mdpcD[OF])
        ultimately show ?thesis
          unfolding ec_def by auto
      qed
      hence *: \<open>m = restrict_states (states m) M\<close>
        using \<open>mec M m\<close> le unfolding mec_def
        by (auto intro!: antisym intro: restrict_states_le)
      have \<open>bmec M m\<close>
        unfolding bmec_def
        using assms *
        by (metis actions_restrict_states)
    }
    thus \<open>\<exists>s a. s \<in> states m \<and> a \<in> actions M s \<and> \<not> set_pmf a \<subseteq> states m\<close>
      using assms by auto
  qed
  
  lemma(in -) bmec_nexit:
    assumes \<open>bmec M m\<close> \<open>s \<in> m\<close> \<open>a \<in> actions M s\<close>
    shows \<open>a \<subseteq> m\<close>
    by (meson assms(1) assms(2) assms(3) bmec_closed subsetI)
  
  subsection \<open>Collapsing MECs\<close>
  
  subsubsection \<open>Definition\<close>
  
  text \<open>We collapse MECs into single states, and show that the resulting MDP is well-formed.\<close>
  
  definition M_mec :: "'a mdptc \<Rightarrow> 'a mdpc mdptc" where
    \<open>M_mec \<M> = Abs_mdptc (map_mdpc (the_mec \<M>) \<M>, the_mec \<M> ` (avoids \<M>), the_mec \<M> ` (targets \<M>))\<close>
  
  lemma states_M_mec: \<open>states (M_mec M) = the_mec M ` states M\<close>
    unfolding M_mec_def
    apply transfer
    by auto
  
  lemma states_M_mec_mem: \<open>x \<in> states (M_mec M) \<longleftrightarrow> x \<in> the_mec M ` states M\<close>
    unfolding states_M_mec
    by auto
  
  lemma actions_M_mec: \<open>s \<in> states (to_mdpc \<M>) \<Longrightarrow> 
    actions (M_mec \<M>) (the_mec \<M> s) = (\<Union>s' \<in> the_mec \<M> s. map_pmf (the_mec \<M>) ` (actions \<M> s'))\<close>
    unfolding M_mec_def
    using in_states[of \<M>]
    apply transfer
    by (auto simp: actions_map_mdpc image_iff states_the_mec')
  
  lemma actions_M_mec': \<open>s \<in> states (M_mec \<M>) \<Longrightarrow> 
    actions (M_mec \<M>) s = (\<Union>s' \<in> s. map_pmf (the_mec \<M>) ` (actions \<M> s'))\<close>
    by (fastforce simp: actions_M_mec states_M_mec)
  
  lemma to_mdpc_M_mec: "to_mdpc (M_mec \<M>) = map_mdpc (the_mec \<M>) \<M>"
    unfolding M_mec_def by (transfer; auto)
  
  lemma avoids_M_mec: "avoids (M_mec \<M>) = the_mec \<M> ` (avoids \<M>)"
    unfolding M_mec_def by (transfer; auto)
  
  lemma targets_M_mec: "targets (M_mec \<M>) = the_mec \<M> ` (targets \<M>)"
    unfolding M_mec_def by (transfer; auto)
  
  lemma avoids_M_mec_mem: "x \<in> avoids (M_mec \<M>) \<longleftrightarrow> x \<in> the_mec \<M> ` (avoids \<M>)"
    using avoids_M_mec by blast
  
  lemma targets_M_mec_mem: "x \<in> targets (M_mec \<M>) \<longleftrightarrow> x \<in> the_mec \<M> ` (targets \<M>)"
    using targets_M_mec by blast
  
  context MDPC_Reach_Avoid_defs
  begin
  
    subsection \<open>Min-Reduced MDP\<close>
    text \<open>The reduction function: trivial MECs remain, everything else becomes either an avoid or target state:\<close>
    abbreviation "m_mec \<equiv> M_mec \<M>"
  
    lemma targets_m_mec[simp, intro!]: "s \<in> targets \<M> \<Longrightarrow> the_mec \<M> s \<in> targets m_mec"
      unfolding M_mec_def
      apply transfer
      by auto
  
    lemma avoids_m_mec[simp, intro!]: "s \<in> avoids \<M> \<Longrightarrow> the_mec \<M> s \<in> avoids m_mec"
      unfolding M_mec_def
      apply transfer
      by auto
      
  end
  
  context MDPC_Reach_Avoid
  begin
    
    lemma computes_m_mec: "computes m_mec = the_mec \<M> ` (computes \<M>)"
      unfolding computes_def M_mec_def 
      by (auto simp: states.abs_eq to_mdpc.abs_eq avoids.abs_eq targets.abs_eq)
    
    lemma computes_m_mec_mem: "x \<in> computes m_mec \<longleftrightarrow> x \<in> the_mec \<M> ` (computes \<M>)"
      using computes_m_mec by presburger
    
    lemma actions_M_mec_ne: \<open>s \<in> states m_mec \<Longrightarrow> actions m_mec s \<noteq> {}\<close>
      using actions_neq_empty_M
      by (fastforce simp: states_M_mec actions_M_mec')
    
    lemma sub_states: 
      "avoids m_mec \<subseteq> states m_mec"
      "targets m_mec \<subseteq> states m_mec" 
      "computes m_mec \<subseteq> states m_mec"
      unfolding avoids_M_mec targets_M_mec states_M_mec computes_def
      by (auto simp del: Avd_the_mec_loop Tgt_the_mec_loop)
    
    lemmas sub_states'[simp] = sub_states[THEN in_mono[THEN mp]]
    
    
    lemma en_avoids_id: "s \<in> avoids \<M> \<Longrightarrow> (s, s') \<in> en (to_mdpc \<M>) \<Longrightarrow> s' = s"
      by (simp add: Avd_loop en_def)
    
    lemma en_targets_id: "s \<in> targets \<M> \<Longrightarrow> (s, s') \<in> en (to_mdpc \<M>) \<Longrightarrow> s' = s"
      by (auto simp add: Tgt_loop en_def)
    
    lemma m_mec_closed: \<open>closed_mdpc m_mec\<close>
      unfolding M_mec_def
      using closed_M
      apply transfer
      by (auto intro!: closed_mdpc_map)
    
    lemma m_mec_nbot: \<open>to_mdpc m_mec \<noteq> \<bottom>\<close>
      by (auto simp: eq_bot_iff_states states_M_mec S_not_empty)
    
    lemma m_mec_finite: \<open>finite (states m_mec)\<close>
      by (auto simp: states_M_mec intro!: finite_states_M)
    
    lemma m_mec_fin_act: \<open>finite (actions m_mec s)\<close>
    proof (cases \<open>s \<in> states m_mec\<close>)
      case True
      then show ?thesis
        by (auto simp: states_M_mec actions_M_mec' 
            intro!: finite_actions_M finite_subset[OF states_the_mec_subs S_finite])
    next
      case False
      then show ?thesis
        using in_states[of m_mec s] 
        by fastforce
    qed
    
    sublocale M_mec: Finite_MDP m_mec
      using m_mec_closed m_mec_finite m_mec_nbot actions_M_mec_ne m_mec_fin_act
      by unfold_locales auto
    
    subsubsection \<open>Reachability Problem on the MEC-reduced MDP\<close>
    
    lemma targets_states_m_mec: "targets m_mec \<subseteq> states m_mec"
      unfolding M_mec_def
      using Tgt_states
      apply transfer
      by auto
    
    lemma avoids_states_m_mec: "avoids m_mec \<subseteq> states m_mec"
      unfolding M_mec_def
      using Avd_states
      apply transfer
      by auto
    
    sublocale M_mec: 
      Reachability_Problem 
        \<open>actions' m_mec\<close> 
        \<open>states m_mec\<close> 
        \<open>computes m_mec\<close> 
        \<open>targets m_mec\<close>
      apply unfold_locales
      using targets_states_m_mec
      by auto
    
    lemma AT_M_mec_disj: "targets m_mec \<inter> avoids m_mec = {}"
      using AT_disj
      unfolding avoids_M_mec targets_M_mec 
      by (auto simp: eq_loop_state) 
    
    
    lemma MDPC_Reach_Avoid_m_mec: "MDPC_Reach_Avoid m_mec"
      apply unfold_locales
      subgoal
        by (simp add: avoids_states_m_mec) 
      subgoal 
        by (simp add: M_mec.S2)
      subgoal
        using AT_M_mec_disj .
      subgoal 
        by (auto simp: actions_M_mec' targets_M_mec Tgt_loop)  
      subgoal 
        by (auto simp: actions_M_mec' avoids_M_mec Avd_loop)  
      done
    
    interpretation M_mec': MDPC_Reach_Avoid m_mec
      using MDPC_Reach_Avoid_m_mec .
    
    
    text \<open>Collapsing MECs may only shorten paths towards \<^term>\<open>None\<close>, 
    so the maximum reachability probabilities do not decrease:\<close>
    lemma p_fin_le_mec:
      assumes \<open>s \<in> states \<M>\<close>
      shows \<open>R.p_fin i s \<le> M_mec.p_fin i (the_mec \<M> s)\<close>
      using assms
    proof (induction i arbitrary: s)
      case 0
      then show ?case
        apply (cases \<open>s \<in> targets \<M>\<close>)
        subgoal 
          apply(frule M_mec.p_fin_S2[OF targets_m_mec, of _ 0])
          by auto
        subgoal by auto
        done
    next
      case (Suc i)
      then show ?case
        using set_pmf_closed'[of _ s] targets_m_mec[of s]
        apply (auto simp: R.p_fin_Suc M_mec.p_fin_Suc states_M_mec_mem actions_M_mec' computes_m_mec_mem
            intro!: nn_integral_mono_AE SUP_mono bexI[of _ \<open>map_pmf (the_mec \<M>) _\<close>])
        done
    qed
    
    lemma p_mec_ge: 
      assumes \<open>s \<in> states \<M>\<close>
      shows \<open>R.p s \<le> M_mec.p (the_mec \<M> s)\<close>
      unfolding R.p_eq_Sup_p_fin M_mec.p_eq_Sup_p_fin
      using p_fin_le_mec[OF assms]
      by (auto intro!: SUP_mono)
    
    subsubsection \<open>MECs are MDPs\<close>
    lemma ecE:
      assumes \<open>ec m\<close> 
      obtains \<open>closed_mdpc m\<close> \<open>sc m\<close>
      using assms unfolding ec_def
      by auto
    
    lemma mec_closed_mdpc: \<open>mec \<M> m \<Longrightarrow> closed_mdpc m\<close>
      using ecE mec_ec
      by auto
    
    lemma mec_MDP:
      assumes \<open>mec \<M> m\<close> \<open>\<nexists>x. trivial x = m\<close>
      shows \<open>Finite_MDP m\<close>
    proof
      have \<open>m \<le> \<M>\<close> \<open>sc m\<close> \<open>closed_mdpc m\<close>
        using assms mec_le ecE mec_ec by fastforce+
      thus \<open>closed_mdpc m\<close> 
        by auto
      show \<open>actions m s \<noteq> {}\<close> if \<open>s \<in> states m\<close> for s
        using \<open>sc m\<close> that sc_eq_trivial assms
        by fastforce
      show \<open>m \<noteq> \<bottom>\<close>
        using assms mec_bot_imp_bot M_neq_bot
        by fastforce
      show \<open>\<And>s. finite (actions m s)\<close>
        by (meson \<open>m \<le> \<M>\<close> finite_actions_M finite_subset le_mdpc_iff)
      show \<open>finite (states m)\<close>
        by (meson \<open>m \<le> \<M>\<close> S_finite infinite_super states_mono)
    qed
    
    subsection \<open>States that cannot Reach the Target State\<close>
    text \<open>We show that reachability probability of 0 means that the state is not connected to the target
    in the graph of the MDP.\<close>
    
    lemma un_eq_states: \<open>R.S\<^sub>r \<union> (R.S\<^sub>e \<union> targets \<M>) = states \<M>\<close>
      using R.S\<^sub>r R.S\<^sub>e
      by (auto simp add: R.S\<^sub>r_def)
    
    lemma Sr_nNone: \<open>\<And>t. t \<in> R.S\<^sub>r \<Longrightarrow> t \<in> states \<M> - targets \<M>\<close>
      by (simp add: R.S\<^sub>r_eq)
    
    lemma mec_None_nS\<^sub>e: \<open>u \<in> targets \<M> \<Longrightarrow> the_mec \<M> u \<notin> M_mec.S\<^sub>e\<close>
      unfolding M_mec.S\<^sub>e_def
      using targets_m_mec by force
    
    lemmas M_mec.S\<^sub>e[THEN subsetD, dest]
    lemmas R.S\<^sub>e[THEN subsetD, dest]
    
    lemma S\<^sub>e_en: \<open>s \<in> R.S\<^sub>e \<Longrightarrow> (s, s') \<in> en \<M> \<Longrightarrow> s' \<in> R.S\<^sub>e\<close>
      apply(cases s rule: state_cases[of _ \<M>])
      subgoal
        using R.S\<^sub>e_E_iff R.S\<^sub>e_def
        apply (subst (asm) E_en[symmetric])
        by (auto simp: R.S\<^sub>e_E_iff)+ 
      subgoal
        using None_nS\<^sub>e by blast
      subgoal using en_avoids_id by blast 
      subgoal 
        by blast
      done
    
    lemma act_S\<^sub>e_en: \<open>s \<in> M_mec.S\<^sub>e \<Longrightarrow> (s, s') \<in> en m_mec \<Longrightarrow> s' \<in> M_mec.S\<^sub>e\<close>
      apply(cases s rule: state_cases[of _ m_mec])
      subgoal 
        using M_mec.E_en M_mec.S\<^sub>e_E_iff by blast
      subgoal
        by (simp add: M_mec.S\<^sub>e_def)
      subgoal
        using M_mec'.en_avoids_id by blast
      subgoal 
        by blast
      done
    
    lemma in_S\<^sub>e_iff:
      assumes \<open>s \<in> states \<M>\<close>
      shows \<open>s \<in> R.S\<^sub>e \<longleftrightarrow> (\<forall>t \<in> targets \<M>. (s, t) \<notin> (en \<M>)\<^sup>*)\<close>
    proof -
      have \<open>s \<notin> R.S\<^sub>e\<close> if \<open>(s, t) \<in> (en \<M>)\<^sup>*\<close> and \<open>t \<in> targets \<M>\<close> for t
        using that assms None_nS\<^sub>e S\<^sub>e_en
        by (induction rule: converse_rtrancl_induct) blast+
    
      moreover have \<open>s \<in> R.S\<^sub>e\<close> if \<open>(\<forall>t \<in> targets \<M>. (s, t) \<notin> (en \<M>)\<^sup>*)\<close>
      proof -
        have \<open>R.v cfg = 0\<close> if \<open>cfg \<in> cfg_on s\<close> for cfg
          using that assms  \<open>(\<forall>t \<in> targets \<M>. (s, t) \<notin> (en \<M>)\<^sup>*)\<close>
        proof (coinduction arbitrary: cfg s rule: R.v_eq_0_coinduct)
          case valid
          then show ?case using valid_cfgI by auto
        next
          case (nS2 cfg1)
          then show ?case by auto
        next
          case (cont cfg' cfg s)
          hence 1: \<open>(state cfg, state cfg') \<in> en \<M>\<close>
            using E_en R.K_cfg_E by blast
          show ?case
            using action_closed cont converse_rtrancl_into_rtrancl[OF 1]
            by (auto simp: en_def set_K_cfg intro!: exI[of _ \<open>state cfg'\<close>])
        qed 
        thus ?thesis
          by (simp add: R.S\<^sub>e_def R.p_eq_0_iff assms)
      qed
      ultimately show ?thesis by auto
    qed
    
    lemma act_in_S\<^sub>e_iff:
      assumes \<open>s \<in> states m_mec\<close>
      shows \<open>s \<in> M_mec.S\<^sub>e \<longleftrightarrow> (\<forall>t \<in> targets \<M>. (s, the_mec \<M> t) \<notin> (en m_mec)\<^sup>*)\<close>
    proof -
      have \<open>s \<notin> M_mec.S\<^sub>e\<close> if \<open>(s, the_mec \<M> t) \<in> (en m_mec)\<^sup>*\<close> and \<open>t \<in> targets \<M>\<close> for t
        using that assms mec_None_nS\<^sub>e act_S\<^sub>e_en states_M_mec
        by (induction rule: converse_rtrancl_induct) blast+
      moreover have \<open>s \<in> M_mec.S\<^sub>e\<close> if \<open>(\<forall>t \<in> targets \<M>. (s, the_mec \<M> t) \<notin> (en m_mec)\<^sup>*)\<close>
      proof -
        have \<open>M_mec.v cfg = 0\<close> if \<open>cfg \<in> M_mec.cfg_on s\<close> for cfg
          using that assms M_mec.valid_cfgI  \<open>(\<forall>t \<in> targets \<M>. (s, the_mec \<M> t) \<notin> (en m_mec)\<^sup>*)\<close>
        proof (coinduction arbitrary: cfg s rule: M_mec.v_eq_0_coinduct)
          case valid
          then show ?case by auto
        next
          case nS2
          then show ?case by (auto simp: targets_M_mec_mem)
        next
          case (cont cfg' cfg s)
          hence 1: \<open>(state cfg, state cfg') \<in> en m_mec\<close>
            using M_mec.E_en M_mec.K_cfg_E by blast
          show ?case
            using M_mec.action_closed[of s cfg] cont converse_rtrancl_into_rtrancl[OF 1]
            by (auto simp: en_def set_K_cfg intro!: exI[of _ \<open>state cfg'\<close>])
        qed 
        thus ?thesis
          by (simp add: M_mec.S\<^sub>e_def M_mec.p_eq_0_iff assms)
      qed
      ultimately show ?thesis by auto
    qed
    
    
    subsection \<open>Qualitative Reachability\<close>
    text \<open>If the target is reachable using \<^term>\<open>ct\<close>, then the value is not zero:\<close>
    lemma None_reach_imp_v_gt0:
      assumes 
        \<open>(s, t) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*\<close> 
        \<open>t \<in> targets m_mec\<close>
        \<open>ct \<in> Pi\<^sub>E (states m_mec) (actions' m_mec)\<close> \<open>s \<in> (states m_mec)\<close>
      shows \<open>M_mec.v (M_mec.simple ct s) > 0\<close>
      using assms
    proof (induction rule: converse_rtrancl_induct)
      case (step y z)
      then show ?case
      proof (cases \<open>y \<in> targets m_mec\<close>)
        case True
        then show ?thesis
          using step by (auto simp: targets_M_mec_mem) 
      next
        case False
    
        hence \<open>z \<in> states m_mec\<close>
          using step M_mec.K_closed[of y] M_mec.Pi_closed[of ct y z] step
          by auto
    
        moreover have "y \<notin> avoids m_mec"
        proof(rule notI)
          assume 1: "y \<in> avoids m_mec"
          with step(1) have 2: "y = z"
            using step(5)[THEN PiE_mem, of y]
            unfolding Sigma_def
            by (simp add: M_mec'.Avd_loop)
    
          have 3: "z \<notin> avoids m_mec" 
            apply(rule notI)
            using step(3)[OF step(4-5) \<open>z \<in> states m_mec\<close>] using M_mec'.Avd_Tgt_disj[of z]
            apply(subst(asm) M_mec.v_nS12)
            apply (auto simp add: local.step(5) )
            done
    
          from 1 2 3 show False 
             by auto
        qed
    
        ultimately show ?thesis
          apply (subst M_mec.v_S1)
          subgoal using step False by auto
          subgoal using step(6) False by(auto intro!: computesI)
          subgoal
            apply (rule le_less_trans[OF _ nn_integral_less[where f = \<open>\<lambda>_. 0\<close>]]) 
            using step False
            by fastforce+
          done
      qed
    qed auto
    
    
    subsection \<open>Qualitative Reachability on the Collapsed MDP equals Original MDP\<close>
    
    text \<open>Connectedness in the collapsed MDP implies connectedness in the original MDP:\<close>
    lemma en_act_subs_en_star: 
      assumes \<open>(the_mec \<M> s, the_mec \<M> s') \<in> (en m_mec)\<^sup>*\<close>
      assumes \<open>s \<in> states \<M>\<close> \<open>s' \<in> states \<M>\<close>
      shows \<open>(s, s') \<in> (en \<M>)\<^sup>*\<close>
      using assms
    proof (induction \<open>the_mec \<M> s\<close> \<open>the_mec \<M> s'\<close> arbitrary: s s' rule: rtrancl.induct)
      case rtrancl_refl
      then show ?case
        by (metis ec_def en_scD2 mec_ec mec_le states_the_mec the_mec)
    next
      case (rtrancl_into_rtrancl y)
    
      hence y: \<open>y \<in> states m_mec\<close>
        using en_states by fastforce
      then obtain a where \<open>a \<in> actions m_mec y\<close> \<open>the_mec \<M> s' \<in> a\<close>
        using rtrancl_into_rtrancl en_def by fast
      then obtain t t' where *: \<open>(t, t') \<in> en \<M>\<close> \<open>the_mec \<M> t = y\<close> \<open>the_mec \<M> t' = the_mec \<M> s'\<close>
        using y[unfolded states_M_mec] 
        apply (clarsimp simp: y actions_M_mec'[of _ \<M>] en_def)
        by blast
      have \<open>(s, t) \<in> (en \<M>)\<^sup>*\<close>
        using * en_states
        by (force intro: rtrancl_into_rtrancl)
      moreover have \<open>(t', s') \<in> (en \<M>)\<^sup>*\<close>
        by (metis "*" E_closed E_en ec_def en_scD2 en_states local.rtrancl_into_rtrancl(5) mec_ec mec_le states_the_mec the_mec)
      ultimately show ?case
        using *
        by (auto intro: rtrancl_into_rtrancl converse_rtrancl_into_rtrancl )
    qed
    
    lemma en_subs_en_act_star: 
      assumes \<open>(s, s') \<in> (en \<M>)\<^sup>*\<close>
      shows \<open>(the_mec \<M> s, the_mec \<M> s') \<in> (en m_mec)\<^sup>*\<close>
      by (simp add: M_mec_def assms en_star_map_mdpc to_mdpc.abs_eq)
    
    lemma en_mec_star_eq: 
      assumes \<open>s \<in> states \<M>\<close> \<open>s' \<in> states \<M>\<close>
      shows \<open>(s, s') \<in> (en \<M>)\<^sup>* \<longleftrightarrow> (the_mec \<M> s, the_mec \<M> s') \<in> (en m_mec)\<^sup>*\<close>
      using en_act_subs_en_star en_subs_en_act_star assms 
      by auto
    
    lemma mec_S\<^sub>e: \<open>M_mec.S\<^sub>e = the_mec \<M> ` R.S\<^sub>e\<close>
      using M_mec.S\<^sub>e act_in_S\<^sub>e_iff in_S\<^sub>e_iff
      by (auto simp: R.S\<^sub>e_def en_mec_star_eq states_M_mec) 
    
    lemma m_mec_S\<^sub>e: 
      assumes \<open>s \<in> R.S\<^sub>r\<close>
      shows \<open>the_mec \<M> s \<in> M_mec.S\<^sub>r\<close>
      using assms R.S\<^sub>e R.S\<^sub>r_S1 
      unfolding R.S\<^sub>r_def M_mec.S\<^sub>r_def mec_S\<^sub>e 
      by(auto simp: in_S\<^sub>e_iff states_M_mec computes_m_mec en_mec_star_eq)
    
    
    lemma m_mec_S\<^sub>r: \<open>s \<in> states \<M> \<Longrightarrow> the_mec \<M> s \<in> M_mec.S\<^sub>e \<Longrightarrow> s \<in> R.S\<^sub>e\<close>
      unfolding R.S\<^sub>r_def M_mec.S\<^sub>r_def mec_S\<^sub>e
      using en_mec_star_eq in_S\<^sub>e_iff  
      apply clarsimp
      by (auto simp: states_M_mec)
    
    lemma m_mec_S\<^sub>r_imp_S\<^sub>r: \<open>s \<in> states \<M> \<Longrightarrow> the_mec \<M> s \<in> M_mec.S\<^sub>r \<Longrightarrow> s \<in> R.S\<^sub>r\<close>
      unfolding R.S\<^sub>r_def M_mec.S\<^sub>r_def mec_S\<^sub>e
      by (auto simp: states_M_mec)
    
    text \<open>
    For any state in a non-trivial MEC \<^term>\<open>m \<le> M\<close>, 
    there exists strategy that can reach that from every other state in \<^term>\<open>m\<close>. 
    \<close>
    lemma mec_ex_reach:
      assumes \<open>mec \<M> m\<close> \<open>m \<le> \<M>\<close> \<open>s \<in> m\<close> \<open>\<nexists>x. trivial x = m\<close>
      obtains ct where \<open>ct \<in> Pi\<^sub>E (states m) (actions' m)\<close>
        and \<open>\<And>s'. s' \<in> states m \<Longrightarrow> (s', s) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*\<close>
    proof atomize_elim
      interpret R': Reachability_Problem \<open>actions' m\<close> \<open>states m\<close> \<open>states m - {s}\<close> \<open>{s}\<close>
        using assms mec_MDP[of m] Finite_MDP_def closed_mdpcD
        by unfold_locales (auto simp: actions'_def)
    
      have \<open>R'.p s' > 0\<close> if \<open>s' \<in> states m\<close> for s'
      proof -
        have \<open>(s', s) \<in> (en m)\<^sup>*\<close>
          by (meson assms ec_def mec_def scD that)
    
        hence \<open>(s', s) \<in> (SIGMA s:states m - {s}. \<Union> (set_pmf ` actions' m s))\<^sup>*\<close>
          using that
        proof (induction rule: converse_rtrancl_induct)
          case base
          then show ?case
            by auto
        next
          case (step y z)
          moreover have \<open>z \<in> states m\<close>
            by (metis assms(3) calculation(2) converse_rtranclE en_states)
          ultimately show ?case
            by (cases \<open>y = s\<close>) (force simp: en_def actions'_def intro: converse_rtrancl_into_rtrancl[of _ z])+
        qed
    
        thus ?thesis
          by (intro R'.p_pos[of _ s]) auto
      qed
    
      moreover obtain ct where ct: \<open>ct \<in> Pi\<^sub>E (states m) (actions' m)\<close> and ct_opt: \<open>R'.p = R'.v  o (R'.simple ct)\<close>
        using R'.p_v_memoryless by auto
    
      ultimately have *: \<open>s \<in> states m \<Longrightarrow> 0 < R'.v (R'.simple ct s)\<close> for s
        by auto
    
      have \<open>(s', s) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*\<close> if \<open>s' \<in> states m\<close> for s'
      proof -
        {
          assume \<open>(s', s) \<notin> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*\<close>
          hence \<open>R'.v (R'.simple ct s') = 0\<close>
            using that ct
            by (coinduction arbitrary: s' rule: R'.v_eq_0_coinduct) (auto simp: set_K_cfg  intro: converse_rtrancl_into_rtrancl)
        }
        thus ?thesis
          using * that by fastforce
      qed
      thus \<open>\<exists>ct. ct \<in> Pi\<^sub>E (states m) (actions' m) \<and> (\<forall>s'. s' \<in> states m \<longrightarrow> (s', s) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*)\<close>
        using ct
        by (auto intro!: exI[of _ ct])
    qed
    
    text \<open>
    Given 
      - a function \<^term>\<open>f\<close>, that selects a state in each MEC, and 
      - a policy \<^term>\<open>a\<close>, that selects an action in each such state,
    We obtain a policy that in each MEC, reaches the state selected by f.\<close>
    lemma mec_pol_ex:
      assumes 
        f: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> f (the_mec \<M> s) \<in> the_mec \<M> s\<close> and
        a: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> a (the_mec \<M> s) \<in> actions \<M> (f (the_mec \<M> s))\<close>
      obtains ct where
        \<open>ct \<in> Pi\<^sub>E (states \<M>) (actions \<M>)\<close>
        \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> (s, f (the_mec \<M> s)) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*\<close>
        \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> s \<noteq> f (the_mec \<M> s) \<Longrightarrow> ct s \<in> actions (the_mec \<M> s) s\<close> and
        \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> ct (f (the_mec \<M> s)) = a (the_mec \<M> s)\<close>
    proof (atomize_elim, goal_cases)
      case 1
      have mec: \<open>mec \<M> s\<close> \<open>s \<le> \<M>\<close> if \<open>s \<in> states m_mec\<close> for s
        using that states_M_mec mec_le by (fastforce intro!: mec_le)+
      then have \<open>\<exists>ct. (\<nexists>x. trivial x = s) \<longrightarrow> 
        ct \<in> Pi\<^sub>E (states s) (actions' s) \<and> (\<forall>s' \<in> states s. (s', f s) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*)\<close> 
        if \<open>s \<in> states m_mec\<close> for s
        using mec_ex_reach that f that[unfolded states_M_mec, THEN imageE] by metis
      then obtain ct where ct: \<open>\<And>s. s \<in> states m_mec \<Longrightarrow> (\<nexists>x. trivial x = s) \<Longrightarrow> 
        ct s \<in> Pi\<^sub>E (states s) (actions' s) \<and> (\<forall>s' \<in> states s. (s', f s) \<in> (SIGMA x:UNIV. set_pmf (ct s x))\<^sup>*)\<close>
        by auto metis
      let ?ct = \<open>\<lambda>s \<in> states \<M>. if s = f (the_mec \<M> s) then a (the_mec \<M> s) else ct (the_mec \<M> s) s\<close>
    
      have ct_eq: \<open>s \<in> states \<M> \<Longrightarrow> s \<notin> trivials \<M> \<Longrightarrow> ct (the_mec \<M> s) \<in> Pi\<^sub>E (states (the_mec \<M> s)) (actions' (the_mec \<M> s)) \<and> 
        (\<forall>s' \<in> states (the_mec \<M> s). (s', f (the_mec \<M> s)) \<in> (SIGMA x:UNIV. set_pmf (ct (the_mec \<M> s) x))\<^sup>*)\<close> for s
        using ct[of \<open>the_mec \<M> s\<close>]
        by (metis image_eqI in_trivials_the_mec singletonD states_M_mec states_the_mec states_trivial)
    
      have eq_trivial: \<open>s = f (the_mec \<M> s)\<close> 
          if \<open>s \<in> states \<M>\<close> \<open>\<exists>x. trivial x = the_mec \<M> s\<close> for s
        using that f[of s]
        by (metis singletonD states_the_mec states_trivial)
    
      have trivials_f[simp]: \<open>s \<in> trivials \<M> \<Longrightarrow> f (the_mec \<M> s) = s\<close> for s
        using ct  actions'_states
        by auto (metis eq_trivial in_trivials_the_mec)
    
      have act_mec_le: \<open>actions (the_mec \<M> s) s \<subseteq> actions \<M> s\<close> if \<open>s \<in> states \<M>\<close> for s
        using mec_le that le_mdpc_iff by fast
    
      moreover have the_mec_f[simp]: \<open>s \<in> states \<M> \<Longrightarrow> the_mec \<M> (f (the_mec \<M> s)) = the_mec \<M> s\<close> for s
        using assms empty_iff in_states[of \<M> s]  the_mec_eq[of \<open>f (the_mec \<M> s)\<close> s]
        by (simp add: states_the_mec')
    
      have \<open>?ct s \<in> actions \<M> s\<close> if \<open>s \<in> states \<M>\<close> for s
        using eq_trivial[of s] assms[of s] that ct[of \<open>the_mec \<M> s\<close>]  act_mec_le[of s] PiE_mem
        by (fastforce simp: states_M_mec image_iff actions'_def[abs_def])
       
      hence \<open>?ct \<in> Pi\<^sub>E (states \<M>) (actions \<M>)\<close>
        by auto
    
      moreover have \<open>s \<in> states \<M> \<Longrightarrow> ?ct (f (the_mec \<M> s)) = a (the_mec \<M> s)\<close> for s
        using assms
        by (simp add: states_the_mec')
    
      moreover have ct_actions: \<open>s \<in> states \<M> \<Longrightarrow> s \<noteq> f (the_mec \<M> s) \<Longrightarrow> ?ct s \<in> actions (the_mec \<M> s) s\<close> for s
        using ct_eq Finite_MDP.actions'_states[OF mec_MDP] eq_trivial  
        by fastforce+
    
      moreover have *: \<open>(s, f (the_mec \<M> s)) \<in> (SIGMA x:UNIV. set_pmf (ct (the_mec \<M> s) x))\<^sup>*\<close> if \<open>s \<in> states \<M>\<close> for s s'
        by (metis ct_eq rtrancl.intros(1) states_the_mec that trivials_f)
    
      moreover have \<open>(s, f (the_mec \<M> s)) \<in> (SIGMA x:UNIV. set_pmf (?ct x))\<^sup>*\<close> if \<open>s \<in> states \<M>\<close> for s
      proof -
        define m where \<open>m = the_mec \<M> s\<close>
        have \<open>s \<in> m\<close>
          unfolding m_def that
          using that
          by blast
    
        have set_pmf_m: \<open>z \<in> states m\<close> if \<open>z \<in> set_pmf (ct m y)\<close> \<open>y \<in> m\<close> \<open>y \<noteq> f m\<close> for y z
          using that ct_actions \<open>s \<in> states \<M>\<close> mec_closed[OF the_mec, of s \<M> y \<open>ct m y\<close> z] states_the_mec'[of s]
          unfolding m_def 
          by (smt (verit, ccfv_SIG) mem_Collect_eq restrict_apply')
    
        have \<open>(s, f m) \<in> (SIGMA x:UNIV. set_pmf (ct (the_mec \<M> s) x))\<^sup>*\<close>
          using * that m_def by auto
        hence \<open>(s, f m) \<in> (SIGMA x:UNIV. set_pmf (?ct x))\<^sup>*\<close>
          using that \<open>s \<in> m\<close>
        proof (induction rule: converse_rtrancl_induct)
          case base
          then show ?case
            by (auto simp: m_def assms that)
        next
          case (step y z)
          then show ?case
            using set_pmf_m[of s] set_pmf_m[of z]
            by (cases \<open>y = f (the_mec \<M> y)\<close>) 
              (auto simp: m_def states_the_mec' that converse_rtrancl_into_rtrancl[of y z])
        qed
        thus ?thesis
          unfolding m_def by auto
      qed
      ultimately show ?case
        by blast
    qed
    
      text \<open>If the state can reach the bottom, we can reach the bottom via ct.\<close>
    lemma mec_S\<^sub>r_reach_None: 
      assumes s: \<open>s \<in> M_mec.S\<^sub>r\<close> and
        ct: \<open>ct \<in> Pi\<^sub>E (states m_mec) (actions' m_mec)\<close> and
        ct_opt: \<open>M_mec.p = M_mec.v o (M_mec.simple ct)\<close>
      obtains t where \<open>t \<in> targets m_mec\<close> and \<open>(s, t) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*\<close>    
    proof -
      have s_states: \<open>s \<in> states m_mec\<close>
        using assms M_mec.S\<^sub>r by auto
          
        have \<open>M_mec.p s > 0\<close>
          using s unfolding M_mec.S\<^sub>r_def M_mec.S\<^sub>e_def
          by fastforce
        hence \<open>M_mec.v (M_mec.simple ct s) > 0\<close>
          using ct_opt by fastforce
        have rNone: \<open>s \<in> M_mec.S\<^sub>r \<union> {t}\<close>
          using \<open>s \<in> M_mec.S\<^sub>r\<close> by auto
        have 1: \<open>M_mec.v (M_mec.simple ct s) = 0\<close> if \<open>\<And>t'. t' \<in> targets m_mec \<Longrightarrow> (s, t') \<notin> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*\<close>
          using that rNone s_states
        proof (coinduction arbitrary: s rule: M_mec.v_eq_0_coinduct)
          case valid
          then show ?case
            using ct M_mec.simple_valid_cfg_iff' that(1) states_M_mec 
            by (auto simp: image_iff)
        next
          case cont
          obtain s' where \<open>state cfg' = s'\<close> \<open>s' \<in> states m_mec\<close>
            using cont ct  \<open>s \<in> states m_mec\<close> set_pmf_closed'
            by (auto simp: set_K_cfg actions_M_mec)
          then show ?case
            using cont(1, 4-5) M_mec.v_neq_0_imp[of \<open>(M_mec.simple ct s')\<close>] ct 
              converse_rtrancl_into_rtrancl[of _ _ \<open>(SIGMA x:UNIV. set_pmf (ct x))\<close>]
            by (auto intro!: exI[of _ \<open>s'\<close>] simp: set_K_cfg) 
        qed auto
        thus ?thesis
          using s 
          by(auto simp: M_mec.S\<^sub>e_def M_mec.S\<^sub>r_eq ct_opt intro: that)
    qed
    
    text \<open>We can finally prove, that the reachability probabilities do not increase:\<close>
    lemma p_mec_le:
      assumes \<open>s \<in> states \<M>\<close>
      shows \<open>M_mec.p (the_mec \<M> s) \<le> R.p s\<close>
    proof -
    
      text \<open>We consider an optimal policy in the collapsed MDP:\<close>
      obtain ct where
        ct: \<open>ct \<in> Pi\<^sub>E (states m_mec) (actions' m_mec)\<close> and
        ct_opt: \<open>M_mec.p = M_mec.v o (M_mec.simple ct)\<close>
        using M_mec.p_v_memoryless
        by auto
    
      text \<open>Given a MEC, return a state in the MEC that enables the action chosen by \<^term>\<open>ct\<close>.\<close>
      define f where \<open>f s = (SOME s'. s' \<in> states s \<and> (\<exists>a. a \<in> actions \<M> s' \<and> map_pmf (the_mec \<M>) a = ct s))\<close> for s
      text \<open>Given a MEC, return an action at state \<^term>\<open>f\<close> that matches \<^term>\<open>ct\<close>.\<close>
      define a where \<open>a s = (SOME a. a \<in> actions \<M> (f s) \<and> map_pmf (the_mec \<M>) a = ct s)\<close> for s
    
      text \<open>All choice operators work have witnesses\<close>
      have ex_state_action: 
        \<open>\<exists>s' \<in> states s. (\<exists>a. a \<in> actions \<M> s' \<and> map_pmf (the_mec \<M>) a = ct s)\<close> if \<open>s \<in> states m_mec\<close> for s
        by (rule PiE_E[OF ct, of s]) (insert that, auto simp: states_M_mec actions_M_mec')+
      have f_states: \<open>f s \<in> states s\<close> and 
        f_ex_act: \<open>\<exists>a. a \<in> actions \<M> (f s) \<and> map_pmf (the_mec \<M>) a = ct s\<close> if \<open>s \<in> states m_mec\<close> for s
        by (auto simp: that f_def intro: someI2_bex[OF ex_state_action])
      have a_act: \<open>a s \<in> actions \<M> (f s)\<close> and 
        a_ct: \<open>map_pmf (the_mec \<M>) (a s) = ct s\<close> if \<open>s \<in> states m_mec\<close> for s  
        unfolding a_def 
        by (auto intro: that someI2_ex[OF f_ex_act])
    
      text \<open>Now obtain a policy that resembles \<^term>\<open>ct\<close>, but on the original MDP: it exits the MECs by
        using actions from \<^term>\<open>ct\<close>.\<close>
      obtain K where
        K: \<open>K \<in> Pi\<^sub>E (states \<M>) (actions \<M>)\<close> and
        ct'_reach: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> (s, f (the_mec \<M> s)) \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*\<close> and
        ct'_neq: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> s \<noteq> f (the_mec \<M> s) \<Longrightarrow> K s \<in> actions (the_mec \<M> s) s\<close> and
        ct'_ct: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> K (f (the_mec \<M> s)) = a (the_mec \<M> s)\<close>
        using f_states a_act a_ct by (auto simp: states_M_mec intro: mec_pol_ex[of f a])
    
      text \<open>At the exit points, \<^term>\<open>K\<close> equals \<^term>\<open>ct\<close>\<close>
      hence map_pmf_ct': \<open>map_pmf (the_mec \<M>) (K (f s)) = ct s\<close> if \<open>s \<in> states m_mec\<close> for s
        using that a_ct  ct'_ct
        by(auto simp: states_M_mec_mem) 
    
      text \<open>Everywhere else, we stay within the MEC:\<close>
      have set_pmf_nex: \<open>s \<noteq> f (the_mec \<M> s) \<Longrightarrow> K s \<subseteq> states (the_mec \<M> s)\<close> if \<open>s \<in> states \<M>\<close> for s
        using that ct'_neq[of s] mec_closed[of \<M> \<open>the_mec \<M> s\<close> s]
        by auto
    
      have nn_integral_p_le: \<open>s \<in> R.S\<^sub>r \<Longrightarrow> nn_integral (K s) (\<lambda>t. (R.p t)) \<le> (R.p s)\<close> for s
        using Sr_nNone[of s] K R.S\<^sub>r_S1 
        apply (subst (2) R.p_S1)
        by (auto intro!: SUP_upper)
    
    
      text \<open>Taking a step with \<^term>\<open>K\<close> does not change lower the reachability probability:\<close>
      have p_mec_le: \<open>M_mec.p (the_mec \<M> s) \<le> nn_integral (K s) (\<lambda>t. M_mec.p (the_mec \<M> t))\<close> if \<open>s \<in> R.S\<^sub>r\<close> for s
      proof (cases \<open>s = f (the_mec \<M> s)\<close>)
        case True
        hence \<open>K s \<in> actions \<M> s\<close> and *: \<open>map_pmf (the_mec \<M>) (K s) = ct (the_mec \<M> s)\<close>
          using K R.S\<^sub>r that ct'_ct[of s] a_ct states_M_mec
          by force+
    
    
        have \<open>M_mec.p (the_mec \<M> s) = nn_integral (ct (the_mec \<M> s)) M_mec.p\<close>
          unfolding ct_opt
          using that ct R.S\<^sub>r_S1
          by (auto intro!: nn_integral_cong_AE simp: M_mec.v_S1 M_mec.simple_valid_cfg_iff'[OF ct] states_M_mec_mem R.S\<^sub>r_eq computes_m_mec_mem )
        also have \<open>\<dots> = (\<integral>\<^sup>+ t. M_mec.p (the_mec \<M> t) \<partial>measure_pmf (K s))\<close>
          by (subst *[symmetric]) auto
        finally show ?thesis
          by auto
      next
        case False
        hence \<open>the_mec \<M> s' = the_mec \<M> s\<close> if \<open>s' \<in> K s\<close> for s'
          using the_mec_unique \<open>s \<in> R.S\<^sub>r\<close>set_pmf_nex that  R.S\<^sub>r
          by blast
        then have \<open>M_mec.p (the_mec \<M> s) = \<integral>\<^sup>+ t. M_mec.p (the_mec \<M> t) \<partial>measure_pmf (K s)\<close>
          by (subst nn_integral_cong_AE[of _  \<open>\<lambda>_. M_mec.p (the_mec \<M> s)\<close>]) auto
        thus ?thesis by auto
      qed
    
      text \<open>If we can reach the target, then \<^term>\<open>K\<close> reaches it\<close>
      have None_reach: \<open>\<exists> t \<in> targets \<M>. (s, t) \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*\<close> if \<open>s \<in> R.S\<^sub>r\<close> for s
      proof -
        have S\<^sub>r: \<open>the_mec \<M> s \<in> M_mec.S\<^sub>r\<close>
          using m_mec_S\<^sub>e that
          by auto
    
        obtain t where P:"(the_mec \<M> s, the_mec \<M> t) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>*" and TTM: "t \<in> targets \<M>"
          using mec_S\<^sub>r_reach_None[OF S\<^sub>r ct ct_opt] 
          by(auto simp: targets_M_mec_mem)
    
        hence TTMM: "the_mec (to_mdpc \<M>) t \<in> targets m_mec"
          by (auto simp: targets_M_mec_mem)
    
        text \<open>We perform an induction on the length of the path to the target in the collapsed MDP:\<close> 
        have "(s, t) \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*"
          using P that
        proof (induction \<open>the_mec \<M> s\<close> arbitrary: s rule: converse_rtrancl_induct)
          case base
          then show ?case
            using R.S\<^sub>r_def the_mec_eq_None_iff 
            using TTM by fastforce
        next
          case (step z)
          hence s: \<open>s \<in> states \<M>\<close>
            using R.S\<^sub>r by auto
          hence mec_s: \<open>the_mec \<M> s \<in> states m_mec\<close>
            using states_M_mec
            by auto
    
          hence z: \<open>z \<in> states m_mec\<close>
            using ct M_mec.K_closed[of \<open>the_mec \<M> s\<close>] M_mec.Pi_closed[of ct \<open>the_mec \<M> s\<close> z] step
            by blast
    
          have \<open>(s, f (the_mec \<M> s)) \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*\<close>
            using R.S\<^sub>r ct'_reach step.prems by blast
    
          moreover obtain s' where s': \<open>the_mec \<M> s' = z\<close> \<open>s' \<in> K (f (the_mec \<M> s))\<close>
            using step(1) map_pmf_ct'[of \<open>the_mec \<M> s\<close>] s
            by (auto simp: states_M_mec) (metis (no_types, lifting) imageE pmf.set_map)
    
          ultimately have s_s': \<open>(s, s') \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*\<close>
            using rtrancl.intros(2) by force
    
          moreover have s'_states: \<open>s' \<in> states \<M>\<close>
            using the_mec_eq_None_iff s' ct'_ct states_M_mec mec_s
            by (auto intro!: closed_M[THEN closed_mdpcD, OF a_act] simp: s) 
          moreover have \<open>(s', t) \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*\<close>
          proof (cases \<open>z = the_mec \<M> t\<close>)
            case True
            hence \<open>s' = t\<close>
              using s' s'_states TTM the_mec_eq_None_iff by blast
            then show ?thesis 
              by auto
          next
            case False
            moreover have \<open>s' \<in> R.S\<^sub>r\<close>
            proof -
              have znt: "z \<notin> targets m_mec"
              proof(rule notI) 
                assume A: "z \<in> targets m_mec"
                hence NSZ: "set_pmf (ct z) \<subseteq> {z}" 
                  using PiE_mem[OF ct z] s'_states None_bot[unfolded in_bottoms_the_mec, of s']
                  by(auto simp: actions_M_mec' targets_M_mec_mem 
                    simp flip:  s'(1) intro!: the_mec_unique elim: bmec_closed
                    simp del: Tgt_the_mec_loop) 
    
                have "(z, y) \<in> (SIGMA x:UNIV. set_pmf (ct x))\<^sup>* \<Longrightarrow> z \<in> targets m_mec \<Longrightarrow> y = z" for y
                proof (induction rule: rtrancl_induct)
                  case base
                  then show ?case by blast
                next
                  case (step y' z')
                  then show ?case 
                    using NSZ
                    by auto 
                qed
                thus False 
                  using A calculation local.step(2) by blast
              qed
    
              have \<open>M_mec.p z > 0\<close>
                using None_reach_imp_v_gt0[OF step(2) TTMM ct] ct_opt z 
                by fastforce
              hence \<open>z \<in> M_mec.S\<^sub>r\<close>
                unfolding M_mec.S\<^sub>r_def M_mec.S\<^sub>e_def 
                using False z znt
                by auto 
              thus \<open>s' \<in> R.S\<^sub>r\<close>
                using m_mec_S\<^sub>r_imp_S\<^sub>r[of s'] s' s'_states
                by auto
            qed
            ultimately show ?thesis
              using rtrancl_trans step(3)[of s'] s'
              by auto
          qed
          thus ?case
            using s_s' 
            by auto
        qed
        thus ?thesis 
          using TTM by blast
      qed
    
      have \<open>M_mec.p (the_mec \<M> s) \<le> R.p s\<close> if \<open>s \<in> R.S\<^sub>r\<close>
      proof -
        have \<open>enn2real (M_mec.p (the_mec \<M> s)) \<le> enn2real (R.p s)\<close>
        proof (rule mono_les[where S = \<open>R.S\<^sub>r\<close> and N = \<open>R.S\<^sub>e \<union> targets \<M>\<close> and K = K and c = \<open>\<lambda>_. 0\<close>])
          show \<open>s \<in> R.S\<^sub>r\<close> using that by auto
          show \<open>(\<Union>s\<in>R.S\<^sub>r. set_pmf (K s)) \<subseteq> R.S\<^sub>r \<union> (R.S\<^sub>e \<union> targets \<M>)\<close>
            unfolding un_eq_states
            using K closed_M R.S\<^sub>r set_pmf_closed'
            by blast
          show \<open>\<And>s. s \<in> R.S\<^sub>r \<Longrightarrow> integrable (measure_pmf (K s)) (\<lambda>a. enn2real (R.p a))\<close>
            \<open>\<And>s. s \<in> R.S\<^sub>r \<Longrightarrow> integrable (measure_pmf (K s)) (\<lambda>a. enn2real (M_mec.p (the_mec \<M> a)))\<close>
            using K R.S\<^sub>r
            by (auto intro!: integrable_measure_pmf_finite set_pmf_finite simp: R.S\<^sub>r_def)
          show \<open>\<And>s. s \<in> R.S\<^sub>r \<Longrightarrow> \<exists>t'\<in>R.S\<^sub>e \<union> targets \<M>. (s, t') \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*\<close>
            using None_reach 
            by auto
          show \<open>measure_pmf.expectation (K s) (\<lambda>t. enn2real (R.p t)) + 0 \<le> enn2real (R.p s)\<close> if \<open>s \<in> R.S\<^sub>r\<close> for s
          proof -
            have s: \<open>s \<in> states \<M> - targets \<M>\<close>
              using that unfolding R.S\<^sub>r_def by auto
            have \<open>ennreal (measure_pmf.expectation (K s) (\<lambda>t. enn2real (R.p t))) \<le> R.p s\<close>
            using set_pmf_closed' K R.S\<^sub>r that s
            by (subst measure_pmf.ennreal_integral_real[of _ _ 1]) (auto intro!: R.p_le_1 SUP_upper nn_integral_p_le simp: R.p_S1) 
    
          thus ?thesis
            by (metis DiffE R.real_p add.right_neutral enn2real_nonneg ennreal_le_iff s)
        qed
        show \<open>enn2real (M_mec.p (the_mec \<M> s)) \<le> measure_pmf.expectation (K s) (\<lambda>t. enn2real (M_mec.p (the_mec \<M> t))) + 0\<close> if \<open>s \<in> R.S\<^sub>r\<close> for s
        proof -
            have s: \<open>s \<in> states \<M> - targets \<M>\<close>
              using that unfolding R.S\<^sub>r_def by auto
          have \<open>M_mec.p (the_mec \<M> s) \<le> ennreal (measure_pmf.expectation (K s) (\<lambda>t. enn2real (M_mec.p (the_mec \<M> t))))\<close>
            using K R.S\<^sub>r that s
            apply (subst measure_pmf.ennreal_integral_real[of _ _ 1])
            by (auto intro!: p_mec_le M_mec.p_le_1 simp: states_M_mec_mem PiE_mem)+
          thus ?thesis
            by (simp add: enn2real_leI)
        qed
          show \<open>\<And>s. s \<in> R.S\<^sub>e \<union> targets \<M> \<Longrightarrow> enn2real (M_mec.p (the_mec \<M> s)) \<le> enn2real (R.p s)\<close>
            using mec_S\<^sub>e targets_m_mec
            by (fastforce simp: M_mec.S\<^sub>e_def R.S\<^sub>e_def)  
          show \<open>finite ((\<lambda>x. enn2real (M_mec.p (the_mec \<M> x)) - enn2real (R.p x)) ` (R.S\<^sub>r \<union> (R.S\<^sub>e \<union> targets \<M>)))\<close>
            unfolding un_eq_states
            using finite_states_M 
            by auto
        qed
        thus ?thesis
          using assms
          by (auto dest!: enn2real_le simp: R.real_p states_M_mec_mem)
      qed
      moreover have \<open>(M_mec.p (the_mec \<M> s)) \<le> (R.p s)\<close> if \<open>s \<in> R.S\<^sub>e\<close>
        using M_mec.S\<^sub>e_def m_mec_S\<^sub>e R.S\<^sub>e_def that mec_S\<^sub>e by auto
      moreover have \<open>(M_mec.p (the_mec \<M> t)) \<le> (R.p t)\<close> if \<open>t \<in> targets \<M>\<close> for t
        using that targets_m_mec by auto
      ultimately show ?thesis
        using assms
        using R.S\<^sub>e_def R.S\<^sub>r_eq R.p_nS12 by blast
    qed
    
    lemma p_mec_eq: \<open>s \<in> states \<M> \<Longrightarrow> M_mec.p (the_mec \<M> s) = R.p s\<close>
      by(auto intro!: order_antisym p_mec_ge p_mec_le)
    
  end
  
  
  subsection \<open>Max-Reduction\<close>
  
  text \<open>In a second step, we eliminate all bottom MECs and self-loops:\<close>
  
  definition "bmecs M = {m. bmec M m}"
  
  lemma bmecs_eq_bmec[simp]: "m \<in> bmecs \<M> \<longleftrightarrow> bmec \<M> m"
    unfolding bmecs_def by blast
  
  
  
  
  definition Max_red :: "'a mdptc \<Rightarrow> 'a mdpc mdptc" where "Max_red \<M> = 
    (let M' = M_mec \<M>; A' = avoids M' \<union> bmecs \<M> - targets M' in 
    Abs_mdptc (map_actions (\<lambda>s a. if s \<in> computes M' - bmecs \<M> then a - {return_pmf s} else {return_pmf s}) M', A', targets M'))"
  
  lemma states_Max_red: \<open>states (Max_red \<M>) = states (M_mec \<M>)\<close>
    unfolding Max_red_def Let_def
    apply transfer
    by auto
  
  lemma states_Max_red_mem[simp]: \<open>x \<in> states (Max_red \<M>) \<longleftrightarrow> x \<in> states (M_mec \<M>)\<close>
    unfolding states_Max_red
    by auto
  
  lemma to_mdpc_Max_red: "to_mdpc (Max_red \<M>) = map_actions (\<lambda>s a. if s \<in> computes (M_mec \<M>) - bmecs \<M> then a - {return_pmf s} else {return_pmf s}) (M_mec \<M>)"
    unfolding Max_red_def Let_def 
    by (auto simp: to_mdpc.abs_eq)
  
  
  lemma avoids_Max_red: "avoids (Max_red \<M>) = avoids (M_mec \<M>) \<union> bmecs \<M> - targets (M_mec \<M>)"
    unfolding Max_red_def Let_def by (auto simp: avoids.abs_eq)
  
  lemma avoids_Max_red_mem: "x \<in> avoids (Max_red \<M>) \<longleftrightarrow> x \<in> avoids (M_mec \<M>) \<union> bmecs \<M> - targets (M_mec \<M>)"
    using avoids_Max_red by blast
  
  lemma targets_Max_red: "targets (Max_red \<M>) = targets (M_mec \<M>)"
    unfolding Max_red_def Let_def by (auto simp: targets.abs_eq)
  
  lemma targets_Max_red_mem: "x \<in> targets (Max_red \<M>) \<longleftrightarrow> x \<in> targets (M_mec \<M>)"
    using targets_Max_red by blast
  
  lemma computes_Max_red: "computes (Max_red \<M>) = computes (M_mec \<M>) - bmecs \<M>"
    unfolding computes_def avoids_Max_red targets_Max_red states_Max_red
    by auto
  
  lemma computes_Max_red_mem: "x \<in> computes (Max_red \<M>) \<longleftrightarrow> x \<in> computes (M_mec \<M>) - bmecs \<M>"
    using computes_Max_red by blast
  
  lemma actions_Max_red: \<open>s \<in> states (M_mec \<M>) \<Longrightarrow> 
    actions (Max_red \<M>) s = (if s \<in> computes (Max_red \<M>) then actions (M_mec \<M>) s - {return_pmf s} else {return_pmf s})\<close>
    unfolding computes_Max_red_mem
    apply transfer
    unfolding Max_red_def Let_def
    apply transfer
    by (auto simp: actions_map_mdpc states_the_mec')
  
  
  context MDPC_Reach_Avoid_defs
  begin
  
    subsection \<open>Min-Reduced MDP\<close>
    text \<open>The reduction function: trivial MECs remain, everything else becomes either an avoid or target state:\<close>
    abbreviation "max_red \<equiv> Max_red \<M>"
  
    
  
  end
  
  context MDPC_Reach_Avoid
  begin
    
    lemma bmec_states_mec: "bmec \<M> m \<Longrightarrow> m \<in> states (M_mec \<M>)"
      apply(frule bmec_neq_bot)
      unfolding bmec_def
      apply clarify
      apply(frule mec_le)
      apply(clarsimp simp: states_M_mec eq_bot_iff_states le_mdpc_iff)
      using the_mec_eqI by fast
    
    lemma False_in_max: \<open>u \<in> avoids max_red \<Longrightarrow> u \<in> states max_red\<close>
      by (auto simp: avoids_Max_red bmec_states_mec) 
    
    lemma True_in_max: \<open>u \<in> targets max_red \<Longrightarrow> u \<in> states max_red\<close>
      by(auto simp: targets_Max_red)
    
    lemma actions_max_red_nself[simp]: \<open>u \<in> computes m_mec \<Longrightarrow> \<not>bmec \<M> u \<Longrightarrow> actions max_red u = actions m_mec u - {return_pmf u}\<close>
      using computes_states
      by(auto simp: computes_Max_red_mem actions_Max_red split: if_splits)
    
    lemma actions_max_red_bottoms[simp]: \<open>u \<in> bmecs \<M> \<Longrightarrow> actions max_red u = {return_pmf u}\<close>
      by(auto simp: bmec_states_mec computes_Max_red_mem actions_Max_red split: if_splits)
    
    lemma actions_max_red_ncomputes[simp]: \<open>u \<in> states m_mec \<Longrightarrow> u \<notin> computes m_mec \<Longrightarrow> actions max_red u = {return_pmf u}\<close>
      by(auto simp: computes_Max_red_mem actions_Max_red split: if_splits)
    
    lemma states_targets[simp]: "u \<in> targets \<M> \<Longrightarrow> states (the_mec \<M> u) = {u}"
      by (auto simp add: the_mec_None)
    
    lemma states_avoids[simp]: "u \<in> avoids \<M> \<Longrightarrow> states (the_mec \<M> u) = {u}"
      by (auto simp add: the_mec_None)
    
    lemma actions_targets[simp]: \<open>u \<in> targets \<M> \<Longrightarrow> actions m_mec (the_mec \<M> u) = {return_pmf (the_mec \<M> u)}\<close>
      by (subst actions_M_mec) (auto simp: Tgt_loop) 
    
    lemma actions_avoids[simp]: \<open>u \<in> avoids \<M> \<Longrightarrow> actions m_mec (the_mec \<M> u) = {return_pmf (the_mec \<M> u)}\<close>
      by (subst actions_M_mec) (auto simp: Avd_loop) 
    
    lemma states_max_red: \<open>states max_red = avoids max_red \<union> targets max_red \<union> { s. s \<in> states m_mec \<and> \<not>bmec \<M> s}\<close>
      by(auto simp: targets_Max_red_mem avoids_Max_red_mem in_bottoms_the_mec bmec_states_mec ) 
    
    lemma computes_max_red_sub: "computes max_red \<subseteq> { s. s \<in> states m_mec \<and> \<not>bmec \<M> s}"
      unfolding computes_def states_max_red 
      by(auto simp: states_max_red)
    
    lemma states_inv_the_mec: \<open>s \<in> m_mec \<Longrightarrow> states s \<subseteq> the_mec \<M> -` {s}\<close>
      by(auto simp: states_M_mec)
    
    lemma actions_Inl_ne: 
      assumes \<open>s \<in> computes max_red\<close>
      shows \<open>actions max_red s \<noteq> {}\<close>
    proof -
      from assms have [simp]: \<open>s \<in> max_red\<close> \<open>s \<notin> avoids max_red\<close> \<open>s \<notin> targets max_red\<close> 
        unfolding computes_def by auto
    
      have NBMEC: \<open>\<not>bmec \<M> s\<close>
        using \<open>s \<in> states (to_mdpc max_red)\<close> states_max_red by force
    
      have s: \<open>s \<in> states m_mec\<close>
        using \<open>s \<in> states (to_mdpc max_red)\<close> by auto
    
      then obtain s' a' where s': \<open>s' \<in> s\<close> \<open>a' \<in> actions \<M> s'\<close> \<open>\<not>a' \<subseteq> s\<close>
        using assms nbmec_exit[OF NBMEC] 
        by (auto simp: states_max_red states_M_mec_mem dest!:the_mec) metis
      hence map_a': \<open>map_pmf (the_mec \<M>) a' \<in> actions m_mec (the_mec \<M> s')\<close>
        apply(subst actions_M_mec)
        using in_states apply fastforce
        using assms states_inv_the_mec[of s] computes_max_red_sub
        by blast
      moreover have mec_s': \<open>the_mec \<M> s' = s\<close>
        using s' s assms states_max_red states_M_mec
        by (metis (no_types, opaque_lifting) imageE the_mec_eq)
      moreover obtain mec' where mec': \<open>mec' \<noteq> s\<close> \<open>mec' \<in> map_pmf (the_mec \<M>) a'\<close>
      proof -
        assume a1: "\<And>mec'. \<lbrakk>mec' \<noteq> s; mec' \<in> set_pmf (map_pmf (the_mec \<M>) a')\<rbrakk> \<Longrightarrow> thesis"
        obtain zz :: "'v set \<Rightarrow> 'v set \<Rightarrow> 'v" and zza :: "'v set \<Rightarrow> 'v set \<Rightarrow> 'v" where
          f2: "\<forall>Z Za. Z \<subseteq> Za \<or> zz Z Za \<in> Z \<and> zz Z Za \<notin> Za"
          by (metis (no_types) subsetI)
        then have f3: "zz (set_pmf a') (states s) \<in> set_pmf a'"
          using s'(3) by blast
        then have "zz (set_pmf a') (states s) \<in> states \<M>"
          by (metis actions'_states empty_iff in_states s'(2) set_pmf_closed)
        then show ?thesis
          using f3 f2 a1 by (metis (no_types) image_iff pmf.set_map s'(3) states_the_mec)
      qed
    
      ultimately show ?thesis
        by (auto simp: s actions_Max_red map_pmf_eq_return_pmf_iff)
    qed
    
    lemma actions_max_ne: 
      assumes \<open>s \<in> max_red\<close>
      shows \<open>actions max_red s \<noteq> {}\<close> 
      by (metis actions_Inl_ne actions_Max_red assms empty_not_insert states_Max_red)
    
    lemma max_red_nbot: \<open>to_mdpc max_red \<noteq> \<bottom>\<close>
      unfolding Max_red_def eq_bot_iff_states
      by (metis M_mec.S_not_empty Max_red_def states_Max_red)
    
    
    lemma closed_mdpc_remove_loop: \<open>closed_mdpc X \<Longrightarrow> closed_mdpc (map_actions (\<lambda>s a. if s \<in> computes M' - bmecs M then a - {return_pmf s} else {return_pmf s}) X)\<close>
      unfolding closed_mdpc_def using in_states
      by (fastforce simp: en_def subset_iff split: if_splits) 
    
    lemma finite_states_max: \<open>finite (states max_red)\<close>
      unfolding states_Max_red 
      by (auto intro: M_mec.S_finite)
    
    lemma max_red_closed: \<open>closed_mdpc max_red\<close>
      unfolding to_mdpc_Max_red
      apply(rule closed_mdpc_remove_loop)
      by (auto intro!: closed_mdpc_fix_loop closed_mdpc_map M_mec.closed_M)
    
    lemma finite_actions_max_red: \<open>finite (actions max_red s)\<close>
      apply(cases "s \<in> states m_mec")
      subgoal 
        by(auto simp: actions_Max_red M_mec.finite_actions_M)
      subgoal 
        using in_states[of max_red s] finite.simps
        by(auto simp: states_Max_red)
      done
    
    
    sublocale max_red: Finite_MDP max_red  
      apply standard
      using max_red_nbot actions_max_ne max_red_closed finite_states_max finite_actions_max_red
      by auto
    
    
    lemma states_max_red_I[simp, intro]: \<open>s \<in> states m_mec \<Longrightarrow> s \<in> states max_red\<close>
      unfolding states_max_red avoids_Max_red by (auto simp: targets_Max_red_mem)
    
    lemma arb_actI': \<open>s \<in> states \<M> \<Longrightarrow> arb_act s \<in> actions \<M> s\<close>
      using actions'_states arb_actI
      by blast
    
    lemma actions_M_mec_bot:
      assumes \<open>bmec \<M> s\<close> \<open>s \<in> states m_mec\<close>
      shows \<open>actions m_mec s = {return_pmf s}\<close>
      using assms bmec_closed[OF \<open>bmec \<M> s\<close>] arb_actI' (*TODO: fix this proof*)
      by (auto simp: image_iff actions_M_mec' states_M_mec intro!: map_pmf_eq_return_pmf_iff[THEN iffD2])
         (smt (verit, ccfv_threshold) states_the_mec the_mec_eq map_pmf_eq_return_pmf_iff)
    
    lemma max_red_bmec[simp]:
      assumes \<open>bmec \<M> s\<close> \<open>s \<notin> targets max_red\<close>
      shows \<open>s \<in> avoids max_red\<close>
      using assms 
      by (simp add: avoids_Max_red_mem targets_Max_red_mem)
    
    subsubsection \<open>Reachability Problem on the Max-reduced MDP\<close>
    
    sublocale max_red: Reachability_Problem \<open>actions' max_red\<close> \<open>states max_red\<close> \<open>computes max_red\<close> \<open>targets max_red\<close>
      by standard (auto simp: True_in_max computes_Max_red targets_Max_red)
    
    lemma AT_max_red_disj: "targets max_red \<inter> avoids max_red = {}"
      using AT_M_mec_disj
      by(auto simp: targets_Max_red avoids_Max_red)
    
    lemma p_fin_bmec[simp]:
      assumes \<open>bmec \<M> s\<close> \<open>s \<notin> targets max_red\<close>
      shows \<open>M_mec.p_fin i s = 0\<close>
    proof -
      have \<open>s \<in> states m_mec\<close>
        using assms unfolding bmec_def states_M_mec
        by (auto simp: image_iff)
          (metis Set.basic_monos(7) all_not_in_conv assms(1) bmec_has_state mec_le states_mono the_mec_eqI)
      thus ?thesis
        using assms
        by (induction i arbitrary: s) (auto simp: targets_Max_red M_mec.p_fin_Suc actions_M_mec_bot)
    qed
    
    lemma p_fin_False[simp]: 
      assumes "s \<in> avoids max_red"
      shows \<open>max_red.p_fin i s = 0\<close>
      using AT_max_red_disj False_in_max assms
      by (auto intro: max_red.p_fin_nS12)
    
    
    lemma (in Reachability_Problem) p_fin_le_Suc: \<open>p_fin i \<le> p_fin (Suc i)\<close>
      unfolding p_fin_def
      using reach_fin_mono[of i \<open>Suc i\<close>]
      by (auto intro!: le_funI simp: P_sup_def intro!: SUP_mono' emeasure_mono)
    
    lemma max_p_fin_le_sup: \<open>s \<in> states m_mec \<Longrightarrow> 
      max_red.p_fin i s \<le> (\<Squnion>a \<in> actions max_red s. integral\<^sup>N (measure_pmf a) (max_red.p_fin i))\<close>
      apply (rule order.trans[OF max_red.p_fin_le_Suc[THEN le_funD]])
      unfolding max_red.p_fin_Suc
      by (auto simp: max_red.p_fin_Suc computes_Max_red dest!: actions_max_red_ncomputes[of s])
    
    
    lemma actions_max_redI:
      \<open>s \<in> states m_mec \<Longrightarrow> a \<in> actions m_mec s \<Longrightarrow> a \<noteq> return_pmf s \<Longrightarrow> a \<in> actions max_red s\<close>
      apply(cases s rule: state_cases[of _ max_red])
      subgoal
        by(auto simp: actions_Max_red)
      subgoal 
        by (simp add: MDPC_Reach_Avoid.Tgt_loop[OF MDPC_Reach_Avoid_m_mec] targets_Max_red_mem)
      subgoal                                                  
        by (metis Diff_iff MDPC_Reach_Avoid.Inr_actions MDPC_Reach_Avoid_m_mec actions_M_mec_bot
            actions_Max_red actions_max_red_nself bmecs_eq_bmec computes_def)
      subgoal 
        by simp
      done
    
    lemma p_fin_eq_mec_max: 
      assumes \<open>s \<in> states m_mec\<close>
      shows \<open>M_mec.p_fin i s = max_red.p_fin i s\<close>
      using assms
    proof (induction i arbitrary: s)
      case 0
      then show ?case
        apply (cases \<open>s \<in> targets max_red\<close>)
        by (auto simp: targets_Max_red intro!: M_mec.p_fin_0 M_mec.p_fin_S2)
    next
      case (Suc i)
      show ?case
      proof (cases \<open>s \<in> targets max_red \<or> bmec \<M> s\<close>)
        case True
        then show ?thesis
        apply(cases "s \<in> targets max_red")
        subgoal by (auto simp add: targets_Max_red)
        subgoal 
          using Suc by auto
        done
      next
        case False
    
    
        have 1: \<open>M_mec.p_fin (Suc i) s \<le> max_red.p_fin (Suc i) s\<close>
        proof -
          have \<open>integral\<^sup>N x (M_mec.p_fin i) \<le> (\<Squnion>x\<in>actions max_red s. integral\<^sup>N (measure_pmf x) (max_red.p_fin i))\<close> if
            \<open>x \<in> actions m_mec s\<close> for x
          proof (cases \<open>x = return_pmf s\<close>)
            case True
            then show ?thesis
              using max_p_fin_le_sup[of s i] Suc by auto
          next
            case False
            then show ?thesis 
              using Suc that M_mec.set_pmf_closed[of s]
              by (fastforce intro!: actions_max_redI nn_integral_mono_AE SUP_upper2)
          qed
          thus ?thesis
            unfolding M_mec.p_fin_Suc max_red.p_fin_Suc
            using Suc False
            by (auto intro!: SUP_least simp: computes_Max_red_mem targets_Max_red_mem)
        qed
        moreover have \<open>max_red.p_fin (Suc i) s \<le> M_mec.p_fin (Suc i) s\<close>
          unfolding M_mec.p_fin_Suc max_red.p_fin_Suc 
          using M_mec.set_pmf_closed[of s ]
          by (fastforce simp: Suc states_max_red targets_Max_red computes_Max_red intro!: nn_integral_mono_AE SUP_mono)
          ultimately show ?thesis
          by auto
      qed
    qed
    
    lemma p_eq_mec_max:\<open>s \<in> states m_mec \<Longrightarrow> M_mec.p s = max_red.p s\<close>
      using p_fin_eq_mec_max[of s] 
      unfolding M_mec.p_eq_Sup_p_fin max_red.p_eq_Sup_p_fin
      by (auto intro!: SUP_cong simp: image_image)
    
    lemma p_eq_max:\<open>s \<in> states \<M> \<Longrightarrow> R.p s = max_red.p (the_mec \<M> s)\<close>
      using p_mec_eq p_eq_mec_max
      by (auto simp: states_M_mec)
    
    lemmas closed_close[intro]
    
    text \<open>Every state in the collapsed MDP is its own MEC:\<close>
    lemma mec_mec_simple:
      assumes \<open>s \<in> states m_mec\<close>
      shows \<open>mec m_mec (close (restrict_states {s} m_mec))\<close>
    proof -
      let ?m = \<open>close ((restrict_states {s} m_mec))\<close> \<comment> \<open>the MEC for \<^term>\<open>s\<close>\<close>
    
      have \<open>sc ?m\<close>
        by (rule scI) auto
      hence \<open>ec ?m\<close>
        by (auto intro: ecI)
    
      have \<open>\<exists>s \<in> states \<M>. S' = (close (restrict_states {the_mec \<M> s} m_mec))\<close> if mec: \<open>mec m_mec S'\<close> for S'
        \<comment> \<open>Assume we have a MEC \<^term>\<open>S'\<close>, show that there is a state in the MDP that it is equal to.\<close>
      proof -
    
        have \<open>S' \<le> m_mec\<close>
          using \<open>mec m_mec S'\<close> mec_le 
          by blast
    
        hence states_S': \<open>states S' \<subseteq> states m_mec\<close>
          by (simp add: states_mono)
    
        \<comment> \<open>project S' back to R\<close>
        define R where \<open>R = close ((restrict_states {s | s s'. s' \<in> S' \<and>  s \<in> states s'} \<M>))\<close>
    
        have states_R: \<open>states R = (\<Union>s' \<in> S'. states s')\<close>
          unfolding R_def
          using states_S' states_the_mec_subs
          apply (clarsimp simp: states_M_mec)     
          by fast
        define R' where \<open>R' =
          map_actions (\<lambda>s a. {d \<in> a. map_pmf (the_mec \<M>) d \<in> actions m_mec (the_mec \<M> s)}) R\<close>
    
        have states_R'[simp]: \<open>states R' = states R\<close>
          unfolding R'_def by auto
    
        have states_R_D: \<open>s \<in> states R \<Longrightarrow> the_mec \<M> s \<in> S'\<close> for s
          unfolding states_R 
          using states_S' the_mec_eq
          by (auto simp: states_M_mec)
    
        have actions_R: \<open>actions R s = {a \<in> actions \<M> s. a \<subseteq> states R}\<close> if \<open>s \<in> states R\<close> for s
          using that
          unfolding R_def
          by auto
    
        have states_R_D[dest]: \<open>s \<in> states R \<Longrightarrow> s \<in> states \<M>\<close> for s
          by (simp add: R_def)
    
        have \<open>s \<in> states R \<Longrightarrow> the_mec \<M> s \<le> \<M>\<close> for s
          by (simp add: local.R_def mec_le the_mec)
    
        have the_mec_in_S': \<open>s \<in> states R \<Longrightarrow> the_mec \<M> s \<in> S'\<close> for s
          using states_S' the_mec_unique[of _ s]
          by (auto simp: states_R states_M_mec)
    
    
        have in_act_mecD[dest]: \<open>a \<in> actions (the_mec \<M> s) s' \<Longrightarrow> s \<in> states \<M> \<Longrightarrow> a \<in> actions \<M> s'\<close> for a s s'
          using the_mec[of s \<M>] mec_le le_mdpc_iff 
          by fast
    
        have states_R'_sup: \<open>s \<in> states R \<Longrightarrow> states (the_mec \<M> s) \<subseteq> states R\<close> for s 
          using states_R states_R_D[of s] the_mec_in_S'
          by auto
    
        moreover have \<open>s \<in> states R' \<Longrightarrow> s' \<in> states R' \<Longrightarrow> actions (the_mec \<M> s) s' \<subseteq> actions R' s'\<close> for s s'
          unfolding R'_def
          using states_R'_sup[of s] actions_M_mec closed_mdpcD[OF mec_closed_mdpc]
          by (fastforce simp: actions_R)
    
        ultimately have the_mec_in_R: \<open>s \<in> states R' \<Longrightarrow> the_mec \<M> s \<le> R'\<close> for s
          by (force intro!: le_mdpcI)
    
        have R'_in_M: \<open>R' \<le> \<M>\<close>
          using actions_R in_states
          by (fastforce simp: le_mdpc_iff R'_def)
    
        have S'_in_mec: \<open>states S' \<subseteq> states m_mec\<close>
          using  mec_le[OF mec]
          by (auto simp: le_mdpc_iff states_M_mec image_iff)
    
        have S'_acts_subs: \<open>actions S' s \<subseteq> (\<Union>x\<in>states s. map_pmf (the_mec \<M>) ` actions \<M> x)\<close> if \<open>s \<in> S'\<close> for s
          using that mec_le[OF mec] actions_M_mec'[of s]
          by (fastforce simp: le_mdpc_iff)
    
        have S'_act_M: \<open>\<exists>s' \<in> states s. \<exists>a' \<in> actions \<M> s'. map_pmf (the_mec \<M>) a' = a\<close> if \<open>a \<in> actions S' s\<close> \<open>s \<in> S'\<close> for a s
          using mec_le[OF mec] actions_M_mec'[of s] that
          by (fastforce simp: le_mdpc_iff subset_iff)
    
        have S'_act_R: \<open>\<exists>s' \<in> states s. \<exists>a' \<in> actions R' s'. map_pmf (the_mec \<M>) a' = a\<close> if \<open>a \<in> actions S' s\<close> \<open>s \<in> S'\<close> for a s
          using mec_le[OF mec] S'_in_mec S'_act_M[of a s]
          unfolding R'_def
          using that
          apply auto
          subgoal for s' a'
            apply (intro bexI[of _ s'] exI[of _ a'])
             apply (subst actions_R)
            using states_R set_pmf_closed'[of a' s'] mec_closed[OF mec, of s a] 
              apply auto
            apply (metis image_eqI states_the_mec pmf.set_map)
            apply (subst actions_M_mec[OF states_R_D])
            by (fastforce simp: image_iff)+
          done
    
        have \<open>closed_mdpc R'\<close>
          unfolding closed_mdpc_def en_def
          using in_states[of R]       
          by auto (auto simp: R_def R'_def)
    
        moreover have \<open>sc R'\<close>
        proof -
          { fix s s'
            assume s: \<open>s \<in> states R'\<close> and s': \<open>s' \<in> states R'\<close>
            hence \<open>the_mec \<M> s \<in> S'\<close> \<open>the_mec \<M> s' \<in> S'\<close>
              unfolding R'_def
              using the_mec_in_S'
              by auto
            hence \<open>(the_mec \<M> s, the_mec \<M> s') \<in> (en S')\<^sup>*\<close>
              using mec unfolding mec_def ec_def sc_def by auto
            hence \<open>(s, s') \<in> (en R')\<^sup>*\<close>
              using s s'
            proof (induction \<open>the_mec \<M> s\<close> \<open>the_mec \<M> s'\<close> arbitrary: s s' rule: rtrancl.induct)
              case (rtrancl_refl s)
              then have \<open>(s, s') \<in> (en (the_mec \<M> s))\<^sup>*\<close>
                using mec_ec ec_def
                by (auto intro!: scD)
              thus ?case
                using the_mec_in_R[of s] rtrancl_refl rtrancl_mono en_mono
                by auto
            next
              case (rtrancl_into_rtrancl a b c)
    
              hence a: \<open>a \<in> states S'\<close>
                using en_states by fastforce
    
              obtain act_mec where \<open>the_mec \<M> c \<in> set_pmf act_mec\<close> \<open>act_mec \<in> actions S' a\<close>
                using rtrancl_into_rtrancl(3) en_def
                by force
    
              then obtain a' c' where a'_c': \<open>the_mec \<M> a' = a\<close> \<open>the_mec \<M> c = the_mec \<M> c'\<close> \<open>(a', c') \<in> en R'\<close>
                unfolding en_def
                using S'_act_R[of act_mec a] a S'_in_mec 
                by (fastforce simp: states_M_mec)
              have \<open>(b, a') \<in> (en R')\<^sup>*\<close>
                using rtrancl_into_rtrancl
                by (metis \<open>(a', c') \<in> en R'\<close> \<open>the_mec \<M> a' = a\<close> en_states)
              moreover have \<open>(c', c) \<in> (en R')\<^sup>*\<close>
              proof -
                have \<open>c' \<in> states \<M>\<close>
                using a'_c' en_mono[OF R'_in_M] E_closed en_states[of _ _ \<M>] E_en
                by auto
                
                hence \<open>(c', c) \<in> (en (the_mec \<M> c))\<^sup>*\<close>
                using mec_ec ec_def a'_c' rtrancl_into_rtrancl(5) 
                by (auto intro!: scD)
              thus ?thesis
                using the_mec_in_R[of c] rtrancl_refl rtrancl_mono en_mono rtrancl_into_rtrancl
                by auto
            qed
                  ultimately show ?case
                using a'_c'(3) by fastforce
            qed
          }
          thus ?thesis
            unfolding sc_def
            by (auto simp: en_def)
        qed
        hence \<open>ec R'\<close>
          using calculation ecI by blast
        hence \<open>\<And>s. s \<in> states R' \<Longrightarrow> R' \<le> the_mec \<M> s\<close>
          using R'_in_M mec_def states_mono the_mec_in_R
          by blast
    
        then obtain s where s: \<open>s \<in> states \<M>\<close> \<open>states R' \<subseteq> the_mec \<M> s\<close>
          unfolding R'_def
          using S_not_empty states_R_D
          by (fastforce simp: le_mdpc_iff)
        hence \<open>states S' \<subseteq> {the_mec \<M> s}\<close>
          using states_S' 
          apply (auto simp: states_R  states_M_mec)
          using states_the_mec[of _ \<M>] the_mec_eq[of _ s]
          by blast
        hence states_S': \<open>states S' = {the_mec \<M> s}\<close>
          using M_neq_bot M_mec.M_neq_bot mec_bot_imp_bot mec eq_bot_iff_states   
          by (cases \<open>S' = \<bottom>\<close>) (auto simp: R'_def subset_iff)
        have ec_close: \<open>ec (close (restrict_states {the_mec \<M> s} m_mec))\<close>
          by (auto intro!: ecI scI)
        moreover have le: \<open>S' \<le> close (restrict_states {the_mec \<M> s} m_mec)\<close>
          using  \<open>S' \<le> m_mec\<close> ec_close in_states states_S' mec_closed[OF mec]
          by (fastforce simp: le_mdpc_iff s states_M_mec)
    
        hence \<open>S' = close (restrict_states {the_mec \<M> s} m_mec)\<close>
          using close_le restrict_states_le
          by (intro mec_least[OF mec] antisym ) (auto intro: order.trans ec_close)
        thus ?thesis
          using s by auto
      qed
      thus ?thesis
        using assms mec_exists' by force
    qed
    
    
    lemma avoids_en_min': \<open>x \<in> avoids max_red \<Longrightarrow> (x, y) \<in> (en max_red) \<Longrightarrow> y \<in> avoids max_red\<close>
      using False_in_max[of x]
      by (auto simp: en_def actions_Max_red split: if_splits) 
    
    lemma targets_en_min': \<open>x \<in> targets max_red \<Longrightarrow> (x, y) \<in> (en max_red) \<Longrightarrow> y \<in> targets max_red\<close>
      using True_in_max[of x]
      by (auto simp: en_def actions_Max_red split: if_splits) 
    
    
    lemma avoids_en_min_star': \<open>x \<in> avoids max_red \<Longrightarrow> (x, y) \<in> (en max_red)\<^sup>* \<Longrightarrow> y \<in> avoids max_red\<close>
      apply(rotate_tac)
      by (induction rule: rtrancl_induct) (auto simp: avoids_en_min')
    
    
    lemma targets_en_min_star': \<open>x \<in> targets max_red \<Longrightarrow> (x, y) \<in> (en max_red)\<^sup>* \<Longrightarrow> y \<in> targets max_red\<close>
      apply(rotate_tac)
      by (induction rule: rtrancl_induct) (auto simp: targets_en_min')
    
    
    lemma Inl_red_trivials:
      assumes \<open>s \<in> computes max_red\<close>
      shows \<open>s \<in> trivials max_red\<close>
    proof -
      let ?sink = \<open>targets max_red \<union> avoids max_red\<close>
    
      have \<open>\<exists>s. S' = trivial s\<close> if 
        mec: \<open>mec max_red S'\<close> and no_trap: \<open>states S' \<inter> ?sink = {}\<close> for S'
      proof -
        have \<open>S' \<le> max_red\<close>
          using \<open>mec max_red S'\<close> mec_le
          by blast
    
        hence S'_max_red: \<open>states S' \<subseteq> states max_red\<close>
          by (simp add: states_mono)
    
        have S'_inl[dest]: \<open>(mec \<M> x) \<and>  \<not> bmec \<M> x\<close> if \<open>x \<in> states S'\<close> for x
          using \<open>states S' \<inter> ?sink = {}\<close> \<open>states S' \<subseteq> states max_red\<close> that 
          unfolding states_max_red
          by (auto simp: states_M_mec subset_iff image_iff)
    
        have closed_S': \<open>closed_mdpc S'\<close>
          using \<open>mec max_red S'\<close> ec_def mec_def by blast
    
    
        have targets_S'[iff]: \<open>x \<in> states S' \<longleftrightarrow> False\<close> if \<open>x \<in> targets max_red\<close> for x
          using S'_inl[of x] that no_trap by blast
    
        have avoids_S'[iff]: \<open>x \<in> states S' \<longleftrightarrow> False\<close> if \<open>x \<in> avoids max_red\<close> for x
          using S'_inl[of x] that no_trap by blast
    
        have actions_Inr[simp]: \<open>actions S' s = {}\<close>  if \<open>s \<in> targets max_red\<close> for s
          using in_states targets_S'[OF that] by fast
    
        have actions_Inr[simp]: \<open>actions S' s = {}\<close>  if \<open>s \<in> avoids max_red\<close> for s
          using in_states avoids_S'[OF that] by fast
    
        have states_R': \<open>states S' = {s |s. s \<in> states S' \<and> s \<in> computes max_red}\<close>
          using S'_max_red
          by (auto intro!: computesI)
    
        have \<open>ec S'\<close>
          using mec_ec that(1) ec_map by blast
    
        have \<open>states S' \<noteq> {}\<close>
          using \<open>mec max_red S'\<close>
          by (metis eq_bot_iff_states mec_bot_imp_bot max_red.M_neq_bot)
    
        then obtain s where s[simp]: \<open>s \<in> states S'\<close>
          using states_R' by auto
    
        hence \<open>mec \<M> s\<close> \<open>\<not>bmec \<M> s\<close>
          by (auto simp add: S'_inl)
    
    
        hence d_act_S': \<open>a \<in> actions S' s \<Longrightarrow> a \<in> actions max_red s \<and> set_pmf a \<subseteq> computes max_red\<close> for a s
          using \<open>S' \<le> max_red\<close>[unfolded le_mdpc_iff] closed_mdpcD[OF closed_S', of a s] 
          by (auto intro!: computesI)
    
        have \<open>a \<in> actions m_mec s\<close> if \<open>a \<in> actions S' s\<close> \<open>s \<in> states S'\<close> for s a
        proof -
          have \<open>mec \<M> s\<close> \<open>\<not>bmec \<M> s\<close>
            using states_R' that(2) by auto
    
          have \<open>x \<notin> set_pmf a\<close> if \<open>bmec \<M> x\<close> for x
            using \<open>ec S'\<close> closed_mdpcD ec_def states_R' that 
            by (metis S'_inl \<open>a \<in> actions S' s\<close>)
    
          have s_mec: \<open>s \<in> states m_mec\<close>
            using S'_max_red states_Max_red that(2) by blast
    
          have s_states_max: \<open>s \<in> states max_red\<close>
            by (simp add: s_mec)
    
          thus ?thesis
            by (metis DiffE actions_Max_red avoids_S' d_act_S' s_mec state_cases targets_S'
                that(1,2))
        qed
    
        have R': \<open>states S' \<subseteq> states m_mec\<close>
          using mec_le[OF mec] 
          apply(rewrite states_R')
          by (auto simp: le_mdpc_iff states_max_red)
    
        have \<open>actions S' s \<subseteq> actions m_mec s\<close> if \<open>s \<in> states S'\<close> for s
          using that
          using
            \<open>\<And>s a. a \<in> actions S' s \<Longrightarrow> s \<in> states S' \<Longrightarrow> a \<in> actions (to_mdpc m_mec) s\<close>
          by blast
    
        hence \<open>S' \<le> m_mec\<close>
          by (intro le_mdpcI \<open>states S' \<subseteq> states m_mec\<close>) auto
    
        then obtain s' where \<open>s' \<in> states \<M>\<close> \<open>the_mec \<M> s' \<in> states S'\<close>
          by (metis s R' image_iff states_M_mec subset_iff)
    
        obtain R_mec where R_mec: \<open>S' \<le> R_mec\<close> \<open>mec m_mec R_mec\<close>
          by (metis \<open>S' \<le> m_mec\<close> \<open>ec S'\<close> \<open>states S' \<noteq> {}\<close> eq_bot_iff_states mec_exists)
    
        moreover have \<open>S' \<sqinter> (close (restrict_states {the_mec \<M> s'} m_mec)) \<noteq> \<bottom>\<close>
          using R' \<open>the_mec \<M> s' \<in> states S'\<close>
          by (auto simp: eq_bot_iff_states)
    
        ultimately have \<open>R_mec \<sqinter>  (close (restrict_states {the_mec \<M> s'} m_mec)) \<noteq> \<bottom>\<close>
          by (simp add: Int_absorb1 \<open>the_mec \<M> s' \<in> states S'\<close> eq_bot_iff_states le_mdpc_iff subset_iff)
    
        hence \<open>S' \<le> (close (restrict_states {the_mec \<M> s'} m_mec))\<close>
          using mec_unique[OF mec_mec_simple[of s], of R_mec] R_mec
          by (metis \<open>states S' \<subseteq> states m_mec\<close> \<open>the_mec \<M> s' \<in> states S'\<close> mec_mec_simple mec_unique subset_eq)
    
        moreover have Inl_s': \<open>the_mec \<M> s' \<in> states max_red\<close>
          using \<open>s' \<in> states \<M>\<close> \<open>the_mec \<M> s' \<in> states S'\<close> S'_max_red by blast
    
        moreover have \<open>return_pmf (the_mec \<M> s') \<notin> actions S' (the_mec \<M> s')\<close>
          using mec_le[OF mec ] Inl_s' actions_Max_red d_act_S' by fastforce
    
        moreover have \<open>states S' = {the_mec \<M> s'}\<close>
          using \<open>the_mec \<M> s' \<in> states S'\<close>  \<open>S' \<le> (close (restrict_states {the_mec \<M> s'} m_mec))\<close>
          by (auto simp: le_mdpc_iff)
    
        ultimately have \<open>actions S' (the_mec \<M> s') = {}\<close>
          using  \<open>the_mec \<M> s' \<in> states S'\<close> mec_closed[OF mec_refl[OF \<open>ec S'\<close>]] set_pmf_subset_singleton[of _ \<open>(the_mec \<M> s')\<close>]
          by (fastforce simp: subset_iff)
    
        hence \<open>S' = trivial (the_mec \<M> s')\<close>
          by (meson \<open>ec S'\<close> \<open>the_mec \<M> s' \<in> states S'\<close> ec_def sc_eq_trivial)
    
        hence \<open>actions S' (the_mec \<M> s') = {}\<close>
          using actions_trivial
          by (auto simp: actions_map_mdpc)
        thus ?thesis
          by (metis \<open>the_mec \<M> s' \<in> states S'\<close> ec_def mec_ec sc_eq_trivial that(1))
      qed
      note * = this
    
      have no_sc_lr_min_ta: \<open>m \<le> (to_mdpc max_red) \<Longrightarrow> x \<in> states m \<Longrightarrow> x \<in> computes max_red \<Longrightarrow> y \<in> states m \<Longrightarrow> y \<in> targets max_red \<Longrightarrow> sc m \<Longrightarrow> False\<close> for m y x
        using targets_en_min_star'[of y \<open>x\<close>] en_mono[of m max_red, THEN rtrancl_mono]
        by (auto dest: scD[of m \<open>y\<close>])
    
      have no_sc_lr_min_av: \<open>m \<le> (to_mdpc max_red) \<Longrightarrow> x \<in> states m \<Longrightarrow> x \<in> computes max_red \<Longrightarrow> y \<in> states m \<Longrightarrow> y \<in> avoids max_red \<Longrightarrow> sc m \<Longrightarrow> False\<close> for m y x
        using avoids_en_min_star'[of y \<open>x\<close>] en_mono[of m max_red, THEN rtrancl_mono]
        by (auto dest: scD[of m \<open>y\<close>])
        
      obtain m where \<open>mec max_red m\<close> \<open>s \<in> states m\<close>
        using assms by blast
    
      hence \<open>x \<in> states m \<Longrightarrow> x \<in> targets max_red \<Longrightarrow> \<not>sc m\<close> and \<open>x \<in> states m \<Longrightarrow> x \<in> avoids max_red \<Longrightarrow> \<not>sc m\<close> for x
        using no_sc_lr_min_ta  no_sc_lr_min_av
        by (meson assms mec_le)+
    
      hence \<open>states m \<inter> ?sink = {}\<close>
        using \<open>mec max_red m\<close> ec_def mec_ec
        by blast
    
      thus ?thesis
        using * \<open>mec max_red m\<close> \<open>s \<in> states m\<close>
        by (fastforce simp: subset_iff trivials_def)
    qed
    
    lemma MDPC_Reach_Avoid_max_red: "MDPC_Reach_Avoid max_red"
      apply(unfold_locales)
      subgoal 
        using False_in_max by blast
      subgoal 
        by (simp add: max_red.S2)
      subgoal 
        by (simp add: AT_max_red_disj)
      subgoal 
        using actions_max_red_ncomputes sub_states'(2) targets_Max_red by blast
      subgoal
        by (metis False_in_max actions_Max_red computes_nAvd states_Max_red)
      done
    
    interpretation max_red: MDPC_Reach_Avoid max_red
      using MDPC_Reach_Avoid_max_red .
    
    lemma targets_max_bottoms[intro]: \<open>x \<in> targets max_red \<Longrightarrow> x \<in> bottoms max_red\<close>
      unfolding in_bottoms_the_mec
      using max_red.Tgt_loop[of x] 
      by (auto simp: targets_Max_red_mem intro!: mec_loop)
    
    lemma avoids_max_bottoms[intro]: \<open>x \<in> avoids max_red \<Longrightarrow> x \<in> bottoms max_red\<close>
      unfolding in_bottoms_the_mec
      using max_red.Avd_loop[of x] Avd_the_mec_loop
      by (auto simp: avoids_Max_red_mem avoids_M_mec Avd_loop bmec_loop intro!: mec_loop bmec_states_mec)
    
    
    interpretation Max_red: Reduced_MDP_Target max_red
      by standard (auto simp: states_max_red intro!: Inl_red_trivials)                   
    
  end
end