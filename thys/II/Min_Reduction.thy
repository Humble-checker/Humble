theory Min_Reduction
  imports II_Def
begin    

  section \<open>Min-Reduction\<close>
  text \<open>We transform a general MDP (with a single target state) into one with equivalent
  minimum reachability probabilities, where every state is either a bottom or a trivial MEC.\<close>
  
  lemmas states_map_mdpc[simp]
  
  text \<open>The transformation keeps trivial MECs, everything else is collapsed to a (non-target) bottom MEC.\<close>
  definition "Min_red = (\<lambda> \<M>. let A' = avoids \<M> \<union> (states \<M> - trivials \<M> - targets \<M>) in
      (Abs_mdptc (map_actions (\<lambda>u a. if u \<in> A' then {return_pmf u} else a) \<M>, A', targets \<M>)))"

  text \<open>We assume the following arbitrary MDP with a single target state as input.
  Such an MDP can be easily obtained from an MDP with multiple target states by collapsing all target states.\<close>
  context MDPC_Reach_Avoid_defs
  begin
  
    subsection \<open>Min-Reduced MDP\<close>
    text \<open>The reduction function: trivial MECs remain, everything else becomes either an avoid or target state:\<close>
    abbreviation "min_red \<equiv> Min_red \<M>"
    
    abbreviation "avoids_min_red \<equiv> avoids \<M> \<union> (states \<M> - trivials \<M> - targets \<M>)"
    lemma avoids_min_red_def[simp]: "avoids min_red = avoids_min_red"
      unfolding Min_red_def
      apply transfer
      by auto

    (*WARNING: Do not use this unless strictly necessary, it will break the coercions*)
    lemma to_mdpc_min_red_def: "to_mdpc min_red = map_actions (\<lambda>u a. if u \<in> avoids min_red then {return_pmf u} else a) \<M>"
      unfolding Min_red_def avoids_min_red_def
      apply transfer
      apply auto
      done
    
    lemma targets_min_red_def[simp]: "targets min_red = targets \<M>"
      unfolding Min_red_def
      apply transfer
      by auto

    abbreviation "computes_min_red \<equiv> computes \<M> - (states \<M> - trivials \<M>)"
    lemma computes_min_red_def[simp]: "computes min_red = computes_min_red"
      unfolding computes_def
      by (auto simp: to_mdpc_min_red_def)

    lemma states_min_red[simp]: "states min_red = states \<M>"
      by(auto simp: to_mdpc_min_red_def)

    lemma actions_min_red[simp]: "u \<in> states \<M> \<Longrightarrow> actions min_red u = (if u \<in> avoids min_red then {return_pmf u} else actions \<M> u)"
      by(auto simp: to_mdpc_min_red_def)

    definition "actions'_min_red u = (if u \<in> avoids_min_red then {return_pmf u} else actions' \<M> u)"
    lemma actions'_min_red[simp]: "actions' min_red u = actions'_min_red u"
      unfolding actions'_min_red_def
      apply(cases "u \<in> states \<M>")
      subgoal 
        by(auto simp: to_mdpc_min_red_def)
      subgoal
        by (auto simp: to_mdpc_min_red_def actions'_def)
      done
    lemma actions'_min_red_mem[simp]: "a \<in> actions'_min_red u \<longleftrightarrow> a \<in> (if u \<in> avoids_min_red then {return_pmf u} else actions' \<M> u)"
      unfolding actions'_min_red_def by(rule refl)

    lemma avoids_sub_min: "avoids \<M> \<subseteq> avoids min_red"
      by (auto)
    lemma computes_min_sub: "computes min_red \<subseteq> computes \<M>"  
      using avoids_sub_min 
      by (simp)
  end
  
  context MDPC_Reach_Avoid
  begin
  
  lemma avoids_min_Tgt_disj: "avoids min_red \<inter> targets \<M> = {}"
    using AT_disj by auto

  lemma actions_min_red[simp]: "actions min_red u = (if u \<in> avoids min_red then {return_pmf u} else actions \<M> u)"
    by(auto simp: to_mdpc_min_red_def)
  
  text \<open>The reduced MDP is a well-formed MDP:\<close>
  sublocale Min: Finite_MDP "to_mdpc min_red"
    apply unfold_locales
    subgoal
      by(auto simp: set_pmf_closed' closed_mdpc_map_actions to_mdpc_min_red_def)
    subgoal
      by(auto simp: eq_bot_iff_states S_not_empty)
    subgoal
      using actions_finite' by auto
    subgoal
      by (simp add: S_finite)
    subgoal
      by (auto simp: finite_actions_M)
    done
 

  lemma MDPC_Reach_Avoid_min_red: "MDPC_Reach_Avoid min_red" (*We cannot instantiate this here*)
    apply(unfold_locales)
    subgoal 
      by auto
    subgoal 
      by (simp add: R.S2)
    subgoal 
      using avoids_min_Tgt_disj by auto
    subgoal
      by (simp add: Tgt_loop)
    subgoal
      by simp
    done

  interpretation Min: MDPC_Reach_Avoid min_red (*We use interpretation because sublocale will cause an infinite dependency loop*)
    using MDPC_Reach_Avoid_min_red .
    
  text \<open>Some basic facts about the state space:\<close>


  
  lemma avoids_min_red_states: "avoids min_red \<subseteq> states \<M>"
    using Avd_states by auto
  
  lemma states_M_alt: "states \<M> = avoids min_red \<union> targets \<M> \<union> trivials \<M>"
    using Avd_states Tgt_states by auto

  lemma Inl_in_red[intro]: \<open>a \<in> trivials \<M> \<Longrightarrow> a \<in> states min_red\<close>
    by (force simp: image_iff)

  
  text \<open>Basic properties of the actions:\<close>
  
  lemma actions_avoids_min_red[simp]: \<open>u \<in> avoids min_red \<Longrightarrow> actions min_red u = { return_pmf u }\<close>
    by auto
  
  lemma actions_Avd[simp]: \<open>u \<in> avoids \<M> \<Longrightarrow> actions min_red u = { return_pmf u }\<close>
    by auto
  
  lemma actions_Tgt[simp]: \<open>u \<in> targets \<M> \<Longrightarrow> actions min_red u = { return_pmf u }\<close>
    using Tgt_states by(auto simp: Tgt_loop subset_eq)
  
  lemma action_cfg_avoids_min_red: \<open>u \<in> avoids_min_red \<Longrightarrow> cfg \<in> Min.cfg_on u \<Longrightarrow> action cfg = return_pmf u\<close>
    using Min.actions'_states[simplified]
    by (metis Min.cfg_onD_action actions'_min_red actions'_min_red_def singletonD)
  
  lemma actions_min_red_eq: \<open>u \<notin> avoids_min_red \<Longrightarrow> u \<notin> targets \<M> \<Longrightarrow> actions min_red u = actions \<M> u\<close>
    by auto
  
  lemma actions'_min_red_Inl: \<open>u \<in> states \<M> \<Longrightarrow> u \<notin> avoids_min_red \<Longrightarrow> u \<notin> targets \<M>
    \<Longrightarrow> actions' min_red u = actions' \<M> u\<close>
    by (auto simp: actions'_min_red_def)

  lemma Tgt_the_mec_loop[simp]: "u \<in> targets \<M> \<Longrightarrow> the_mec min_red u = loop u"
    by auto
  
  lemma Avd_the_mec_loop[simp]: "u \<in> avoids \<M> \<Longrightarrow> the_mec min_red u = loop u"
    by(auto intro!: mec_loop)
  
  lemma avoids_min_red_the_mec_loop[simp]: "u \<in> avoids min_red \<Longrightarrow> the_mec min_red u = loop u"
    by(auto intro!: mec_loop) 
  
  lemma Comp_in_bottoms[intro]: \<open>u \<in> targets \<M> \<union> avoids min_red \<Longrightarrow> u \<in> bottoms min_red\<close>
    by(auto simp: Min.None_bot bmec_loop in_bottoms_the_mec Tgt_loop intro!: bmec_loop) 


  
  
  subsection \<open>The Reduced Reachability Problem\<close>
  
  text \<open>Reachability Target: \<^term>\<open>Inr True\<close>\<close>
  sublocale R_red: Reachability_Problem 
    \<open>actions'_min_red\<close> 
    \<open>states \<M>\<close> 
    \<open>computes_min_red\<close> 
    \<open>targets \<M>\<close>
    apply unfold_locales 
    by(auto simp: S_not_empty S_finite finite_actions_M K_wf set_pmf_closed' actions'_min_red_def) 

  lemma avoids_min_red_nTgt[intro]: "u \<in> avoids min_red \<Longrightarrow> u \<notin> targets \<M>"
    using Min.Avd_Tgt_disj targets_min_red_def by blast
  
  lemma n_fin_0_nTgt[simp]: \<open>u \<in> states \<M> \<Longrightarrow> u \<notin> targets \<M> \<Longrightarrow> R_red.n_fin 0 u = 0\<close>
    by (subst R_red.n_fin_0) (auto simp:) 
  
  lemma n_fin_0_avoids_min_red[simp]: \<open>u \<in> avoids min_red \<Longrightarrow> R_red.n_fin 0 u = 0\<close>
    using avoids_min_red_states  n_fin_0_nTgt Min.Avd_Tgt_disj targets_min_red_def by blast
  
  lemma Min_valid_cfgI': "s \<in> states \<M> \<Longrightarrow> cfg \<in> Min.cfg_on s \<Longrightarrow> cfg \<in> Min.valid_cfg" 
    using Min.valid_cfgI by auto

  lemma avoids_targets_impn: "u \<in> avoids \<M> \<Longrightarrow> u \<notin> targets \<M>" and "u \<in> targets \<M> \<Longrightarrow> u \<notin> avoids \<M>"
    using AT_disj by auto
  
  lemma v_fin_False[simp]: 
    assumes "u \<in> avoids_min_red" "cfg \<in> R_red.cfg_on u" 
    shows "R_red.v_fin i cfg = 0"
  using assms
  apply (induction i arbitrary: cfg) 
  subgoal
    using Avd_Tgt_disj 
    by(fastforce intro!: R_red.v_fin_0)
  subgoal
    by (force simp: R_red.valid_cfgI avoids_targets_impn intro!: R_red.v_fin_nS12) 
  done

  lemma n_fin_False[simp]: \<open>u \<in> avoids min_red \<Longrightarrow> R_red.n_fin i u = 0\<close>
    using Min.Avd_alt R_red.n_fin_nS12 computes_min_red_def states_min_red targets_min_red_def
    by blast
  
  text \<open>The finite-horizon reachability probabilitites coincide\<close>
  lemma n_fin_eq_red:
    assumes \<open>s \<in> states \<M>\<close>
    shows \<open>R.n_fin i s = R_red.n_fin i s\<close>
    using assms
  proof (induction i arbitrary: s)
    case 0
    then show ?case
      apply(cases "s \<in> targets \<M>") 
      using R.n_fin_S2 R_red.n_fin_S2 apply presburger
      using n_fin_0_Some n_fin_0_nTgt by presburger
  next
    case (Suc i)
  
    have AUX: "s \<in> avoids min_red \<Longrightarrow> R.n_fin i s = 0" for i s
      using R.n_fin_nS12 Avd_alt n_fin_not_triv 
      by (metis Diff_iff Un_iff avoids_min_red_def)

    from Suc consider \<open>s \<in> targets \<M>\<close> | \<open>s \<in> avoids min_red\<close> | (triv) \<open>s \<in> trivials \<M> - targets \<M> - avoids min_red\<close>
      using states_M_alt by blast
    then show ?case
    proof cases
      case triv
  
      moreover have \<open>R.n_fin (Suc i) s = R_red.n_fin (Suc i) s\<close>
      proof -
        have \<open>R.n_fin (Suc i) s = 
            (\<Sqinter>a\<in>actions' \<M> s. integral\<^sup>N (measure_pmf a) (R.n_fin i))\<close>
          using triv by (subst R.n_fin_Suc_S1) (auto intro!: computesI)
        also have \<open>\<dots> = (\<Sqinter>a::('v pmf)\<in>actions' \<M> s. integral\<^sup>N a (R_red.n_fin i))\<close>
          using Suc set_pmf_closed'
          by (auto intro!: INF_cong nn_integral_cong_AE)
        also have \<open>\<dots> = (\<Sqinter>a\<in>actions' min_red s. integral\<^sup>N (measure_pmf a) (R_red.n_fin i))\<close>
          using triv
          by (auto simp: actions'_min_red_def image_image actions'_min_red_Inl)
        finally show ?thesis
          using triv
          by (subst R_red.n_fin_Suc_S1) (auto intro!: computesI)
      qed
      ultimately show ?thesis
        using triv
        by auto
    qed (auto simp: AUX)
  qed
  
  text \<open>Equivalence for the infinite-horizon case follows immediately:\<close>
  lemma n_eq_red: \<open>s \<in> states \<M> \<Longrightarrow> R.n s = R_red.n s\<close>
    using n_fin_eq_red[of s]
    unfolding R.n_eq_Sup_n_fin R_red.n_eq_Sup_n_fin
    by (auto intro!: SUP_cong simp: image_image)
  
  
  lemma min_red_eq_R_red_n: "s \<in> states \<M> \<Longrightarrow> Min.R.n s = R_red.n s"
    unfolding states_min_red computes_min_red_def targets_min_red_def
    using MDPC_Reach_Avoid_defs.actions'_min_red
    by (metis (lifting) ext MDPC_Reach_Avoid_defs.actions'_min_red)

  lemma n_real_eq_min: "s \<in> states \<M> \<Longrightarrow> n_real s = Min.n_real s"
    unfolding n_real_def Min.n_real_def 
    using min_red_eq_R_red_n n_eq_red
    by (simp add: states_min_red)
  
  subsection \<open>MECs of the Min-Reduced MDP\<close>
  text \<open>We show that the Min-Reduced MDP is in fact a reduced MDP.\<close>
  
  lemma trivials_not_target: "u \<in> trivials (to_mdpc \<M>) \<Longrightarrow> u \<notin> targets \<M>"
    using None_not_triv by blast

  lemma Inr_en_min: \<open>x \<in> states \<M> \<Longrightarrow> x \<notin> computes_min_red \<Longrightarrow> (x, y) \<in> en min_red \<Longrightarrow> y = x\<close>
    by (auto split: if_splits simp: Tgt_loop en_def dest: computesI[OF _ _ trivials_not_target, of x]) 

  
  lemma Inr_en_min_star: \<open>(x, y) \<in> (en min_red)\<^sup>* \<Longrightarrow> x \<in> states \<M> \<Longrightarrow> x \<notin> computes_min_red \<Longrightarrow> y = x\<close>
    by (induction rule: rtrancl_induct) (auto intro: Inr_en_min)
  
  lemma no_sc_lr_min: \<open>m \<le> to_mdpc min_red \<Longrightarrow> x \<in> states m \<Longrightarrow> x \<in> computes_min_red \<Longrightarrow> y \<in> states m \<Longrightarrow> y \<notin> computes_min_red \<Longrightarrow> sc m \<Longrightarrow> False\<close>
    using Inr_en_min_star[of y x] en_mono[of m min_red, THEN rtrancl_mono] 
    by (auto simp: le_mdpc_iff dest!: scD[of m y]) 
  
  
  (* Lemma 1 *)
  text \<open>All trivial MECs remain trivial MECs in the reduced MDP:\<close>
  lemma Inl_red_trivials:
    assumes \<open>s \<in> computes_min_red\<close>
    shows \<open>s \<in> trivials min_red\<close>
  proof -
    let ?sink = \<open>avoids min_red \<union> targets min_red\<close>
  
    from assms have "s \<in> states \<M>" and "s \<notin> avoids min_red" and "s \<notin> targets \<M>"
      unfolding computes_min_red_def by auto
  
    text \<open>Given any MEC that does not contain a sink state, we show it is trivial:\<close>
    have \<open>\<exists>s. S' = trivial s\<close> if mec: \<open>mec min_red S'\<close> and no_trap: \<open>states S' \<inter> ?sink = {}\<close> for S'
    proof -
  
      have \<open>S' \<le> min_red\<close>
        using \<open>mec min_red S'\<close> mec_le 
        by blast
      
      hence States_sub: \<open>states S' \<subseteq> states \<M>\<close>
        by (simp add: le_mdpc_iff states_mono)
  
      have S'_inl: \<open>x \<in> computes_min_red\<close> \<open>x \<in> trivials \<M>\<close> if \<open>x \<in> states S'\<close> for x
        using \<open>states S' \<inter> ?sink = {}\<close> States_sub that
        unfolding states_min_red computes_def
        by auto

      have closed_S': \<open>closed_mdpc S'\<close>
        using \<open>mec min_red S'\<close> ec_def mec_def
        by blast
  
      have inl_S'[dest]: \<open>x \<in> states S' \<Longrightarrow> x \<in> trivials \<M>\<close> for x
        using S'_inl
        by (simp add: \<open>\<And>x. x \<in> states S' \<Longrightarrow> x \<in> trivials \<M>\<close>)
  
      have inr_S'[simp]: \<open>x \<in> ?sink \<Longrightarrow> x \<in> states S' \<longleftrightarrow> False\<close> for x
        using S'_inl that(2) by auto
  
      have actions_Inr[simp]: \<open>s \<in> ?sink \<Longrightarrow> actions S' s = {}\<close>  for s
        by (meson in_states inr_S')

      have states_R': \<open>states S' = {s. s \<in> trivials \<M> \<and> s \<in> states S'}\<close>
        by (auto simp: image_iff split: sum.splits)
  
      have \<open>ec S'\<close>
        using mec_ec that(1) ec_map by blast
      
      have \<open>states S' \<noteq> {}\<close> 
        by (metis bmec_def Min.bmec_has_state equals0D mec) 
    
      then obtain s where s[simp]: \<open>s \<in> states S'\<close>
        using states_R' by auto
    
      hence \<open>s \<in> trivials \<M>\<close>
        using states_R' by blast
    
      hence \<open>mec \<M> (trivial s)\<close>
        unfolding trivials_def
        using \<open>s \<in> states S'\<close>
        by blast
    
      have d_act_S': \<open>a \<in> actions S' s \<Longrightarrow> a \<in> actions min_red s \<and> set_pmf a \<subseteq> computes_min_red\<close> for a s
        using \<open>S' \<le> min_red\<close> in_states[of S' s]
        by (auto simp: le_mdpc_iff split: if_splits
          dest: mec_closed[OF that(1), THEN S'_inl(1)])    
      have R_to_M: \<open>a \<in> actions \<M> s\<close> if \<open>a \<in> actions S' s\<close> \<open>s \<in> states S'\<close> for s a
      proof -
    
        have \<open>a \<in> actions min_red s\<close>
          using d_act_S' that(1) by blast
    
        moreover have \<open>s \<in> trivials \<M>\<close>
          using states_R' that(2) by auto
    
        ultimately show \<open>a \<in> actions \<M> s\<close> 
          using inr_S' that(2) 
          by (auto split: if_splits)
      qed
    
      hence \<open>actions S' s \<subseteq> actions \<M> s\<close> if \<open>s \<in> states S'\<close> for s
        using that states_R' by auto
  
    
      with States_sub have \<open>S' \<le> \<M>\<close>
        by (intro le_mdpcI) auto
    
      hence \<open>S' \<le> trivial s\<close>
        using \<open>ec S'\<close>
        by (intro mec_least[OF \<open>mec \<M> (trivial s)\<close>]) (auto simp: trivial_le_iff)
        
      hence \<open>S' = trivial s\<close>
        by (simp add: antisym trivial_le)
      thus \<open>\<exists>s. S' = trivial s\<close>
        by auto
    qed
    note * = this
  
    obtain m where \<open>mec min_red m\<close> \<open>s \<in> states m\<close>
      using \<open>s \<in> states \<M>\<close> states_min_red by blast
  
    hence \<open>x \<in> ?sink \<Longrightarrow> x \<in> states m \<Longrightarrow> \<not>sc m\<close> for x
      using no_sc_lr_min[of m s x] assms
      unfolding mec_def computes_min_red_def
      by auto
  
    hence \<open>states m \<inter> ?sink = {}\<close>
      using \<open>mec min_red m\<close> ec_def mec_ec
      by auto
     
    thus ?thesis
      using * \<open>mec min_red m\<close> \<open>s \<in> states m\<close>
      by (fastforce simp: subset_iff trivials_def)
  qed

  lemma trivials_in_min_red_trivials: assumes TRIV:"s \<in> trivials \<M>" and SAVD: "s \<notin> avoids \<M>" shows "s \<in> trivials min_red"
  proof -
    from TRIV SAVD have "s \<in> computes \<M>"
      by(auto simp: None_not_triv intro!: computesI)

    thus ?thesis
      by(auto intro!: Inl_red_trivials simp: TRIV)
  qed

  
  lemma min_red_triv_bot: \<open>states min_red = trivials min_red \<union> bottoms min_red\<close>
    unfolding states_min_red
    by (auto simp: in_bottoms_the_mec intro!: Inl_red_trivials computesI)

  
  subsection \<open>Instantiation as Reduced_MDP\<close>

  interpretation Red: Reduced_MDP_Target min_red
    using min_red_triv_bot Inl_red_trivials
    by unfold_locales auto

  end

end