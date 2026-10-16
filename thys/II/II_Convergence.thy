theory II_Convergence
  imports II_Def
begin

context Reduced_MDP_Target
begin

subsection \<open>Convergence of Interval Iteration\<close>

lemma lb_n_tendsto_n: 
  \<open>R.n = (\<Squnion>i. lb_n i)\<close>
  \<open>\<And>s. (\<lambda>i. lb_n i s) \<longlonglongrightarrow> R.n s\<close>
proof -
  have \<open>R.n = (\<Squnion>i. (R.F_inf ^^ i) \<bottom>)\<close>
    by (simp add: R.n_eq_lfp_F_inf R.sup_continuous_F_inf sup_continuous_lfp)
  also have \<open>\<dots> = (\<Squnion>i. lb_n i)\<close>
    apply (rule antisym)
    subgoal by (auto intro!: SUP_mono' simp: funpow_mono R.mono_F_inf lb_n_def)
    subgoal by (simp add: lb_n_le_n SUP_least calculation[symmetric])
    done
  finally show \<open>R.n = (\<Squnion>i. lb_n i)\<close> .
  thus \<open>(\<lambda>i. lb_n i s) \<longlonglongrightarrow> R.n s\<close> for s
    by (metis SUP_apply lb_tendsto_SUP)
qed

lemma F_inf1_fix_iff: \<open>R.F_inf1 x = x \<longleftrightarrow> R.F_inf x = x \<and> (\<forall>s \<in> states \<M>. x s \<le> 1)\<close>
  using R.F_inf1_le1
  unfolding R.F_inf1_def fun_eq_iff 
  by auto (metis min_le_iff_disj order.refl)+

lemma F_inf1_fp_unique: \<open>R.F_inf1 x = x \<longleftrightarrow> x = R.n\<close>
  unfolding F_inf1_fix_iff
  using F_inf_fp_unique[of x] R.F_inf_n R.n_le_1
  by auto (metis  ennreal_top_neq_one  neq_top_trans)

lemma 
  gfp_F_inf1: \<open>gfp R.F_inf1 = R.n\<close> and
  lfp_F_inf1: \<open>lfp R.F_inf1 = R.n\<close>
  by (metis R.F_inf1_mono F_inf1_fp_unique def_gfp_unfold def_lfp_unfold)+

lemma ub_n_F_inf1: \<open>ub_n i = (R.F_inf1 ^^ i) R.ub_0\<close>
  using ub_n_le_1 R.F_inf1_le1 
  apply (induction i)
  by auto (metis le_funD restrict_apply')

lemma ub_n_tendsto_n:
  \<open>R.n = (\<Sqinter>i. ub_n i)\<close>
  \<open>\<And>s. (\<lambda>i. ub_n i s) \<longlonglongrightarrow> R.n s\<close>
proof -
  have \<open>(\<Sqinter>i. (R.F_inf1 ^^ i) \<top>) = R.n\<close>
    by (metis R.F_inf1_inf_continuous gfp_F_inf1 inf_continuous_gfp)
  moreover have \<open>(\<Sqinter>i. (R.F_inf1 ^^ i) \<top>) = (\<Sqinter>i. ub_n i)\<close>
    apply (rule antisym)
    subgoal by (simp add: INF_greatest calculation ub_n_ge_n)
    subgoal by (auto simp: R.F_inf1_mono funpow_mono ub_n_F_inf1 intro!: INF_mono')
    done
  ultimately show \<open>R.n = (\<Sqinter>i. ub_n i)\<close> by auto
  thus \<open>(\<lambda>i. ub_n i s) \<longlonglongrightarrow> R.n s\<close> for s
    using antimono_lb_n 
    by (metis INF_apply ub_tendsto_INF)
qed

subsection \<open>Bounds are Finite-Horizon Probabilities\<close>

lemma lb_n_eq_n_fin: \<open>lb_n i = R.n_fin i\<close>
  by (simp add: R.n_fin_eq_F_inf R.lb_0_def lb_n_def)

lemma ub_n_eq_p_fin:
  \<open>ub_n i = (\<lambda>s \<in> states \<M>. 1 - S.p_fin i s)\<close>
  proof (induction i)
    case 0
    hence \<open>ub_n 0 = (\<lambda>s \<in> states \<M>. 1 - S.p_fin 0 s)\<close>
      by force
    moreover have \<open>S.v_fin 0 cfg = S.p_fin 0 s\<close> if \<open>cfg \<in> cfg_on s\<close> for cfg s
      using that by (cases s rule: state_fn_cases) auto
    ultimately show ?case 
      by (meson n_memoryless simple_cfg_on)
  next
    case (Suc i)
    then obtain cfg_i where
      cfg_i: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> cfg_i s \<in> cfg_on s\<close> and
      cfg_i_opt: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> S.v_fin i (cfg_i s) = S.p_fin i s\<close>
      using S.p_fin_eq_F_sup(2)[of _ i]
      by metis

    define D' where \<open>D' s = arg_max_on (\<lambda>D. nn_integral (measure_pmf D) (S.p_fin i)) (actions \<M> s)\<close> for s

    have D': \<open>D' s \<in> actions \<M> s\<close> if \<open>s \<in> states \<M>\<close> for s
      by (auto simp: D'_def actions_neq_empty_M arg_max_if_finite(1) finite_actions_M that)

    define cfg' where \<open>cfg' s = Cfg s (D' s) cfg_i\<close> for s

    have cfg': \<open>cfg' s \<in> cfg_on s\<close> if \<open>s \<in> states \<M>\<close> for s
      using that cfg_i D' closed_mdpcD[OF closed_M D']
      by (intro cfg_onI[of _ s]) (auto simp: cfg'_def)

    { fix s assume s_states[intro]: \<open>s \<in> states \<M>\<close> and s_triv: \<open>s \<in> trivials \<M>\<close>

      have cont_cfg[simp]: \<open>(cont (Cfg s (D' s) cfg_i) x) = cfg_i x\<close> if \<open>x \<in> set_pmf (D' s)\<close> for x
        using D' s_states closed_M that cfg_i[of x]
        by (cases x rule: state_fn_cases) (fastforce dest: cfg_onD_state closed_mdpcD)+

      have \<open>S.v_fin (Suc i) (cfg' s) = S.p_fin (Suc i) s\<close>
      proof -      
        have \<open>S.v_fin (Suc i) (cfg' s) = \<integral>\<^sup>+ x. S.v_fin i (cont (Cfg s (D' s) cfg_i) x) \<partial>(D' s)\<close>
          using cfg' s_triv
          unfolding cfg'_def 
          by (subst S.v_fin_Suc) (auto simp: trivials_computes K_cfg_def  intro!: INF_greatest)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. S.v_fin i (cfg_i x) \<partial>(D' s)\<close>
          by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. S.p_fin i x \<partial>(D' s)\<close>
          using D' closed_mdpcD[OF closed_M]
          by (fastforce intro!: nn_integral_cong_AE simp: cfg_i_opt)
        also have \<open>\<dots> = (MAX a \<in> actions \<M> s. \<integral>\<^sup>+ x. S.p_fin i x \<partial>measure_pmf a)\<close>
          unfolding D'_def
          using D' finite_actions_M
          by (intro arg_max_on_Max) auto
        also have \<open>\<dots> = (\<Squnion>a\<in>actions' \<M> s. \<integral>\<^sup>+ x. S.p_fin i x \<partial>measure_pmf a)\<close>
          using D' K_finite s_states by (subst cSup_eq_Max) auto
        also have \<open>\<dots> = S.p_fin (Suc i) s\<close>
          using s_triv by (auto simp: trivials_computes S.p_fin_Suc_S1)
        finally show ?thesis  .
      qed
    }
    hence v_fin_cfg': \<open>S.v_fin (Suc i) (cfg' s) = S.p_fin (Suc i) s\<close> if \<open>s \<in> states \<M>\<close> for s
      using trivials_computes cfg' that by (cases s rule: state_fn_cases) auto
    moreover have \<open>ub_n (Suc i) s = 1 - S.p_fin (Suc i) s\<close> if \<open>s \<in> trivials \<M>\<close> for s
    proof -
      have *: \<open>integral\<^sup>N (measure_pmf x) (S.p_fin i) \<noteq> \<top>\<close> if \<open>x \<in> actions \<M> s\<close> for x
        using that \<open>s \<in> trivials \<M>\<close> set_pmf_closed set_pmf_finite
        by (intro finite_nn_integral_lt_topI neq_top_trans[OF ennreal_one_neq_top S.p_fin_le_1]) auto
      have \<open>ub_n (Suc i) s = (\<Sqinter>D\<in>actions' \<M> s. integral\<^sup>N (measure_pmf D) (ub_n i))\<close>
        unfolding ub_n_Suc R.F_inf_def
        using Suc.IH that
        by (auto simp: S.p_fin_Suc R.F_inf_def trivials_computes)
      also have \<open>\<dots> = (\<Sqinter>D\<in>actions' \<M> s. integral\<^sup>N (measure_pmf D) (\<lambda>s. 1 - S.p_fin i s))\<close>
        using set_pmf_closed that
        by (fastforce intro!: INF_cong nn_integral_cong_AE simp: Suc.IH)
      also have \<open>\<dots> = 1 - (\<Squnion>x\<in>actions \<M> s. integral\<^sup>N (measure_pmf x) (S.p_fin i))\<close> 
        using * that actions_neq_empty_M
        by (subst ennreal_SUP_const_minus[symmetric])
          (auto simp: nn_integral_diff S.p_fin_le_1 closed_M closed_mdpcD)
      also have \<open>\<dots> = 1 - S.p_fin (Suc i) s\<close>
        unfolding S.p_fin_Suc
        using that
        by auto
      finally show ?thesis .
    qed
    moreover then have \<open>ub_n (Suc i) = (\<lambda>s\<in>states \<M>. 1 - S.p_fin (Suc i) s)\<close>
      by (auto intro!: state_fn_eqI)
    thus ?case
      using v_fin_cfg' cfg'
      by auto
  qed

lemma lb_p_eq_p_fin: \<open>lb_p i = R.p_fin i\<close>
  by (simp add: lb_p_def R.lb_0_def R.p_fin_eq_F_sup(1))

lemma ub_p_eq_n_fin: \<open>ub_p i = (\<lambda>s \<in> states \<M>. 1 - S.n_fin i s)\<close>
  proof (induction i)
    case 0
    hence \<open>ub_p 0 = (\<lambda>s \<in> states \<M>. 1 - S.n_fin 0 s)\<close>
      by (auto intro!: state_fn_eqI)
    moreover have \<open>S.v_fin 0 cfg = S.n_fin 0 s\<close> if \<open>cfg \<in> cfg_on s\<close> for cfg s
      using that by (cases s rule: state_fn_cases) auto
    ultimately show ?case 
      by (meson n_memoryless simple_cfg_on)
  next
    case (Suc i)
    then obtain cfg_i where
      cfg_i: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> cfg_i s \<in> cfg_on s\<close> and
      cfg_i_opt: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> S.v_fin i (cfg_i s) = S.n_fin i s\<close>
      using S.n_fin_eq_F_inf(2)[of _ i]
      by metis

    define D' where \<open>D' s = arg_min_on (\<lambda>D. nn_integral (measure_pmf D) (S.n_fin i)) (actions \<M> s)\<close> for s

    have D': \<open>D' s \<in> actions \<M> s\<close> if \<open>s \<in> states \<M>\<close> for s
      by (auto simp: D'_def actions_neq_empty_M arg_min_if_finite(1) finite_actions_M that)

    define cfg' where \<open>cfg' s = Cfg s (D' s) cfg_i\<close> for s

    have cfg': \<open>cfg' s \<in> cfg_on s\<close> if \<open>s \<in> states \<M>\<close> for s
      using that cfg_i D' closed_mdpcD[OF closed_M D']
      by (intro cfg_onI[of _ s]) (auto simp: cfg'_def)

    { fix s assume s_states[intro]: \<open>s \<in> states \<M>\<close> and s_triv: \<open>s \<in> trivials \<M>\<close>

      have cont_cfg[simp]: \<open>(cont (Cfg s (D' s) cfg_i) x) = cfg_i x\<close> if \<open>x \<in> set_pmf (D' s)\<close> for x
        using D' s_states closed_M that cfg_i[of x]
        by (cases x rule: state_fn_cases) (fastforce dest: cfg_onD_state closed_mdpcD)+

      have \<open>S.v_fin (Suc i) (cfg' s) = S.n_fin (Suc i) s\<close>
      proof -      
        have \<open>S.v_fin (Suc i) (cfg' s) = \<integral>\<^sup>+ x. S.v_fin i (cont (Cfg s (D' s) cfg_i) x) \<partial>(D' s)\<close>
          using cfg' s_triv
          unfolding cfg'_def 
          by (subst S.v_fin_Suc) (auto simp: trivials_computes K_cfg_def  intro!: INF_greatest)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. S.v_fin i (cfg_i x) \<partial>(D' s)\<close>
          by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. S.n_fin i x \<partial>(D' s)\<close>
          using D' closed_mdpcD[OF closed_M]
          by (fastforce intro!: nn_integral_cong_AE simp: cfg_i_opt AE_measure_pmf_iff)
        also have \<open>\<dots> = (MIN a \<in> actions \<M> s. \<integral>\<^sup>+ x. S.n_fin i x \<partial>measure_pmf a)\<close>
          unfolding D'_def
          using D' finite_actions_M
          by (intro arg_min_on_Min) auto
        also have \<open>\<dots> = (\<Sqinter>a\<in>actions' \<M> s. \<integral>\<^sup>+ x. S.n_fin i x \<partial>measure_pmf a)\<close>
          using D' K_finite s_states by (subst cInf_eq_Min) auto
        also have \<open>\<dots> = S.n_fin (Suc i) s\<close>
          using s_triv by (auto simp: trivials_computes S.n_fin_Suc_S1)
        finally show ?thesis  .
      qed
    }
    hence v_fin_cfg': \<open>S.v_fin (Suc i) (cfg' s) = S.n_fin (Suc i) s\<close> if \<open>s \<in> states \<M>\<close> for s
      using computes_triv cfg' that by (cases s rule: state_fn_cases) auto
    moreover have \<open>ub_p (Suc i) s = 1 - S.n_fin (Suc i) s\<close> if \<open>s \<in> trivials \<M>\<close> for s
    proof -
      have *: \<open>integral\<^sup>N (measure_pmf x) (S.n_fin i) \<noteq> \<top>\<close> if \<open>x \<in> actions \<M> s\<close> for x
        using that \<open>s \<in> trivials \<M>\<close> set_pmf_closed set_pmf_finite
        by (intro finite_nn_integral_lt_topI neq_top_trans[OF ennreal_one_neq_top S.n_fin_le_1]) auto
      have \<open>ub_p (Suc i) s = (\<Squnion>D\<in>actions' \<M> s. integral\<^sup>N (measure_pmf D) (ub_p i))\<close>
        unfolding ub_p_Suc R.F_sup_def
        using Suc.IH that trivials_computes
        by auto
      also have \<open>\<dots> = (\<Squnion>D\<in>actions' \<M> s. integral\<^sup>N (measure_pmf D) (\<lambda>s. 1 - S.n_fin i s))\<close>
        using set_pmf_closed that
        by (fastforce intro!: SUP_cong nn_integral_cong_AE simp: Suc.IH)
      also have \<open>\<dots> = 1 - (\<Sqinter>x\<in>actions \<M> s. integral\<^sup>N (measure_pmf x) (S.n_fin i))\<close> 
        using that actions_neq_empty_M *
        by (subst ennreal_INF_const_minus[symmetric])
          (auto simp: nn_integral_diff S.n_fin_le_1 closed_M closed_mdpcD)
      also have \<open>\<dots> = 1 - S.n_fin (Suc i) s\<close>
        unfolding S.n_fin_Suc
        using that
        by auto
      finally show ?thesis .
    qed
    moreover then have \<open>ub_p (Suc i) = (\<lambda>s\<in>states \<M>. 1 - S.n_fin (Suc i) s)\<close>
      by (auto intro!: state_fn_eqI)
    thus ?case
      using v_fin_cfg' cfg'
      by auto
  qed

subsection \<open>Convergence Rate of Interval Iteration\<close>

lemma R_S_sum_v_fin: \<open>cfg \<in> valid_cfg \<Longrightarrow> S.v_fin i cfg + R.v_fin i cfg = R_G.R.v_fin i cfg\<close>
proof (induction i arbitrary: cfg)
  case 0
  then show ?case 
    apply (cases \<open>state cfg\<close> rule: state_fn_cases) 
    subgoal by (simp add: trivials_computes_mem) 
    subgoal using Avd_Tgt_disj by auto
    subgoal by (simp add: Avd_bot valid_cfgD)
    subgoal by blast
    done
next
  case (Suc i)
  then show ?case 
    apply (cases \<open>state cfg\<close> rule: state_fn_cases)
    subgoal
      apply (frule iffD1[OF trivials_computes_mem])
      apply (auto simp: nn_integral_add[symmetric] K_cfg_def valid_cfg_cont intro: nn_integral_cong_AE) 
      done
    subgoal
      using valid_cfgD by fastforce
    subgoal
      by (metis R_G.R.v_fin_S2 Avd_bot S.v_fin_S2 v_fin_False valid_cfgD)
    subgoal by blast
    done
qed

lemma S_R_p_n_fin_ge_plim:
  assumes \<open>s \<in> states \<M>\<close>
  shows \<open>S.p_fin (i * R_G.I) s + R.n_fin (i * R_G.I) s \<ge> R_G.plim i\<close>
proof -
  let ?i = \<open>(i * R_G.I)\<close>
  obtain p_cfg where p_cfg: \<open>p_cfg \<in> cfg_on s\<close> and
    v_eq_p: \<open>S.v_fin ?i p_cfg = S.p_fin ?i s\<close>
    using S.p_fin_eq_F_sup assms by blast
  obtain n_cfg where n_cfg: \<open>n_cfg \<in> cfg_on s\<close> and
    v_eq_n: \<open>R.v_fin ?i n_cfg = R.n_fin ?i s\<close>
    using assms R.n_fin_eq_F_inf by blast

  have \<open>1 - (1 - R_G.min_prob ^ R_G.I) ^ i \<le> R_G.R.v_fin ?i n_cfg\<close>
    using R_G.v_fin_Ii_ge assms n_cfg by blast
  also have \<open>\<dots> = S.v_fin ?i n_cfg + R.v_fin ?i n_cfg\<close>
    using n_cfg assms R_S_sum_v_fin
    by auto
  also have \<open>\<dots> \<le> S.v_fin ?i p_cfg + R.v_fin ?i n_cfg\<close>
    unfolding v_eq_p S.p_fin_v_fin
    using n_cfg
    by (auto intro!: Sup_upper2)
  also have\<open>\<dots> =  S.p_fin ?i s + R.n_fin ?i s\<close>
    using v_eq_p v_eq_n by auto
  finally show ?thesis .
qed

lemma S_R_n_p_fin_ge_plim:
  assumes \<open>s \<in> states \<M>\<close>
  shows \<open>S.n_fin (i * R_G.I) s + R.p_fin (i * R_G.I) s \<ge> R_G.plim i\<close>
proof -
  let ?i = \<open>(i * R_G.I)\<close>
  obtain p_cfg where p_cfg: \<open>p_cfg \<in> cfg_on s\<close> and
    v_eq_n: \<open>S.v_fin ?i p_cfg = S.n_fin ?i s\<close>
    using assms S.n_fin_eq_F_inf by blast
  obtain n_cfg where n_cfg: \<open>n_cfg \<in> cfg_on s\<close> and
    v_eq_p: \<open>R.v_fin ?i n_cfg = R.p_fin ?i s\<close>
    using assms R.p_fin_eq_F_sup by blast

  have \<open>1 - (1 - R_G.min_prob ^ R_G.I) ^ i \<le> R_G.R.v_fin ?i p_cfg\<close>
    using R_G.v_fin_Ii_ge assms p_cfg by blast
  also have \<open>\<dots> = S.v_fin ?i p_cfg + R.v_fin ?i p_cfg\<close>
    using p_cfg assms R_S_sum_v_fin by auto
  also have \<open>\<dots> \<le> S.v_fin ?i p_cfg + R.v_fin ?i n_cfg\<close>
    unfolding v_eq_p R.p_fin_v_fin
    using p_cfg
    by (auto intro!: Sup_upper2)
  also have\<open>\<dots> =  S.n_fin ?i s + R.p_fin ?i s\<close>
    using v_eq_p v_eq_n by auto
  finally show ?thesis .
qed

text \<open>Convergence of II for minimum reachability\<close>
lemma diff_ub_lb_n_bound:
  assumes \<open>s \<in> states \<M>\<close>
  shows \<open>ub_n (i * R_G.I) s - lb_n (i * R_G.I) s \<le> (1 - R_G.min_prob ^ R_G.I) ^ i\<close>
proof -
  have *: \<open>(1 - R_G.min_prob ^ R_G.I) ^ i = (1 - R_G.plim i)\<close>
    by (smt (verit, best) R_G.min_prob_le1 R_G.min_prob_pos ennreal_1 ennreal_minus power_le_one zero_less_power)
  have \<open>R_G.plim i \<le> S.p_fin (i * R_G.I) s + R.n_fin (i * R_G.I) s\<close>
    using assms S_R_p_n_fin_ge_plim by (auto)
  hence \<open>1 - (S.p_fin (i * R_G.I) s + R.n_fin (i * R_G.I) s) \<le> 1 - R_G.plim i\<close>
    using ennreal_mono_minus by blast
  thus ?thesis
    by (auto simp: algebra_simps ennreal_minus_le_iff * lb_n_eq_n_fin(1) assms ub_n_eq_p_fin(1))
qed

lemma diff_ub_lb_n_convergence:
  assumes \<open>s \<in> states \<M>\<close> \<open>eps > 0\<close> \<open>R_G.min_prob \<noteq> 1\<close>
  defines \<open>step_bound \<equiv> nat \<lceil> log (1 - R_G.min_prob ^ R_G.I) eps \<rceil> * R_G.I\<close>
  assumes \<open>i \<ge> step_bound\<close>
  shows \<open>ub_n i s - lb_n i s \<le> eps\<close>
proof (cases \<open>R_G.I = 0\<close>)
  case True
  hence \<open>states \<M> = bottoms \<M>\<close>
    using R_G.G.simps(1) R_G.R.S2 R_G.lvl_ltI R_G.state_in_lvl by auto
  hence \<open>s \<in> avoids \<M> \<or> s \<in> targets \<M>\<close>
    using assms
    by (simp add: bottoms_Avd_Tgt)
  moreover have \<open>ub_n i s = lb_n i s\<close>
    unfolding lb_n_eq_n_fin ub_n_eq_p_fin
    using assms \<open>s \<in> avoids \<M> \<or> s \<in> targets \<M>\<close>
    by auto
  ultimately show ?thesis
    using assms lb_n_eq_n_fin(1) by fastforce
next
  case False

  let ?i = \<open>nat \<lceil> log (1 - R_G.min_prob ^ R_G.I) eps \<rceil>\<close>
  have min_prob_lt1: \<open>R_G.min_prob < 1\<close>
    using assms R_G.min_prob_le1 by auto

  have \<open>ub_n i s - lb_n i s \<le> ub_n (?i * R_G.I) s - lb_n (?i * R_G.I) s\<close>
    using assms mono_lb_n antimono_lb_n
    by (auto intro: ennreal_minus_mono dest: monoD antimonoD le_funD)
  also have \<open>\<dots> \<le> (1 - R_G.min_prob ^ R_G.I) ^ ?i\<close>
    using diff_ub_lb_n_bound[OF \<open>s \<in> states \<M>\<close>, of ?i]
    by auto
  also have \<open>\<dots> \<le> eps\<close>
    using assms min_prob_lt1 False R_G.min_prob_pos
    by (intro ennreal_leI power_of_ceil_nat_log_le) (auto simp: power_less_one_iff intro!: zero_less_power)
  finally show ?thesis .
qed

text \<open>Convergence of II for maximum reachability probabilities\<close>

lemma diff_ub_lb_p_bound:
  assumes \<open>s \<in> states \<M>\<close>
  shows \<open>ub_p (i * R_G.I) s - lb_p (i * R_G.I) s \<le> (1 - R_G.min_prob ^ R_G.I) ^ i\<close>
proof -
  have *: \<open>(1 - R_G.min_prob ^ R_G.I) ^ i = (1 - R_G.plim i)\<close>
    by (smt (verit, best) R_G.min_prob_le1 R_G.min_prob_pos ennreal_1 ennreal_minus power_le_one zero_less_power)
  have \<open>R_G.plim i \<le> S.n_fin (i * R_G.I) s + R.p_fin (i * R_G.I) s\<close>
    using assms S_R_n_p_fin_ge_plim by auto
  hence \<open>1 - (S.n_fin (i * R_G.I) s + R.p_fin (i * R_G.I) s) \<le> 1 - R_G.plim i\<close>
    using ennreal_mono_minus by blast
  thus ?thesis
    by (auto simp: algebra_simps ennreal_minus_le_iff * lb_p_eq_p_fin(1) assms ub_p_eq_n_fin(1))
qed

lemma diff_ub_lb_p_convergence:
  assumes \<open>s \<in> states \<M>\<close> \<open>eps > 0\<close> \<open>R_G.min_prob \<noteq> 1\<close>
  defines \<open>step_bound \<equiv> nat \<lceil> log (1 - R_G.min_prob ^ R_G.I) eps \<rceil> * R_G.I\<close>
  assumes \<open>i \<ge> step_bound\<close>
  shows \<open>ub_p i s - lb_p i s \<le> eps\<close>
proof (cases \<open>R_G.I = 0\<close>)
  case True
  hence \<open>states \<M> = bottoms \<M>\<close>
    using R_G.G.simps(1) R_G.R.S2 R_G.lvl_ltI R_G.state_in_lvl by auto
  hence \<open>s \<in> avoids \<M> \<or> s \<in> targets \<M>\<close>
    using assms by (simp add: bottoms_Avd_Tgt)
  hence \<open>ub_p i s = lb_p i s\<close>
    unfolding lb_p_eq_p_fin ub_p_eq_n_fin
    using assms
    by auto
  thus ?thesis
    using assms lb_p_eq_p_fin(1) \<open>s \<in> avoids \<M> \<or> s \<in> targets \<M>\<close> by fastforce
next
  case False

  let ?i = \<open>nat \<lceil> log (1 - R_G.min_prob ^ R_G.I) eps \<rceil>\<close>
 
  have min_prob_lt1: \<open>R_G.min_prob < 1\<close>
    using assms R_G.min_prob_le1 by auto
  
  have \<open>ub_p i s - lb_p i s \<le> ub_p (?i * R_G.I) s - lb_p (?i * R_G.I) s\<close>
    using assms mono_lb_p antimono_lb_p
    by (auto intro: ennreal_minus_mono dest: monoD antimonoD le_funD)
  also have \<open>\<dots> \<le> (1 - R_G.min_prob ^ R_G.I) ^ ?i\<close>
    using diff_ub_lb_p_bound[OF \<open>s \<in> states \<M>\<close>, of ?i]
    by auto
  also have \<open>\<dots> \<le> eps\<close>
    using assms min_prob_lt1 False R_G.min_prob_pos
    by (intro ennreal_leI power_of_ceil_nat_log_le) (auto simp: power_less_one_iff intro!: zero_less_power)
  finally show ?thesis .
qed

end

end