theory MDP_Util
  imports Markov_Models.Markov_Models "Markov_Models.MDP_RP" Util
begin

subsection \<open>MDP Preliminaries\<close>

subsubsection \<open>MDPs\<close>
context Finite_MDP
begin

lemma actions'_states[simp]:
  assumes \<open>x \<in> states M\<close>
  shows \<open>actions' M x = actions M x\<close>
  using assms
  unfolding actions'_def
  by simp

end

context Markov_Decision_Process
begin

lemma state_measurable[measurable]: "state \<in> count_space UNIV \<rightarrow>\<^sub>M count_space UNIV"
  by auto

lemma pmf_K_cfg_cont: \<open>pmf (K_cfg cfg) (cont cfg s') = pmf (action cfg) s'\<close>
proof -
  have \<open>cont cfg -` {cont cfg s'} = {s'}\<close>
    by auto (metis state_cont)
  thus ?thesis
    unfolding K_cfg_def
    by (auto simp: pmf_map pmf.rep_eq)
qed

lemma AE_T_eq:                                 
  assumes \<open>Measurable.pred St P\<close>
  shows \<open>(AE \<omega> in T cfg. P \<omega>) \<longleftrightarrow> (\<forall>s' \<in> action cfg. AE \<omega> in T (cont cfg s'). P (s' ## \<omega>))\<close>
  unfolding T_def
  using assms
  by (auto simp: AE_distr_iff MC.AE_T_iff[of _ cfg] set_K_cfg)

lemma AE_T_eq':                                 
  assumes \<open>Measurable.pred St P\<close>
  shows \<open>(AE \<omega> in T cfg. P \<omega>) \<longleftrightarrow> (\<forall>cfg' \<in> K_cfg cfg. AE \<omega> in T cfg'. P (state cfg' ## \<omega>))\<close>
  using assms
  by (auto simp: AE_T_eq set_K_cfg)

end

context Finite_Markov_Decision_Process
begin

lemmas valid_cfgI[rotated, dest]
lemmas valid_cfg_state_in_S[intro]

lemma eq_on_statesI[intro]:
  assumes \<open>\<And>s. s \<notin> S \<Longrightarrow> f s = g s\<close> \<open>\<And>s. s \<in> S \<Longrightarrow> f s = g s\<close>
  shows \<open>f = g\<close>
  using assms by auto

lemma le_on_statesI[intro]:
  assumes \<open>\<And>s. s \<notin> S \<Longrightarrow> f s \<le> g s\<close> \<open>\<And>s. s \<in> S \<Longrightarrow> f s \<le> g s\<close>
  shows \<open>f \<le> g\<close>
  using assms le_funI by metis

lemma simple_valid_cfg_iff'[simp]: \<open>ct \<in> Pi\<^sub>E S K \<Longrightarrow> simple ct x \<in> valid_cfg \<longleftrightarrow> x \<in> S\<close>
  by (simp add: PiE_def simple_valid_cfg_iff)


lemma sup_continuous_K_sup: \<open>sup_continuous (\<lambda>v. (\<Squnion> D \<in> K s. nn_integral (measure_pmf D) v))\<close>
  by (simp add: sup_continuous_apply_SUP sup_continuous_nn_integral_pmf)

lemma inf_continuous_K_inf: \<open>s \<in> S \<Longrightarrow> inf_continuous (\<lambda>v. (\<Sqinter> D \<in> K s. nn_integral (measure_pmf D) v))\<close>
  using set_pmf_finite
  by (auto simp add: intro: inf_continuous_apply_INF  intro!: inf_continuous_nn_integral_pmf)

lemma sup_inf_succs_le:
  shows \<open>(\<Squnion>i. (\<Sqinter>D \<in> K s. nn_integral (measure_pmf D) (M i) :: ennreal)) \<le> ((\<Sqinter>D \<in> K s. nn_integral (measure_pmf D) (\<Squnion> range M)))\<close>
  by (auto intro!: Sup_least Inf_greatest Inf_lower2 nn_integral_mono simp: Sup_upper)
  
lemma sup_inf_succs_ge:
  assumes \<open>incseq M\<close> \<open>s \<in> S\<close>
  shows \<open>(\<Sqinter>D \<in> K s. nn_integral (measure_pmf D) (\<Squnion> range M)) \<le> (\<Squnion>i. (\<Sqinter> D \<in> K s. nn_integral (measure_pmf D) (M i)))\<close>
proof -
  have \<open>(\<Sqinter>D \<in> K s. nn_integral (measure_pmf D) (\<Squnion> range M)) \<le> (\<Sqinter>D \<in> K s. (\<Squnion>i. nn_integral (measure_pmf D) (M i)))\<close>
    using assms sup_continuous_K_sup
    by (auto simp add: sup_continuousD sup_continuous_nn_integral_pmf)

  also have \<open>\<dots> \<le> 
    \<Squnion> (Inf ` {(\<lambda>x. f (range (\<lambda>i. ((nn_integral (measure_pmf x) (M i)))))) ` K s |f. \<forall>Y\<in>(\<lambda>a. range (\<lambda>x. ((nn_integral (measure_pmf a) (M x))))) ` K s. f Y \<in> Y})\<close>
    using Inf_Sup_le[of \<open>((\<lambda>a. range (\<lambda>x. (nn_integral (measure_pmf a) (M x)))) ` K s)\<close>]
    by (auto simp: image_image)
  also have \<open>\<dots> \<le> (\<Squnion>i. (\<Sqinter>D \<in> K s. nn_integral (measure_pmf D) (M i)))\<close>
  proof -
    {
      fix f
      assume h: \<open>\<forall>Y\<in>K s. \<exists>x. f Y = ((nn_integral (measure_pmf Y) (M x)))\<close>

      have \<open>\<exists>x'. \<forall>Y\<in>K s. \<exists>x \<le> x'. f Y = nn_integral (measure_pmf Y) (M x)\<close>
        using h K_finite \<open>s \<in> S\<close>
        by (intro finite_indexed_bound) auto

      moreover have \<open>i \<le> j \<Longrightarrow> nn_integral (measure_pmf Y) (M i) \<le> nn_integral (measure_pmf Y) (M j)\<close> for i j Y
        using monoD[OF \<open>mono M\<close>] 
        by (auto intro!: nn_integral_mono simp: le_funD)

      ultimately obtain i where i: \<open>\<forall>Y \<in> K s. f Y \<le> nn_integral Y (M i)\<close>
        by metis

      hence \<open>(\<Sqinter>D\<in>K s. f D) \<le> (\<Sqinter>a\<in>K s. nn_integral (measure_pmf a) (M i))\<close>
        using K_wf
        by (auto intro!: INF_mono)

      hence \<open>\<exists>i. (\<Sqinter>xa\<in>K s. f xa) \<le> (\<Sqinter>a\<in>K s. nn_integral (measure_pmf a) (M i))\<close>
        by auto
    }
    thus ?thesis
      by (auto intro: SUP_mono simp: ereal_Inf' image_image Setcompr_eq_image image_iff)
  qed
  finally show ?thesis
    by auto
qed


lemma sup_continuous_inf_succs: 
  assumes \<open>s \<in> S\<close>
  shows \<open>sup_continuous (\<lambda>v. (\<Sqinter>a\<in>K s. nn_integral (measure_pmf a) v))\<close>
  unfolding sup_continuous_def
  using assms sup_inf_succs_le sup_inf_succs_ge antisym
  by blast


lemma valid_cfg_action_in_K: "cfg \<in> valid_cfg \<Longrightarrow> action cfg \<in> K (state cfg)"
  by (auto dest!: valid_cfgD)

lemma valid_cfg_measurable[measurable]: \<open>Measurable.pred (count_space UNIV) (\<lambda>x. x \<in> valid_cfg)\<close>
  by auto

lemma AE_valid_cfg: \<open>cfg \<in> valid_cfg \<Longrightarrow> AE \<omega> in MC.T cfg. ((cfg##\<omega>) !! i \<in> valid_cfg)\<close>
  by (induction i arbitrary: cfg) (subst MC.AE_T_iff[of _ ] | auto)+

lemma AE_valid_cfg': \<open>cfg \<in> valid_cfg \<Longrightarrow> AE \<omega> in MC.T cfg. \<forall>i. ((cfg##\<omega>) !! i \<in> valid_cfg)\<close>
  using AE_valid_cfg[of cfg] 
  by (auto simp: AE_all_countable)

end

subsubsection \<open>Reachability Problems\<close>

lemmas AE_measure_pmf_iff[simp]

context Reachability_Problem
begin

lemma S1D[dest]: \<open>s \<in> S1 \<Longrightarrow> s \<in> S\<close>
  using S1 by auto

lemma set_pmf_ctD[dest]:
  assumes \<open>t \<in> set_pmf (ct s)\<close> \<open>ct \<in> Pi\<^sub>E S K\<close> \<open>s \<in> S\<close> 
  shows \<open>t \<in> S\<close>
  using assms 
  by (metis PiE_E set_pmf_closed)

paragraph \<open>Function Intros\<close>
lemma R_eq_on_statesI[intro]:
  assumes 
    \<open>\<And>s. s \<notin> S \<Longrightarrow> f s = g s\<close> 
    \<open>\<And>s. s \<in> S1 \<Longrightarrow> f s = g s\<close> 
    \<open>\<And>s. s \<in> S2 \<Longrightarrow> f s = g s\<close> 
    \<open>\<And>s. s \<in> S - S1 - S2 \<Longrightarrow> f s = g s\<close>
  shows \<open>f = g\<close>
  using assms
  by fastforce

lemma R_le_on_statesI[intro]:
  assumes 
    \<open>\<And>s. s \<notin> S \<Longrightarrow> f s \<le> g s\<close> 
    \<open>\<And>s. s \<in> S1 \<Longrightarrow> f s \<le> g s\<close> 
    \<open>\<And>s. s \<in> S2 \<Longrightarrow> f s \<le> g s\<close> 
    \<open>\<And>s. s \<in> S - S1 - S2 \<Longrightarrow> f s \<le> g s\<close>
  shows \<open>f \<le> g\<close>
  using assms
  by blast

declare eq_on_statesI[rule del]
declare le_on_statesI[rule del]

paragraph \<open>Bellman Optimality Operator\<close>

lemma sup_continuous_F_inf: \<open>sup_continuous F_inf\<close>
  apply (rule sup_continuous_fun)
  unfolding sup_continuous_def F_inf_def
  using sup_continuousD[OF sup_continuous_inf_succs]
  by auto

lemma F_inf_le_one:
  assumes \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<le> 1\<close> \<open>s \<in> S\<close>
  shows \<open>F_inf x s \<le> 1\<close>
  unfolding F_inf_def
  using assms K_wf set_pmf_closed
  by (fastforce intro!: measure_pmf.nn_integral_le_const Inf_less_eq)

lemma F_sup_le_one:
  assumes \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<le> 1\<close> \<open>s \<in> S\<close>
  shows \<open>F_sup x s \<le> 1\<close>
  unfolding F_sup_def
  using assms K_wf set_pmf_closed
  by (fastforce intro!: measure_pmf.nn_integral_le_const SUP_least)

lemma F_sup_p: \<open>F_sup p = p\<close>
  unfolding F_sup_def 
  by (auto simp: fun_eq_iff p_nS12 p_S1)
lemma F_inf_le_iter:
  assumes \<open>x \<le> n\<close>
  shows \<open>F_inf x \<le> n\<close>
  using assms mono_F_inf[THEN monoD] F_inf_n
  by fastforce

lemma F_inf_ge_iter:
  assumes \<open>x \<ge> n\<close>
  shows \<open>F_inf x \<ge> n\<close>
  using assms mono_F_inf[THEN monoD] F_inf_n 
  by fastforce                            

lemma F_sup_le_iter:
  assumes \<open>x \<le> p\<close>
  shows \<open>F_sup x \<le> p\<close>
  using assms mono_F_sup[THEN monoD] F_sup_p
  by fastforce

lemma F_sup_ge_iter:
  assumes \<open>x \<ge> p\<close>
  shows \<open>F_sup x \<ge> p\<close>
  using assms mono_F_sup[THEN monoD] F_sup_p
  by fastforce

lemma F_inf_S1: \<open>s \<in> S1 \<Longrightarrow> F_inf f s = (\<Sqinter>D\<in>K s. integral\<^sup>N (measure_pmf D) f)\<close>
  unfolding F_inf_def
  using S1_S2 S1 S2
  by auto

lemma F_sup_S1: \<open>s \<in> S1 \<Longrightarrow> F_sup f s = (\<Squnion>D\<in>K s. integral\<^sup>N (measure_pmf D) f)\<close>
  unfolding F_sup_def
  using S1_S2 S1 S2
  by auto

lemma F_sup_nS[simp]: \<open>s \<notin> S \<Longrightarrow> F_sup f s = undefined\<close>
  unfolding F_sup_def
  by auto

text \<open>Version of @{const F_inf} restricted to probabilities, has well-behaved gfp.\<close>
definition \<open>F_inf1 x = (\<lambda>s \<in> S. min 1 (F_inf x s))\<close>

lemma F_inf1_le1:
  assumes \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<le> 1\<close>
  shows \<open>F_inf1 x = F_inf x\<close>
  using assms K_closed K_wf
  by (auto simp: F_inf1_def F_inf_def AE_measure_pmf_iff 
      intro!: ext min.absorb2 Inf_less_eq measure_pmf.nn_integral_le_const) blast

lemma F_inf1_mono: \<open>mono F_inf1\<close>
  unfolding F_inf1_def using mono_F_inf[THEN monoD]
  by (auto intro!: monoI le_funI min.coboundedI2 simp: le_funD)

lemmas inf_continuous_K_inf[order_continuous_intros]

lemma F_inf1_sup_continuous: \<open>sup_continuous F_inf1\<close>
  unfolding F_inf1_def 
  using sup_continuous_F_inf
  by (auto intro!: order_continuous_intros intro: sup_continuous_applyD)

lemma F_inf_inf_continuous[order_continuous_intros]: \<open>inf_continuous F_inf\<close>
  unfolding F_inf_def 
  by (fastforce intro: order_continuous_intros sup_continuous_applyD)

lemma F_inf1_inf_continuous[order_continuous_intros]: \<open>inf_continuous F_inf1\<close>
  unfolding F_inf1_def
  by (auto intro!: order_continuous_intros intro: inf_continuous_applyD)

paragraph \<open>Bellman Operator for Policies\<close>
definition \<open>F_\<sigma> \<sigma> x =
    (\<lambda>s\<in>S.
        if s \<in> S2 then 1
        else if s \<in> S1 then integral\<^sup>N (measure_pmf (\<sigma> s)) x else 0)\<close>

lemma F_\<sigma>_S2[simp]: 
  assumes \<open>s \<in> S2\<close>
  shows \<open>F_\<sigma> \<sigma> x s = 1\<close>
  unfolding F_\<sigma>_def
  using S2 assms
  by auto

lemma F_\<sigma>_undefined[simp]: 
  assumes \<open>s \<notin> S\<close>
  shows \<open>F_\<sigma> \<sigma> x s = undefined\<close>
  unfolding F_\<sigma>_def
  using assms
  by auto

lemma F_\<sigma>_cont:
  assumes \<open>s \<in> S\<close> \<open>s \<notin> S2\<close> \<open>s \<in> S1\<close>
  shows \<open>F_\<sigma> \<sigma> x s = integral\<^sup>N (measure_pmf (\<sigma> s)) x\<close>
  using assms
  unfolding F_\<sigma>_def
  by auto

lemma mono_F_\<sigma>: \<open>mono (F_\<sigma> \<sigma>)\<close>
  by (auto intro!: monoI le_funI nn_integral_mono dest: le_funD simp: F_\<sigma>_def)

lemma F_\<sigma>_v:
  assumes \<open>ct \<in> Pi S K\<close>
  shows "F_\<sigma> ct (v o (simple ct)) = (v o (simple ct))"
  using S1_nS2 assms S1
  unfolding fun_eq_iff F_\<sigma>_def
  by (auto intro!: nn_integral_cong_AE simp: v_S1 simple_valid_cfg_iff AE_measure_pmf_iff)

paragraph \<open>Minimal Reachability Probability\<close>
lemma n_pos_succs:
  assumes succs_pos: \<open>\<And>a. a \<in> K s \<Longrightarrow> \<exists>s'\<in> set_pmf a. 0 < n s'\<close>
  and s: \<open>s \<in> S1\<close>
  shows \<open>n s > 0\<close>
proof -
  have exp_pos: \<open>0 < integral\<^sup>N (measure_pmf D) n\<close> if \<open>D \<in> K s\<close> for D
    apply (rule le_less_trans[of _ \<open>integral\<^sup>N (measure_pmf D) (\<lambda>_. 0)\<close>])
    subgoal by auto
    apply (rule nn_integral_less)
    using succs_pos that using zero_order
    by (auto simp: AE_measure_pmf_iff)
   
  show \<open>n s > 0\<close>
    using s n_S1 S1 exp_pos K_finite K_wf assms
    by (auto simp: finite_less_Inf_iff)
  qed 

lemma n_zero_succs:
  assumes \<open>n s = 0\<close> \<open>s \<in> S1\<close>
  shows \<open>\<exists>a \<in> K s. \<forall>s' \<in> set_pmf a. n s' = 0\<close>
  using assms n_pos_succs by force

lemma n_le_p: \<open>n \<le> p\<close>
  by (auto intro!: le_on_statesI Inf_le_Sup simp: n_def p_def P_inf_def P_sup_def)

paragraph \<open>Value Function\<close>
lemma v_eq_lfp_F_\<sigma>:
  assumes Pi_ct: \<open>ct \<in> Pi S K\<close>
  shows \<open>v o (simple ct) = lfp (F_\<sigma> ct)\<close>
proof -
  let ?F = "\<lambda>P. HLD S2 or (HLD S1 aand nxt P)"
  define P where "P s n =
      emeasure (T (simple ct s)) {x\<in>space (T (simple ct s)). (?F ^^ n) (\<lambda>x. False) (s ## x)}"
    for s n
  { 
    fix s
    assume "s \<in> S"
    with S1 have [simp, measurable]: "s \<in> S" by auto

    have "v (simple ct s) = emeasure (T (simple ct s)) {x\<in>space (T (simple ct s)). lfp ?F (s ## x)}"
      using S1_S2
      by (simp add: v_eq[OF simple_valid_cfg[OF Pi_ct \<open>s\<in>S\<close>]])
        (simp add: suntil_lfp space_T[symmetric, of "simple ct s"] del: space_T)
    also have "\<dots> = (\<Squnion>n. P s n)" 
      unfolding P_def
      apply (rule emeasure_lfp2[where P="\<lambda>M. \<exists>s. M = T (simple ct s)" and M="T (simple ct s)"])
      apply (intro exI[of _ s] refl)
      by (fastforce simp: sup_continuous_def)+
    also have "\<dots> \<le> lfp (F_\<sigma> ct) s"
    proof (intro SUP_least)
      fix n from \<open>s\<in>S\<close> show "P s n \<le> lfp (F_\<sigma> ct) s"
      proof (induct n arbitrary: s)
        case 0 with S1 show ?case
          by (subst lfp_unfold[OF mono_F_\<sigma>]) (auto simp: P_def)
      next
        case (Suc n)
    have *: \<open>Measurable.pred St (\<lambda>x. ((\<lambda>P xs. HLD S2 xs \<or> HLD S1 xs \<and> nxt P xs) ^^ Suc i) (\<lambda>x. False) (s ## x))\<close> for i
      by (rule measurable_compose[OF measurable_Stream[OF measurable_const measurable_ident_sets[OF refl]]]) measurable 
        show ?case
        proof cases
          assume "s \<in> S1" with S1_S2 S1 have s[simp]: "s \<notin> S2" "s \<in> S" "s \<in> S1" by auto
          have "P s (Suc n) = (\<integral>\<^sup>+t. P t n \<partial>ct s)"
            unfolding P_def space_T
            using *
            by (subst emeasure_Collect_T) (auto simp: K_cfg_def intro!: nn_integral_cong_AE)
          also have "\<dots> \<le> (\<integral>\<^sup>+t. lfp (F_\<sigma> ct) t \<partial>ct s)"
            using Pi_closed[OF Pi_ct \<open>s \<in> S\<close>]
            by (auto intro!: nn_integral_mono_AE Suc simp: AE_measure_pmf_iff)
          also have "\<dots> = lfp (F_\<sigma> ct) s"
            by (subst (3) lfp_unfold[OF mono_F_\<sigma>]) (auto simp: F_\<sigma>_def)
          finally show ?thesis .
        next
          assume "s \<notin> S1" with S2 \<open>s \<in> S\<close> show ?case
            using T.emeasure_space_1[of "simple ct s"]
            by (subst lfp_unfold[OF mono_F_\<sigma>]) (auto simp: F_\<sigma>_def P_def)
        qed
      qed
    qed
    finally have \<open>v (simple ct s) \<le> lfp (F_\<sigma> ct) s\<close> .
  }
  moreover have "s \<notin> S \<Longrightarrow> v (simple ct s) \<le> lfp (F_\<sigma> ct) s" for s
    using Pi_ct
    by (subst lfp_unfold[OF mono_F_\<sigma>]) (simp add: simple_valid_cfg_iff)
  ultimately show ?thesis
      using F_\<sigma>_v assms
    by (intro antisym lfp_lowerbound le_funI)  auto
qed


paragraph \<open>Finite Reachability On Traces\<close>
definition \<open>reach_fin i \<omega> \<equiv> ((\<lambda>P. HLD S2 or (HLD S1 aand nxt P)) ^^ Suc i) (\<lambda>x. False) \<omega>\<close>

lemma reach_fin_mono: 
  assumes \<open>i \<le> j\<close> \<open>reach_fin i \<omega>\<close>
  shows \<open>reach_fin j \<omega>\<close>
proof -
  have \<open>mono (\<lambda>i. reach_fin i \<omega>)\<close>
    unfolding reach_fin_def
    by (intro funpow_mono2[THEN le_funD] monoI) auto
  thus ?thesis
    using monoD assms 
    by fastforce
qed

lemma reach_fin_S2[simp, intro]: \<open>s \<in> S2 \<Longrightarrow> reach_fin i (s##\<omega>)\<close>
  by (auto simp: reach_fin_def)

lemma reach_fin_0[simp]: \<open>reach_fin 0 (s##\<omega>) \<longleftrightarrow> s \<in> S2\<close>
  by (auto simp: reach_fin_def)

lemma reach_fin_Suc: \<open>reach_fin (Suc i) (s##\<omega>) \<longleftrightarrow> (s \<in> S2 \<or> s \<in> S1 \<and> reach_fin i \<omega>)\<close>
  by (auto simp: reach_fin_def)

lemma reach_fin_nS12[simp]: \<open>s \<notin> S1 \<Longrightarrow> s \<notin> S2 \<Longrightarrow> reach_fin i (s##\<omega>) \<longleftrightarrow> False\<close>
  by (auto simp: reach_fin_def)

lemma reach_fin_measurable[measurable]: \<open>Measurable.pred St (reach_fin i)\<close>
  unfolding reach_fin_def
  by measurable

lemma reach_fin_measurable_Scons[measurable]: \<open>Measurable.pred St (\<lambda>\<omega>. reach_fin i (s##\<omega>))\<close>
  by measurable


abbreviation \<open>reach_fin0 i \<omega> \<equiv> ((\<lambda>P. HLD S2 or (HLD S1 aand nxt P)) ^^ i) (\<lambda>x. False) \<omega>\<close>

lemma reach_fin0_reach_fin: \<open>reach_fin i = reach_fin0 (Suc i)\<close>
  unfolding reach_fin_def 
  by auto

lemma reach_fin0_mono: \<open>mono reach_fin0\<close>
proof -
  have \<open>((\<lambda>P xs. HLD S2 xs \<or> HLD S1 xs \<and> P (stl xs)) ^^ i) (\<lambda>x. False) x \<Longrightarrow>
           ((\<lambda>P xs. HLD S2 xs \<or> HLD S1 xs \<and> P (stl xs)) ^^ i) (HLD S2) x\<close> for i x
    by (induction i arbitrary: x) auto
  thus ?thesis
    by (auto intro: incseq_SucI simp: funpow_simps_right simp del: funpow.simps) 
qed

lemma Sup_reach': 
  \<open>(HLD S1 suntil HLD S2) = (\<Squnion>i. ((\<lambda>P xs. HLD S2 xs \<or> HLD S1 xs \<and> P (stl xs)) ^^ i) (\<lambda>x. False))\<close>
  unfolding suntil_lfp
  by (subst sup_continuous_lfp) (auto intro!: SUP_cong order_continuous_intros simp: bot_fun_def)

lemma Sup_reach_fin: 
  \<open>(\<Squnion>i. reach_fin i) = (HLD S1 suntil HLD S2)\<close>
  unfolding Sup_reach' reach_fin_def
  using reach_fin0_mono
  by (subst Sup_Suc_mono) auto

paragraph \<open>Finite-Horizon Value Function\<close>

definition
  \<open>v_fin i = (\<lambda>cfg \<in> valid_cfg. emeasure (T cfg) {x \<in> space St. reach_fin i (state cfg ## x)})\<close>


lemma v_fin_invalid[simp]: \<open>cfg \<notin> valid_cfg \<Longrightarrow> v_fin i cfg = undefined\<close>
  by (auto simp: v_fin_def)

lemma v_fin0[simp]: \<open>cfg \<in> valid_cfg \<Longrightarrow> v_fin 0 cfg = (if state cfg \<in> S2 then 1 else 0)\<close>
  by (auto simp: v_fin_def)

lemma v_fin_nS12[simp]: \<open>cfg \<in> valid_cfg \<Longrightarrow> state cfg \<notin> S1 \<Longrightarrow> state cfg \<notin> S2 \<Longrightarrow> v_fin i cfg = 0\<close>
  unfolding v_fin_def
  by auto

lemma v_fin_S2[simp]: \<open>cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S2 \<Longrightarrow> v_fin i cfg = 1\<close>
  unfolding v_fin_def
  by auto

lemma v_fin_Suc[simp]: \<open>cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S1 \<Longrightarrow> v_fin (Suc i) cfg = (\<integral>\<^sup>+cfg'. v_fin i cfg' \<partial>K_cfg cfg)\<close>
  unfolding v_fin_def
  using S1_nS2
  by (subst emeasure_Collect_T) (auto simp: AE_measure_pmf_iff reach_fin_Suc intro!: nn_integral_cong_AE)

lemma v_fin_eq_F_\<sigma>_iter:
  assumes ct: \<open>ct \<in> Pi\<^sub>E S K\<close>
  shows \<open>v_fin (Suc i) o (simple ct) = F_\<sigma> ct (v_fin i o (simple ct))\<close>
  using ct S1_nS2
  by (auto intro!: R_eq_on_statesI nn_integral_cong_AE simp: F_\<sigma>_def K_cfg_def)

lemma v_fin_eq_F_\<sigma>0:
  assumes ct: \<open>ct \<in> Pi\<^sub>E S K\<close>
  shows \<open>v_fin 0 o (simple ct) = (F_\<sigma> ct) (\<lambda>s \<in> S. 0)\<close>
  using assms 
  by (fastforce simp: F_\<sigma>_def intro!: nn_integral_zero')

lemma v_fin_eq_F_\<sigma>:
  assumes ct: \<open>ct \<in> Pi\<^sub>E S K\<close>
  shows \<open>v_fin i o (simple ct) = ((F_\<sigma> ct) ^^ Suc i) (\<lambda>s \<in> S. 0)\<close>
  using assms v_fin_eq_F_\<sigma>_iter v_fin_eq_F_\<sigma>0
  by (induction i) auto

lemma v_fin_mono:
  assumes \<open>i \<le> j\<close>
  assumes ct: \<open>cfg \<in> valid_cfg\<close>
  shows \<open>v_fin i cfg \<le> v_fin j cfg\<close>
  unfolding v_fin_def
  using reach_fin_mono assms
  by (auto intro!: emeasure_mono_AE)

lemma v_SUP_fin: \<open>v cfg = (\<Squnion>i. v_fin i cfg)\<close>
proof -
  { assume cfg: \<open>cfg \<in> valid_cfg\<close>
    hence \<open>v cfg = emeasure (T cfg) {x \<in> space St. (HLD S1 suntil HLD S2) (state cfg ## x)}\<close>
      unfolding v_def by auto
    also have \<open>\<dots> = (\<Squnion>i. emeasure (T cfg) {x \<in> space St. reach_fin i (state cfg ## x)})\<close>
      by (subst SUP_emeasure_incseq) (auto intro!: monoI emeasure_eq_AE simp: reach_fin_mono  Sup_reach_fin[symmetric])
    also have \<open>\<dots> = (\<Squnion>i. v_fin i cfg)\<close>
      unfolding v_fin_def using cfg by auto
    finally have ?thesis .
  }
  thus ?thesis by fastforce
qed

lemma measurable_v_fin_op[measurable]:
  \<open>Measurable.pred St (\<lambda>x. ((\<lambda>P xs. HLD S2 xs \<or> HLD S1 xs \<and> nxt P xs) ^^ j) (\<lambda>x. False) (x))\<close>
  by measurable auto

lemma measurable_v_fin_op_cons[measurable]:
  \<open>Measurable.pred St (\<lambda>x. ((\<lambda>P xs. HLD S2 xs \<or> HLD S1 xs \<and> nxt P xs) ^^ j) (\<lambda>x. False) (s##x))\<close>
  by measurable auto

lemma v_fin_measurable[measurable]: \<open>v_fin j \<in> borel_measurable ((count_space UNIV))\<close>
  by measurable

lemma v_fin_0[simp]: \<open>cfg \<in> valid_cfg \<Longrightarrow> state cfg \<notin> S2 \<Longrightarrow> v_fin 0 cfg = 0\<close>
  by (auto simp: v_fin_def)


lemma v_fin_0_nS2[simp]: \<open>cfg \<in> cfg_on s \<Longrightarrow> s \<in> S - S2 \<Longrightarrow> v_fin 0 cfg = 0\<close>
  using S2 S1 S1_S2
  by (auto simp: v_fin_def valid_cfgI)

lemma v_fin_nS[simp]: \<open>cfg \<in> cfg_on s \<Longrightarrow> s \<notin> S \<Longrightarrow> v_fin i cfg = undefined\<close>
  using S2 S1 S1_S2 
  by (auto simp: v_fin_def dest: valid_cfg_state_in_S)

lemma v_fin_le_1: \<open>cfg \<in> valid_cfg \<Longrightarrow> v_fin i cfg \<le> 1\<close>
  unfolding v_fin_def
  using T.emeasure_le_1
  by auto

lemma v_fin_mono': \<open>mono v_fin\<close>
  using v_fin_mono v_fin_invalid 
  by (metis diff_le_self_ennreal monoI ennreal_minus_zero le_funI)


paragraph \<open>Finite-Horizon Maximal Reachability Probabilities\<close>

definition \<open>p_fin i = (\<lambda>s \<in> S. P_sup s (\<lambda>\<omega>. reach_fin i (s##\<omega>)))\<close>

lemma p_fin_v_fin: \<open>p_fin i = (\<lambda>s \<in> S. \<Squnion>cfg \<in> cfg_on s. v_fin i cfg)\<close>
proof -
  { fix s
    assume s: \<open>s \<in> S\<close>
    hence \<open>p_fin i s = (\<Squnion>cfg \<in> cfg_on s. v_fin i cfg)\<close>
      unfolding p_fin_def P_sup_def
      by (simp add: v_fin_def valid_cfgI[OF s])
  }
  thus ?thesis
    unfolding p_fin_def
    by auto
qed

lemma p_fin_Suc_S1: \<open>s \<in> S1 \<Longrightarrow> p_fin (Suc i) s = (\<Squnion>a \<in> K s. \<integral>\<^sup>+s'. p_fin i s' \<partial>measure_pmf a)\<close>
  unfolding p_fin_def
    using S1_nS2 set_pmf_closed S1
    by (subst P_sup_iterate) 
      (auto intro!: SUP_cong nn_integral_cong_AE simp: AE_measure_pmf_iff reach_fin_Suc)

lemma p_fin_S2[simp]: \<open>s \<in> S2 \<Longrightarrow> p_fin i s = 1\<close>
  unfolding p_fin_def
  using S2
  by auto

lemma p_fin_nS12[simp]: \<open>s \<in> S - S1 - S2 \<Longrightarrow> p_fin i s = 0\<close>
  unfolding p_fin_def
  by auto

lemma p_fin_nS[simp]: \<open>s \<notin> S \<Longrightarrow> p_fin i s = undefined\<close>
  unfolding p_fin_def
  by auto

lemma p_fin_0[simp]: \<open>s \<in> S - S2 \<Longrightarrow> p_fin 0 s = 0\<close>
  using cfg_on_not_empty[of s]
  by (auto simp: p_fin_def)

lemma p_fin_Suc: \<open>p_fin (Suc i) = 
  (\<lambda>s \<in> S. if s \<in> S2 then 1 else if s \<in> S1 then \<Squnion>a \<in> K s. \<integral>\<^sup>+s'. p_fin i s' \<partial>measure_pmf a else 0)\<close>
  using p_fin_Suc_S1 S1 S2 S1_nS2 
  by auto

lemma p_fin_le_1[intro]: \<open>s \<in> S \<Longrightarrow> p_fin i s \<le> 1\<close>
  unfolding p_fin_v_fin
  using valid_cfgI
  by (auto intro!: SUP_least v_fin_le_1)

lemma p_fin_eq_F_sup:
  fixes i
  shows
    \<open>p_fin i = (F_sup ^^ i) (\<lambda>s \<in> S. if s \<in> S2 then 1 else 0)\<close> (is ?P)
    \<open>\<And>s. s \<in> S \<Longrightarrow> (\<exists>cfg \<in> cfg_on s. v_fin i cfg = p_fin i s)\<close> (is \<open>\<And>s. _ \<Longrightarrow> ?Q s\<close>)
proof -
  define init where [simp]: \<open>init \<equiv> (\<lambda>s \<in> S. if s \<in> S2 then 1 else 0 :: ennreal)\<close>

  have \<open>?P \<and> (\<forall>s \<in> S. ?Q s)\<close>
  proof (induction i)
    case 0
    hence \<open>init = p_fin 0\<close>
      by auto
    moreover have \<open>v_fin 0 cfg = p_fin 0 s\<close> if \<open>cfg \<in> cfg_on s\<close> for cfg s
      using that S2
      by (cases \<open>s \<in> S\<close>; cases \<open>s \<in> S2\<close>) (auto simp: valid_cfgI)
    ultimately show ?case 
      by (metis cfg_on_not_empty equals0I funpow_0 init_def)
  next
    case (Suc i)
    then obtain cfg_i where
      cfg_i: \<open>\<And>s. s \<in> S \<Longrightarrow> cfg_i s \<in> cfg_on s\<close> and
      cfg_i_opt: \<open>\<And>s. s \<in> S \<Longrightarrow> v_fin i (cfg_i s) = p_fin i s\<close>
      by metis

    define D' where \<open>D' s = arg_max_on (\<lambda>D. nn_integral (measure_pmf D) (p_fin i)) (K s)\<close> for s

    have D': \<open>D' s \<in> K s\<close> if \<open>s \<in> S\<close> for s
      using K_finite set_pmf_finite S_finite
      by (auto simp: D'_def K_wf arg_max_if_finite(1) that)

    define cfg' where \<open>cfg' s = Cfg s (D' s) cfg_i\<close> for s

    have cfg': \<open>cfg' s \<in> cfg_on s\<close> if \<open>s \<in> S\<close> for s
      using that cfg_i D' K_closed
      by (auto simp: cfg'_def intro: set_pmf_closed intro!: cfg_onI[of _ s] cfg_onD_cont[of _ s] cont_Cfg cfg_of_cfg_onI)

    { fix s assume s_states[intro]: \<open>s \<in> S\<close> and s_triv: \<open>s \<in> S1 - S2\<close>

      have cont_cfg[simp]: \<open>(cont (Cfg s (D' s) cfg_i) x) = cfg_i x\<close> if \<open>x \<in> set_pmf (D' s)\<close> for x
        using D' s_states K_closed that cfg_i[of x]
        by (fastforce dest: cfg_onD_state)+

      have \<open>v_fin (Suc i) (cfg' s) = p_fin (Suc i) s\<close>
      proof -      
        have \<open>v_fin (Suc i) (cfg' s) = \<integral>\<^sup>+ x. v_fin i (cont (Cfg s (D' s) cfg_i) x) \<partial>(D' s)\<close>
          using cfg' s_triv
          unfolding cfg'_def 
          by (subst v_fin_Suc) (auto simp:  K_cfg_def  intro!:  valid_cfgI INF_greatest)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. v_fin i (cfg_i x) \<partial>(D' s)\<close>
          by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. p_fin i x \<partial>(D' s)\<close>
          using D' K_closed
          by (fastforce intro!: nn_integral_cong_AE simp: cfg_i_opt AE_measure_pmf_iff)
        also have \<open>\<dots> = (MAX a \<in> K s. \<integral>\<^sup>+ x. p_fin i x \<partial>measure_pmf a)\<close>
          unfolding D'_def
          using D' K_finite
          by (intro arg_max_on_Max) auto
        also have \<open>\<dots> = (\<Squnion>a\<in>K s. \<integral>\<^sup>+ x. p_fin i x \<partial>measure_pmf a)\<close>
          using D' K_finite s_states 
          by (auto intro!: cSup_eq_Max[symmetric])
        also have \<open>\<dots> = p_fin (Suc i) s\<close>
          using s_triv by (auto simp: p_fin_Suc_S1)
        finally show ?thesis  .
      qed
    }
    hence v_fin_cfg': \<open>v_fin (Suc i) (cfg' s) = p_fin (Suc i) s\<close> if \<open>s \<in> S\<close> for s
      using cfg' that 
      by auto (metis Diff_iff v_fin_S2 cfg_onD_state p_fin_S2 p_fin_nS12 v_fin_nS12 valid_cfgI)
    moreover have \<open>p_fin (Suc i) =  (F_sup ^^ (Suc i)) init\<close>
      apply (auto simp: p_fin_Suc F_sup_def init_def intro!: ext)
      using Suc.IH by presburger
    thus ?case
      using v_fin_cfg' cfg' init_def
      by blast
  qed
  thus \<open>?P\<close> \<open>\<And>s. s \<in> S \<Longrightarrow> ?Q s\<close> by auto
qed

lemma p_eq_Sup_p_fin: \<open>p = (\<Squnion>i. p_fin i)\<close>proof -
  have *: \<open>(\<lambda>s\<in>S. if s \<in> S2 then 1 else 0) \<le> F_sup \<bottom>\<close>
    unfolding F_sup_def
    by auto

  have \<open>p = (\<Squnion>i. (F_sup ^^ i) \<bottom>)\<close>
  unfolding p_eq_lfp_F_sup
  by (subst sup_continuous_lfp[OF continuous_F_sup]) auto
  also have \<open>\<dots> = (\<Squnion>i. (F_sup ^^ i) (\<lambda>s\<in>S. if s \<in> S2 then 1 else 0))\<close>
    using bot_least mono_F_sup
    by (auto intro!: antisym SUP_mono''[of _ _ Suc] funpow_mono * simp del: funpow.simps simp: funpow_simps_right)
  also have \<open>\<dots> = (\<Squnion>i. p_fin i)\<close>
    by (subst p_fin_eq_F_sup(1)[abs_def]) auto
  finally show ?thesis .
qed

paragraph \<open>Finite-Horizon Minimal Reachability Probabilities\<close>

definition \<open>n_fin i = (\<lambda>s \<in> S. P_inf s (\<lambda>\<omega>. reach_fin i (s##\<omega>)))\<close>

lemma n_fin_v_fin: \<open>n_fin i = (\<lambda>s \<in> S. \<Sqinter>cfg \<in> cfg_on s. v_fin i cfg)\<close>
proof -
  { fix s
    assume s: \<open>s \<in> S\<close>
    hence \<open>n_fin i s = (\<Sqinter>cfg \<in> cfg_on s. v_fin i cfg)\<close>
      unfolding n_fin_def P_inf_def
      by (simp add: v_fin_def valid_cfgI[OF s])
  }
  thus ?thesis
    unfolding n_fin_def
    by auto
qed

lemma n_fin_0[simp]: \<open>s \<in> S - S2 \<Longrightarrow> n_fin 0 s = 0\<close>
  using cfg_on_not_empty[of s]
  by (auto simp del: cfg_on_not_empty simp: valid_cfgI n_fin_def MC.INF_eq_zero_iff_ennreal)

lemma n_fin_S2[simp]: \<open>s \<in> S2 \<Longrightarrow> n_fin i s = 1\<close>
  using cfg_on_not_empty[of s] S2
  by (auto simp: valid_cfgI n_fin_def MC.INF_eq_zero_iff_ennreal)

lemma n_fin_nS12[simp]: \<open>s \<in> S - S1 - S2 \<Longrightarrow> n_fin i s = 0\<close>
  by (auto simp: n_fin_def)

lemma n_fin_nS[simp]: \<open>s \<notin> S \<Longrightarrow> n_fin i s = undefined\<close>
  by (auto simp: n_fin_def)

lemma n_fin_Suc_S1: \<open>s \<in> S1 \<Longrightarrow> n_fin (Suc i) s = (\<Sqinter>a \<in> K s. \<integral>\<^sup>+s'. n_fin i s' \<partial>measure_pmf a)\<close>
  unfolding n_fin_def
    using S1_nS2 set_pmf_closed S1
    by (subst P_inf_iterate) 
      (auto intro!: INF_cong nn_integral_cong_AE simp: AE_measure_pmf_iff reach_fin_Suc P_inf_def)

lemma n_fin_Suc: \<open>n_fin (Suc i) = 
  (\<lambda>s \<in> S. if s \<in> S2 then 1 else if s \<in> S1 then \<Sqinter>a \<in> K s. \<integral>\<^sup>+s'. n_fin i s' \<partial>measure_pmf a else 0)\<close>
  using n_fin_Suc_S1 S1 S2 S1_nS2 
  by auto


lemma n_fin_eq_F_inf:
  fixes i
  shows
    \<open>n_fin i = (F_inf ^^ i) (\<lambda>s \<in> S. if s \<in> S2 then 1 else 0)\<close> (is ?P)
    \<open>\<And>s. s \<in> S \<Longrightarrow> (\<exists>cfg \<in> cfg_on s. v_fin i cfg = n_fin i s)\<close> (is \<open>\<And>s. _ \<Longrightarrow> ?Q s\<close>)
proof -
  define init where [simp]: \<open>init \<equiv> (\<lambda>s \<in> S. if s \<in> S2 then 1 else 0 :: ennreal)\<close>

  have \<open>?P \<and> (\<forall>s \<in> S. ?Q s)\<close>
  proof (induction i)
    case 0
    hence \<open>init = n_fin 0\<close>
      by auto
    moreover have \<open>v_fin 0 cfg = n_fin 0 s\<close> if \<open>cfg \<in> cfg_on s\<close> for cfg s
      using that S2
      by (cases \<open>s \<in> S\<close>; cases \<open>s \<in> S2\<close>) (auto simp add:  valid_cfgI)
    ultimately show ?case 
      by (metis cfg_on_not_empty equals0I funpow_0 init_def)
  next
    case (Suc i)
    then obtain cfg_i where
      cfg_i: \<open>\<And>s. s \<in> S \<Longrightarrow> cfg_i s \<in> cfg_on s\<close> and
      cfg_i_opt: \<open>\<And>s. s \<in> S \<Longrightarrow> v_fin i (cfg_i s) = n_fin i s\<close>
      by metis

    define D' where \<open>D' s = arg_min_on (\<lambda>D. nn_integral (measure_pmf D) (n_fin i)) (K s)\<close> for s

    have D': \<open>D' s \<in> K s\<close> if \<open>s \<in> S\<close> for s
      using K_finite set_pmf_finite S_finite
      by (auto simp: D'_def K_wf arg_min_if_finite(1) that)

    define cfg' where \<open>cfg' s = Cfg s (D' s) cfg_i\<close> for s

    have cfg': \<open>cfg' s \<in> cfg_on s\<close> if \<open>s \<in> S\<close> for s
      using that cfg_i D' K_closed
      by (auto simp: cfg'_def intro: set_pmf_closed intro!: cfg_onI[of _ s] cfg_onD_cont[of _ s] cont_Cfg cfg_of_cfg_onI)

    { fix s assume s_states[intro]: \<open>s \<in> S\<close> and s_triv: \<open>s \<in> S1 - S2\<close>

      have cont_cfg[simp]: \<open>(cont (Cfg s (D' s) cfg_i) x) = cfg_i x\<close> if \<open>x \<in> set_pmf (D' s)\<close> for x
        using D' s_states K_closed that cfg_i[of x]
        by (fastforce dest: cfg_onD_state)+

      have \<open>v_fin (Suc i) (cfg' s) = n_fin (Suc i) s\<close>
      proof -      
        have \<open>v_fin (Suc i) (cfg' s) = \<integral>\<^sup>+ x. v_fin i (cont (Cfg s (D' s) cfg_i) x) \<partial>(D' s)\<close>
          using cfg' s_triv
          unfolding cfg'_def 
          by (subst v_fin_Suc) (auto simp:  K_cfg_def  intro!:  valid_cfgI INF_greatest)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. v_fin i (cfg_i x) \<partial>(D' s)\<close>
          by (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff)
        also have \<open>\<dots> = \<integral>\<^sup>+ x. n_fin i x \<partial>(D' s)\<close>
          using D' K_closed
          by (fastforce intro!: nn_integral_cong_AE simp: cfg_i_opt AE_measure_pmf_iff)
        also have \<open>\<dots> = (MIN a \<in> K s. \<integral>\<^sup>+ x. n_fin i x \<partial>measure_pmf a)\<close>
          unfolding D'_def
          using D' K_finite
          by (intro arg_min_on_Min) auto
        also have \<open>\<dots> = (\<Sqinter>a\<in>K s. \<integral>\<^sup>+ x. n_fin i x \<partial>measure_pmf a)\<close>
          using D' K_finite s_states by (subst cInf_eq_Min) auto
        also have \<open>\<dots> = n_fin (Suc i) s\<close>
          using s_triv by (auto simp: n_fin_Suc_S1)
        finally show ?thesis  .
      qed
    }
    hence v_fin_cfg': \<open>v_fin (Suc i) (cfg' s) = n_fin (Suc i) s\<close> if \<open>s \<in> S\<close> for s
      using cfg' that 
      by auto (metis Diff_iff v_fin_S2 cfg_onD_state n_fin_S2 n_fin_nS12 v_fin_nS12 valid_cfgI)
    moreover have \<open>n_fin (Suc i) =  (F_inf ^^ (Suc i)) init\<close>
      apply (auto simp: n_fin_Suc F_inf_def init_def intro!: ext)
      using Suc.IH by presburger
    thus ?case
      using v_fin_cfg' cfg' init_def
      by blast
  qed
  thus \<open>?P\<close> \<open>\<And>s. s \<in> S \<Longrightarrow> ?Q s\<close> by auto
qed

lemma n_eq_Sup_n_fin: \<open>n = (\<Squnion>i. n_fin i)\<close>
proof -
  have *: \<open>(\<lambda>s\<in>S. if s \<in> S2 then 1 else 0) \<le> F_inf \<bottom>\<close>
    unfolding F_inf_def
    by auto

  have \<open>n = (\<Squnion>i. (F_inf ^^ i) \<bottom>)\<close>
  unfolding n_eq_lfp_F_inf
  by (subst sup_continuous_lfp[OF sup_continuous_F_inf]) auto
  also have \<open>\<dots> = (\<Squnion>i. (F_inf ^^ i) (\<lambda>s\<in>S. if s \<in> S2 then 1 else 0))\<close>
    using bot_least mono_F_inf
    by (auto intro!: antisym SUP_mono''[of _ _ Suc] funpow_mono * simp del: funpow.simps simp: funpow_simps_right)
  also have \<open>\<dots> = (\<Squnion>i. n_fin i)\<close>
    by (subst n_fin_eq_F_inf(1)[abs_def]) auto
  finally show ?thesis .
qed

lemma n_fin_le_n: \<open>n_fin i \<le> n\<close>
  unfolding n_fin_def n_def P_inf_def
  by (auto intro!: emeasure_mono le_funI INF_mono' simp: Sup_reach_fin[symmetric])

lemma n_fin_le_1[intro]: \<open>s \<in> S \<Longrightarrow> n_fin i s \<le> 1\<close>
  by (metis order.trans le_funE n_fin_le_n n_le_1)

lemma n_fin_mono: \<open>mono n_fin\<close>
  using monoD[OF v_fin_mono']
  by (auto simp: n_fin_v_fin le_funD intro!: INF_mono' le_funI intro!: monoI)

end
end