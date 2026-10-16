section \<open>Reduced MDPs\<close>

theory Reduced_MDP
  imports MDP_Components MDP_Util
begin

hide_const R

subsection \<open>Reduced MDP Locale\<close>
text \<open>
We define reduced MDPs: they only contain trivial and bottom MECs.
This ensures that we a.s. reach the bottom MECs, not matter which configuration.
\<close>
locale Reduced_MDP = Finite_MDP M for M :: \<open>'s mdpc\<close> +
  assumes triv_or_bot: \<open>\<And>s. s \<in> states M \<Longrightarrow> s \<in> trivials M \<or> s \<in> bottoms M\<close>
begin

lemma states_triv_bot: \<open>states M = trivials M \<union> bottoms M\<close>
  using triv_or_bot trivials_subset_states bottoms_subset_states
  by force

lemma reduced_cases:
  obtains \<open>s \<in> trivials M \<and> s \<notin> bottoms M\<close> | \<open>s \<in> bottoms M \<and> s \<notin> trivials M\<close> | \<open>s \<notin> states M\<close>
  using triv_or_bot trivials_bottoms_disj 
  by auto

subsection \<open>Level Graph\<close>
text \<open>
We separate the states into different levels according to their distance to\<^term>\<open>bottoms M\<close>.
The function \<^term>\<open>G\<close> builds a partition of the state space.\<close>
fun G where
  \<open>G 0 = bottoms M\<close> |
  \<open>G (Suc n) = {s \<in> states M - \<Union>(G ` {..n}). \<forall>a \<in> actions M s. (\<Union>(G ` {..n}) \<inter> a \<noteq> {})}\<close>

text \<open>cf. Proposition 1.1\<close>
proposition ex_less_G:
  assumes \<open>D \<in> actions' M s\<close> \<open>s \<in> G i\<close> \<open>i > 0\<close> 
  shows \<open>\<exists>s' \<in> D. \<exists>i' < i. s' \<in> G i'\<close>
  using assms
  by (cases i) auto

lemma G_empty_Suc:
  assumes \<open>G i = {}\<close>
  shows \<open>G (Suc i) = {}\<close>
proof (cases i)
  case 0
  then show ?thesis 
    using bottoms_ne assms by auto
next
  case (Suc i')
  hence \<open>\<Union>(G ` {..Suc i'}) = \<Union>(G ` {..i'})\<close>
    using assms
    by (fastforce simp: atMost_Suc image_iff le_Suc_eq)
  thus ?thesis
    using Suc
    by (auto simp: atMost_Suc)
qed

lemma G_empty_succs:
  assumes \<open>G i = {}\<close> \<open>j \<ge> i\<close>
  shows \<open>G j = {}\<close>
  using assms G_empty_Suc
  by (induction j) (auto simp del: G.simps elim: le_SucE)

lemma G_Suc_disj: \<open>G i \<inter> G (Suc i) = {}\<close>
  by (auto simp: atMost_Suc)

lemma G_notin_succs:
  assumes \<open>x \<in> G i\<close> \<open>j > i\<close>
  shows \<open>x \<notin> G j\<close>
  using assms
  by (induction j arbitrary: x) auto

lemma G_disj:
  assumes \<open>i \<noteq> j\<close>
  shows \<open>G i \<inter> G j = {}\<close>
  using assms G_notin_succs[of _ i j] G_notin_succs[of _ j i]
  by fastforce

lemma G_in_states: \<open>G i \<subseteq> states M\<close>
  using bottoms_subset_states
  by (cases i) (fastforce)+

lemma disjntI: \<open>A \<inter> B = {} \<Longrightarrow> disjnt A B\<close>
  unfolding disjnt_def
  by auto

lemma G_empty_ex: \<open>\<exists>i. G i = {}\<close>
proof (rule ccontr)
  assume ne: \<open>\<nexists>i. G i = {}\<close>
  hence \<open>infinite (\<Union>i. (G i))\<close>
    using G_disj 
    by (intro infinite_disjoint_family_imp_infinite_UNION disjoint_image_disjoint_family_on) 
      (fastforce intro: disjntI pairwise_imageI injI)+
  hence \<open>infinite (states M)\<close>
    using G_in_states
    by (meson SUP_le_iff finite_subset)
  thus False
    using S_finite 
    by auto
qed

subsection \<open>@{term I}\<close>
text \<open>\<^term>\<open>I + 1\<close> denotes the number of levels in the MDP.\<close>
definition \<open>I = (GREATEST i. G i \<noteq> {})\<close>

lemma G_I_ne: \<open>G I \<noteq> {}\<close>
  unfolding I_def
  using GreatestI_ex_nat[where P = \<open>\<lambda>i. G i \<noteq> {}\<close>] G_empty_succs
  by (metis G.simps(1) nle_le bottoms_ne)

lemma G_ne_le_I: \<open>G k \<noteq> {} \<Longrightarrow> k \<le> I\<close>
  unfolding I_def
  using Greatest_le_nat[where P = \<open>\<lambda>i. G i \<noteq> {}\<close>] G_empty_ex nle_le  G_empty_succs
  by metis

lemma gt_I_empty: \<open>j > I \<Longrightarrow> G j = {}\<close>
  using G_ne_le_I 
  by fastforce

lemma G_SucI_empty: \<open>G (Suc I) = {}\<close>
  using gt_I_empty 
  by blast

lemma G_cover: \<open>(\<Union>i. G i) = states M\<close>
proof -
  define S' where \<open>S' = states M - (\<Union>i \<le> I. G i)\<close>

  have bottoms_notin_S': \<open>bottoms M \<inter> S' = {}\<close>
    unfolding S'_def
    by fastforce

  hence S'_trivs: \<open>S' \<subseteq> trivials M\<close>
    using S'_def states_triv_bot
    by auto

  text \<open>Towards a contradiction, assume @{term S'} is not empty.\<close>
  {
    assume \<open>S' \<noteq> {}\<close>

    hence some_in_S'[simp, intro]: "(SOME s. s \<in> S') \<in> S'"
      using some_in_eq
      by auto

    have S'_states: \<open>S' \<subseteq> states M\<close>
      unfolding S'_def
      by auto

    have \<open>\<exists>a \<in> actions M s. \<forall>s' \<in> (\<Union>i \<le> I. G i). s' \<notin> set_pmf a\<close> if \<open>s \<in> S'\<close> for s 
      using that G_SucI_empty
      unfolding S'_def
      by auto (metis UN_I mem_simps(2) mem_simps(4))

    hence in_S': \<open>\<exists>a \<in> actions M s. a \<subseteq> S'\<close> if \<open>s \<in> S'\<close> for s
      using that
      unfolding S'_def
      by (metis (no_types, lifting) actions'_states mem_simps(6) set_pmf_closed subsetI)

    define m where \<open>m = close (restrict_states S' M)\<close>

    have \<open>m \<le> M\<close>
      unfolding m_def
      by (metis close_closed close_mono closed_M restrict_states_le)

    \<comment> \<open>Then, @{term S'} forms the MDP @{term m}.\<close>
    interpret M': Finite_MDP m
    proof
      show \<open>closed_mdpc m\<close>
        by (simp add: closed_close m_def)
      show \<open>actions m s \<noteq> {}\<close> if \<open>s \<in> states m\<close> for s
        using that in_S' S'_states
        unfolding m_def actions_close
        by fastforce
      show \<open>m \<noteq> \<bottom>\<close>
        unfolding m_def
        using S'_states
        by (auto simp: eq_bot_iff_states)
      show \<open>\<And>s. finite (actions m s)\<close> \<open>finite (states m)\<close>
        using S_finite finite_actions_M \<open>m \<le> M\<close>
        by (meson finite_subset le_mdpc_iff)+
    qed

    have states_m[simp]: \<open>states m = S'\<close>
      unfolding m_def S'_def states_close 
      by auto

    have \<open>s \<in> trivials m\<close> if \<open>s \<in> S'\<close> \<open>s \<in> trivials M\<close> for s  
      using that \<open>m \<le> M\<close>
      unfolding trivials_def mec_def
      by (auto simp: trivial_le_iff)

    hence \<open>S' \<subseteq> trivials m\<close>
      using S'_trivs
      by auto
    hence \<open>s \<in> S' \<Longrightarrow> s \<notin> bottoms m\<close> for s
      using M'.trivials_bottoms_disj 
      by blast
    hence False        
      \<comment> \<open>this MDP has a bottom MEC, but all it's states are trivial MECs, a contradiction.\<close>
      using M'.bottoms_ne bottoms_subset_states
      by fastforce
  }
  thus ?thesis
    unfolding S'_def
    using G_in_states
    by auto
qed

lemma state_in_G:
  assumes \<open>s \<in> states M\<close>
  shows \<open>\<exists>i. s \<in> G i\<close>
  using G_cover assms by auto

lemma state_in_one_G:
  assumes \<open>s \<in> states M\<close>
  shows \<open>\<exists>!i. s \<in> G i\<close>
  using G_cover assms G_disj
  by auto

text \<open>The inverse function: determine the level given a state:\<close>
definition \<open>lvl s = (THE i. s \<in> G i)\<close>

lemma state_in_lvl[intro]: \<open>s \<in> states M \<Longrightarrow> s \<in> G (lvl s)\<close>
  unfolding lvl_def
  by (metis state_in_one_G theI)

lemma lvl_ltI[intro]: \<open>s \<in> states M \<Longrightarrow> lvl s \<le> I\<close>
  using G_ne_le_I by blast

lemma lvl_descE:
  assumes \<open>s \<in> states M\<close> \<open>0 < lvl s\<close> \<open>a \<in> actions' M s\<close>
  obtains s' where  \<open>s' \<in> a\<close> \<open>lvl s' < lvl s\<close>
  using ex_less_G[of a s \<open>lvl s\<close>] assms set_pmf_closed state_in_one_G
  by blast

text \<open>We can define a well-founded relation over the states based on \<^const>\<open>G\<close>:\<close>
definition \<open>Grel = {(s', s) | s s'. s \<in> states M \<and> s' \<in> states M \<and> lvl s' < lvl s}\<close>

lemma wf_Grel: \<open>wf Grel\<close>
proof (rule finite_acyclic_wf)
  show \<open>finite Grel\<close>
  unfolding Grel_def
  by (auto intro: S_finite finite_subset[of _ \<open>states M \<times> states M\<close>])
  have \<open>acyclic (Grel\<inverse>)\<close>
    unfolding Grel_def
    by (fastforce intro!: acyclicI_order[of _ lvl])
  thus \<open>acyclic Grel\<close>
    by auto
qed

subsection \<open>Minimum probability\<close>
text \<open>The minimum probability at any transition of the MDP\<close>
definition \<open>min_prob = (\<Sqinter>s \<in> states M. \<Sqinter>a \<in> actions M s. \<Sqinter>s' \<in> a. pmf a s')\<close>

lemma min_prob_le: 
  assumes \<open>s \<in> states M\<close> \<open>a \<in> actions M s\<close> \<open>s' \<in> a\<close>
  shows \<open>min_prob \<le> pmf a s'\<close>
  unfolding min_prob_def
  using assms S_not_empty actions_neq_empty_M set_pmf_not_empty 
  by (auto intro!: cINF_lower2 cINF_greatest bdd_belowI[of _ 0])

lemma min_prob_pos: \<open>0 < min_prob\<close>
  unfolding min_prob_def
  using S_finite S_not_empty actions_neq_empty_M finite_actions_M set_pmf_finite 
  by (auto simp: finite_less_Inf_iff pmf_positive_iff set_pmf_not_empty)

lemma min_prob_le1: \<open>min_prob \<le> 1\<close>
  using set_pmf_not_empty S_not_empty actions_neq_empty_M
  by (fastforce intro: order.trans[OF min_prob_le pmf_le_1])

subsection \<open>Reachability Problem\<close>
text \<open>We define the reachability problem to the bottom MECs.\<close>
sublocale R: Reachability_Problem \<open>actions' M\<close> \<open>states M\<close> \<open>trivials M - bottoms M\<close> \<open>bottoms M\<close>
  using trivials_bottoms_disj states_triv_bot
  by unfold_locales auto


subsection \<open>Reachability of Bottom MECs\<close>
text \<open>We can give a lower bound on the reachability probability in \<^const>\<open>I\<close> steps.
However, we use a simple custom induction rule for the proof:\<close>
lemma nat_induct_strong[case_names 0 Suc]:
  assumes \<open>P 0\<close> \<open>\<And>i. (\<And>j. j \<le> i \<Longrightarrow> P j) \<Longrightarrow> P (Suc i)\<close>
  shows \<open>P n\<close>
  using assms
  by (induction n rule: less_induct) (metis gr0I gr0_conv_Suc le_imp_less_Suc)

lemma v_fin_I_ge:
  assumes ct: \<open>ct \<in> valid_cfg\<close>
  shows \<open>min_prob ^ I \<le> R.v_fin I ct\<close>
proof -
  \<comment> \<open>First, we show how the probability to reach the bottom level depends on the current level.\<close>
  have \<open>min_prob ^ lvl (state ct) \<le> R.v_fin (lvl (state ct)) ct\<close> 
    using ct
  proof (induction \<open>lvl (state ct)\<close> arbitrary: ct rule: nat_induct_strong)
    case 0 \<comment> \<open>We are already at the bottom, trivial:\<close>
    then show ?case
      using state_in_lvl[of \<open>state ct\<close>]
      by auto
  next
    case (Suc i)
      \<comment> \<open>Otherwise, there is a successor state one level down:\<close>
    then obtain ct' where s': \<open>state ct' \<in> action ct\<close> and lt: \<open>lvl (state ct') < lvl (state ct)\<close> 
        and ct'_eq: \<open>ct' = cont ct (state ct')\<close> and ct': \<open>ct' \<in> valid_cfg\<close>
        using valid_cfg_cont lvl_descE
        by (metis R.valid_cfg_action_in_K state_cont valid_cfg_state_in_S zero_less_Suc)

      hence \<open>min_prob ^ lvl (state ct) \<le> min_prob ^ Suc (lvl (state ct'))\<close>
        using min_prob_pos min_prob_le1
        by (intro power_decreasing) auto
      also have \<open>\<dots> \<le> min_prob ^ lvl (state ct') * min_prob\<close>
        by auto
      also have \<open>\<dots> \<le> R.v_fin i ct' * min_prob\<close>
      proof -
        \<comment> \<open>By I.H., the successor already reaches the bottom with the desired probability:\<close>
        have IH: \<open>min_prob ^ lvl (state ct') \<le> R.v_fin i ct'\<close>
        using lt ct' Suc(2)
        by (auto intro: order.trans[OF Suc(1) R.v_fin_mono])
        thus ?thesis
          using ennreal_mult' min_prob_pos mult_right_mono by fastforce
      qed
      also have \<open>\<dots> \<le> R.v_fin i ct' * pmf (K_cfg ct) ct'\<close>
      proof -
        have \<open>min_prob \<le> pmf (action ct) (state ct')\<close>
          using valid_cfg_state_in_S valid_cfg_action_in_K s' Suc
          by (auto intro!: min_prob_le)
        also have \<open>\<dots> \<le> pmf (K_cfg ct) ct'\<close>
          by (subst ct'_eq) (auto simp: pmf_K_cfg_cont)
        finally show ?thesis
          by (auto intro!: mult_left_mono)
      qed
      also have \<open>\<dots> \<le> set_nn_integral (K_cfg ct) {ct'} (R.v_fin i)\<close>
        by (simp add: emeasure_pmf_single)
      also have \<open>\<dots> \<le> set_nn_integral (K_cfg ct) UNIV (R.v_fin i)\<close>
        by (rule nn_set_integral_set_mono) auto
      also have \<open>\<dots> \<le> integral\<^sup>N (K_cfg ct) (R.v_fin i)\<close>
        by auto
      also have \<open>\<dots> \<le> R.v_fin (Suc i) ct\<close>
      proof -
        have state_triv: \<open>state ct \<in> trivials M\<close>
          by (metis G.simps(1) G_notin_succs Suc(2) Suc(3) state_in_lvl triv_or_bot valid_cfg_state_in_S zero_less_Suc)
      thus ?thesis  
      using Suc s' trivials_bottoms_disj
      by (subst R.v_fin_Suc) auto
    qed
      finally show ?case
        using ennreal_leI Suc by argo
    qed
  moreover have \<open>min_prob ^ I \<le> min_prob ^ lvl (state ct)\<close> 
    using assms min_prob_pos min_prob_le1 valid_cfg_state_in_S 
    by (auto intro!: power_decreasing)
  moreover have \<open>R.v_fin (lvl (state ct)) ct \<le> R.v_fin I ct\<close>
    using assms valid_cfg_state_in_S 
    by (intro R.v_fin_mono) auto
  ultimately show ?thesis
    using R.v_fin_mono lvl_ltI assms
    by (metis ennreal_leI order.trans)
qed

text \<open>In the trace space, the \<^const>\<open>R.reach_fin\<close> predicate is equivalent to being in a bottom MEC.\<close>
lemma bottoms_iff_reach_fin:
  assumes \<open>cfg \<in> valid_cfg\<close>
  shows \<open>AE x in MC.T cfg. state ((cfg ## x) !! i) \<in> bottoms M = R.reach_fin i (state cfg ## smap state x)\<close>
  using assms
proof (induction i arbitrary: cfg)
  case (Suc i)
  then show ?case
    using valid_cfg_state_in_S bottom_absorb_cfg_AE[of cfg \<open>Suc i\<close>]
    by (cases \<open>state cfg\<close> rule: reduced_cases) (auto simp: MC.AE_T_iff[of _ cfg] R.reach_fin_Suc valid_K_cfg)
qed auto

text \<open>The probability of reaching the target can be split, this is important to derive a better 
lower bound of \<^const>\<open>R.v_fin\<close>.\<close>
lemma v_fin_add:
  assumes ct: \<open>cfg \<in> valid_cfg\<close>
  shows \<open>R.v_fin (i + j) cfg = 
    R.v_fin i cfg + (\<integral>\<^sup>+\<omega>. indicator {\<omega>. \<not>R.reach_fin i ((state cfg ## \<omega>))} (smap state \<omega>) * (R.v_fin j (snth (cfg ## \<omega>) i)) \<partial>MC.T cfg)\<close>
  using assms
proof (induction i arbitrary: cfg)
  case (Suc i)
  thus ?case
  proof (cases \<open>state cfg \<in> bottoms M\<close>)
    case False
    let ?nreach = \<open>\<lambda>cfg \<omega> i. indicator {\<omega>. \<not>R.reach_fin i ((state cfg ## \<omega>))} (smap state \<omega>)\<close>

    have state_triv: \<open>state cfg \<in> trivials M\<close>
      using False triv_or_bot Suc.prems valid_cfg_state_in_S by blast
    have \<open>R.v_fin (Suc i + j) cfg = R.v_fin (Suc (i + j)) cfg\<close>
      by auto
    also have \<open>\<dots> = integral\<^sup>N (measure_pmf (K_cfg cfg)) (R.v_fin (i + j))\<close>
      using False valid_cfg_state_in_S Suc triv_or_bot
      by (subst R.v_fin_Suc) auto
    also have \<open>\<dots> = (\<integral>\<^sup>+cfg'. R.v_fin i cfg' + (\<integral>\<^sup>+\<omega>. ?nreach cfg' \<omega> i * R.v_fin j (snth (cfg' ## \<omega>) i) \<partial>MC.T cfg') \<partial>K_cfg cfg)\<close>
      using Suc
      by (intro nn_integral_cong_AE) auto
    also have \<open>\<dots> = R.v_fin (Suc i) cfg + (\<integral>\<^sup>+cfg'. (\<integral>\<^sup>+\<omega>. ?nreach cfg' \<omega> i * R.v_fin j (snth (cfg' ## \<omega>) i) \<partial>MC.T cfg') \<partial>K_cfg cfg)\<close>
      using False Suc triv_or_bot
      by (subst R.v_fin_Suc) (auto simp: nn_integral_add)
    also have \<open>\<dots> = R.v_fin (Suc i) cfg + (\<integral>\<^sup>+ \<omega>. ?nreach cfg \<omega> (Suc i) * R.v_fin j ((cfg ## \<omega>) !! Suc i) \<partial>MC.T cfg)\<close>
      by (subst (2) MC.nn_integral_T) (simp add: indicator_def state_triv False R.reach_fin_Suc)+
    finally show ?thesis .
  qed fastforce
qed auto

text \<open>We can now show that we almost surely tend towards the bottom MECs. 
Notice that the lhs tends to \<^term>\<open>1\<close> for large \<^term>\<open>i\<close>.\<close>
theorem v_fin_Ii_ge:
  assumes ct: \<open>ct \<in> valid_cfg\<close>
  shows \<open>1 - (1 - min_prob ^ I) ^ i \<le> R.v_fin (i * I) ct\<close>
  using assms
proof (induction i arbitrary: ct)
  let ?pI = \<open>1 - min_prob ^ I\<close>

  case (Suc i)
  have min_prob_pow_bd[simp, intro]: \<open>min_prob ^ I \<le> 1\<close> \<open>min_prob ^ I \<ge> 0\<close> \<open>?pI \<ge> 0\<close> \<open>?pI ^ i \<le> 1\<close>
    using min_prob_le1 min_prob_pos
    by (fastforce intro!: power_le_one)+

  have v_fin_not_top[simp, intro]: \<open>R.v_fin I ct \<noteq> \<top>\<close>
    by (metis R.v_fin_le_1 Suc(2) ennreal_one_less_top linorder_not_le)

  have \<open>1 - (?pI ^ Suc i) = 1 - (?pI ^ i) * (1 - min_prob ^ I)\<close>
    by auto
  also have \<open>\<dots> \<le> 1 - (?pI ^ i) * (1 - R.v_fin I ct)\<close>
  proof -
    have \<open>min_prob ^ I \<le> R.v_fin I ct\<close>
      using Suc v_fin_I_ge by blast
    hence \<open>?pI ^ i * (1 - R.v_fin I ct) \<le> ?pI ^ i * ?pI\<close>
      by (auto intro!: ennreal_mono_minus mult_mono' simp: ennreal_mult'' ennreal_minus[symmetric])
    thus ?thesis
      using min_prob_pow_bd
      by (auto simp: ennreal_minus[symmetric] intro!: mult_nonneg_nonneg ennreal_mono_minus mult_mono')
  qed
  also have \<open>\<dots> = R.v_fin I ct + (1 - ?pI ^ i) * (1 - R.v_fin I ct)\<close>
  proof -
    have *: \<open>1 - ?pI ^ i * (1 - enn2real (R.v_fin I ct)) = enn2real (R.v_fin I ct) + (1 - ?pI ^ i) * (1 - enn2real (R.v_fin I ct))\<close>
      by (auto simp: algebra_simps)
    show ?thesis
      using ennreal_cong[OF *] Suc R.v_fin_le_1
    by (auto simp: ennreal_mult enn2real_leI ennreal_enn2real_if ennreal_minus[symmetric] split: if_splits)
  qed
  also have \<open>\<dots> = R.v_fin I ct + (1 - ?pI ^ i) * (1 - emeasure (MC.T ct) {\<omega> \<in> space (MC.T ct). R.reach_fin I (smap state (ct ## \<omega>))})\<close>
  proof -
    have \<open>R.v_fin I ct = emeasure (MC.T ct) {\<omega> \<in> space (MC.T ct). R.reach_fin I (smap state (ct ## \<omega>))}\<close>
      using Suc
      by (auto simp: R.v_fin_def T_def emeasure_distr) (auto simp: space_stream_space)
    thus ?thesis
      by auto
  qed
  also have \<open>\<dots> = R.v_fin I ct + (1 - ?pI ^ i) * (\<integral>\<^sup>+ \<omega>. indicator {\<omega> \<in> space (MC.T ct). \<not> R.reach_fin I (smap state (ct ## \<omega>))} \<omega> \<partial>MC.T ct)\<close>
    using MC.T.prob_space_axioms Suc
    apply (subst emeasure_prob_space_compl[symmetric])
    by auto (auto simp: space_stream_space Compl_eq_Diff_UNIV[symmetric] Collect_neg_eq)
  also have \<open>\<dots> \<le> R.v_fin I ct + \<integral>\<^sup>+ \<omega>. indicator {\<omega>. \<not> R.reach_fin I (smap state (ct ## \<omega>))} \<omega> * ennreal (1 - ?pI ^ i) \<partial>MC.T ct\<close>
    by (auto simp: nn_integral_multc space_stream_space) (auto simp: mult.commute)
  also have \<open>\<dots> \<le> R.v_fin I ct + \<integral>\<^sup>+ \<omega>. indicator {\<omega>. \<not> R.reach_fin I (smap state (ct ## \<omega>))} \<omega> * R.v_fin (i * I) ((ct ## \<omega>) !! I) \<partial>MC.T ct\<close>
    using AE_valid_cfg'[of ct] \<open>ct \<in> valid_cfg\<close> Suc.IH
    by (auto intro!: nn_integral_mono_AE simp: mult_left_mono)
  also have \<open>\<dots> \<le> R.v_fin (I + i * I) ct\<close>
    using Suc  
    by (subst v_fin_add) (auto simp: indicator_def)
  also have \<open>\<dots> \<le> R.v_fin (Suc i * I) ct\<close>
    by auto
  finally show ?case .
qed auto

text \<open>Now we can show that both \<^const>\<open>R.n\<close> and \<^const>\<open>R.p\<close> equal 1 as a direct consequence.
The only annoyance is dealing with the conversion between reals and ennreals.\<close>
lemma n_fin_Ii_ge: \<open>s \<in> states M \<Longrightarrow> ennreal (1 - (1 - min_prob ^ I) ^ i) \<le> R.n_fin (i * I) s\<close>
  unfolding R.n_fin_v_fin
  using v_fin_Ii_ge valid_cfgI
  by (auto intro!: INF_greatest)

lemma minprob_tendsto0: \<open>(\<lambda>i. (1 - min_prob ^ I) ^ i) \<longlonglongrightarrow> 0\<close>
  by (smt (verit, best) LIMSEQ_realpow_zero min_prob_le1 min_prob_pos power_le_one zero_less_power)

lemma minprob_tendsto1: \<open>(\<lambda>i. 1 - (1 - min_prob ^ I) ^ i) \<longlonglongrightarrow> 1\<close>
  using minprob_tendsto0 tendsto_const tendsto_diff by fastforce

abbreviation \<open>plim i \<equiv> ennreal (1 - (1 - min_prob ^ I) ^ i)\<close>

lemma plim_mono: \<open>incseq plim\<close>
  using min_prob_le1 min_prob_pos
  by (auto simp: power_le_one_iff intro!: incseq_SucI ennreal_leI mult_left_le_one_le)

lemma minprob_tendsto1': \<open>plim \<longlonglongrightarrow> 1\<close>
  by (metis ennreal_1 minprob_tendsto1 tendsto_ennrealI)

lemma SUP_plim: \<open>(\<Squnion>i. plim i) = 1\<close>
  using LIMSEQ_SUP[OF plim_mono] minprob_tendsto1' LIMSEQ_unique
  by auto

lemma n_fin_tendsto1: 
  assumes \<open>s \<in> states M\<close>
  shows \<open>(\<lambda>i. R.n_fin i s) \<longlonglongrightarrow> 1\<close> and
    n_fin_SupI_1: \<open>(\<Squnion>i. R.n_fin (i * I) s) = 1\<close> and
    n_fin_Sup1: \<open>(\<Squnion>i. R.n_fin i s) = 1\<close>
proof -
  have \<open>(\<Squnion>i. R.n_fin (i * I) s) \<le> 1\<close> \<open>(\<Squnion>i. R.n_fin i s) \<le> 1\<close>
    by (meson R.n_fin_le_1 SUP_least assms)+
  moreover have \<open>(\<Squnion>i. R.n_fin (i * I) s) \<ge> (\<Squnion>i. plim i)\<close>
    using R.n_fin_le_1[OF assms] SUP_plim n_fin_Ii_ge[OF assms]
    by (blast intro: SUP_mono')
  moreover have \<open>(\<Squnion>i. R.n_fin i s) \<ge> (\<Squnion>i. plim i)\<close>
    using n_fin_Ii_ge[OF assms]
    by (auto intro: SUP_least SUP_upper2)
  ultimately show \<open>(\<Squnion>i. R.n_fin (i * I) s) = 1\<close> \<open>(\<Squnion>i. R.n_fin i s) = 1\<close>
    using SUP_plim by order+
  moreover have \<open>(\<lambda>i. R.n_fin i s) \<longlonglongrightarrow> (\<Squnion>i. R.n_fin i s)\<close>
    using LIMSEQ_SUP R.n_fin_mono monoD monoI le_funD
    by (metis (no_types, lifting))
  ultimately show \<open>(\<lambda>i. R.n_fin i s) \<longlonglongrightarrow> 1\<close>
    using LIMSEQ_unique by auto
qed

text \<open>cf. Proposition 1, 3 in Haddad, Monmege\<close>
lemma as_reach_bottom:
  assumes \<open>s \<in> states M\<close>
  shows \<open>R.n s = 1\<close>
proof -
  have \<open>R.n s \<ge> (\<Squnion>i. R.n_fin i s)\<close>
    by (meson R.n_fin_le_n SUP_least le_funD)
  thus ?thesis
    using R.n_le_1 assms n_fin_Sup1 by fastforce
qed

lemma as_reach_bottom_p:
  assumes \<open>s \<in> states M\<close>
  shows \<open>R.p s = 1\<close>
  using as_reach_bottom[OF assms] R.n_le_p[THEN le_funD] assms R.p_le_1
  by (auto intro!: antisym) metis

text \<open>Currently unused\<close>
lemma v_fin_bottoms:
  assumes \<open>cfg \<in> valid_cfg\<close>
  shows \<open>R.v_fin i cfg = emeasure (T cfg) {\<omega> \<in> space St. (state cfg ## \<omega>) !! i \<in> bottoms M}\<close>
  using assms
proof (induction i arbitrary: cfg)
  case (Suc i)
  thus ?case
  proof (cases \<open>state cfg \<in> bottoms M\<close>)
    case True
    then show ?thesis
      using bottom_absorb_AE[OF True \<open>cfg \<in> valid_cfg\<close>, of \<open>Suc i\<close>] Suc
      by (auto intro!: T.emeasure_eq_1_AE)
  next
    case False
    hence \<open>R.v_fin (Suc i) cfg = integral\<^sup>N ((K_cfg cfg)) (R.v_fin i)\<close>
      using Suc valid_cfg_state_in_S states_triv_bot 
      by (subst R.v_fin_Suc) auto
    also have \<open>\<dots> = emeasure (T cfg) {\<omega> \<in> space St. (state cfg ## \<omega>) !! Suc i \<in> bottoms M}\<close>
      using Suc
      by (subst nn_integral_cong_AE) (auto simp: emeasure_Collect_T[of _ cfg])
    finally show ?thesis .
  qed
qed auto

end

end