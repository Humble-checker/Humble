theory MDP_Components
  imports "Markov_Models.Markov_Models" "Markov_Models.MDP_RP" MDP_Util
begin

text \<open>Auxiliary Theorems\<close>
lemma en_restrict: \<open>en (restrict_states X M) = (SIGMA x : X. en M `` {x})\<close>
  unfolding en_def
  by auto

lemma en_restrict': \<open>en (restrict_states X M) = (Id_on X) O (en M)\<close>
  unfolding en_def
  by auto

lemma en_map_mdpc: \<open>(x, y) \<in> en \<phi> \<Longrightarrow> (f x, f y) \<in> en (map_mdpc f \<phi>)\<close>
  unfolding en_def
  by (auto simp: actions_map_mdpc)

lemma en_star_map_mdpc: \<open>(x, y) \<in> (en \<phi>)\<^sup>* \<Longrightarrow> (f x, f y) \<in> (en (map_mdpc f \<phi>)) \<^sup>*\<close>
  by (induction rule: rtrancl_induct) (simp add: en_map_mdpc rtrancl.rtrancl_into_rtrancl)+


lemma sc_map: \<open>sc \<phi> \<Longrightarrow> sc (map_mdpc f \<phi>)\<close>
  unfolding sc_def
  using en_star_map_mdpc
  by (auto simp: sc_def en_star_map_mdpc subset_iff states_map_mdpc)


lemma ecI: \<open>sc \<phi> \<Longrightarrow> closed_mdpc \<phi> \<Longrightarrow> ec \<phi>\<close>
  unfolding ec_def
  by auto

lemma ec_map: \<open>ec \<phi> \<Longrightarrow> ec (map_mdpc f \<phi>)\<close>
  by (simp add: closed_mdpc_map ec_def sc_map)

context Finite_MDP
begin

lemma en_subs_states: \<open>en M \<subseteq> states M \<times> states M\<close>
  using closed_M closed_mdpc_def by blast

lemma en_plus_subs_states: \<open>(en M)\<^sup>+ \<subseteq> states M \<times> states M\<close>
  by (simp add: en_subs_states trancl_subset_Sigma)

lemma fin_en: \<open>finite (en M)\<close>
  using en_subs_states finite_states_M
  by (simp add: finite_subset)

lemma fin_en_star: \<open>finite ((en M)\<^sup>+)\<close>
  using fin_en by fastforce

lemma en_emptyD: \<open>en M = {} \<Longrightarrow> (\<forall>s \<in> states M. actions M s = {})\<close>
  unfolding en_def
  using set_pmf_not_empty
  by fastforce

lemma fin_en_star_restr[intro]: 
  \<open>finite X \<Longrightarrow> finite ((en M)\<^sup>* `` X)\<close>
  by (simp add: fin_en)

end

section \<open>MECs\<close>

lemma mec_closed: \<open>mec M m \<Longrightarrow> s \<in> m \<Longrightarrow> a \<in> actions m s \<Longrightarrow> s' \<in> a \<Longrightarrow> s' \<in> m\<close>
  by (simp add: closed_mdpcD ec_def mec_def)

definition \<open>the_mec M s = (THE m. s \<in> states m \<and> mec M m)\<close>

theorem mec_unique_state:
  assumes "mec M \<phi>" "mec M \<psi>"
    and "s \<in> states \<phi>" "s \<in> states \<psi>"
  shows "\<phi> = \<psi>"
  using assms mec_unique
  by (metis Int_iff empty_iff states_bot states_inf)

lemma mec_exists1:
  assumes \<open>s \<in> states M\<close>
  shows \<open>\<exists>!m. s \<in> states m \<and> mec M m\<close>
  using assms mec_exists' mec_unique_state 
  by metis

lemma the_mec[intro]: \<open>s \<in> states M \<Longrightarrow> mec M (the_mec M s)\<close>
  unfolding the_mec_def
  using theI'[OF mec_exists1[of s M]]
  by auto

lemma states_the_mec[intro]: "s \<in> states M \<Longrightarrow> s \<in> states (the_mec M s)"
  unfolding the_mec_def
  using theI'[OF mec_exists1[of s M]]
  by auto

lemma the_mec_eqI[intro]: \<open>mec M m \<Longrightarrow> s \<in> states m \<Longrightarrow> the_mec M s = m\<close>
  using theI'[OF mec_exists1[of s M]] mec_unique_state
  unfolding the_mec_def
  by fastforce

lemma the_mec_eqE[elim]: \<open>the_mec M s = m \<Longrightarrow> s \<in> states M \<Longrightarrow> (mec M m \<Longrightarrow> s \<in> states m \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using theI'[OF mec_exists1[of s M]] mec_unique_state
  unfolding the_mec_def
  by fastforce

lemma in_trivials_the_mec: \<open>s \<in> trivials M \<longleftrightarrow> s \<in> states M \<and> (the_mec M s) = trivial s\<close>
  unfolding trivials_def
  by (auto dest: mec_le the_mec simp: trivial_le_iff)

lemma trivials_in_states[dest]: \<open>s \<in> trivials M \<Longrightarrow> s \<in> states M\<close>
  by (simp add: in_trivials_the_mec)

lemmas states_the_mec[simp]

lemma (in Finite_MDP) the_mec_eq: \<open>s \<in> states (the_mec M s') \<Longrightarrow> s' \<in> states M \<Longrightarrow> the_mec M s = the_mec M s'\<close>
  by auto

section \<open>Strongly Connected Components\<close>
definition \<open>is_scc M X \<longleftrightarrow> 
  (X \<subseteq> states M \<and> X \<times> X \<subseteq> (en M)\<^sup>* \<and> (\<forall>X' \<subseteq> states M. X' \<times> X' \<subseteq> (en M)\<^sup>* \<longrightarrow> X \<subseteq> X' \<longrightarrow> X' = X))\<close>

lemma is_ssc_ex:
  assumes \<open>X \<times> X \<subseteq> (en M)\<^sup>*\<close> \<open>X \<subseteq> states M\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>X'. is_scc M X' \<and> X \<subseteq> X'\<close>
proof -
  define scs where \<open>scs = {X'. X' \<subseteq> states M \<and> X \<le> X' \<and> X' \<times> X' \<subseteq> (en M)\<^sup>*}\<close>

  have \<open>(\<Squnion>scs) \<times> (\<Squnion>scs) \<subseteq> (en M)\<^sup>*\<close>
    unfolding scs_def
    using assms
    by auto (metis mem_Sigma_iff subsetD rtrancl_trans )
  moreover have \<open>X \<le> (\<Squnion>scs)\<close>
    unfolding scs_def
    using assms
    by (auto intro!: Sup_upper2)
  moreover have le: \<open>m' \<le> (\<Squnion>scs)\<close> if \<open>X \<subseteq> m'\<close> \<open>m' \<times> m' \<subseteq> (en M)\<^sup>*\<close> \<open>m'\<le>M\<close> for m'
    using that
    unfolding scs_def
    by (auto intro!: assms sc_supI Sup_upper2[of \<open>m' \<squnion> X\<close>] simp: assms inf_absorb2)
  moreover have \<open>\<Squnion>scs \<le> M\<close>
    unfolding scs_def
    by (auto intro!: Sup_least)
  ultimately have \<open>is_scc M (\<Squnion>scs)\<close>
    unfolding is_scc_def
    by auto (metis Union_iff equalityI order.trans)
  thus \<open>\<exists>m'. is_scc M m' \<and> X \<le> m'\<close>
    using \<open>X \<le> \<Squnion>scs\<close> by blast
qed

lemma is_scc_exists':
  assumes \<open>s \<in> states M\<close>
  shows \<open>\<exists>X. s \<in> X \<and> is_scc M X\<close>
  using assms is_ssc_ex[of \<open>{s}\<close> M]
  by auto

lemma scc_en_closed:
  assumes 
    \<open>is_scc M X\<close> \<open>x \<in> X\<close> \<open>(x, x') \<in> (en M)\<^sup>*\<close> \<open>(x', x) \<in> (en M)\<^sup>*\<close>
  shows \<open>x' \<in> X\<close>
proof -
  have \<open>X \<times> X \<subseteq> (en M)\<^sup>*\<close>
    using assms unfolding is_scc_def
    by auto
  hence \<open>insert x' X \<times> insert x' X \<subseteq> (en M)\<^sup>*\<close>
    using assms
    by auto
  moreover have \<open>x' \<in> states M\<close>
    by (metis Set.set_insert assms(1) assms(2) assms(4) converse_rtranclE en_states insert_subset is_scc_def)
  ultimately show \<open>x'  \<in> X\<close>
    using assms 
    unfolding is_scc_def
    by (metis insert_subset subset_insertI)
qed

section \<open>Bottom SCCs\<close>

definition \<open>is_bscc M X \<longleftrightarrow> (is_scc M X \<and> (en M)\<^sup>* `` X \<subseteq> X)\<close>

lemma bscc_emptyD: \<open>is_bscc M {} \<Longrightarrow> states M = {}\<close>
  unfolding is_bscc_def is_scc_def
  by fast

text \<open>Every MDP has a bottom SCC:\<close>
lemma (in Finite_MDP) bscc_ex: \<open>\<exists>m. is_bscc M m\<close>
proof -
  {
    fix u v
    assume v: \<open>v \<in> states M\<close>
    have "finite ((en M)\<^sup>* `` {v})"
      by auto
    hence \<open>\<exists>m. is_bscc M m\<close> using v
    proof(induction "(en M)\<^sup>* `` {v}" arbitrary: v rule: finite_psubset_induct)
      case psubset
      obtain m where is_scc: "is_scc M m" "v \<in> m"
        using is_scc_exists'[OF \<open>v \<in> states M\<close>] by auto
      then show ?case
      proof(cases "is_bscc M m")
        case False
        have \<open>m \<subseteq> states M\<close>
          using is_scc
          unfolding is_scc_def
          by auto

        have \<open>m \<times> m \<subseteq> (en M)\<^sup>*\<close>
          using is_scc(1) is_scc_def by blast+

        have \<open>(en M)\<^sup>* `` m \<noteq> m\<close>
          using False is_scc
          unfolding is_bscc_def 
          by auto

        then obtain u1 v1 where uv1: "(u1,v1) \<in> en M" and u1: "u1 \<in> m" and v1: "v1 \<notin> m"
          by (metis Image_closed_trancl Image_iff subset_iff)

        hence "(en M)\<^sup>* `` {v1} \<subseteq> (en M)\<^sup>* `` {u1}"
          by auto
        moreover have "u1 \<notin> (en M)\<^sup>* `` {v1}"
          using scc_en_closed[OF is_scc(1)] u1 v1 uv1
          by auto
        moreover have \<open>v1 \<in> states M\<close>
          using en_subs_states uv1 by auto
        moreover have en_eq: \<open>(en M)\<^sup>* `` {u1} = (en M)\<^sup>* `` {v}\<close>
          using u1 \<open>v \<in> m\<close> \<open>m \<times> m \<subseteq> (en M)\<^sup>*\<close>
          by auto
        ultimately have "(en M)\<^sup>* `` {v1} \<subset> (en M)\<^sup>* `` {v}" by blast
        then show ?thesis
          using psubset(2) uv1 \<open>u1 \<in> m\<close> \<open>v1 \<in> states M\<close> \<open>m \<subseteq> states M\<close>
          by auto
      qed auto
    qed
  }
  note * = this

  thus ?thesis
  proof (cases \<open>en M = {}\<close>)
    case True
    then show ?thesis
      using S_not_empty actions_neq_empty_M en_emptyD 
      by force
  next
    case False
    then show ?thesis
      using * en_subs_states
      by auto
  qed
qed

section \<open>Bottom MECs\<close>
hide_const bmec (* wrong definition *)

definition bmec :: "'s mdpc \<Rightarrow> 's mdpc \<Rightarrow> bool"
  where "bmec M \<phi> \<longleftrightarrow> mec M \<phi> \<and> (\<forall>s\<in>states \<phi>. actions \<phi> s = actions M s)"

lemma bmecE[elim]: 
  assumes \<open>bmec M m\<close>
  obtains \<open>mec M m\<close> \<open>\<And>s. s \<in> states m \<Longrightarrow> actions m s = actions M s\<close>
  using assms unfolding bmec_def
  by auto

lemma bmecI[intro]: 
  assumes \<open>mec M m\<close> \<open>\<And>s. s \<in> states m \<Longrightarrow> actions m s = actions M s\<close>
  shows \<open>bmec M m\<close> 
  using assms unfolding bmec_def
  by auto

theorem bmec_unique_state:
  assumes "bmec M \<phi>" "bmec M \<psi>"
    and "s \<in> states \<phi>" "s \<in> states \<psi>"
  shows "\<phi> = \<psi>"
  using assms mec_unique_state bmecE
  by metis

lemma bmec_loop: "u \<in> states M \<Longrightarrow> actions M u = {return_pmf u} \<Longrightarrow> bmec M (loop u)"
  unfolding bmec_def by (auto intro: mec_loop)


definition \<open>bottoms M = {s \<in> states M. bmec M (the_mec M s)}\<close>

lemma in_bottoms_the_mec: \<open>s \<in> bottoms M \<longleftrightarrow> s \<in> states M \<and> bmec M (the_mec M s)\<close>
  unfolding bottoms_def
  by auto

lemma bottoms_subset_states: \<open>bottoms M \<subseteq> states M\<close>
  using in_bottoms_the_mec 
  by fastforce

lemma bmec_actions: \<open>bmec M m \<Longrightarrow> s \<in> m \<Longrightarrow> actions m s = actions M s\<close>
  by (metis bmec_def)

lemma bmec_closed: \<open>bmec M m \<Longrightarrow> s \<in> m \<Longrightarrow> a \<in> actions M s \<Longrightarrow> s' \<in> a \<Longrightarrow> s' \<in> m\<close>
  by (metis bmec_def mec_closed)

context Finite_MDP
begin

lemma ex_bmec: \<open>\<exists>m. bmec M m\<close>
proof -
  obtain X where \<open>is_bscc M X\<close>
    using bscc_ex by auto

  have \<open>X \<noteq> {}\<close>
    using S_not_empty \<open>is_bscc M X\<close> bscc_emptyD by blast

  define m where \<open>m = restrict_states X M\<close>

  have X_states: \<open>X \<subseteq> states M\<close> and states_m[simp]: \<open>states m = X\<close> and \<open>X \<times> X \<subseteq> (en M)\<^sup>*\<close> and ec: \<open>(en M)\<^sup>* `` X \<subseteq> X\<close>
    using \<open>is_bscc M X\<close>
    unfolding is_bscc_def is_scc_def m_def
    by auto

  hence en_X[simp]: \<open>(en M)\<^sup>* `` X = X\<close>
    by blast

  hence en_X'[dest]: \<open>(a, b) \<in> (en M)\<^sup>* \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X\<close> for a b
    using ec by blast

  hence \<open>closed_mdpc m\<close>
    unfolding closed_mdpc_def m_def en_restrict
    using en_subs_states
    by (auto simp: en_states)

  moreover have in_sigma: \<open>(x, y) \<in> (en M)\<^sup>* \<Longrightarrow> x \<in> X \<Longrightarrow> (x, y) \<in> (en m)\<^sup>*\<close> for x y
    unfolding m_def en_restrict
    by (induction rule: rtrancl_induct) (auto intro: rtrancl.intros)

  moreover have \<open>sc m\<close>
    using \<open>X \<times> X \<subseteq> (en M)\<^sup>*\<close>
    unfolding sc_def
    by (auto intro!: in_sigma)

  ultimately have \<open>ec m\<close>
    unfolding m_def ec_def sc_def
    by auto

  moreover have \<open>\<psi> \<le> m\<close> if \<open>ec \<psi>\<close> \<open>m \<le> \<psi>\<close> \<open>\<psi> \<le> M\<close> for \<psi>
  proof -
    have \<open>(en \<psi>)\<^sup>* `` X \<subseteq> X\<close>
      using en_mono[OF \<open>\<psi> \<le> M\<close>] en_X' rtrancl_mono
      by blast
    moreover have \<open>sc \<psi>\<close>
      using that unfolding ec_def by auto
    ultimately have \<open>states \<psi> = X\<close>
      using \<open>X \<noteq> {}\<close> states_mono[OF that(2)]
      by (auto dest: scD subsetD)
    thus \<open>\<psi> \<le> m\<close>
      unfolding m_def
      using \<open>\<psi> \<le> M\<close>
      by (subst restrict_states_idem[symmetric, of _ \<open>states \<psi>\<close>]) (auto intro: restrict_states_mono)
  qed

  moreover have \<open>m \<le> M\<close>
    unfolding m_def
    using restrict_states_le
    by auto
  ultimately have \<open>mec M m\<close>
    unfolding mec_def
    by auto
  hence \<open>bmec M m\<close>
    unfolding m_def bmec_def
    by auto
  thus ?thesis
    by auto
qed

lemma trivial_not_bmec: \<open>\<not>bmec M (trivial s)\<close>
  using actions_neq_empty_M[of s]
  by (fastforce dest: mec_le simp: trivial_le_iff)

lemma bmec_neq_bot: \<open>bmec M m \<Longrightarrow> m \<noteq> bot\<close>
  unfolding bmec_def
  using mec_bot_imp_bot M_neq_bot
  by metis

lemma bmec_has_state: \<open>bmec M m \<Longrightarrow> states m \<noteq> {}\<close>
  using bmec_neq_bot eq_bot_iff_states
  by blast

lemma bmec_not_triv:
  assumes \<open>bmec M m\<close> \<open>s \<in> states m\<close>
  shows \<open>s \<notin> trivials M\<close>
  using trivial_not_bmec assms
  by (metis bmecE in_trivials_the_mec the_mec_eqI)

lemma trivials_bottoms_disj:
  shows \<open>trivials M \<inter> bottoms M = {}\<close>
  using trivial_not_bmec
  by (auto simp: in_trivials_the_mec in_bottoms_the_mec)

lemma bottoms_ne: \<open>bottoms M \<noteq> {}\<close>
proof-
  obtain s m where \<open>bmec M m\<close> \<open>s \<in> states m\<close>
    using ex_bmec bmec_has_state by blast
  thus ?thesis
    using in_bottoms_the_mec[of s M]
    by (auto dest: mec_le states_mono the_mec_eqI)
qed

lemma bottoms_absorb: \<open>s \<in> bottoms M \<Longrightarrow> a \<in> actions M s \<Longrightarrow> s' \<in> a \<Longrightarrow> s' \<in> bottoms M\<close>
  using set_pmf_closed bmec_closed[of M \<open>the_mec M s\<close> s a s'] the_mec_eq[of s' s]
  by (auto simp: in_bottoms_the_mec)

lemma state_bottoms_measurable[measurable]: \<open>Measurable.pred ((count_space UNIV)) (\<lambda>\<omega>. state \<omega> \<in> bottoms M)\<close>
  by auto

lemma bottoms_measurable[measurable]: \<open>Measurable.pred ((count_space UNIV)) (\<lambda>\<omega>. \<omega> \<in> bottoms M)\<close>
  by auto

lemmas valid_cfg_action_in_K[intro]

lemma action_in_actions[intro]: \<open>cfg \<in> valid_cfg \<Longrightarrow> action cfg \<in> actions M (state cfg)\<close>
  using actions'_states by blast

lemma bottom_absorb_cfg_AE:
  assumes \<open>state cfg \<in> bottoms M\<close> \<open>cfg \<in> valid_cfg\<close>
  shows \<open>AE \<omega> in MC.T cfg. state ((cfg ## \<omega>) !! i) \<in> bottoms M\<close>
  using assms
proof (induction i arbitrary: cfg)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have \<open>state cfg' \<in> bottoms M\<close> if \<open>cfg' \<in> K_cfg cfg\<close> for cfg'
    using that Suc
    by (auto simp: K_cfg_def intro: bottoms_absorb)
  then show ?case
    using Suc
    by (auto dest: valid_K_cfg simp: MC.AE_T_iff[of _ cfg] intro: Suc.IH)
qed

lemma bottom_absorb_AE:
  assumes \<open>state cfg \<in> bottoms M\<close> \<open>cfg \<in> valid_cfg\<close>
  shows \<open>AE \<omega> in T cfg. (state cfg ## \<omega>) !! i \<in> bottoms M\<close>
  using assms 
proof (induction i arbitrary: cfg)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have \<open>state cfg' \<in> bottoms M\<close> if \<open>cfg' \<in> K_cfg cfg\<close> for cfg'
    using that Suc  
    by (auto simp: K_cfg_def intro: bottoms_absorb)
  then show ?case
    using Suc
    by (auto dest: valid_K_cfg intro: Suc simp: AE_T_eq'[of _ cfg])
qed

end
end