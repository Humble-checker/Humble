theory II_Def
  imports Reduced_MDP
begin

section \<open>General theorems\<close>
  
  lemma fix_loop_id: "u \<in> states M \<Longrightarrow> actions M u = {return_pmf u} \<Longrightarrow> fix_loop u M = M"
    by (transfer; rule ext; force)
  
  lemma closed_mdpc_map_actions: "closed_mdpc (map_actions f M) \<longleftrightarrow> (\<forall>u \<in> states M. \<Union>(set_pmf ` f u (actions M u)) \<subseteq> states M)"
    unfolding closed_mdpc_def en_def map_actions_def apply clarsimp
    apply transfer
    apply safe
    apply (force split!: option.splits) 
    apply (force split!: option.splits) 
    apply (force simp: subset_iff split: option.splits) 
    done
  
  lemma pmf_map_inj2: "(\<And>y. f y = f x \<Longrightarrow> y = x) \<Longrightarrow> pmf (map_pmf f M) (f x) = pmf M x"
    by (auto simp: pmf.rep_eq intro!: measure_pmf.finite_measure_eq_AE) 
  
  lemma nn_integral_measure_map_pmf: "(\<And>x. x \<in> set_pmf a \<Longrightarrow> f x = g (h x)) \<Longrightarrow> integral\<^sup>N (measure_pmf a) f = integral\<^sup>N (measure_pmf (map_pmf h a)) g"
    by (simp add: nn_integral_cong_AE)
  
  lemma (in Finite_MDP) set_pmf_closed': \<open>D \<in> actions M s \<Longrightarrow> t \<in> set_pmf D \<Longrightarrow> t \<in> states M\<close>
    using closed_mdpcD[OF closed_M] by auto
  
  lemma actions_map_actions'[simp]: "s \<in> states \<phi> \<Longrightarrow> actions (map_actions f \<phi>) s = f s (actions \<phi> s)"
    by transfer (auto split: option.splits)

  lemma actions'_map_actions[simp]: "s \<in> states \<phi> \<Longrightarrow> actions' (map_actions f \<phi>) s = f s (actions' \<phi> s)"
    unfolding actions'_def
    by(auto simp: actions'_def split: option.splits)

  lemma in_states_Rep_mdpc: "x \<in> states M \<longleftrightarrow> (\<exists>y. Rep_mdpc M x = Some y)"
    apply transfer
    by auto

  lemma Rep_mdpc_actions: "Rep_mdpc M u = Some a \<Longrightarrow> a = actions M u"
    apply transfer by auto

  lemma not_in_states_Rep_mdpc: "x \<notin> states M \<longleftrightarrow> Rep_mdpc M x = None"
    apply transfer
    by blast

  lemma Rep_mdpc_actions_None: "Rep_mdpc M u = None \<Longrightarrow> actions M u = {}"
    apply transfer by auto

  lemma map_mdpc_trivial[simp]: "map_mdpc f (trivial u) = trivial (f u)"
    by(auto simp: sc_map actions_map_mdpc_eq_Collect states_map_mdpc intro!: sc_eq_trivial)

  lemma mdpc_le_trivials_antimono: "M \<le> M' \<Longrightarrow> u \<in> states M \<Longrightarrow> u \<in> trivials M' \<Longrightarrow> u \<in> trivials M"
    by(auto simp: in_trivials_the_mec mec_def trivial_le_iff dest!: the_mec[of u M'])

  lemma ec_actions_sub: "ec \<phi> \<Longrightarrow> \<phi> \<le> M \<Longrightarrow> actions \<phi> u \<subseteq> {a \<in> actions M u. set_pmf a \<subseteq> states \<phi>}"
    by (simp add: closed_mdpcD ec_def le_mdpc_iff subset_eq)

  lemma en_sub_map_actions: "(\<And> u a. a \<subseteq> f u a) \<Longrightarrow> en \<phi> \<subseteq> en (map_actions f \<phi>)" 
    apply(rule en_mono)
    apply(rule le_mdpcI)
    by auto

  lemma en_sup_map_actions: "(\<And> u a. f u a \<subseteq> a) \<Longrightarrow> en (map_actions f \<phi>) \<subseteq> en \<phi>" 
    apply(rule en_mono)
    apply(rule le_mdpcI) 
    by auto

  lemma mdpc_eqE: "\<phi> = \<psi> \<Longrightarrow> (states \<phi> = states \<psi> \<Longrightarrow> (\<And>s. s \<in> states \<phi> \<Longrightarrow> actions \<phi> s = actions \<psi> s) \<Longrightarrow> P) \<Longrightarrow> P"
    apply transfer
    by auto

  lemma mec_actions: "mec M \<phi> \<Longrightarrow> u \<in> states \<phi> \<Longrightarrow> actions \<phi> u = {a \<in> actions M u. set_pmf a \<subseteq> states \<phi>}"
  proof(rule ccontr)
    assume MEC: "mec M \<phi>"
    and US: "u \<in> states \<phi>"
    and ACT: "actions \<phi> u \<noteq> {a \<in> actions M u. set_pmf a \<subseteq> states \<phi>}"

    note EC = mec_ec[OF MEC]
    note LE = mec_le[OF MEC]

    from ACT have "actions \<phi> u \<subset> {a \<in> actions M u. set_pmf a \<subseteq> states \<phi>}" using ec_actions_sub[OF EC LE]
      by blast
    then obtain a where ADEF: "a \<in> actions M u" "set_pmf a \<subseteq> states \<phi>" "a \<notin> actions \<phi> u"
      by blast

    define \<phi>' where "\<phi>' \<equiv> map_actions (\<lambda> u' a'. if u' = u then insert a a' else a') \<phi>"

    have EN: "en \<phi> \<subseteq> en \<phi>'"
      unfolding \<phi>'_def
      by(force intro!: en_sub_map_actions)

    have [simp]: "states \<phi>' = states \<phi>"
      unfolding \<phi>'_def by auto

    have A1: "\<phi>' \<le> M"
      unfolding \<phi>'_def
      using states_mono LE
      apply(intro le_mdpcI)
      by (auto split: if_splits simp: ADEF le_mdpc_iff )


    have "sc \<phi>'"
      using EC EN by (auto simp: ec_def scD dest!: rtrancl_mono[of "en \<phi>"] intro!: scI)

    moreover have "closed_mdpc \<phi>'"
      unfolding \<phi>'_def closed_mdpc_map_actions using ADEF(2) 
      by (auto elim: mec_closed[OF MEC]) 

    ultimately have A2: "ec \<phi>'"
      by(auto intro: ecI)


    have A3: "\<phi> \<le> \<phi>'"
      unfolding \<phi>'_def
      apply(intro le_mdpcI)
      by auto

    have A4: "\<phi> \<noteq> \<phi>'" 
      unfolding \<phi>'_def 
      apply(rule notI)
      apply(erule mdpc_eqE)
      using ADEF(3) US 
      by fastforce

    from A1 A2 A3 A4 MEC show False
      unfolding mec_def by blast
  qed

  lemma actions_the_mec: "u \<in> states M \<Longrightarrow> actions (the_mec M u) u = {a \<in> actions M u. set_pmf a \<subseteq> states (the_mec M u)}"
    using mec_actions by fast

  lemma le_trivial_eq: "M \<le> trivial u \<longleftrightarrow> M = \<bottom> \<or> M = trivial u"
    by(fastforce simp: le_mdpc_iff eq_bot_iff_states mdpc_eqI dest!: subset_singletonD)

  lemma ecD1: "ec M \<Longrightarrow> sc M"
    unfolding ec_def by presburger

  lemma ecD2: "ec M \<Longrightarrow> closed_mdpc M"
    unfolding ec_def by presburger

  lemma trivial_eq_no_actions:
    assumes u: "u \<in> states M" and t: "\<And>v. v \<in> states M \<Longrightarrow> v = u" shows "M = trivial u \<longleftrightarrow> actions M u = {}"
  proof -
    {  
      fix t assume "t \<in> M" "t \<noteq> u"
      hence False
        using t by (auto) 
    }
    then have "states M = {u}"
      using u by auto
    then show ?thesis
      by (auto simp: u intro!: mdpc_eqI)
  qed

section \<open>Interval Iteration\<close>
text \<open> We first define a notion of an MDP with target and avoid state to simplify working with the mcsta data structure.
We then define an MDP in the reduced form that interval iteration expects.\<close>

subsection \<open>Extensions to Reachability Problems\<close>
  definition (in Reachability_Problem) \<open>lb_0 = (\<lambda>s \<in> S. if s \<in> S2 then 1 else 0)\<close>
  definition (in Reachability_Problem) \<open>ub_0 = (\<lambda>s \<in> S. if s \<in> S - S2 - S1 then 0 else 1)\<close>

  context Reachability_Problem
  begin
  
    lemma F_inf_restrict: \<open>F_inf x = F_inf (restrict x S)\<close>
      unfolding F_inf_def
      using K_closed
      by (fastforce simp: fun_eq_iff intro!: INF_cong nn_integral_cong_AE)
      
    lemma F_sup_restrict: \<open>F_sup x = F_sup (restrict x S)\<close>
      unfolding F_sup_def
      using K_closed
      by (fastforce simp: fun_eq_iff intro!: SUP_cong nn_integral_cong_AE)
    
    lemma F_inf_ge_iter:
      assumes \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<ge> n s\<close>
      shows \<open>F_inf x \<ge> n\<close>
          using assms
          by (subst F_inf_n[symmetric])
            (auto simp: F_inf_restrict[of x] 
              intro!: mono_F_inf[THEN monoD, THEN le_funD] le_funI)
    
    lemma F_inf_le_iter:
      assumes \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<le> n s\<close>
      shows \<open>F_inf x \<le> n\<close>
          using assms
          by (subst F_inf_n[symmetric])
            (auto simp: F_inf_restrict[of x] 
              intro!: mono_F_inf[THEN monoD, THEN le_funD] le_funI)
    
    lemma lb_le_Rn: \<open>lb_0 \<le> n\<close>
      unfolding lb_0_def
      by (rule le_funI) auto
    
    lemma ub_ge_Rn: \<open>n \<le> ub_0\<close>
      unfolding ub_0_def
      using n_le_1 n_nS12
      by (intro le_funI) auto
    
    definition F_inf_real :: \<open>('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real\<close> where
      \<open>F_inf_real x = (\<lambda>s \<in> S. enn2real (F_inf (\<lambda>s. ennreal (x s)) s))\<close>
    
    definition F_sup_real :: \<open>('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real\<close> where
      \<open>F_sup_real x = (\<lambda>s \<in> S. enn2real (F_sup (\<lambda>s. ennreal (x s)) s))\<close>
    
    lemma F_inf_real:
      assumes \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<ge> 0\<close> \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<le> 1\<close>
      shows \<open>F_inf_real x = (\<lambda>s\<in>S. if s \<in> S2 then 1 else if s \<in> S1 then (\<Sqinter>D\<in>K s. measure_pmf.expectation D x) else 0)\<close>
    proof -
      {
        fix s
        assume \<open>s \<in> S1 - S2\<close>
        hence \<open>F_inf_real x s = enn2real (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ s. ennreal (x s) \<partial>measure_pmf D)\<close>
          using S1_nS2 S1
          unfolding F_inf_real_def F_inf_def
          by auto
        also have \<open>\<dots> = (\<Sqinter>D\<in>K s. enn2real (\<integral>\<^sup>+ s. ennreal (x s) \<partial>measure_pmf D))\<close>
          apply (subst enn2real_Inf)
          using K_wf
          using measure_pmf.nn_integral_le_const[of \<open>ennreal 1\<close> x] assms
            apply (auto simp: AE_measure_pmf_iff less_top_ennreal image_image)
          by (metis Diff_iff S1 \<open>s \<in> S1 - S2\<close> ennreal_1 le_ennreal_iff set_pmf_closed subset_eq zero_less_one_class.zero_le_one)
        also have \<open>\<dots> = (\<Sqinter>D\<in>K s. measure_pmf.expectation D x)\<close>
          apply (auto simp: enn2real_Inf image_iff image_image intro!: INF_cong)
          apply (subst integral_eq_nn_integral)
          using K_closed S1_nS2 \<open>s \<in> S1 - S2\<close> S1
          by (auto intro!: assms)
        finally have \<open>F_inf_real x s = (\<Sqinter>D\<in>K s. measure_pmf.expectation D x)\<close> .
      }
      thus ?thesis
        apply (intro ext)
        subgoal for s
          apply (cases \<open>s  \<in> S1 - S2\<close>)
          using S1 apply auto[1]
          unfolding F_inf_real_def F_inf_def
          by auto
        done
    qed

    lemma F_sup_real:
      assumes \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<ge> 0\<close> \<open>\<And>s. s \<in> S \<Longrightarrow> x s \<le> 1\<close>
      shows \<open>F_sup_real x = (\<lambda>s\<in>S. if s \<in> S2 then 1 else if s \<in> S1 then (\<Squnion>D\<in>K s. measure_pmf.expectation D x) else 0)\<close>
    proof -
      {
        fix s
        assume \<open>s \<in> S1 - S2\<close>
          have \<open>s \<in> S\<close>
            using \<open>s \<in> S1 - S2\<close> S1 by auto
          have \<open>F_sup_real x s = enn2real (\<Squnion>D\<in>K s. \<integral>\<^sup>+ s. ennreal (x s) \<partial>measure_pmf D)\<close>
          using S1_nS2 S1 \<open>s \<in> S1 - S2\<close>
          unfolding F_sup_real_def F_sup_def
          by auto
        also have \<open>\<dots> = (\<Squnion>D\<in>K s. enn2real (\<integral>\<^sup>+ s. ennreal (x s) \<partial>measure_pmf D))\<close>
        proof -
          have \<open>(\<Squnion>D\<in>K s. \<integral>\<^sup>+ s. ennreal (x s) \<partial>measure_pmf D) \<le> 1\<close>
            using assms  set_pmf_closed \<open>s \<in> S\<close>
            by (auto intro!: SUP_least measure_pmf.nn_integral_le_const simp: AE_measure_pmf_iff)
          moreover have \<open>\<not>\<top> \<le> (1 :: ennreal)\<close>
            using ennreal_one_less_top ennreal_top_neq_one by order
          ultimately show ?thesis
            using K_wf
            by (auto simp del: Sup_eq_top_iff SUP_eq_top_iff simp: enn2real_Sup image_image)
        qed
          also have \<open>\<dots> = (\<Squnion>D\<in>K s. measure_pmf.expectation D x)\<close>
            apply (rule SUP_cong[OF refl])
            apply (subst integral_eq_nn_integral)
            subgoal by auto
            subgoal using assms K_closed \<open>s \<in> S\<close> set_pmf_closed
              by (auto intro!: assms simp:  AE_measure_pmf_iff)
            by force
        finally have \<open>F_sup_real x s = (\<Squnion>D\<in>K s. measure_pmf.expectation D x)\<close> .
      }
      thus ?thesis
        apply (intro ext)
        subgoal for s
          using S1
          unfolding F_sup_real_def F_sup_def
          by (cases \<open>s \<in> S1 - S2\<close>) auto
        done
    qed
  
  end


subsection \<open>A Standard Data Structure for Abstract MECs with Reachability\<close>

  lifting_forget mdpc.lifting

  typedef 'v mdptc = "UNIV :: ('v mdpc \<times> 'v set \<times> 'v set) set"
    by auto

  setup_lifting type_definition_mdptc

  lift_definition to_mdpc :: "'v mdptc \<Rightarrow> 'v mdpc"
    is fst .

  declare [[coercion to_mdpc]]

  lift_definition avoids :: "'v mdptc \<Rightarrow> 'v set"
    is "fst o snd" .

  lift_definition targets :: "'v mdptc \<Rightarrow> 'v set"
    is "snd \<circ> snd" .

  definition computes :: "'v mdptc \<Rightarrow> 'v set" where
    "computes \<M> = states \<M> - avoids \<M> - targets \<M>"

  locale MDPC_Reach_Avoid_defs = 
    fixes \<M>::"'v mdptc"
  begin



  end

  lemma computes_states[simp]: "u \<in> computes \<M> \<Longrightarrow> u \<in> states \<M>"
    unfolding computes_def by blast

  lemma computes_nAvd[simp]: "u \<in> computes \<M> \<Longrightarrow> u \<notin> avoids \<M>"
    unfolding computes_def by blast

  lemma computes_nTgt[simp]: "u \<in> computes \<M> \<Longrightarrow> u \<notin> targets \<M>"
    unfolding computes_def by blast

  lemma computesI: "u \<in> states (to_mdpc \<M>) \<Longrightarrow> u \<notin> avoids \<M> \<Longrightarrow> u \<notin> targets \<M> \<Longrightarrow> u \<in> computes \<M>"
    unfolding computes_def by blast

  lemma computes_Tgt_disj[simp,dest]: "u \<in> computes \<M> \<Longrightarrow> u \<in> targets \<M> \<Longrightarrow> False"
    unfolding computes_def by blast

  lemma computes_Avd_disj[simp,dest]: "u \<in> computes \<M> \<Longrightarrow> u \<in> avoids \<M> \<Longrightarrow> False"
    unfolding computes_def by blast

  lemma state_cases:
    obtains \<open>s \<in> computes \<M>\<close> | \<open>s \<in> targets \<M>\<close> | \<open>s \<in> avoids \<M>\<close> | \<open>s \<notin> states \<M>\<close>
    by (meson computesI)

  locale MDPC_Reach_Avoid = MDPC_Reach_Avoid_defs \<M> + Finite_MDP \<M> for \<M>::"'v mdptc" +
    assumes
      Avd_states: \<open>avoids \<M> \<subseteq> states \<M>\<close> and
      Tgt_states: \<open>targets \<M> \<subseteq> states \<M>\<close> and
      AT_disj: \<open>targets \<M> \<inter> avoids \<M> = {}\<close> and
      Tgt_loop: "u \<in> targets \<M> \<Longrightarrow> actions \<M> u = {return_pmf u}" and
      Avd_loop: "u \<in> avoids \<M> \<Longrightarrow> actions \<M> u = {return_pmf u}"
  begin

    lemma Avd_Tgt_disj[simp]: "u \<in> avoids \<M> \<Longrightarrow> u \<in> targets \<M> \<Longrightarrow> False"
      using AT_disj by blast

    lemma Avd_sub_states[simp]: "u \<in> avoids \<M> \<Longrightarrow> u \<in> states \<M>"
      using Avd_states by blast

    lemma Tgt_sub_states[simp]: "u \<in> targets \<M> \<Longrightarrow> u \<in> states \<M>"
      using Tgt_states by blast



    sublocale R: Reachability_Problem "actions' \<M>" "states \<M>" "computes \<M>" "targets \<M>"
      apply unfold_locales 
      by auto

    definition n_real :: "'v \<Rightarrow> real" where 
      "n_real = (\<lambda>s \<in> states \<M>. enn2real (R.n s))"
    
    definition p_real :: "'v \<Rightarrow> real" where 
      "p_real = (\<lambda>s \<in> states \<M>. enn2real (R.p s))"

    lemma Avd_alt: "avoids \<M> = states \<M> - computes \<M> - targets \<M>"
      unfolding computes_def
      using Avd_states AT_disj
      by auto

    lemma actions'_states: \<open>u \<in> states \<M> \<Longrightarrow> actions' \<M> u = actions \<M> u\<close>
      unfolding actions'_def by auto
    
    lemma actions_finite': \<open>u \<in> states \<M> \<Longrightarrow> finite' (actions \<M> u)\<close>
      using finite_actions_M actions_neq_empty_M
      by auto
    
    
    lemma F_inf_le_iter':
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<le> n_real t\<close> 
      shows \<open>R.F_inf_real x \<le> n_real\<close>
      using  R.n_not_inf assms
      unfolding R.F_inf_real_def n_real_def
      apply (auto intro!: le_funI enn2real_leI)
      apply (subst ennreal_enn2real)
      using R.n_not_inf                                                     
       apply (auto simp: less_top[symmetric]  intro!: ennreal_leI R.F_inf_le_iter[THEN le_funD])
      by (metis ennreal_leI R.real_n)
    
    lemma F_sup_nS[simp]: \<open>s \<notin> states \<M> \<Longrightarrow> R.F_sup x s = undefined\<close>
      unfolding R.F_sup_def
      by auto
    
    lemma F_sup_le_iter:
      assumes \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> x s \<le> R.p s\<close> 
      shows  \<open>R.F_sup x \<le> R.p\<close>
    proof -
      have \<open>restrict x (states \<M>) \<le> R.p\<close>
        using assms
        unfolding R.p_def
        by (auto intro!: le_funI)
      hence \<open>R.F_sup (restrict x (states \<M>)) \<le> R.F_sup R.p\<close>
        using R.mono_F_sup monoD by auto
      thus \<open>R.F_sup x \<le> R.p\<close>
        using R.F_sup_restrict R.F_sup_p by auto 
    qed
    
    lemma F_sup_ge_iter:
      assumes \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> x s \<ge> R.p s\<close> 
      shows  \<open>R.F_sup x \<ge> R.p\<close>
    proof -
      have \<open>restrict x (states \<M>) \<ge> R.p\<close>
        using assms
        unfolding R.p_def
        by (auto intro!: le_funI)
      hence \<open>R.F_sup (restrict x (states \<M>)) \<ge> R.F_sup R.p\<close>
        using R.mono_F_sup monoD by auto
      thus \<open>R.F_sup x \<ge> R.p\<close>
        using R.F_sup_restrict R.F_sup_p by auto 
    qed
    
    
    lemma F_sup_le_iter':
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<le> p_real t\<close> 
      shows \<open>R.F_sup_real x \<le> p_real\<close>
      using R.p_not_inf assms
      unfolding R.F_sup_real_def p_real_def
      apply (auto intro!: le_funI enn2real_leI)
      apply (subst ennreal_enn2real)
      using R.p_not_inf
       apply (auto simp: less_top[symmetric]  intro!: ennreal_leI F_sup_le_iter[THEN le_funD])
      by (metis ennreal_leI R.real_p)
    
    
    lemma F_inf_le_iter'_state:
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<le> n_real t\<close> \<open>s \<in> states M\<close>
      shows \<open>R.F_inf_real x s \<le> n_real s\<close>
      using F_inf_le_iter' assms
      unfolding le_fun_def
      by auto
    
    
    lemma F_sup_le_iter'_state:
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<le> p_real t\<close> \<open>s \<in> states M\<close>
      shows \<open>R.F_sup_real x s \<le> p_real s\<close>
      using F_sup_le_iter' assms
      unfolding le_fun_def
      by auto
    
    lemma Ball_imp_Bex: \<open>X \<noteq> {} \<Longrightarrow> \<forall>x \<in> X. P x \<Longrightarrow> \<exists>x \<in> X. P x\<close>
      by auto
    
    lemma nn_integral_lt_inf_finite:
      assumes "\<And>s. s \<in> set_pmf P \<Longrightarrow> f s < \<infinity>" \<open>finite (set_pmf P)\<close>
      shows "integral\<^sup>N (measure_pmf P) f < \<infinity>"
    proof -
                                          
      have \<open>integral\<^sup>N (measure_pmf P) f \<le> Max (f ` set_pmf P)\<close>
        apply (rule  measure_pmf.nn_integral_le_const)
        using assms
        by (auto intro!: Max.coboundedI simp: AE_measure_pmf_iff)
    
      moreover have \<open>Max (f ` set_pmf P) < \<infinity>\<close>
        apply (subst Max_less_iff)
        using assms set_pmf_not_empty 
        by auto
      ultimately show ?thesis by auto
    qed
    
    lemma F_inf_ninfty: 
      assumes \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> x s < \<infinity>\<close> \<open>s \<in> states \<M>\<close>
      shows \<open>R.F_inf x s < \<infinity>\<close>
      using assms actions_neq_empty_M 
      unfolding R.F_inf_def
      by (auto simp: less_top[symmetric]  closed_M closed_mdpcD set_pmf_finite finite_nn_integral_lt_topI)
      
    lemma F_sup_ninfty: 
      assumes \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> x s < \<infinity>\<close> \<open>s \<in> states \<M>\<close>
      shows \<open>R.F_sup x s < \<infinity>\<close>
    proof -
      have \<open>(\<Squnion>D\<in>actions' \<M> s. integral\<^sup>N (measure_pmf D) x) < \<infinity>\<close> if \<open>s \<in> states \<M>\<close> for s
        apply (rule finite_imp_Sup_less[of _ \<open>integral\<^sup>N (measure_pmf (SOME D. D \<in> actions' \<M> s)) x\<close>])
        subgoal using \<open>s \<in> states \<M>\<close> by (auto intro!: finite_imageI finite_actions_M)
        subgoal using K_wf by (auto simp: image_iff some_in_eq)
        subgoal using set_pmf_finite assms that set_pmf_closed by (auto intro!: nn_integral_lt_inf_finite[unfolded infinity_ennreal_def])
        done
      thus ?thesis
        using assms
        unfolding R.F_sup_def
        by auto
    qed
    
    
    lemma F_inf_ge_iter':
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<ge> n_real t\<close> 
      shows \<open>R.F_inf_real x \<ge> n_real\<close>
      using  R.n_not_inf assms
      unfolding R.F_inf_real_def n_real_def
      apply (auto intro!: le_funI enn2real_leI )
      apply (subst ennreal_enn2real)
      subgoal using F_inf_ninfty by auto
      subgoal
        apply (rule R.F_inf_ge_iter[THEN le_funD])
      using R.n_not_inf F_inf_ninfty
       apply (auto simp: less_top[symmetric]  intro!:  ennreal_leI R.F_inf_ge_iter[THEN le_funD] le_funI)
      by (metis ennreal_leI R.real_n)
      done
    
    
    lemma F_sup_ge_iter':
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<ge> p_real t\<close> 
      shows \<open>R.F_sup_real x \<ge> p_real\<close>
      using R.p_not_inf assms
      unfolding R.F_sup_real_def p_real_def
      apply (auto intro!: le_funI enn2real_leI )
      apply (subst ennreal_enn2real)
      subgoal using F_sup_ninfty by auto
      subgoal
        apply (rule F_sup_ge_iter[THEN le_funD])
      using R.n_not_inf F_inf_ninfty
       apply (auto simp: less_top[symmetric]  intro!:  ennreal_leI F_sup_ge_iter[THEN le_funD] le_funI)
      by (metis ennreal_leI R.real_p)
      done
    
    
    lemma F_inf_ge_iter'_state:
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<ge> n_real t\<close> \<open>s \<in> states M\<close>
      shows \<open>R.F_inf_real x s \<ge> n_real s\<close>
      using F_inf_ge_iter' assms
      unfolding le_fun_def
      by auto
    
    
    lemma F_sup_ge_iter'_state:
      assumes \<open>\<And>t. t \<in> states \<M> \<Longrightarrow> x t \<ge> p_real t\<close> \<open>s \<in> states M\<close>
      shows \<open>R.F_sup_real x s \<ge> p_real s\<close>
      using F_sup_ge_iter' assms
      unfolding le_fun_def
      by auto
    
    
    lemma lb_le_n_real: \<open>R.lb_0 \<le> n_real\<close>
      unfolding R.lb_0_def n_real_def
      by (auto intro!: le_funI)
    
    
    lemma ub_ge_n_real: \<open>n_real \<le> R.ub_0\<close>
      unfolding R.ub_0_def n_real_def
      using R.n_le_1 
      by (auto intro!: R.n_nS12 le_funI enn2real_mono simp flip: enn2real_1 enn2real_0)

    
    lemma lb_le_p_real: \<open>R.lb_0 \<le> p_real\<close>
      unfolding R.lb_0_def p_real_def
      by (auto intro!: le_funI)
    
    
    lemma ub_ge_p_real: \<open>p_real \<le> R.ub_0\<close>
      unfolding R.ub_0_def p_real_def
      using R.p_le_1
      apply (auto intro!: le_funI enn2real_mono simp flip: enn2real_1)
      by (simp add: R.p_nS12)
  
  end

  context MDPC_Reach_Avoid (*TODO: Do I even need u_AT?*)
  begin

    lemma Inr_actions[simp]: \<open>s \<in> states \<M> \<Longrightarrow> s \<notin> computes \<M> \<Longrightarrow> actions \<M> s = {return_pmf s}\<close>
      unfolding computes_def
      using Avd_loop Tgt_loop
      by auto
    
    lemma Avd_the_mec_loop[simp]: "u \<in> avoids \<M> \<Longrightarrow> the_mec \<M> u = loop u"
      using Avd_states by(auto simp: Avd_loop intro!: the_mec_eqI mec_loop)

    lemma Avd_bot: \<open>u \<in> avoids \<M> \<Longrightarrow> u \<in> bottoms \<M>\<close>
      using Avd_loop Avd_states
      by (metis Avd_the_mec_loop bmec_loop in_bottoms_the_mec subsetD)

    lemma Tgt_the_mec_loop[simp]: "u \<in> targets \<M> \<Longrightarrow> the_mec \<M> u = loop u"
      using Tgt_states by(auto simp: Tgt_loop intro!: the_mec_eqI mec_loop)

    lemma None_bot: \<open>u \<in> targets \<M> \<Longrightarrow> u \<in> bottoms \<M>\<close>
      using Tgt_loop Tgt_states
      by (metis Tgt_the_mec_loop bmec_loop in_bottoms_the_mec subsetD)
    lemma None_not_triv: \<open>u \<in> targets \<M> \<Longrightarrow> u \<notin> trivials \<M>\<close>
      using None_bot trivials_bottoms_disj 
      by auto

    lemma n_fin_0_Some[simp]:\<open>u \<in> states \<M> \<Longrightarrow> u \<notin> targets \<M> \<Longrightarrow> R.n_fin 0 u = 0\<close>
      using R.n_fin_0 by auto
    
    lemma n_fin_not_triv[simp]:
      assumes \<open>s \<notin> trivials \<M>\<close> \<open>s \<notin> targets \<M>\<close> \<open>s \<in> states \<M>\<close>
      shows \<open>R.n_fin i s = 0\<close>
      using assms
    proof (induction i arbitrary: s)
      case 0
      then show ?case
        by auto
    next
      case (Suc i)
      have \<open>s \<in> the_mec \<M> s\<close> \<open>the_mec \<M> s \<le> \<M>\<close>
        using Suc.prems(3) using Suc(4) mec_le by blast+
      then obtain a where a: \<open>a \<in> actions (the_mec \<M> s) s\<close>
        by (meson Suc(2) Suc(4) all_not_in_conv ec_def in_trivials_the_mec mec_def sc_eq_trivial the_mec)
      have \<open>mec \<M> (the_mec \<M> s)\<close>
        using Suc(4) by blast
      have a_M: \<open>a \<in> actions \<M> s\<close>
        using a \<open>the_mec \<M> s \<le> \<M>\<close> 
        by (auto simp: le_mdpc_iff)

      have a_mec: \<open>set_pmf a \<subseteq> the_mec \<M> s\<close>
        by (meson \<open>a \<in> actions (the_mec \<M> s) s\<close> \<open>mec \<M> (the_mec \<M> s)\<close> \<open>s \<in> states (the_mec \<M> s)\<close> mec_closed subsetI)
      have \<open>R.n_fin (Suc i) s \<le> nn_integral a (R.n_fin i)\<close>
        using Suc a_M 
        apply(cases "s \<in> avoids \<M>")
        by (auto intro!: INF_lower  simp: R.n_fin_Suc_S1 Avd_alt)
      moreover have \<open>s' \<in> the_mec \<M> s \<Longrightarrow> R.n_fin i s' = 0\<close> for s'
        apply(cases "s' \<in> avoids \<M>")
        subgoal
          using Avd_alt R.n_fin_nS12 by blast
        subgoal
          apply (rule Suc)
          subgoal 
            using a_M a_mec
            by (metis \<open>mec \<M> (the_mec \<M> s)\<close> a actions_trivial ex_in_conv in_trivials_the_mec the_mec_eqI)
          subgoal 
            using Suc(3-4) a  
            by(clarsimp dest!: the_mec_eq[symmetric]) auto
          subgoal
            using \<open>the_mec \<M> s \<le> \<M>\<close> states_mono 
            by auto
          done
        done
      moreover then have \<open>nn_integral a (R.n_fin i) = 0\<close>
        using a_mec
        by (auto intro!: nn_integral_zero')+
      ultimately show ?case
        by auto
    qed
    
    
    lemma None_nS\<^sub>e: \<open>u \<in> targets \<M> \<Longrightarrow> u \<notin> R.S\<^sub>e\<close>
      unfolding R.S\<^sub>e_def by auto
    
    lemma v_None[simp]: \<open>cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> targets \<M> \<Longrightarrow> R.v cfg = 1\<close>
      by auto
    
    lemma p_None[simp]: \<open>u \<in> targets \<M> \<Longrightarrow> R.p u = 1\<close>
      by auto
    
    lemma the_mec_unique: \<open>s \<in> states \<M> \<Longrightarrow> t \<in> the_mec \<M> s \<Longrightarrow> the_mec \<M> t = the_mec \<M> s\<close>
      by blast
    
    lemma(in -) mecI: 
      assumes \<open>ec m\<close> \<open>m \<le> M\<close> \<open>\<And>m'. ec m' \<Longrightarrow> m' \<le> M \<Longrightarrow> m \<le> m' \<Longrightarrow> m' \<le> m\<close>
      shows \<open>mec M m\<close>
      using assms unfolding mec_def by auto
    
    lemma (in Finite_MDP) E_en: \<open>s \<in> states M \<Longrightarrow> (s, s') \<in> E \<longleftrightarrow> (s, s') \<in> en M\<close>
      unfolding en_def E_def by auto
    
    lemmas (in Reachability_Problem) 
      refl[of p_fin, cong] refl[of valid_cfg, cong] refl[of simple, cong]
      refl[of p, cong] refl[of n, cong] refl[of v, cong] 
      refl[of S\<^sub>e, cong]
    
    lemmas (in Finite_Markov_Decision_Process)
      refl[of valid_cfg, cong]
    
    
    lemma ec_None: \<open>u \<in> targets \<M> \<Longrightarrow> ec (restrict_states {u} \<M>)\<close>
      using Tgt_states by (auto intro!: scI ecI simp: closed_mdpc_def en_def Tgt_loop)
    
    
    lemma states_sc_None:
      assumes \<open>sc m\<close> \<open>m \<le> \<M>\<close> \<open>u \<in> m\<close> \<open>u \<in> targets \<M>\<close>
      shows \<open>states m = {u}\<close>
    proof -
      have \<open>actions m u \<subseteq> {return_pmf u}\<close>
        using assms Tgt_loop
        by (fastforce simp: le_mdpc_iff)
      thus ?thesis
        using sc_eq_loop[of m u] assms sc_eq_trivial
        by fastforce
    qed
    
    lemma states_ec_None:
      assumes \<open>ec m\<close> \<open>m \<le> \<M>\<close> \<open>u \<in> m\<close> \<open>u \<in> targets \<M>\<close>
      shows \<open>states m = {u}\<close>
      using states_sc_None assms unfolding ec_def 
      by auto
    
    lemma mec_None: assumes "u \<in> targets \<M>" shows \<open>mec \<M> (restrict_states {u} \<M>)\<close>
    proof (rule mecI)
      fix m'
      assume \<open>ec m'\<close> \<open>m' \<le> \<M>\<close> \<open>restrict_states {u} \<M> \<le> m'\<close>
      hence \<open>u \<in> states m'\<close>
        using assms Tgt_states
        unfolding le_mdpc_iff  
        by auto
      have \<open>states m' \<subseteq> states \<M>\<close>
        using \<open>m' \<le> \<M>\<close> 
        unfolding le_mdpc_iff 
        by auto
      hence \<open>states m' \<subseteq> states (restrict_states {u} \<M>)\<close>
        using \<open>u \<in> states m'\<close> \<open>ec m'\<close> \<open>m' \<le> \<M>\<close> states_ec_None assms by auto
      thus \<open>m' \<le> restrict_states {u} \<M>\<close>
        using states_ec_None[OF \<open>ec m'\<close> \<open>m' \<le> \<M>\<close>] \<open>u \<in> states m'\<close> assms
        unfolding le_mdpc_iff 
        by (metis \<open>m' \<le> \<M>\<close> actions_restrict_states bot_least in_states le_mdpc_iff)
    qed (auto simp: assms ec_None restrict_states_le)
    
    lemma the_mec_None: \<open>u \<in> targets \<M> \<Longrightarrow> the_mec \<M> u = (restrict_states {u} \<M>)\<close>
      using mec_None by fastforce
    
    lemma the_mec_eq_None_iff[simp]: \<open>u \<in> targets \<M> \<Longrightarrow> x \<in> states \<M> \<Longrightarrow> the_mec \<M> x = the_mec \<M> u \<longleftrightarrow> x = u\<close>
      using the_mec_None states_the_mec by force
  
  end


subsection \<open>Reduced MDPs for Interval Interation\<close>
  locale Reduced_MDP_Target = MDPC_Reach_Avoid \<M> for \<M>::"'v mdptc" +
    assumes 
      computes_triv: \<open>\<And>s. s \<in> computes \<M> \<Longrightarrow> s \<in> trivials \<M>\<close> 
  begin    
    lemma trivials_computes_mem: \<open>s \<in> trivials \<M> \<longleftrightarrow> s \<in> computes \<M>\<close>
      using bmec_loop[of s \<M>, OF trivials_in_states Inr_actions] bmec_not_triv computes_triv
      by force

    lemma trivials_computes: "trivials \<M> = computes \<M>"
      using trivials_computes_mem by blast

    lemma the_mec_eq_trivial: "s \<in> states \<M> \<Longrightarrow> s \<notin> avoids \<M> \<Longrightarrow> s \<notin> targets \<M> \<Longrightarrow> the_mec \<M> s = trivial s"
      using computes_triv[OF computesI, unfolded in_trivials_the_mec] by presburger

    lemma bottoms_Avd_Tgt_mem: "s \<in> bottoms \<M> \<longleftrightarrow> s \<in> avoids \<M> \<union> targets \<M>"
      apply(rule iffI)
      subgoal
        apply(clarsimp simp: in_bottoms_the_mec )
        using the_mec_eq_trivial trivial_not_bmec ccontr[of "s \<in> avoids \<M>"]
        by force
      subgoal
        using Avd_bot None_bot by blast
      done

    lemma bottoms_Avd_Tgt: "bottoms \<M> = avoids \<M> \<union> targets \<M>"
      using bottoms_Avd_Tgt_mem by blast


    lemma triv_or_bot: "states \<M> = trivials \<M> \<union> bottoms \<M>"
      using trivials_computes Avd_bot None_bot bottoms_subset_states[of \<M>]
      unfolding computes_def by auto


    lemma loop_Avd: \<open>s \<in> avoids \<M> \<Longrightarrow> loop s \<le> \<M>\<close>
      by (rule le_mdpcI) (auto simp: Avd_loop Avd_states[THEN set_mp])

    lemma loop_Tgt: \<open>s \<in> targets \<M> \<Longrightarrow> loop s \<le> \<M>\<close>
      by (rule le_mdpcI) (auto simp: Tgt_loop Tgt_states[THEN set_mp])
    
    lemma restrict_Avd[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> restrict_states {s} \<M> = loop s\<close>
      by (auto intro!: mdpc_eqI simp: Avd_loop Avd_states[THEN set_mp])

    lemma restrict_Tgt[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> restrict_states {s} \<M> = loop s\<close>
      by (auto intro!: mdpc_eqI simp: Tgt_loop Tgt_states[THEN set_mp])
    
    lemma triv_not_bot[simp]: \<open>s \<in> trivials \<M> \<Longrightarrow> s \<notin> bottoms \<M>\<close>
          using trivials_bottoms_disj
          by auto
    
    lemmas Avd_bot None_bot[simp]
    
    lemma state_fn_cases:
      obtains \<open>s \<in> trivials \<M>\<close> | \<open>s \<in> targets \<M>\<close> | \<open>s \<in> avoids \<M>\<close> | \<open>s \<notin> states \<M>\<close>
      using triv_or_bot bottoms_Avd_Tgt by blast
    
    lemma state_fn_eqI[intro]:
      assumes \<open>\<And>s. s \<in> trivials \<M> \<Longrightarrow> x s = y s\<close>
        and \<open>\<And>s. s \<in> targets \<M> \<Longrightarrow> x s = y s\<close>
        and \<open>\<And>s. s \<in> avoids \<M> \<Longrightarrow> x s = y s\<close>
        and \<open>\<And>s. s \<notin> states \<M> \<Longrightarrow> x s = y s\<close>
      shows \<open>x = y\<close>
      apply(rule ext) 
      subgoal for s
        apply(cases s rule: state_fn_cases)
        using assms by auto
      done
    
    lemma state_fn_leI[intro]:
      assumes \<open>\<And>s. s \<in> trivials \<M> \<Longrightarrow> x s \<le> y s\<close>
        and \<open>\<And>s. s \<in> targets \<M> \<Longrightarrow> x s \<le> y s\<close>
        and \<open>\<And>s. s \<in> avoids \<M> \<Longrightarrow> x s \<le> y s\<close>
        and \<open>\<And>s. s \<notin> states \<M> \<Longrightarrow> x s \<le> y s\<close>
      shows \<open>x \<le> y\<close>
      apply(rule le_funI)
      subgoal for s
        apply(cases s rule: state_fn_cases)
        using assms by auto
      done
    
    subsection \<open>Reachability Problems\<close>
    \<comment> \<open>Reachability Problem: Reach Inr True, avoid Inr False\<close>


    \<comment> \<open>Models the Safety Problem: Reach Inr False, avoid Inr True\<close>
    sublocale S: Reachability_Problem "actions' \<M>" "states \<M>" \<open>computes \<M>\<close> \<open>avoids \<M>\<close>
      by unfold_locales (auto simp: Avd_states computes_def trivials_computes)
    
    sublocale R_G: Reduced_MDP \<M>
      using triv_or_bot
      by unfold_locales auto
    
    lemma n_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.n s = 0\<close>
      apply (rule R.n_eq_0_closed[of s "avoids \<M>"])
      using Avd_states AT_disj Avd_loop
      by auto 
    
    lemma n_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> R.n s = 1\<close>
      using R.n_S2 by auto

    lemma 
      n_fin_0_triv[simp]: \<open>s \<in> computes \<M> \<Longrightarrow> R.n_fin 0 s = 0\<close> and
      n_fin_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.n_fin i s = 0\<close>
      using R.S1_nS2[of s, folded computes_def] R.n_fin_0[of s] Avd_alt R.n_fin_nS12
      by auto

    lemma v_fin_0_triv[simp]: \<open>cfg \<in> cfg_on s \<Longrightarrow> s \<in> trivials \<M> \<Longrightarrow> R.v_fin 0 cfg = 0\<close>
      by (subst R.v_fin_0)  (auto simp: trivials_computes)
    
    lemma v_fin_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> R.v_fin i cfg = 1\<close>
      using R.v_fin_S2 cfg_onD_state R.S2 by blast
    
    lemma v_fin_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> R.v_fin i cfg = 0\<close>
      using Avd_alt R.v_fin_nS12 by fastforce
    
    lemma S_v_fin_0_triv[simp]: \<open>cfg \<in> cfg_on s \<Longrightarrow> s \<in> trivials \<M> \<Longrightarrow> S.v_fin 0 cfg = 0\<close>
      apply (rule S.v_fin_0) 
      subgoal
        by blast
      subgoal
        using trivials_computes computes_def cfg_onD_state 
        by force
      done      
    
    lemma S_v_fin_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> S.v_fin i cfg = 0\<close>
      apply(rule S.v_fin_nS12) 
      using R.S2 apply blast
      using R.S1_nS2 cfg_onD_state apply blast
      by (simp add: Avd_alt)
    
    lemma S_v_fin_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> S.v_fin i cfg = 1\<close>
      apply(rule S.v_fin_S2)
      using S.S2 by auto
    
    lemma 
      p_fin_0_triv[simp]: \<open>s \<in> trivials \<M> \<Longrightarrow> R.p_fin 0 s = 0\<close> and
      p_fin_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.p_fin i s = 0\<close> and
      p_fin_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> R.p_fin i s = 1\<close>
      using Avd_states Tgt_states
      by (auto simp: R.p_fin_v_fin)
    
    lemma 
      S_p_fin_0_triv[simp]: \<open>s \<in> trivials \<M> \<Longrightarrow> S.p_fin 0 s = 0\<close> and
      S_p_fin_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> S.p_fin i s = 1\<close> and
      S_p_fin_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> S.p_fin i s = 0\<close>
      using S.S1_nS2 valid_cfgI Avd_states Tgt_states
      by (auto simp: S.p_fin_v_fin trivials_computes)
    
    lemma 
      S_n_fin_0_triv[simp]: \<open>s \<in> trivials \<M> \<Longrightarrow> S.n_fin 0 s = 0\<close> and
      S_n_fin_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> S.n_fin i s = 1\<close> and
      S_n_fin_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> S.n_fin i s = 0\<close> 
      using S.S1_nS2 valid_cfgI Avd_states Tgt_states
      by (auto simp: S.n_fin_v_fin trivials_computes)
    
    lemma
      F_sup_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> R.F_sup x s = 1\<close> and
      F_sup_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.F_sup x s = 0\<close>
      unfolding R.F_sup_def
      using Tgt_states Avd_states AT_disj
      by auto

    lemma 
      F_inf_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> R.F_inf x s = 1\<close> and
      F_inf_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.F_inf x s = 0\<close>
      using Avd_states Tgt_states AT_disj
      unfolding R.F_inf_def by (auto simp: S.S1_nS2)

    subsection \<open>Uniqueness of Fixed Points\<close>
    text \<open>We now show that within a reduced MDP, \<^term>\<open>R.F_\<sigma>\<close>, and \<^term>\<open>R.F_inf\<close> have a unique fixed point.\<close>
    lemmas R_G.R.S1D[rule del]
    
    subsubsection \<open>\<^const>\<open>R.F_\<sigma>\<close>\<close>
    
    lemma F_\<sigma>_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> R.F_\<sigma> \<sigma> v s = 1\<close>
      using Tgt_states
      by (auto simp: R.F_\<sigma>_def)
    
    lemma F_\<sigma>_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.F_\<sigma> \<sigma> v s = 0\<close>
      using Avd_states AT_disj
      by (auto simp: R.F_\<sigma>_def trivials_computes computes_nAvd)


    lemma F_\<sigma>_fp_unique:
      assumes \<open>R.F_\<sigma> \<sigma> v = v\<close> \<open>\<sigma> \<in> Pi (states \<M>) (actions' \<M>)\<close> and 
        v_le: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> v s \<noteq> \<infinity>\<close>
      shows \<open>v = R.v o (simple \<sigma>)\<close>
    proof -
      have v_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> v s = 0\<close> for s
        using assms F_\<sigma>_False
        unfolding fun_eq_iff
        by (metis (no_types, lifting))
    
      have v_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> v s = 1\<close> for s
        using assms F_\<sigma>_True
        unfolding fun_eq_iff
        by (metis (no_types, lifting))
    
      note R.R_eq_on_statesI[rule del]
    
      have v_nS: \<open>s \<notin> states \<M> \<Longrightarrow> v s = undefined\<close> for s
        using assms R.F_\<sigma>_undefined[of s \<sigma> v]
        by (auto simp add: fun_eq_iff split: if_splits)
    
      have ge: \<open>v \<ge> R.v o (simple \<sigma>)\<close>
        using assms R.v_eq_lfp_F_\<sigma>[of \<sigma>]
        by (simp add: lfp_lowerbound)

      moreover have \<open>v \<le> R.v o (simple \<sigma>)\<close>
      proof -
        define X where \<open>X = maximal (\<lambda>s. v s - R.v (simple \<sigma> s)) (states \<M>)\<close>
    
        hence \<open>X \<noteq> {}\<close>
          unfolding X_def
          using finite_states_M S_not_empty
          by (intro maximal_ne) auto
    
        show ?thesis
        proof (cases \<open>\<forall>s \<in> states \<M>. v s - R.v (simple \<sigma> s) = 0\<close>)
          case True
          hence "\<forall>s \<in> states \<M>. R.v (simple \<sigma> s) = v s"
            using ge 
            by (auto simp: le_fun_def fun_eq_iff dest: ennreal_minus_eq_0 intro: antisym)
          then show ?thesis
            using v_nS assms 
            by (auto simp: fun_eq_iff le_fun_def simple_valid_cfg_iff R.v_def)
        next
          case False
          then obtain s' where \<open>s' \<in> states \<M>\<close> \<open>v s' - R.v (simple \<sigma> s') \<noteq> 0\<close>
            by auto
          hence neq: \<open>v s - R.v (simple \<sigma> s) \<noteq> 0\<close> if \<open>s \<in> X\<close> for s
            using maximalD2[of s \<open>(\<lambda>s. v s - R.v (simple \<sigma> s))\<close> \<open>states \<M>\<close> s'] that
            by (auto simp: X_def)
    
          hence \<open>s' \<in> X\<close> if \<open>s' \<in> set_pmf (\<sigma> s)\<close> \<open>s \<in> X\<close> for s s'
          proof -
            {
              have s: \<open>s \<in> states \<M>\<close>
                using that
                unfolding X_def
                by (meson maximalD1)
    
              hence \<open>s \<in> trivials \<M>\<close>
                using neq assms that 
                by (cases s rule: state_fn_cases) fastforce+
    
              { assume diff_s': \<open>v s' - R.v (simple \<sigma> s') < v s - R.v (simple \<sigma> s)\<close> \<open>s' \<in> \<sigma> s\<close>
    
                have diff_int_le: \<open>\<integral>\<^sup>+ s. v s - R.v (simple \<sigma> s) \<partial>measure_pmf (\<sigma> s) \<noteq> \<top>\<close>
                  using v_le[of ] Pi_closed[OF assms(2), of s] assms(2) s 
                  by (intro finite_nn_integral_lt_topI) (auto intro: set_pmf_finite)
    
                have le_one: \<open>integral\<^sup>N (measure_pmf (\<sigma> s)) (R.v \<circ> simple \<sigma>) \<le> 1\<close>
                  using Pi_closed[OF assms(2)] s simple_valid_cfg[OF assms(2)]
                  by (auto intro!: R.v_le_1 measure_pmf.nn_integral_le_const simp: AE_measure_pmf_iff)
                have \<open>v s - R.v (simple \<sigma> s) = integral\<^sup>N (\<sigma> s) v - integral\<^sup>N (\<sigma> s) (R.v o (simple \<sigma>))\<close>
                  using assms \<open>s \<in> trivials \<M>\<close>  R.F_\<sigma>_v[OF assms(2)] s R.S1_nS2
                  apply (clarsimp simp: trivials_computes)
                  using R.F_\<sigma>_cont 
                  by (metis R.S1D R.S1_nS2 o_def)
                also have \<open>\<dots> = integral\<^sup>N (\<sigma> s) (\<lambda>s. v s - (R.v (simple \<sigma> s)))\<close>
                  using le_one ge diff_int_le neq_top_trans[OF ennreal_one_neq_top] 
                  by (subst nn_integral_diff[symmetric]) (auto simp: comp_def le_fun_def AE_measure_pmf_iff)
                also have \<open>\<dots> < integral\<^sup>N (\<sigma> s) (\<lambda>s'. v s - R.v (simple \<sigma> s))\<close>
                  apply (intro nn_integral_less) 
                  subgoal by simp
                  subgoal by simp
                  subgoal
                    using diff_int_le 
                    by auto
                  subgoal 
                    apply clarsimp
                    using  Pi_closed[OF _ s] assms(2) maximalD2[OF that(2)[unfolded X_def]]
                    by presburger
                  subgoal
                    using diff_s'[unfolded linorder_not_le[symmetric]]
                    by(auto simp: X_def dest!: maximalD2)
                  done

                also have \<open>\<dots> = v s - R.v (simple \<sigma> s)\<close>
                  by auto
                finally have \<open>False\<close> by auto
              }
              note * = this
              have \<open>s' \<in> states \<M>\<close>
                using \<open>s' \<in> set_pmf (\<sigma> s)\<close> set_pmf_closed assms  \<open>s \<in> states \<M>\<close>
                by blast
              show  \<open>s' \<in> X\<close>
                unfolding X_def
                using that  \<open>s \<in> X\<close> * \<open>s' \<in> states \<M>\<close>
                by (auto intro!: leI maximalI_trans[of s] simp: X_def )
            }
          qed
          note * = this
    
          moreover have \<open>(\<exists>s' \<in> set_pmf (\<sigma> s). \<exists>i' < i. s' \<in> R_G.G i')\<close>
            if \<open>i > 0\<close> \<open>s \<in> X\<close> \<open>s \<in> R_G.G i\<close>  for s i
            using R_G.ex_less_G[of \<open>\<sigma> s\<close> s i] that assms R_G.G_in_states
            by blast
          hence *: \<open>(\<exists>s' \<in> X. \<exists>i' < i. s' \<in> R_G.G i')\<close>
            if \<open>i > 0\<close> \<open>s \<in> X\<close> \<open>s \<in> R_G.G i\<close>  for s i
            using that *
            by meson
    
          obtain s where \<open>s \<in> X\<close>
            using \<open>X \<noteq> {}\<close> by auto
          then obtain i where \<open>s \<in> R_G.G i\<close>
            using \<open>s' \<in> states \<M>\<close> R_G.state_in_G
            by (metis (no_types, lifting) X_def maximalD1)
          then have \<open>\<exists>s \<in> X. s \<in> R_G.G 0\<close>
            using \<open>s \<in> X\<close> *
            by (intro nat_descent[where P = \<open>\<lambda>i. \<exists>s \<in> X. s \<in> R_G.G i\<close>]) blast+
          hence \<open>\<exists>s \<in> X. s \<in> targets \<M> \<or> s \<in> avoids \<M>\<close>
            by (auto simp add: bottoms_Avd_Tgt)
    
          moreover have[simp]: \<open>s \<in> targets \<M> \<longleftrightarrow> s \<notin> X\<close>
            using assms(2) neq[of s] \<open>s \<in> X\<close>
            by fastforce
          moreover have[simp]: \<open>s \<in> avoids \<M> \<longleftrightarrow> s \<notin> X\<close>
            using assms(2) neq[of s] \<open>s \<in> X\<close>
            by fastforce

          ultimately show ?thesis (*TODO: this case seems to provide inconsistencies, so maybe a case-based proof is not necessary here, but it works*)
            by (force simp: assms(2) dest: neq)
        qed
      qed
      ultimately show ?thesis
        by auto
    qed
    
    text \<open>Interesting corollary: stationary policies achieve the minimal value.
    Note that this holds in general for MDPs, but the proof here is simpler.\<close>
    corollary F_inf_fp_memoryless:
      assumes \<open>R.F_inf v' = v'\<close> and 
        v_le: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> v' s \<noteq> \<infinity>\<close>
      obtains \<sigma> where \<open>\<sigma> \<in> Pi (states \<M>) (actions' \<M>)\<close> \<open>v' = R.v o (simple \<sigma>)\<close>
    proof -
      define \<sigma> where [simp]:
        \<open>\<sigma> = (\<lambda>s \<in> states \<M>. arg_min_on (\<lambda>a. integral\<^sup>N (measure_pmf a) v') (actions' \<M> s))\<close>
    
      have \<sigma>: \<open>\<sigma> \<in> Pi (states \<M>) (actions' \<M>)\<close>
        by (auto intro!: arg_min_if_finite(1) K_finite K_wf)
    
      moreover have \<open>v' = R.v o (simple \<sigma>)\<close>
      proof -
        have \<open>R.F_\<sigma> \<sigma> v' = v'\<close>
          apply (subst (2) assms(1)[symmetric])
          unfolding R.F_\<sigma>_def R.F_inf_def
          using actions_neq_empty_M finite_actions_M
          by (auto simp: Min_Inf arg_min_on_Min[where f = \<open>\<lambda>a. integral\<^sup>N (measure_pmf a) v'\<close>])
        thus ?thesis
          using \<sigma> v_le
          by (intro F_\<sigma>_fp_unique) auto
      qed
    
      ultimately show ?thesis
        using that
        by blast
    qed
    
    lemma n_memoryless:
      obtains \<sigma> where \<open>\<sigma> \<in> Pi (states \<M>) (actions' \<M>)\<close> \<open>R.n = R.v o (simple \<sigma>)\<close>
      using F_inf_fp_memoryless[OF R.F_inf_n] R.n_not_inf
      by auto
    
    subsubsection \<open>\<^const>\<open>R.F_inf\<close>\<close> 
    text \<open>cf. Proposition 3 in Haddad, Monmege\<close>
    text \<open>We already know that @{const R.n} is a fixed point of @{const R.F_inf}.
    We only need to show uniqueness\<close>
    proposition F_inf_fp_unique:
      assumes \<open>R.F_inf v = v\<close> and v_le_one: \<open>\<And>s. s \<in> states \<M> \<Longrightarrow> v s \<noteq> \<infinity>\<close>
      shows \<open>v = R.n\<close>
    proof -
      have v_nostate[simp]: \<open>v s = undefined\<close> if \<open>s \<notin> states \<M>\<close> for s
        using that assms R.F_inf_nS
        by metis
    
      have v_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> v s = 1\<close> for s
        by (subst assms(1)[symmetric]) auto
    
      have v_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> v s = 0\<close> for s
        by (subst assms(1)[symmetric]) auto
    
      have v_ge: \<open>v \<ge> R.n\<close>
        by (subst R.n_eq_lfp_F_inf) (simp add: assms lfp_lowerbound)
    
      obtain \<sigma> where n_v: \<open>R.n = R.v o (simple \<sigma>)\<close> and \<sigma>: \<open>\<sigma> \<in> Pi (states \<M>) (actions' \<M>)\<close>
        using n_memoryless by force
    
      have \<open>v \<le> R.v o (simple \<sigma>)\<close>
      proof -
        define X where \<open>X = maximal (\<lambda>s. v s - R.v (simple \<sigma> s)) (states \<M>)\<close>
    
        hence \<open>X \<noteq> {}\<close>
          unfolding X_def
          using finite_states_M S_not_empty
          by (intro maximal_ne) auto
    
        show ?thesis
        proof (cases \<open>\<forall>s \<in> states \<M>. v s - R.v (simple \<sigma> s) = 0\<close>)
          case True
          hence "\<forall>s \<in> states \<M>. R.v (simple \<sigma> s) = v s"
            using v_ge
            by (auto simp: n_v le_fun_def fun_eq_iff) (meson basic_trans_rules(24) ennreal_minus_eq_0)
          then show ?thesis
            unfolding R.v_def
            using \<sigma>
            by (auto simp: simple_valid_cfg_iff)
        next
          case False
          then obtain s' where \<open>s' \<in> states \<M>\<close> \<open>v s' - R.v (simple \<sigma> s') \<noteq> 0\<close>
            by auto
          hence neq: \<open>v s - R.v (simple \<sigma> s) \<noteq> 0\<close> if \<open>s \<in> X\<close> for s
            using maximalD2[of s \<open>(\<lambda>s. v s - R.v (simple \<sigma> s))\<close> \<open>states \<M>\<close> s'] that
            by (auto simp: X_def)
    
          hence \<open>s' \<in> X\<close> if \<open>s' \<in> set_pmf (\<sigma> s)\<close> \<open>s \<in> X\<close> for s s'
          proof -
            {
              have s: \<open>s \<in> states \<M>\<close>
                using that
                unfolding X_def
                by (meson maximalD1)
    
              hence \<open>s \<in> trivials \<M>\<close>
                using neq \<sigma> that
                by (cases s rule: state_fn_cases) fastforce+
    
              {
                assume diff_s': \<open>v s' - R.v (simple \<sigma> s') < v s - R.v (simple \<sigma> s)\<close> \<open>s' \<in> \<sigma> s\<close>
    
                have diff_int_le: \<open>\<integral>\<^sup>+ s. v s - R.v (simple \<sigma> s) \<partial>measure_pmf (\<sigma> s) \<noteq> \<top>\<close>
                  using  Pi_closed[OF \<sigma>, of s] \<sigma> s  assms(2)
                  by (intro finite_nn_integral_lt_topI) (auto intro: set_pmf_finite)

                have v_le_int: \<open>v s \<le> integral\<^sup>N (\<sigma> s) v\<close>
                  using \<open>s \<in> trivials \<M>\<close>  \<sigma>
                  by (subst \<open> R.F_inf v = v\<close>[symmetric]) (auto simp: trivials_computes R.F_inf_def Pi_iff intro!: INF_lower)
                hence \<open>v s - R.v (simple \<sigma> s) \<le> integral\<^sup>N (\<sigma> s) v -   R.v (simple \<sigma> s)\<close>
                  using assms \<open>s \<in> trivials \<M>\<close>   R.F_\<sigma>_v[OF \<sigma>] ennreal_minus_mono
                  by (auto simp: R.F_\<sigma>_def fun_eq_iff)
                also have \<open>\<dots> = integral\<^sup>N (\<sigma> s) v - integral\<^sup>N (\<sigma> s) ((R.v o (simple \<sigma>)))\<close>
                  using assms \<open>s \<in> trivials \<M>\<close>  R.F_\<sigma>_v[OF \<sigma>] computes_nTgt
                  apply (clarsimp simp: R.F_\<sigma>_def fun_eq_iff trivials_computes) 
                  using  R.S1_nS2 s
                  by presburger
                also have \<open>\<dots> = integral\<^sup>N (\<sigma> s) (\<lambda>s. v s - (R.v (simple \<sigma> s)))\<close>
                  apply (subst nn_integral_diff[symmetric])
                  subgoal by auto
                  subgoal by auto
                  subgoal
                    by (metis computes_def R.F_\<sigma>_cont None_not_triv R.F_\<sigma>_v R.n_not_inf \<open>s \<in> trivials \<M>\<close> \<sigma>
                        infinity_ennreal_def n_v s trivials_computes)
                  using v_ge
                  by (auto simp: comp_def n_v le_fun_def)
                also have \<open>\<dots> < integral\<^sup>N (\<sigma> s) (\<lambda>s'. v s - R.v (simple \<sigma> s))\<close>
                  using diff_int_le Pi_closed[OF \<sigma> s] that(2) diff_s'[unfolded linorder_not_le[symmetric]]
                  by (intro nn_integral_less) (auto simp: X_def dest: maximalD2)
                also have \<open>\<dots> = v s - R.v (simple \<sigma> s)\<close>
                  by auto
                finally have \<open>False\<close> by auto
              }
              note * = this
              have \<open>s' \<in> states \<M>\<close>
                using \<open>s' \<in> set_pmf (\<sigma> s)\<close> set_pmf_closed assms \<open>s \<in> states \<M>\<close> \<sigma>
                by blast
              show \<open>s' \<in> X\<close>
                using that * \<open>s' \<in> states \<M>\<close>
                by (auto intro!: maximalI_trans[of s _ _ s'] leI simp: X_def)
            }
          qed
          note * = this
    
          moreover have \<open>(\<exists>s' \<in> set_pmf (\<sigma> s). \<exists>i' < i. s' \<in> R_G.G i')\<close>
            if \<open>i > 0\<close> \<open>s \<in> X\<close> \<open>s \<in> R_G.G i\<close>  for s i
            using R_G.ex_less_G[of \<open>\<sigma> s\<close> s i] that Pi_mem \<sigma> R_G.G_in_states
            by force
          hence *: \<open>(\<exists>s' \<in> X. \<exists>i' < i. s' \<in> R_G.G i')\<close> if \<open>i > 0\<close> \<open>s \<in> X\<close> \<open>s \<in> R_G.G i\<close> for s i
            using that *
            by meson
    
          obtain s where \<open>s \<in> X\<close>
            using \<open>X \<noteq> {}\<close> by auto
          then obtain i where \<open>s \<in> R_G.G i\<close>
            using \<open>s' \<in> states \<M>\<close> R_G.state_in_G
            by (metis (no_types, lifting) X_def maximalD1)
          then have \<open>\<exists>s \<in> X. s \<in> R_G.G 0\<close>
            using \<open>s \<in> X\<close> *
            by (intro nat_descent[where P = \<open>\<lambda>i. \<exists>s \<in> X. s \<in> R_G.G i\<close>]) blast+
          hence \<open>\<exists>s \<in> X. s \<in> targets \<M> \<or> s \<in> avoids \<M>\<close>
            by (auto simp add: bottoms_Avd_Tgt)
    
          moreover have[simp]: \<open>s \<in> targets \<M> \<longleftrightarrow> s \<notin> X\<close>
            using assms(2) neq[of s] \<open>s \<in> X\<close>
            using \<sigma> by auto
          moreover have[simp]: \<open>s \<in> avoids \<M> \<longleftrightarrow> s \<notin> X\<close>
            using assms(2) neq[of s] \<open>s \<in> X\<close>
            by fastforce
          ultimately show ?thesis
            using n_True neq by (force simp: n_v)
        qed
      qed
      thus ?thesis  
        using v_ge
        by (auto simp: n_v )
    qed
    
    subsection \<open>Definition of Interval Iteration\<close>
    
    definition \<open>lb_n n = (R.F_inf ^^ n) R.lb_0\<close>
    definition \<open>ub_n n = (R.F_inf ^^ n) R.ub_0\<close>
    
    definition \<open>lb_p n = (R.F_sup ^^ n) R.lb_0\<close>
    definition \<open>ub_p n = (R.F_sup ^^ n) R.ub_0\<close>
    
    text \<open>We first show some simple properties:\<close>
    lemma 
      lb_n0[simp]: \<open>lb_n 0 = R.lb_0\<close> and
      lb_n_Suc[simp]: \<open>lb_n (Suc n) = R.F_inf (lb_n n)\<close>
      unfolding lb_n_def
      by auto
    
    lemma 
      ub_n0[simp]: \<open>ub_n 0 = R.ub_0\<close> and
      ub_n_Suc[simp]: \<open>ub_n (Suc n) = R.F_inf (ub_n n)\<close>
      unfolding ub_n_def
      by auto
    
    lemma 
      lb_p0[simp]: \<open>lb_p 0 = R.lb_0\<close> and
      lb_p_Suc[simp]: \<open>lb_p (Suc n) = R.F_sup (lb_p n)\<close>
      unfolding lb_p_def
      by auto
    
    lemma 
      ub_p0[simp]: \<open>ub_p 0 = R.ub_0\<close> and
      ub_p_Suc[simp]: \<open>ub_p (Suc n) = R.F_sup (ub_p n)\<close>
      unfolding ub_p_def
      by auto
    
    lemma 
      lb_0_triv[simp]: \<open>s \<in> trivials \<M> \<Longrightarrow> R.lb_0 s = 0\<close> and
      lb_0_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> R.lb_0 s = 1\<close> and
      lb_0_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.lb_0 s = 0\<close> and
      lb_0_nS[simp]: \<open>s \<notin> states \<M> \<Longrightarrow> R.lb_0 s = undefined\<close>
      unfolding R.lb_0_def
      using AT_disj
      by (auto simp: trivials_computes)
    
    lemma 
      ub_0_triv[simp]: \<open>s \<in> trivials \<M> \<Longrightarrow> R.ub_0 s = 1\<close> and
      ub_0_True[simp]: \<open>s \<in> targets \<M> \<Longrightarrow> R.ub_0 s = 1\<close> and
      ub_0_False[simp]: \<open>s \<in> avoids \<M> \<Longrightarrow> R.ub_0 s = 0\<close> and
      ub_0_nS[simp]: \<open>s \<notin> states \<M> \<Longrightarrow> R.ub_0 s = undefined\<close>
      unfolding R.ub_0_def
      using AT_disj
      by (auto simp: trivials_computes)
  
    lemma lb_n_le_Suc: \<open>lb_n i \<le> lb_n (Suc i)\<close>
      by (induction i) (auto intro!: state_fn_leI R.mono_F_inf[THEN monoD] simp: le_funD R.F_inf_S1) 
    
    lemma lb_p_le_Suc: \<open>lb_p i \<le> lb_p (Suc i)\<close>
      by (induction i) (auto intro!: state_fn_leI R.mono_F_sup[THEN monoD] simp: le_funD R.F_sup_S1)
    
    lemma ub_n_ge_Suc: \<open>ub_n (Suc i) \<le> ub_n i\<close>
    proof (induction i)
      case 0
      show ?case 
        apply(rule le_funI)
        unfolding ub_n_def R.ub_0_def 
        by (fastforce intro!: F_inf_False R.F_inf_le_one simp: Avd_alt)
    next
      case (Suc i)
      then show ?case 
        by(auto intro!: monoD[OF R.mono_F_inf])
    qed 
    
    lemma ub_p_ge_Suc: \<open>ub_p (Suc i) \<le> ub_p i\<close>
    proof (induction i)
      case 0
      show ?case 
        apply(rule le_funI)
        unfolding ub_p_def R.ub_0_def 
        by (fastforce intro!: F_sup_False R.F_sup_le_one simp: Avd_alt)
    next
      case (Suc i)
      then show ?case 
        by(auto intro!: monoD[OF R.mono_F_sup])
    qed 

    lemma mono_lb_n: \<open>mono lb_n\<close>
      using lb_n_le_Suc lift_Suc_mono_le 
      by (blast intro: monoI)
    
    lemma antimono_lb_n: \<open>antimono ub_n\<close>
      using ub_n_ge_Suc lift_Suc_antimono_le  
      by (blast intro: antimonoI)
    
    lemma mono_lb_p: \<open>mono lb_p\<close>
      using lb_p_le_Suc lift_Suc_mono_le 
      by (blast intro: monoI)
    
    lemma antimono_lb_p: \<open>antimono ub_p\<close>
      using ub_p_ge_Suc lift_Suc_antimono_le  
      by (blast intro: antimonoI)
    
    lemma lb_le_one: \<open>s \<in> states \<M> \<Longrightarrow> lb_n n s \<le> 1\<close>
      unfolding lb_n_def R.lb_0_def 
      using R.F_inf_le_one
      by (induction n arbitrary: s) auto
    
    lemma lb_tendsto_SUP: \<open>(\<lambda>n. lb_n n s) \<longlonglongrightarrow> (\<Squnion> range (\<lambda>n. lb_n n s))\<close>
      by (metis LIMSEQ_SUP incseq_def le_funD mono_lb_n)
    
    lemma ub_tendsto_INF: \<open>(\<lambda>n. ub_n n s) \<longlonglongrightarrow> (\<Sqinter> range (\<lambda>n. ub_n n s))\<close>
      by (metis LIMSEQ_INF antimono_lb_n decseq_def le_funD)
    
    lemma lb_le_Rn: \<open>R.lb_0 \<le> R.n\<close>
      unfolding R.lb_0_def
      using AT_disj
      by (auto intro!: state_fn_leI)
    
    lemma ub_ge_Rn: \<open>R.n \<le> R.ub_0\<close>
      unfolding R.ub_0_def
      using R.n_le_1
      by (auto simp: trivials_computes intro!: state_fn_leI)
    
    lemma lb_n_le_n: \<open>lb_n i \<le> R.n\<close>
      using lb_le_Rn R.F_inf_le_iter 
      by (induction i) (auto simp: le_fun_def)
    
    lemma ub_n_ge_n: \<open>ub_n i \<ge> R.n\<close>
      using ub_ge_Rn R.F_inf_ge_iter 
      by (induction i) (auto simp add: le_fun_def)
    
    lemma ub_0_le_1: \<open>R.ub_0 \<le> (\<lambda>s \<in> states \<M>. 1 :: ennreal)\<close>
      unfolding R.ub_0_def
      by (auto intro!: le_funI)
    
    lemma ub_n_le_1: \<open>ub_n i \<le> (\<lambda>s \<in> states \<M>. 1 :: ennreal)\<close>
    proof -
      have \<open>ub_n 0 \<le> (\<lambda>s \<in> states \<M>. 1 :: ennreal)\<close>
        unfolding ub_n_def
        using ub_0_le_1
        by auto
      thus ?thesis
        using decseqD[OF antimono_lb_n, of 0]
        by (auto intro: order.trans)
    qed
    
    lemma lb_le_ub_n: \<open>lb_n i \<le> ub_n i\<close>
      using ub_n_ge_n lb_n_le_n  order.trans 
      by blast
  
  end


end