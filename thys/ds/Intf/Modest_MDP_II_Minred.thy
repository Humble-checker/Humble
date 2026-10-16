theory Modest_MDP_II_Minred
  imports "./Modest_MDP_II_Reach"
begin

  text \<open>This theory refines an MDP (of @{typ \<open>nat mdpc\<close>}}) to the mcsta data structure for MDP's.
    This theory specifically targets the operations for min-reduction and interval iteration.
    Other operations (e.g. for SCC or MEC decomposition) are refined elsewhere for modularity 
    reasons (e.g. in Modest_MDP_MEC Modest_MDP_SCC)\<close>


  locale modest_mdp_ii_inf_def = modest_mdp_input_def N St Tr Br Av Ta Pr for N St Tr Br Pr Av Ta
  begin

    sublocale reachability_opt_mode_defs Inf inf "(\<le>)" 0 1 .

    definition "get_state_val_opt xs u = do {
      let xopt = 1; 
      xopt \<leftarrow> FOREACH (sn_intv (StI ! u)) (\<lambda> t xopt. do{

        ASSERT (t < length Tr - Suc 0);
        val \<leftarrow> get_trans_val xs t;
        RETURN (inf val xopt)

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

  subsubsection \<open>Reduction\<close>

  context modest_mdp_input_def
  begin

    definition "is_trivial D u = do{
      FOREACHc (sn_intv (StI ! u)) (\<lambda> flag. flag) (\<lambda>t flag. do{
        ASSERT (t < length Tr - Suc 0);
        FOREACHc (sn_intv (TrI ! t)) (\<lambda> flag. \<not>flag) (\<lambda>b flag. do{
          ASSERT (b < length Br \<and> (\<exists> i < length D. u \<in> D ! i) \<and> (\<exists> i < length D. Br ! b \<in> D ! i));
          RETURN (\<not>op_in_eq_mec D u (Br ! b))
        }) False
      }) True
    }"
  
    definition "make_sink u = (St,Tr,Br,Pr,Av,Ta)"
  
    definition "make_avd_sink u = (St,Tr,Br,Pr,insert u Av,Ta)"

  end

  subsection \<open>Refinements\<close>

  locale modest_mdp_ii_invar_inf = modest_mdp_input_invar + modest_mdp_ii_inf_def +
    assumes vDom_alt: "vDom = {0..1}"
  begin

    sublocale reachability_opt_mode Inf inf "(\<le>)" 0 1 
      using reachability_opt_mode_inf .



  end

  subsubsection \<open>State & MDP relation\<close>

  abbreviation "\<M>_\<alpha>' N \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr)"
  abbreviation "\<M>_inv N \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta)"

  abbreviation "\<M>_inv_DS N DS \<equiv> (\<lambda> (St,Tr,Br,Pr,Av,Ta). modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta \<and> DS = (St,Tr,Br,Pr,Av,Ta))"


  definition modest_mdp_inf_rel :: "nat \<Rightarrow> (modest_mdp \<times> (nat mdptc)) set" where
    "modest_mdp_inf_rel N = br (\<M>_\<alpha>' N) (\<M>_inv N)"

  definition modest_mdp_inf_DS_rel :: "nat \<Rightarrow> modest_mdp \<Rightarrow> (modest_mdp \<times> (nat mdptc)) set" where
    "modest_mdp_inf_DS_rel N DS = br (\<M>_\<alpha>' N) (\<M>_inv_DS N DS)"

  subsection \<open>Refinement Proofs\<close>

  subsubsection \<open>Interval Iteration\<close>

  text \<open>The min-side interval-iteration refinements are derived from the mode-generic proofs in
    \<open>Modest_MDP_II_Reach\<close> instantiated with \<open>Inf\<close>. The min-specific
    \<^const>\<open>modest_mdp_ii_inf_def.get_state_val_opt\<close> is definitionally the \<open>Inf\<close>-instance of the
    generic backup, so its refinement transfers directly.\<close>

  context modest_mdp_ii_invar_inf
  begin

    sublocale G: modest_mdp_ii_mode_invar N St Tr Br Pr Av Ta Inf inf "(\<le>)" 0 1
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

    lemma MDPC_Reach_Avoid_Inf_M_\<alpha>: "MDPC_Reach_Avoid_Inf \<M>_\<alpha>"
      by(unfold_locales)

    sublocale MDPC_Reach_Avoid_Inf \<M>_\<alpha> using MDPC_Reach_Avoid_Inf_M_\<alpha> .

    lemma updated_state_val_min_gs_refine:
      assumes XB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> x v \<le> 1"
      assumes YB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> y v \<le> 1"
      assumes XSX: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YSY: "(ys,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      shows "updated_state_val_gs xs ys \<le> \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_state_vals_gs \<M>_\<alpha> x y)"
      unfolding updated_state_val_gs_eq by (rule G.updated_state_val_gs_refine[OF assms])

  end



  subsubsection \<open>Reduction\<close>

  context modest_mdp_input_invar
  begin

    lemma is_trivial_correct:
      assumes UCM: "u \<in> Cm"
      assumes D: "set D = mec_decomp' M'" "states M' = states M\<^sub>0_\<alpha>" "distinct D"
      shows "is_trivial D u \<le> RETURN (op_is_trivial \<M>_\<alpha> D u)"
    proof -

      from UCM have US: "u < N" and NTA: "u \<notin> Ta" and NAV: "u \<notin> Av"
        by(auto simp: Cm_def)

      hence US': "u \<in> states M\<^sub>0_\<alpha>"
        unfolding states_M\<^sub>0_\<alpha> by auto 

      define Inv where "Inv \<equiv> (\<lambda> it flag. flag \<longleftrightarrow> (\<forall>t \<in> sn_intv (StI ! u) - it. \<exists>b \<in> sn_intv (TrI ! t). \<not>op_in_eq_mec D u (Br ! b)))"

      have INIT: "Inv (sn_intv (StI ! u)) True"
        unfolding Inv_def by auto

      have FINF: "\<not> op_is_trivial \<M>_\<alpha> D u" if "Inv it False" for it
      proof -
        from that obtain t where TD: "in_intv (StI ! u) t" "\<forall>b\<in>sn_intv (TrI ! t). op_in_eq_mec D u (Br ! b)"
          unfolding Inv_def by auto
        have 1: "t < length Tr - Suc 0" 
          using Tr_in_bound_intvD[OF US TD(1)] .

        obtain i where ID: "u \<in> D ! i" "i < length D"
          using states_in_decomp[simplified, OF US'] D(1-2)[symmetric]
          by (metis US' in_set_conv_nth[of _ D] Finite_MDP_defs.states_in_decomp[of u M'])

        {
          fix b
          assume "in_intv (TrI ! t) b"
          hence "op_in_eq_mec D u (Br ! b)"
            using TD(2) by simp
          moreover have A: "j < length D \<Longrightarrow> u \<in> D ! j \<Longrightarrow> j = i" for j
            apply(drule Finite_MDP_defs.unique_in_mec_decomp[OF ID(1)]) 
            using D nth_mem 
            by (auto simp add: ID(2) nth_eq_iff_index_eq)

          ultimately have "Br ! b \<in> D ! i" 
            unfolding op_in_eq_mec_def by auto
          hence B: "Br ! b \<in> D ! j \<Longrightarrow> j < length D \<Longrightarrow> j = i" for j
            apply(drule Finite_MDP_defs.unique_in_mec_decomp) 
            using D nth_mem 
            by (auto simp add: ID(2) nth_eq_iff_index_eq) 
          note A[rotated] B
        } note AUX = this

        show ?thesis
          unfolding op_is_trivial_def 
          apply(clarsimp simp: actions_M\<^sub>0_\<alpha>[OF US] St_to_pmfs_nta[OF UCM] ) 
          apply(rule bexI[where ?x=t])
          subgoal unfolding set_pmf_Tr_to_pmf[OF 1] 
            apply clarsimp
            apply(frule AUX(1))
            apply blast
            apply blast
            apply(drule AUX(2))
            apply blast
            apply blast
            by blast
          subgoal using TD(1) by simp
          done
      qed


      have FIN: "flag = op_is_trivial \<M>_\<alpha> D u" if "Inv {} flag" for flag
      proof(cases flag)
        case True

        obtain i where ID: "u \<in> D ! i" "i < length D"
          using states_in_decomp[simplified, OF US'] D(1-2)[symmetric]
          by (metis Finite_MDP_defs.states_in_decomp US' in_set_conv_nth)

        {
          fix t
          assume "in_intv (StI ! u) t"
          with True that obtain b where "in_intv (TrI ! t) b" and "\<not> op_in_eq_mec D u (Br ! b)"
            unfolding Inv_def by fastforce

          hence "Br ! b \<in> set_pmf (Tr_to_pmf t)"
            apply(subst set_pmf_Tr_to_pmf) 
            using Cm_mem Tr_in_bound_intvD UCM \<open>in_intv (StI ! u) t\<close> by auto

          moreover obtain j where "Br ! b \<in> D ! j" "j < length D"
            by (metis Br_in_bound Br_in_bound_intvD D(1,2) Finite_MDP_defs.states_in_decomp Tr_in_bound_intvD
                US \<open>in_intv (StI ! u) t\<close> \<open>in_intv (TrI ! t) b\<close> atLeastLessThan_iff in_set_conv_nth states_M\<^sub>0_\<alpha>
                zero_le)

          moreover have "i \<noteq> j" 
            using ID(1,2) \<open>Br ! b \<in> D ! j\<close> \<open>\<not> op_in_eq_mec D u (Br ! b)\<close> op_in_eq_mec_def by blast

          ultimately have "\<exists>v\<in>set_pmf (Tr_to_pmf t). \<exists>i<length D. \<exists>j<length D. i \<noteq> j \<and> u \<in> D ! i \<and> v \<in> D ! j"
            using ID by blast

        }

        with True show ?thesis
          unfolding op_is_trivial_def  op_in_eq_mec_def
          by (auto simp: True actions_M\<^sub>0_\<alpha>[OF US] St_to_pmfs_nta[OF UCM])
      next
        case False
        thus ?thesis
          using FINF that by auto
      qed

      define Inv2 where "Inv2 \<equiv> (\<lambda> t it flag. flag \<longleftrightarrow> (\<exists>b \<in> sn_intv (TrI ! t) - it. \<not>op_in_eq_mec D u (Br ! b)))"

      have INIT2: "Inv2 t (sn_intv (TrI ! t)) False" if "t \<in> sn_intv (StI ! u)" for t
        unfolding Inv2_def by auto

      show ?thesis
        unfolding is_trivial_def RETURN_SPEC_conv
        apply(rule FOREACHc_rule[where ?I= Inv])
        apply(vc_solve solve: INIT FIN dest!: FINF)
        subgoal for t it flag
          apply(refine_vcg FOREACHc_rule[where ?I= "Inv2 t"])
          apply(vc_solve solve: INIT2)
          subgoal 
            using Tr_in_bound_intvD US sn_intv_member by blast
          subgoal
            using Br_in_bound_intvD in_subset_sn_intv by presburger
          subgoal
            by (metis D(1) Finite_MDP_defs.states_in_decomp US' assms(3) in_set_conv_nth)
          subgoal (*TODO, improve*)
            by (metis Br_in_bound Finite_MDP_defs.states_in_decomp
                \<open>\<And>x ita \<sigma>. t \<in> it \<Longrightarrow> it \<subseteq> sn_intv (StI ! u) \<Longrightarrow> Inv it True \<Longrightarrow> flag \<Longrightarrow> t < length Tr - Suc 0 \<Longrightarrow> x \<in> ita \<Longrightarrow> ita \<subseteq> sn_intv (TrI ! t) \<Longrightarrow> Inv2 t ita False \<Longrightarrow> \<not> \<sigma> \<Longrightarrow> x < length Br\<close>
                assms(2,3) atLeast_upt in_set_conv_nth lessThan_iff set_upt states_M\<^sub>0_\<alpha>)
          subgoal 
            unfolding Inv2_def by blast 
          subgoal 
            by (simp add: Inv2_def Inv_def it_step_insert_iff) 
          subgoal 
            using Inv2_def 
            using
              \<open>\<And>\<sigma>. t \<in> it \<Longrightarrow> it \<subseteq> sn_intv (StI ! u) \<Longrightarrow> Inv it True \<Longrightarrow> flag \<Longrightarrow> t < length Tr - Suc 0 \<Longrightarrow> Inv2 t {} \<sigma> \<Longrightarrow> Inv (it - {t}) \<sigma>\<close>
            by blast
          done
        done
    qed
    

    lemma make_avd_sink_\<alpha>: "u \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> op_make_avd_sink \<M>_\<alpha> u = \<M>_\<alpha>' N (make_avd_sink u)"
    proof -
      assume "u \<in> states M\<^sub>0_\<alpha>"
      hence ASM: "u < N"
        by(simp add: states_M\<^sub>0_\<alpha>)
      have [simp]: "states (modest_mdp_input_def.M\<^sub>0_\<alpha> N St Tr Br (insert u Av) Ta Pr) = {0..<N}"
        unfolding modest_mdp_input_def.M\<^sub>0_\<alpha>_def
        by(auto simp: states.abs_eq split: if_splits)

      have [simp]: "actions (modest_mdp_input_def.M\<^sub>0_\<alpha> N St Tr Br (insert u Av) Ta Pr) u = {return_pmf u}"
        unfolding modest_mdp_input_def.M\<^sub>0_\<alpha>_def modest_mdp_input_def.St_to_pmfs_def modest_mdp_input_struc_def.Cm_def
        by(auto simp: ASM actions.abs_eq split: if_splits)

      have [simp]: "s < N \<Longrightarrow> u \<noteq> s 
        \<Longrightarrow> actions (modest_mdp_input_def.M\<^sub>0_\<alpha> N St Tr Br (insert u Av) Ta Pr) s = actions M\<^sub>0_\<alpha> s" for s
        unfolding modest_mdp_input_def.M\<^sub>0_\<alpha>_def modest_mdp_input_def.St_to_pmfs_def modest_mdp_input_struc_def.Cm_def
        by(auto simp: actions.abs_eq split: if_splits)
      have "fix_loop u M\<^sub>0_\<alpha> = modest_mdp_input_def.M\<^sub>0_\<alpha> N St Tr Br (insert u Av) Ta Pr"
        by(auto simp: ASM states_M\<^sub>0_\<alpha> actions_M\<^sub>0_\<alpha>  intro!: mdpc_eqI split: if_splits)


      thus ?thesis
        unfolding op_make_avd_sink_def make_avd_sink_def
        by (auto simp: modest_mdp_input_def.\<M>_\<alpha>_def to_mdpc.abs_eq avoids.abs_eq targets.abs_eq)
    qed

    lemma make_avd_sink_invar: "u \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> u \<notin> Ta \<Longrightarrow> \<M>_inv N (make_avd_sink u)"
      unfolding make_avd_sink_def
      apply clarsimp
      apply(unfold_locales)
      subgoal
        using N_DEF .
      subgoal
        using N0 .
      subgoal
        using AN states_M\<^sub>0_\<alpha> by simp
      subgoal 
        using TN .
      subgoal
        using AT by blast
      subgoal
        using St_dom .
      subgoal
        using Tr_dom .
      subgoal
        using Br_dom .
      subgoal
        using Sorted_St .
      subgoal
        using Sorted_Tr .
      subgoal
        using Pr_lt_one .
      subgoal
        using Pr_gt_zero .
      subgoal by simp
      subgoal 
        using MDPC_Reach_Avoid_Inf.vDom_alt MDPC_Reach_Avoid_Inf_def MDPC_Reach_Avoid_axioms
        by blast
      done

  end



  definition "op_compute_mec_sorted M \<equiv> SPEC (\<lambda>D. set D = Finite_MDP_defs.mec_decomp M \<and> distinct D \<and> sorted_wrt (\<lambda> x y. Inf x < Inf y) D)"
    
  definition "compute_MEC_sorted M = do {
    D \<leftarrow> op_compute_mecs M;
    RETURN (op_sort_by_inf D)
  }"

  text \<open>The sorted MEC decomposition meets its specification: sorting by \<^const>\<open>Inf\<close> preserves
    \<^const>\<open>set\<close> and \<^const>\<open>distinct\<close>, and the least elements of distinct MECs are distinct.\<close>
  lemma compute_MEC_sorted_correct: "compute_MEC_sorted M \<le> op_compute_mec_sorted M"
  proof -

    have mec_decomp'_bot: "mec_decomp' \<bottom> = {{}}"
      unfolding Finite_MDP_defs.mec_decomp_def 
      by (auto 0 3 dest: mec_imp_bot_eq_bot intro: exI[where ?x="\<bottom>"] mec_refl)

    have op_sort_by_inf_empty: "op_sort_by_inf [{}] = [{}]"
    unfolding op_sort_by_inf_def by simp

    have AUX1: "set x = {a} \<Longrightarrow> distinct x \<Longrightarrow> x = [a]" for x a
      by (metis distinct_length_2_or_more insertCI list.distinct(2) list.set(2) list.set_cases neq_NilE
        singleton_iff)

    show ?thesis
      unfolding compute_MEC_sorted_def op_compute_mec_sorted_def op_compute_mecs_def mec_algo_defs.compute_MEC_spec_def
      apply(refine_vcg)
      subgoal unfolding op_sort_by_inf_def Finite_MDP_defs.mec_decomp_def by auto
      subgoal unfolding op_sort_by_inf_def by simp
      subgoal 
        apply(cases "(to_mdpc M) = \<bottom>")
        subgoal
          by (force simp: mec_decomp'_bot op_sort_by_inf_empty dest!: AUX1) 
        subgoal
          unfolding op_sort_by_inf_def 
          by(auto 0 3 intro!: inj_on_nat_Inf sorted_wrt_sort_key_lt 
            simp: eq_bot_iff_states Finite_MDP_defs.mec_decomp_def 
            dest: mec_unique_state mec_imp_bot_eq_bot) 
        done
      done
  qed

end
