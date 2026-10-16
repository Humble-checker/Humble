theory Interval_Iteration_Min_Code
  imports Interval_Iteration_Tool
begin

text \<open>Min-particular abstract algorithm: the in-place MEC \<open>Min_red\<close> reduction
  (collapse_min_defs.mop_min_red_impl) and its correctness, moved out of the shared
  Interval_Iteration_Tool so the latter stays mode-neutral (spec layer only).\<close>

  subsection \<open>Abstract Algorithm\<close>

  locale collapse_min_defs = MDPC_Reach_Avoid_defs
  begin
  
    definition "mop_min_red_impl = do{
      ASSERT(Finite_MDP \<M>);
      D \<leftarrow> op_compute_mecs \<M>;
      \<M> \<leftarrow> FOREACH (states \<M>) (\<lambda>u \<M>'. do{
        ASSERT (u \<in> states \<M> \<and> states (to_mdpc \<M>') = states \<M>);
        if u \<in> avoids \<M>' then
          RETURN \<M>'
        else if u \<in> targets \<M>' then
          RETURN \<M>'
        else if \<not>op_is_trivial \<M>' D u then do{
          ASSERT (u \<notin> avoids \<M>' \<and> u \<notin> targets \<M>');
          RETURN (op_make_avd_sink \<M>' u)
        }
        else
          RETURN \<M>'
      }) \<M>;
      RETURN \<M>
    }"

  end

  locale collapse_min_env = collapse_min_defs + MDPC_Reach_Avoid
  begin

    lemma op_is_trivial_eq_trivials: 
      assumes D: "set D = mec_decomp" "distinct D"
      assumes UM: "u \<in> states \<M>"
      assumes AE: "actions (to_mdpc \<M>') u = actions \<M> u"
      shows "op_is_trivial \<M>' D u \<longleftrightarrow> u \<in> trivials \<M>"
    proof(rule iffI)

      assume "op_is_trivial \<M>' D u"

      moreover have "i = j" if LEN: "i < length D" "j < length D" 
        and DE: "u \<in> D ! i" "v \<in> D ! j" and VU: "v \<in> states (the_mec \<M> u)" for i j v
      proof -
        have "states (the_mec \<M> u) = D ! i" 
          apply(rule unique_in_mec_decomp[of u])
          subgoal 
            using UM by blast
          subgoal 
            by (simp add: DE(1))
          subgoal 
            using UM mec_decomp_def by blast
          subgoal 
            using LEN(1) D nth_mem by blast
          done
        with VU have *: "v \<in> D ! i"
          by blast
        thus ?thesis 
          using D(1) LEN(1,2) nth_eq_iff_index_eq[OF D(2) LEN] 
            nth_mem unique_in_mec_decomp[OF * DE(2)]
          by blast
      qed

      ultimately have "actions (the_mec \<M> u) u = {}"
        apply(subst actions_the_mec)
        using UM apply presburger
        unfolding op_is_trivial_def apply (clarsimp simp: AE ) 
        subgoal for a
          apply(erule ballE[where ?x=a]) 
          by auto
        done

      moreover have "v \<in> states (the_mec \<M> u) \<Longrightarrow> v = u" for v
        by (metis UM calculation ec_def mec_ec sc_eq_trivial singletonD states_the_mec states_trivial
            the_mec)

      ultimately show "u \<in> trivials \<M>"
        unfolding op_is_trivial_def using D 
        by (auto simp: AE in_trivials_the_mec UM trivial_eq_no_actions)
    next
      
      have "u \<in> states \<M>'"
        by (simp add: actions_neq_empty_M assms(3,4) in_states)

      assume TRIV: "u \<in> trivials \<M>"

      with D obtain i where 1: "D ! i = {u}" "i < length D"
        unfolding trivials_def mec_decomp_def
        apply clarsimp
        by (metis (mono_tags, lifting) in_set_conv_nth mem_Collect_eq states_trivial)

      {
        fix a
        assume A: "a \<in> actions \<M> u"

        with TRIV have "\<not> set_pmf a \<subseteq> {u}"
          unfolding trivials_def
          using mec_actions[of \<M> "trivial u" u, simplified] by auto
        then obtain v where "v \<in> set_pmf a" and "u \<noteq> v" by blast
        moreover with A D obtain j where "v \<in> D ! j" 
          by (metis in_set_conv_nth set_pmf_closed' states_in_decomp)
        
        ultimately have "\<exists>v\<in>set_pmf a. \<exists>i<length D. \<exists>j<length D. i \<noteq> j \<and> u \<in> D ! i \<and> v \<in> D ! j"
          by (metis "1" A assms(1) doubleton_eq_iff in_set_conv_nth insert_absorb
              set_pmf_closed' singletonI states_in_decomp)
      }

      thus "op_is_trivial \<M>' D u"
        unfolding op_is_trivial_def by (auto simp: AE)
    qed


    lemma mop_min_red_impl_correct: "mop_min_red_impl \<le> RETURN (op_min_red \<M>)"
    proof -

      define Mi where "Mi \<equiv> (\<lambda> it. map_actions (\<lambda>u a. if u \<in> (avoids \<M> \<union> (states \<M> - trivials \<M> - targets \<M>)) - it then {return_pmf u} else a) \<M>)"

      define Inv where "Inv=(\<lambda> it \<M>'. 
        to_mdpc \<M>' = Mi it \<and>
        avoids \<M>' = avoids \<M> \<union> ((states \<M> - trivials \<M> - targets \<M>) - it) \<and>
        targets \<M>' = targets \<M>
      )"

      have Inv_states: "Inv it \<M>' \<Longrightarrow> states \<M>' = states \<M>" for it \<M>'
        unfolding Inv_def Mi_def by auto

      have Inv_actions: "Inv it \<M>' \<Longrightarrow> u \<in> it \<Longrightarrow> actions \<M>' u = actions \<M> u" for u it \<M>'
        unfolding Inv_def Mi_def by auto

      have AUX: "mop_min_red_impl \<le> do{
        ASSERT(Finite_MDP \<M>);
        \<M> \<leftarrow> FOREACHi Inv (states \<M>) (\<lambda>u \<M>'. do{
          ASSERT (u \<in> states \<M> \<and> states (to_mdpc \<M>') = states \<M>);
          if u \<in> avoids \<M>' then
            RETURN \<M>'
          else if u \<in> targets \<M>' then
            RETURN \<M>'
          else if u \<notin> trivials \<M> then do{
            ASSERT (u \<notin> avoids \<M>' \<and> u \<notin> targets \<M>');
            RETURN (op_make_avd_sink \<M>' u)
          }
          else
            RETURN \<M>'
        }) \<M>;
        RETURN \<M>
      }"
        unfolding mop_min_red_impl_def op_compute_mecs_def mec_algo_defs.compute_MEC_spec_def
        apply(refine_vcg )
        apply(rule bind_le_nofailI)
        apply auto[]
        apply(rule bind_mono)
        apply(refine_vcg FOREACHi_refine_rcg'[where ?R=Id and \<alpha>=id, simplified])
        apply blast
        apply blast
        apply(auto simp: Inv_states Inv_actions op_is_trivial_eq_trivials split: if_splits)
        done


      have INIT: "Inv (states \<M>) \<M>"
        unfolding Inv_def Mi_def by (auto simp: mdpc_eqI) 

      have STEP1: "Inv it \<sigma> \<Longrightarrow> u \<notin> avoids \<sigma> \<Longrightarrow> u \<in> targets \<sigma> \<Longrightarrow> Inv (it - {u}) \<sigma>" for u it \<sigma>
        unfolding Inv_def Mi_def
        by (auto intro!: arg_cong[where ?f="\<lambda> x. map_actions x (to_mdpc \<M>)"] ext split: if_splits) 

      have STEP2: "Inv it \<sigma> \<Longrightarrow> u \<in> it \<Longrightarrow> u \<in> avoids \<sigma> \<Longrightarrow> Inv (it - {u}) \<sigma>" for u it \<sigma>
        unfolding Inv_def Mi_def
        by (auto simp: map_actions_map_actions Avd_loop intro!: map_actions_fun_eq ext split: if_splits) 

      have STEP3: "Inv it \<sigma> \<Longrightarrow> u \<notin> trivials (to_mdpc \<M>) \<Longrightarrow> u \<in> states (to_mdpc \<M>) \<Longrightarrow>
         u \<notin> targets \<sigma> \<Longrightarrow> Inv (it - {u}) (op_make_avd_sink \<sigma> u)" for u it \<sigma>
        unfolding Inv_def Mi_def op_make_avd_sink_def
        apply transfer
        by (auto simp: fix_loop_map_actions intro!: arg_cong[where ?f="\<lambda> x. map_actions x _"] ext split: if_splits)
      have STEP4: "Inv it \<sigma> \<Longrightarrow> u \<notin> avoids \<sigma> \<Longrightarrow> u \<in> trivials (to_mdpc \<M>) \<Longrightarrow> Inv (it - {u}) \<sigma>" for u it \<sigma>
        unfolding Inv_def Mi_def
        by (auto intro!: arg_cong[where ?f="\<lambda> x. map_actions x _"] ext split: if_splits)

      have FIN: "Finite_MDP (to_mdpc \<M>) \<Longrightarrow>
         Inv {} \<sigma> \<Longrightarrow>
         \<sigma> =
         Abs_mdptc
          (map_actions
            (\<lambda>u. If (u \<in> avoids \<M> \<or>
                      u \<in> states (to_mdpc \<M>) \<and>
                      u \<notin> trivials (to_mdpc \<M>) \<and> u \<notin> targets \<M>)
                   {return_pmf u})
            (to_mdpc \<M>),
           avoids_min_red, targets \<M>)" for \<sigma>
        unfolding Inv_def Mi_def
        apply transfer
        by (auto)

      show ?thesis
        apply(rule order_trans[OF AUX])
        unfolding RETURN_SPEC_conv
        unfolding mop_min_red_impl_def op_min_red_def Min_red_def
        apply(refine_vcg FOREACH_rule[where ?I=Inv])
        apply (vc_solve solve: INIT Finite_MDP_axioms Inv_states STEP1 STEP2 STEP3 STEP4 FIN)
        apply blast
        done
    qed

  end

end
