theory Interval_Iteration_Tool
  imports "../ds/Intf/Modest_MDP_II_Ops" "../II/Min_Reduction" "../II/Max_Reduction"
begin

  text \<open>This theory file contains the high-level algorithm specifications of min-reduction, max reduction and 
    interval iteration.\<close>

  section \<open>Auxiliary Theory\<close>

  lemma map_actions_map_actions: "map_actions f (map_actions g M) = map_actions (\<lambda> s. f s o (g s)) M"
    apply transfer 
    by (simp add: option.map_comp)

  lemma map_actions_fun_eq: "(\<And>u. u \<in> states M \<Longrightarrow> x u (actions M u) = y u (actions M u)) \<Longrightarrow> map_actions x M = map_actions y M"
    by (metis actions_map_actions' mdpc_eqI state_map_actions)

  lemma fix_loop_map_actions: "u \<in> states M \<Longrightarrow> fix_loop u (map_actions f M) = map_actions (\<lambda> v a. if u = v then {return_pmf u} else f v a) M"
    apply transfer
    by (auto split: if_splits intro!: ext)

  subsection \<open>Nres Product\<close>

  definition prod_nres :: "'a nres \<Rightarrow> 'b nres \<Rightarrow> ('a \<times> 'b) nres" (infixr "\<times>\<^sub>n" 70) 
    where "prod_nres = (\<lambda>a b. do {x<-a; y<-b; RETURN (x,y)})"

  lemma prod_nres_refine[refine]: "mi1 \<le> m1 \<Longrightarrow> mi2 \<le> m2 \<Longrightarrow> mi1 \<times>\<^sub>n mi2 \<le> (m1 \<times>\<^sub>n m2)"
    unfolding prod_nres_def by (fastforce simp: pw_le_iff refine_pw_simps) 

  lemma prod_nres_rel_refine[refine]: "mi1 \<le> \<Down> R1 m1 \<Longrightarrow> mi2 \<le> \<Down> R2 m2 \<Longrightarrow> mi1 \<times>\<^sub>n mi2 \<le> \<Down>(R1 \<times>\<^sub>r R2) (m1 \<times>\<^sub>n m2)"
    unfolding prod_nres_def by (fastforce simp: pw_le_iff refine_pw_simps) 

  lemma nofail_prod_nres[sep_algebra_simps]: "inres m1 x \<Longrightarrow> nofail (m1 \<times>\<^sub>n m2) \<longleftrightarrow> nofail m1 \<and> nofail m2"
    unfolding prod_nres_def by (auto simp: pw_bind_nofail) 


  subsection \<open>Refinement with ghost variables\<close>

  definition "ghostc_rel R1 = {(a,(c,b)). (a,b) \<in> R1}"

  definition "ghosti_rel R1 = {((c,a),b). (a,b) \<in> R1}"

  lemma ghostc_rel_mem[simp]: "(a,(c,b)) \<in> ghostc_rel R1 \<longleftrightarrow> (a,b) \<in> R1"
    unfolding ghostc_rel_def by simp

  lemma ghosti_rel_mem[simp]: "((c,a),b) \<in> ghosti_rel R1 \<longleftrightarrow> (a,b) \<in> R1"
    unfolding ghosti_rel_def by simp

  
  subsection \<open>Advanced for-loop refinement\<close>

  text \<open>Currently unused, can be used to prove convergence of Gauss-Seidel in a more straightforward
    way. Was abandoned because, although suspectedly easier than a direct proof, it was still a lot 
    of effort. Moreover, it was not necessary in the context of our work, as floating-point errors
    would anyways break this property. However, I estimate that such proof is feasible.

    The idea: Gauss-Seidel converges at least as fast as normal value iteration. However, in Gauss-Seidel,
    the iteration order matters. So we create a refinement relation \<open>R it\<close>, that is dependent on the 
    set of un-iterated items \<open>S - it\<close>, which are provably closer or as close to convergence as the 
    according entries in standard iteration. Moreover, at the end of the iteration, \<open>R {}\<close> is the 
    greater/less-or-equal relation. Because we have a proof that the standard iteration converges, 
    so does Gauss-Seidel.
  \<close>

  lemma FOREACH_dep_refine:
    fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
    fixes S :: "'S set"
    fixes S' :: "'Sa set"
    assumes INJ: "inj_on \<alpha> S"
    assumes REFS: "S' = \<alpha>`S"
    assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R0"
    assumes "(\<And>\<sigma> \<sigma>'. (\<sigma>, \<sigma>') \<in> R0 \<Longrightarrow> (\<sigma>, \<sigma>') \<in> R S')"
    assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
      x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
      (\<sigma>,\<sigma>')\<in>R it'
    \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>(R (it' - {x'})) (f' x' \<sigma>')"
    assumes "(\<And>\<sigma> \<sigma>'. (\<sigma>, \<sigma>') \<in> R {} \<Longrightarrow> (\<sigma>, \<sigma>') \<in> R')"
    shows "FOREACH S f \<sigma>0 \<le> \<Down>R' (FOREACH S' f' \<sigma>0')"
    unfolding FOREACH_def FOREACHc_def FOREACHci_def
    apply (rule FOREACHoci_refine_genR[
      where R = "{((it,\<sigma>),(it',\<sigma>')). (\<sigma>,\<sigma>')\<in>R it'}"
      ])
    apply (rule assms)+
    using assms by auto

  lemma FOREACHi_dep_refine:
    fixes \<alpha> :: "'S \<Rightarrow> 'Sa" \<comment> \<open>Abstraction mapping of elements\<close>
    fixes S :: "'S set" \<comment> \<open>Concrete set\<close>
    fixes S' :: "'Sa set" \<comment> \<open>Abstract set\<close>
    fixes \<sigma>0 :: "'\<sigma>"
    fixes \<sigma>0' :: "'\<sigma>a"
    fixes R :: "'Sa set \<Rightarrow> (('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
    assumes INJ: "inj_on \<alpha> S" 
    assumes REFS[simp]: "S' = \<alpha>`S"
    assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R S'"
    assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
      it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
      it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R it'
    \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
    assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
      it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
      x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R it';
      x\<in>it; x'\<in>it'
    \<rbrakk> \<Longrightarrow> f x \<sigma> 
      \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R (it' - {x'})}) (f' x' \<sigma>')"
    assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R {} \<rbrakk> 
      \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
    shows "FOREACHi \<Phi> S f \<sigma>0 \<le> \<Down>R' (FOREACHi \<Phi>' S' f' \<sigma>0')"
    unfolding FOREACHi_def FOREACHci_def
    apply (rule FOREACHoci_refine_genR[
      where R = "{((it,\<sigma>),(it',\<sigma>')). ((it,\<sigma>),(it',\<sigma>'))\<in>R it'}"
      ])
    apply (fact|simp)+
    using REF0 apply simp
    apply simp
    subgoal for it \<sigma> it' \<sigma>' by(auto intro!: REFPHI[where ?it'=it'])
    using REFSTEP apply auto []
    apply (fact|simp)+
    done

  hide_const (open ) Sigma_Algebra.measure


  section \<open>Interval Iteration\<close>

  locale interval_iteration_defs = 
    fixes M::"'v mdpc"
  begin

    subsubsection \<open>Specification\<close>

    definition interval_iteration_spec :: "('v \<Rightarrow> real) \<Rightarrow> _" where 
      "interval_iteration_spec v = SPEC (\<lambda> (x', y', i). \<forall> u \<in> states M. x' u \<le> v u \<and> v u \<le> y' u)"


  end


  context MDPC_Reach_Avoid_opt
  begin

    subsection \<open>Abstract Algorithm\<close>

    lemma not_avoid_and_target: "\<not>op_is_avoid \<M> u \<or> \<not>op_is_target \<M> u"
      unfolding op_is_avoid_def op_is_target_def using AT_disj by fastforce
  
    lemma avoid_target_cases: "(\<not>op_is_avoid \<M> u \<Longrightarrow> op_is_target \<M> u \<Longrightarrow> P) \<Longrightarrow> (op_is_avoid \<M> u \<Longrightarrow> \<not>op_is_target \<M> u \<Longrightarrow> P) \<Longrightarrow> (\<not>op_is_avoid \<M> u \<Longrightarrow> \<not>op_is_target \<M> u \<Longrightarrow> P) \<Longrightarrow> P"
      using not_avoid_and_target by fast

    sublocale interval_iteration_defs \<M> .

    definition "mop_interval_iteration_gs = (\<lambda>L. do{
      x \<leftarrow> mop_init_lb \<M>;
      y \<leftarrow> mop_init_ub \<M>;
      (x,y,i,flag) \<leftarrow> WHILET (\<lambda> (x,y,i,flag). i < L \<and> flag) (\<lambda> (x,y,i,flag). do {
        ASSERT (\<forall>u \<in> states \<M>. (x u \<ge> 0 \<and> y u \<ge> 0 \<and> x u \<le> 1 \<and> y u \<le> 1));
        (x,y) \<leftarrow> mop_state_vals_gs \<M> x y;
        ASSERT (\<forall>u \<in> states \<M>. x u \<le> y u);
        flag \<leftarrow> SPEC(\<lambda>x. True);
        ASSERT(Suc i \<le> L);
        RETURN (x,y,Suc i,flag)
      }) (x,y,0,True);
      RETURN (x,y,i)
    })"

  end 


  subsection \<open>Specification for Maximal Reachability\<close>

  context MDPC_Reach_Avoid_Sup
  begin

    abbreviation "interval_iteration_pspec \<equiv> interval_iteration_spec p_real"

    lemma mop_interval_iteration_gs_correct:
      shows "mop_interval_iteration_gs L \<le> interval_iteration_pspec"
    proof -
  
      have LB0: "mop_init_lb \<M>' = SPEC(\<lambda> x. \<forall>u \<in> states \<M>. x u = R.lb_0 u)"
        if "\<M> = \<M>'" for \<M>' 
        unfolding mop_init_lb_def R.lb_0_def op_is_target_def using that 
        by(auto)
  
      have UB0: "mop_init_ub \<M>' = SPEC(\<lambda> x. \<forall>u \<in> states \<M>. x u = R.ub_0 u)"
        if "\<M> = \<M>'" for \<M>' 
        unfolding mop_init_ub_def R.ub_0_def op_is_avoid_def        
        using computesI computes_Avd_disj that AT_disj 
        by clarsimp fast 
  
      show ?thesis
        unfolding mop_interval_iteration_gs_def interval_iteration_spec_def 
        apply(clarsimp simp only: LB0 UB0)
        apply(refine_vcg WHILET_rule[where ?R="measure (\<lambda> (_,_,i,_). L - i)" and 
          ?I="(\<lambda> (x', y', i'). \<forall> u \<in> states \<M>. x' u \<le> p_real u \<and> p_real u \<le> y' u \<and> x' u \<ge> 0 \<and> y' u \<ge> 0 \<and> x' u \<le> 1 \<and> y' u \<le> 1)"])
        subgoal by blast
        subgoal 
          using lb_le_p_real ub_ge_p_real
          apply (simp add: le_fun_def)
          by(auto simp:  lb_0_val ub_0_val)
        subgoal by fast 
        subgoal
          apply(refine_vcg mop_state_vals_gs_correct[THEN order_trans, unfolded iip_gs_it_spec_def])
          subgoal by force
          subgoal by fastforce
          subgoal by force
          subgoal by fastforce
          subgoal by force
          done
        subgoal by fast
        done
    qed

  end

  subsection \<open>Specification for Minimal Reachability\<close>

  context MDPC_Reach_Avoid_Inf
  begin

    abbreviation "interval_iteration_nspec \<equiv> interval_iteration_spec n_real"

    lemma mop_interval_iteration_gs_correct:
      shows "mop_interval_iteration_gs L \<le> interval_iteration_nspec"
    proof -
  
      have LB0: "mop_init_lb \<M>' = SPEC(\<lambda> x. \<forall>u \<in> states \<M>. x u = R.lb_0 u)"
        if "\<M> = \<M>'" for \<M>' 
        unfolding mop_init_lb_def R.lb_0_def op_is_target_def using that by(auto)
  
      have UB0: "mop_init_ub \<M>' = SPEC(\<lambda> x. \<forall>u \<in> states \<M>. x u = R.ub_0 u)"
        if "\<M> = \<M>'" for \<M>' 
        unfolding mop_init_ub_def R.ub_0_def op_is_avoid_def 
        using computesI computes_Avd_disj that AT_disj
        by clarsimp fast
  
      show ?thesis
        unfolding mop_interval_iteration_gs_def interval_iteration_spec_def 
        apply(clarsimp simp only: LB0 UB0)
        apply(refine_vcg WHILET_rule[where ?R="measure (\<lambda> (_,_,i,_). L - i)" and 
          ?I="(\<lambda> (x', y', i'). \<forall> u \<in> states \<M>. x' u \<le> n_real u \<and> n_real u \<le> y' u \<and> x' u \<ge> 0 \<and> y' u \<ge> 0 \<and> x' u \<le> 1 \<and> y' u \<le> 1)"])
        subgoal by blast
        subgoal 
          using lb_le_n_real ub_ge_n_real
          apply (simp add: le_fun_def)
          by(auto simp:  lb_0_val ub_0_val)
        subgoal by fast 
        subgoal
          apply(refine_vcg mop_state_vals_gs_correct[THEN order_trans, unfolded iin_gs_it_spec_def])
          subgoal by force
          subgoal by fastforce
          subgoal by simp
          subgoal by fastforce
          subgoal by force
          done
        subgoal by fast
        done
    qed

  end

  text \<open>Interval Iteration as Sepref Operation\<close>
  definition "mop_interval_iteration = (\<lambda>\<M> L. MDPC_Reach_Avoid_Inf.interval_iteration_nspec \<M>)"

  text \<open>Interval Iteration (max/sup case) as Sepref Operation, mirroring \<^const>\<open>mop_interval_iteration\<close>.
    The underlying correctness proof is \<^const>\<open>MDPC_Reach_Avoid_Sup.interval_iteration_pspec\<close> via
    \<open>MDPC_Reach_Avoid_Sup.mop_interval_iteration_gs_correct\<close>.\<close>
  definition "mop_interval_iteration_sup = (\<lambda>\<M> L. MDPC_Reach_Avoid_Sup.interval_iteration_pspec \<M>)"

  
  section \<open>Specification for Pipeline\<close>
  abbreviation ii_tool_nspec :: "'a mdptc \<Rightarrow> (('a mdptc) \<times> ('a \<Rightarrow> real) \<times> ('a \<Rightarrow> real) \<times> nat) nres" where
    "ii_tool_nspec \<M> \<equiv> RETURN (Min_red \<M>) \<times>\<^sub>n (MDPC_Reach_Avoid_Inf.interval_iteration_nspec \<M>)"

  text \<open>Pipeline specification for the max case, mirroring \<^term>\<open>ii_tool_nspec\<close>. Note that
    \<^const>\<open>Max_red\<close> produces a collapsed MDP of type \<^typ>\<open>'a mdpc mdptc\<close>.\<close>
  abbreviation ii_tool_pspec :: "'a mdptc \<Rightarrow> (('a mdpc mdptc) \<times> ('a \<Rightarrow> real) \<times> ('a \<Rightarrow> real) \<times> nat) nres" where
    "ii_tool_pspec \<M> \<equiv> RETURN (Max_red \<M>) \<times>\<^sub>n (MDPC_Reach_Avoid_Sup.interval_iteration_pspec \<M>)"



  section \<open>Min-Reduction\<close>

  text \<open>MEC Decomposition as Sepref Operation\<close>
  definition "mop_compute_MEC = (\<lambda> (M,Avd,Tgt). SPEC (\<lambda>D. set D = Finite_MDP_defs.mec_decomp M))"


  subsection \<open>Specification\<close>

  definition op_min_red where 
    "op_min_red \<M> = Min_red \<M>"


  context MDPC_Reach_Avoid_Inf
  begin
  
  
    definition "ii_tool_pmin L = (RETURN (op_min_red \<M>)) \<times>\<^sub>n (mop_interval_iteration \<M> L)"
  
    theorem ii_tool_pmin_correct: "ii_tool_pmin L \<le> (ii_tool_nspec \<M>)"
      unfolding ii_tool_pmin_def mop_interval_iteration_def op_min_red_def
        interval_iteration_defs.interval_iteration_spec_def
      apply(refine_vcg)
      by presburger
  
  
  end

  section \<open>Max-reduction\<close>

  subsection \<open>Specification\<close>

  definition op_max_red where
    "op_max_red \<M> = Max_red \<M>"

  text \<open>The refinement relation for the collapsed MDP (step 2) — which refines the abstract
    collapsed MDP \<^typ>\<open>nat mdpc mdptc\<close> (the MEC collapse \<^const>\<open>M_mec\<close>) down to the Modest
    sparse-matrix encoding together with a MEC decomposition — lives in
    \<^file>\<open>../ds/Intf/Modest_MDP_II_Maxred.thy\<close>, the analogue of
    \<^file>\<open>../ds/Intf/Modest_MDP_II_Minred.thy\<close>.\<close>

  subsection \<open>Pipeline\<close>

  context MDPC_Reach_Avoid_Sup
  begin


    definition "ii_tool_pmax L = (RETURN (op_max_red \<M>)) \<times>\<^sub>n (mop_interval_iteration_sup \<M> L)"

    theorem ii_tool_pmax_correct: "ii_tool_pmax L \<le> (ii_tool_pspec \<M>)"
      unfolding ii_tool_pmax_def mop_interval_iteration_sup_def op_max_red_def
        interval_iteration_defs.interval_iteration_spec_def
      apply(refine_vcg)
      by presburger


  end


end
