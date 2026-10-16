theory Modest_MDP_II_Reach
  imports "../Modest_MDP_input" "../Modest_MDP_MEC" "Modest_MDP_II_Ops" "./Iterators"
begin

  text \<open>Mode-generic base for interval iteration over the Modest data structure. This theory
    collects the mode-neutral concrete operations (initialisation, transition value, state
    iteration order) together with a mode-generic Bellman backup \<^locale>\<open>reachability_opt_mode_defs\<close>,
    so that the min (\<open>Inf\<close>) and max (\<open>Sup\<close>) reductions share a single refinement proof. It is
    imported by both \<^file>\<open>Modest_MDP_II_Minred.thy\<close> and \<^file>\<open>Modest_MDP_II_Maxred.thy\<close>.\<close>


  section \<open>General Theory\<close>

  lemma sorted_wrt_sort_key_le:"(\<And> a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> g a \<le> g b \<Longrightarrow> f a b) \<Longrightarrow> sorted_wrt f (sort_key g xs)"
    apply(rule sorted_wrt_mono_rel[where ?P = "\<lambda> x y. g x \<le> g y"])
    by(auto simp flip: sorted_map[of g])

  lemma sorted_wrt_sort_key_lt:"(\<And> a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> g a < g b \<Longrightarrow> f a b) \<Longrightarrow> distinct xs \<Longrightarrow> inj_on g (set xs) \<Longrightarrow> sorted_wrt f (sort_key g xs)"
    apply(rule sorted_wrt_mono_rel[where ?P = "\<lambda> x y. g x < g y"])
    by(auto simp flip: sorted_wrt_map[of _ g] simp: strict_sorted_iff distinct_map)

  lemma hd_filter: "P (hd xs) \<Longrightarrow> hd (filter P xs) = hd xs"
    by(induction xs; auto)

  lemma tl_filter: "P (hd xs) \<Longrightarrow> tl (filter P xs) = filter P (tl xs)"
    by(induction xs; auto)

  lemma list_all_to_filter: "list_all P xs \<Longrightarrow> list_all P (filter Q xs)"
    by(induction xs; auto)

  type_synonym 'v vals = "'v \<Rightarrow> real"

  type_synonym modest_mdp = "nat list \<times> nat list \<times> nat list \<times> real list \<times> nat set \<times> nat set"

  subsection \<open>Invariant\<close>


  context modest_mdp_input_invar
  begin

    lemma conc_state_cases: "(u \<in> Cm \<Longrightarrow> P) \<Longrightarrow> (u \<in> Av \<Longrightarrow> P) \<Longrightarrow> (u \<in> Ta \<Longrightarrow> P) \<Longrightarrow> (u \<ge> N \<Longrightarrow> P) \<Longrightarrow> P"
      by (force simp: Cm_def)

    lemma N_card_StI: "N = length StI"
      by (simp add: N_DEF sorted_intvs_def)

  end


  subsection \<open>Concrete Operations\<close>

  subsubsection \<open>Interval Iteration\<close>

  context modest_mdp_input_def
  begin

    definition "is_avoid_state u = (u \<in> Av)"

    definition "is_target_state u = (u \<in> Ta)"

    definition "init_lb = do{
      let xs = replicate N (0::real);
      FOREACH {0..<N} (\<lambda> u xs. do{
        ASSERT (u < N \<and> N_len xs);
        if u \<in> Ta then
          RETURN (xs[u:=1])
        else
          RETURN xs
      }) xs
    }"

    definition "init_ub = do{
      let xs = replicate N (0::real);
      FOREACH {0..<N} (\<lambda> u xs. do{
        ASSERT (u < N \<and> N_len xs);
        if u \<in> Av then
          RETURN xs
        else
          RETURN (xs[u:=1])
      }) xs
    }"

    definition "get_trans_val xs t = do{
      let val = 0;
      val \<leftarrow> FOREACH (sn_intv (TrI ! t)) (\<lambda> b val. do{
        ASSERT(b < length Br \<and> b < length Pr);
        RETURN (val + (xs ! (Br ! b) * Pr ! b))
      }) val;
      RETURN val
    }"

  end

  definition "i_to_s N u = N - Suc u"

  lemma i_to_s0 [simp]: "i_to_s N 0 = N - Suc 0"
    unfolding i_to_s_def by blast

  lemma i_to_sN [simp]: "i_to_s N N = 0"
    unfolding i_to_s_def by simp

  lemma i_to_sNmin1 [simp]: "i_to_s N (N - Suc 0) = 0"
    unfolding i_to_s_def by simp


  subsubsection \<open>State iteration order\<close>

  context modest_mdp_input_def
  begin

    definition "u_iter_\<alpha> i = (filter (\<lambda>i. \<not>is_avoid_state i \<and> \<not>is_target_state i) (if i = N then [] else rev [0..<(Suc (i_to_s N i))]))"

    definition "u_iter_I i = (i \<le> N \<and> (i < N \<longrightarrow> \<not>is_avoid_state (i_to_s N i) \<and> \<not>is_target_state (i_to_s N i)))"

  end

  definition "u_iter_rel = (\<lambda> (St',Tr',Br',Pr',Av',Ta') N. br (modest_mdp_input_def.u_iter_\<alpha> N Av' Ta') (modest_mdp_input_def.u_iter_I N Av' Ta'))"


  subsection \<open>Mode-generic Bellman backup\<close>

  text \<open>The mode-generic optimal state value fold: combine the transition values of all actions
    with \<^term>\<open>opt\<close>, starting from the sub-unit element \<^term>\<open>vsub\<close> (\<open>1\<close> for \<open>Inf\<close>, \<open>0\<close> for \<open>Sup\<close>).\<close>
  locale modest_mdp_ii_mode_def = modest_mdp_input_def N St Tr Br Av Ta Pr + reachability_opt_mode_defs Opt opt nw vopt vsub
    for N St Tr Br Pr Av Ta and Opt opt nw vopt vsub
  begin

    definition "get_state_val_opt xs u = do {
      let xopt = vsub;
      xopt \<leftarrow> FOREACH (sn_intv (StI ! u)) (\<lambda> t xopt. do{

        ASSERT (t < length Tr - Suc 0);
        val \<leftarrow> get_trans_val xs t;
        RETURN (opt val xopt)

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


  subsection \<open>Mode-neutral Refinements\<close>

  context modest_mdp_input_invar
  begin

    lemma MDPC_Reach_Avoid_\<M>_\<alpha>: "MDPC_Reach_Avoid \<M>_\<alpha>"
      apply unfold_locales
      apply clarsimp_all
      subgoal
        by (simp add: closed_mdpc_M\<^sub>0_\<alpha>)
      subgoal
        using Finite_MDP_M\<^sub>0_\<alpha> Finite_MDP_def by blast
      subgoal
        using St_to_pmfs_ne actions_M\<^sub>0_\<alpha> states_M\<^sub>0_\<alpha> by auto
      subgoal
        using Finite_MDP_M\<^sub>0_\<alpha> Finite_MDP_def by blast
      subgoal
        by (simp add: Finite_MDP.finite_actions_M Finite_MDP_M\<^sub>0_\<alpha>)
      subgoal
        by (simp add: AvN states_M\<^sub>0_\<alpha>)
      subgoal
        by (simp add: TaN states_M\<^sub>0_\<alpha>)
      subgoal
        by (simp add: AT inf_commute)
      subgoal
        using St_to_pmfs_ut TaN actions_M\<^sub>0_\<alpha> by presburger
      subgoal
        using AvN St_to_pmfs_ua actions_M\<^sub>0_\<alpha> by presburger
      done

    sublocale MDPC_Reach_Avoid \<M>_\<alpha>
      using MDPC_Reach_Avoid_\<M>_\<alpha> .

    lemma rev_states_ref: "(rev [0..<N], states \<M>_\<alpha>) \<in> \<langle>node_rel' N\<rangle>list_set_rel"
      unfolding is_avoid_state_def is_target_state_def
      by (auto simp flip: Ball_set simp: list_to_set_b_rel states_M\<^sub>0_\<alpha> intro!: list_all_to_filter)

    lemma is_avoid_state_alt:
      assumes UREL: "(ui,u) \<in> node_rel' N"
      shows "is_avoid_state ui = op_is_avoid \<M>_\<alpha> u"
      using UREL unfolding is_avoid_state_def op_is_avoid_def
      by auto

    lemma is_target_state_alt:
      assumes UREL: "(ui,u) \<in> node_rel' N"
      shows "is_target_state ui = op_is_target \<M>_\<alpha> u"
      using UREL unfolding is_target_state_def op_is_target_def
      using AT by auto

    lemma init_ub_refine:
      shows "init_ub \<le> \<Down>(\<langle>node_rel' N,Id\<rangle>list_fun_rel N) (mop_init_ub \<M>_\<alpha>)"
      unfolding init_ub_def mop_init_ub_def op_is_avoid_def
      apply (clarsimp simp: conc_fun_SPEC )
      apply(refine_vcg FOREACH_rule[where ?I="(\<lambda>it \<sigma>. (\<forall>u\<in>it. \<sigma> ! u = 0) \<and> (\<forall>u\<in>{0..<N} - it. \<sigma> ! u = (if u \<in> Av then 0 else 1)) \<and> length \<sigma> = N)"])
      subgoal by blast
      subgoal by force
      subgoal by blast
      subgoal by simp
      subgoal by fastforce
      subgoal unfolding N_len_def by presburger
      subgoal by blast
      subgoal by fastforce
      subgoal by auto
      subgoal by auto
      subgoal by (auto split: if_splits simp: nth_list_update')
      subgoal by (auto split: if_splits simp: nth_list_update')
      subgoal
        apply(intro Ex_fun_eq_list_fun_rel[where ?f=id and ?g=id])
        subgoal by presburger
        subgoal by fastforce
        subgoal by force
        subgoal by fastforce
        subgoal
          by (simp add: states_M\<^sub>0_\<alpha>)
        done
      done


    lemma init_lb_refine:
      shows "init_lb \<le> \<Down>(\<langle>node_rel' N,Id\<rangle>list_fun_rel N) (mop_init_lb \<M>_\<alpha>)"
      unfolding init_lb_def mop_init_lb_def op_is_target_def
      apply (clarsimp simp: conc_fun_SPEC )
      apply(refine_vcg FOREACH_rule[where ?I="(\<lambda>it \<sigma>. (\<forall>u\<in>it. \<sigma> ! u = 0) \<and> (\<forall>u\<in>{0..<N} - it. \<sigma> ! u = (if u \<in> Ta then 1 else 0)) \<and> length \<sigma> = N)"])
      subgoal by blast
      subgoal by force
      subgoal by blast
      subgoal by simp
      subgoal by fastforce
      subgoal unfolding N_len_def by presburger
      subgoal by (auto split: if_splits simp: nth_list_update')
      subgoal by (auto split: if_splits simp: nth_list_update')
      subgoal by auto
      subgoal by blast
      subgoal by force
      subgoal by blast
      subgoal
        apply(intro Ex_fun_eq_list_fun_rel[where ?f=id and ?g=id])
        subgoal by presburger
        subgoal by fastforce
        subgoal by force
        subgoal by fastforce
        subgoal
          by (simp add: states_M\<^sub>0_\<alpha>)
        done
      done

    lemma get_trans_val_min_refine: (*TODO: This proof could be easier if adapted for abstract states*)
      assumes TB: "t < length Tr - Suc 0"
      assumes LFR: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes TID: "(t',t) \<in> Id"
      shows "get_trans_val xs t' \<le> RETURN (op_trans_val \<M>_\<alpha> x (Tr_to_pmf t))"
    proof -

      define f where "f \<equiv> (\<lambda> it v. x v * sum ((!) Pr) {ba. ba \<notin> it \<and> in_intv (TrI ! t) ba \<and> v = (Br ! ba)})"

      define I where "I \<equiv> (\<lambda> (it::nat set) (\<sigma>::real). \<sigma> = (\<Sum>v\<in>{0..<N}. f it v))"

      {
        fix b it \<sigma>
        assume BCM: "Br ! b < N"
        and BIT: "b \<in> it" and ITR: "it \<subseteq> sn_intv (TrI ! t)" and INV: "I it \<sigma>"

        have AUX1: "v = Br ! b \<Longrightarrow> {ba. (ba \<in> it \<longrightarrow> ba = b) \<and> in_intv (TrI ! t) ba \<and> v = Br ! ba} = insert b {ba. ba \<notin> it \<and> in_intv (TrI ! t) ba \<and> v = Br ! ba}" for v
          using BIT ITR by auto

        have AUX2: "v \<noteq> Br ! b \<Longrightarrow> {ba. (ba \<in> it \<longrightarrow> ba = b) \<and> in_intv (TrI ! t) ba \<and> v = Br ! ba} = {ba. ba \<notin> it \<and> in_intv (TrI ! t) ba \<and> v = Br ! ba}" for v
          by auto

        have "sum (f (it - {b})) {0..<N} = sum (f (it - {b})) ({0..<N} - {Br ! b}) + f (it - {b}) (Br ! b)"
          using BCM Cm_mem by (simp add: sum_diff1)
        also have "... = sum (f it) ({0..<N} - {Br ! b}) + f (it - {b}) (Br ! b)"
          unfolding f_def by (auto simp: AUX2 intro!: Finite_Cartesian_Product.sum_cong_aux)
        also have "... = sum (f it) ({0..<N} - {Br ! b}) + f it (Br ! b) + x (Br ! b) * Pr ! b"
          unfolding f_def
          using finite_sn_intv sn_intv_def BIT ITR by (auto simp: AUX1 ring_distribs(1))
        also have "... = sum (f it) {0..<N} + xs ! (Br ! b) * Pr ! b"
          using BCM LFR by (auto simp: sum_diff in_br_conv Cm_mem elim!: list_fun_relE)
        finally have "sum (f (it - {b})) {0..<N} = sum (f it) {0..<N} + xs ! (Br ! b) * Pr ! b" .

        hence "I (it - {b}) (\<sigma> + xs ! (Br ! b) * Pr ! b)"
          using INV unfolding I_def by algebra

      } note STEP1 = this


      have INIT: "I (sn_intv (TrI ! t')) 0"
        unfolding I_def f_def using TID by (auto simp flip: conj_assoc)

      have A: "x < length Br" and B: "x < length Pr" if "x \<in> it" and "it \<subseteq> sn_intv (TrI ! t')" for x it
        using Tr_dom that TB TID by (auto intro!: Br_in_bound_intvD)

      have STEP: "I (it - {b}) (\<sigma> + xs ! (Br ! b) * Pr ! b)"
        if "b \<in> it" and "it \<subseteq> sn_intv (TrI ! t)" and "I it \<sigma>" for b it \<sigma>
        apply(rule STEP1[OF _ that])
        using A Br_in_bound TID that(1,2) by blast

      have FIN: "sum (f {}) {0..<N} = (\<Sum>v\<in>{0..<N}. x v * pmf (Tr_to_pmf t) v)"
        unfolding f_def
        by (auto simp: pmf_Tr_to_pmf_set[OF TB] sum.reindex intro: Finite_Cartesian_Product.sum_cong_aux)

      show ?thesis
        unfolding get_trans_val_def
        apply (refine_vcg FOREACH_rule[where ?I=I])
        subgoal by simp
        subgoal using INIT .
        subgoal using A .
        subgoal using B .
        subgoal using TID by(auto intro: STEP)
        subgoal unfolding I_def
          by (auto simp: op_trans_val_def  states_M\<^sub>0_\<alpha> FIN)
        done
    qed

  end


  subsection \<open>Mode-generic Refinement of the Bellman backup\<close>

  locale modest_mdp_ii_mode_invar = modest_mdp_input_invar + modest_mdp_ii_mode_def + reachability_opt_mode Opt opt nw vopt vsub +
    assumes vDom_alt: "vDom = {0..1}"
  begin

    lemma get_state_val_opt_refine:
      assumes UREL: "(ui,u) \<in> node_rel' N"
      assumes LFR: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes UB: "u \<in> states M\<^sub>0_\<alpha>"
      assumes UNA: "\<not>op_is_avoid \<M>_\<alpha> u"
      assumes UNT: "\<not>op_is_target \<M>_\<alpha> u"
      assumes XB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> x v \<in> vDom"
      shows "get_state_val_opt xs ui \<le> RETURN (op_state_val \<M>_\<alpha> x u)"
    proof -

      from UREL have UIN: "u < N" and [simp]: "ui = u"
        by auto

      from UNA UNT have UNA': "u \<notin> Av" and UNT': "u \<notin> Ta"
        unfolding op_is_avoid_def op_is_target_def  by auto

      with UIN have UIC: "u \<in> Cm"
        unfolding op_is_avoid_def op_is_target_def Cm_mem by blast


      define g where "g \<equiv> (\<lambda> p. \<Sum>v \<in> states M\<^sub>0_\<alpha>. x v * pmf p v)"
      define f where "f \<equiv> (\<lambda> it. (\<lambda> x. Tr_to_pmf x) ` (sn_intv (StI ! u) - it))"


      define I where "I \<equiv> (\<lambda> (it::nat set) (\<sigma>::real). \<sigma> = Opt (insert vsub {g p |p. p \<in> f it}))"


      have FS: "f it \<subseteq> actions M\<^sub>0_\<alpha> u" for it
        unfolding actions_M\<^sub>0_\<alpha>[OF UIN] f_def
        by (auto intro!: imageI simp: St_to_pmfs_nta[OF UIC] UNT' UNA')

      have FUPD: "f (it - {x}) = insert (Tr_to_pmf x) (f it)" if "x \<in> it" "it \<subseteq> sn_intv (StI ! u)" for it x
        unfolding f_def using that
        by (simp add: it_step_insert_iff)

      have GDEF: "g = op_trans_val \<M>_\<alpha> x"
        unfolding op_trans_val_def g_def
        using \<M>_\<alpha>_simps(1) by presburger

      hence AUX1: "in_vDom (g p)" if "u \<in> states M\<^sub>0_\<alpha>" and "p \<in> actions M\<^sub>0_\<alpha> u" for p u
        using XB that unfolding in_vDom_alt vDom_alt
        using expectation_trans_val pmf_expectation_ge_zero pmf_expectation_le_one
        by (auto intro!: op_trans_val_ge_zero_\<M> that op_trans_val_le_one_\<M>)


      have INIT: "I (sn_intv (StI ! u)) vsub"
        unfolding I_def g_def f_def by (auto simp: Opt_singleton)

      have P1: "\<And>x it \<sigma>. x \<in> it \<Longrightarrow> it \<subseteq> sn_intv (StI ! u) \<Longrightarrow> I it \<sigma> \<Longrightarrow> x < length Tr - Suc 0"
        using Tr_in_bound_intvD UB in_subset_sn_intv UREL by simp

      have STEP: "I (it - {xa}) (opt (op_trans_val \<M>_\<alpha> x (Tr_to_pmf xa)) \<sigma>)"
        if "xa \<in> it" "it \<subseteq> sn_intv (StI ! u)" "I it \<sigma>" for it xa \<sigma>
        using that(3) unfolding I_def op_trans_val_def
        apply (simp add: FUPD[OF that(1-2)])
        apply(subst insert_commute)
        apply(subst Opt_insert2[of _ "g (Tr_to_pmf xa)"])
        subgoal using FS UB by (auto simp: sub_vDom_def intro!: AUX1[of u])
        subgoal by blast
        subgoal using that (1-2)
          by (auto intro!: AUX1 UB imageI simp: St_to_pmfs_nta[OF UIC] actions_M\<^sub>0_\<alpha>[OF UIN])
        subgoal unfolding GDEF op_trans_val_def  by auto
        done

      have FIN: "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> \<sigma> = opt vsub (Opt {\<Sum>v \<in> states M\<^sub>0_\<alpha>. x v * pmf p v |p. p \<in> actions M\<^sub>0_\<alpha> u})"
        unfolding I_def f_def
        apply(subst(asm) Opt_insert2)
        subgoal by (auto simp add: sub_vDom_def St_to_pmfs_nta[OF UIC] actions_M\<^sub>0_\<alpha>[OF UIN] intro!: AUX1[OF UB])
        subgoal using UREL by (auto simp: St_nonempty )
        subgoal by simp
        subgoal unfolding Diff_empty actions_M\<^sub>0_\<alpha>[OF UIN]
          apply (simp only: image_image St_to_pmfs_nta[OF UIC] GDEF)
          using UNA' UNT' GDEF g_def
          by presburger
        done

      have "get_state_val_opt xs ui \<le> RETURN (opt vsub (op_state_val \<M>_\<alpha> x u))"
        unfolding get_state_val_opt_def
        apply simp
        apply(refine_vcg FOREACH_rule[where ?I=I])
        subgoal by simp
        subgoal using INIT by blast
        subgoal using P1 by blast
        subgoal using STEP
          by (auto intro!: LFR get_trans_val_min_refine[THEN order_trans])
        subgoal
          apply(drule FIN) using UB unfolding St_to_pmfs_alt op_state_val_def
          by force
        done

      moreover have "opt vsub (op_state_val \<M>_\<alpha> x u) = op_state_val \<M>_\<alpha> x u"
        apply(rule opt_vsub1)
        unfolding op_state_val_def
        apply clarsimp
        apply(rule Opt_vDom)
        using AUX1 assms(3) g_def sub_vDom_def apply auto[1]
        using actions_finite' assms(3) by auto

      ultimately show ?thesis
        by auto
    qed


    lemma updated_state_val_gs_refine:
      assumes XB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> x v \<le> 1"
      assumes YB: "\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> y v \<le> 1"
      assumes XSX: "(xs,x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YSY: "(ys,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      shows "updated_state_val_gs xs ys \<le> \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_state_vals_gs \<M>_\<alpha> x y)"
    proof -

      have AUX1: "get_state_val_opt x1a xi
       \<le> Refine_Basic.SPEC (\<lambda>c. (c, op_state_val \<M>_\<alpha> x1 xa) \<in> Id)"
        if "(xi, xa) \<in> node_rel' N" "(x1a,x1) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N" "xa \<in> states M\<^sub>0_\<alpha>"
          "\<not> op_is_avoid \<M>_\<alpha> xa" "\<not> op_is_target \<M>_\<alpha> xa" "(\<And>v. v \<in> states M\<^sub>0_\<alpha> \<Longrightarrow> x1 v \<in> vDom)"
        for x1a xi x1 xa
          apply(refine_vcg order_trans[OF get_state_val_opt_refine] )
          using that by auto

      have AUX2: "(rev [0..<N], states \<M>_\<alpha>) \<in> \<langle>node_rel' N\<rangle>list_set_rel"
        using rev_states_ref by argo

      have AUX3: "(x,y) \<in> node_rel' N \<Longrightarrow> (x,y) \<in> node_rel' N" for x y
        by presburger

      have AUX4: "(x,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N \<Longrightarrow> (x,y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N" for x y
        by presburger

      have AUX5: "x = y \<Longrightarrow> (x,y) \<in> Id" for x y
        by blast

      show ?thesis
        unfolding updated_state_val_gs_def mop_state_vals_gs_def IT_nfoldli_def
        apply clarsimp
        apply(refine_rcg LFO_refine AUX1  )
        apply(vc_solve simp del: b_rel_simp solve: AUX2 AUX3 AUX4 AUX5)
        subgoal using AUX2 by auto
        subgoal by auto
        subgoal by(auto intro: list_fun_relD1 simp: N_len_def)
        subgoal by(auto intro: list_fun_relD1 simp: N_len_def)
        subgoal by(auto simp: is_avoid_state_alt)
        subgoal by(auto simp: is_target_state_alt)
        subgoal by (auto simp: vDom_alt )
        subgoal by (auto simp: vDom_alt )
        subgoal by (auto intro!: list_fun_rel_upd)
        subgoal using assms(3,4) by blast
        done

    qed

  end

end
