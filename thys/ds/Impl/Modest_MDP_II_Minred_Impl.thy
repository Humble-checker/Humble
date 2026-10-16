theory Modest_MDP_II_Minred_Impl
  imports "Modest_MDP_II_Reach_Impl" "../Intf/Modest_MDP_II_Minred"
begin (*TODO: if I put MEC first, coercions for mdptc break, if I put minred first, nres becomes neM*)

  section \<open>Refinement to LLVM\<close>

  subsection \<open>Extracted operations\<close>

  locale interval_iteration_inf_env_defs = interval_iteration_env_defs
  begin

    sublocale reachability_opt_mode_defs Inf inf "(\<le>)" 0 1 .

    definition "mop_state_vals_gs_inf = mop_state_vals_gs"

    definition makeA :: "modest_mdp \<Rightarrow> nat \<Rightarrow> modest_mdp" where "makeA = (\<lambda> (St,Tr,Br,Pr,Av,Ta) u. (St,Tr,Br,Pr,insert u Av,Ta))"
    definition makeT :: "modest_mdp \<Rightarrow> nat \<Rightarrow> modest_mdp" where "makeT = (\<lambda> (St,Tr,Br,Pr,Av,Ta) u. (St,Tr,Br,Pr,Av,insert u Ta))"

    subsubsection \<open>Interval Iteration\<close>

    interpretation modest_mdp_ii_inf_def .

    definition "get_state_val_lb_impl = (\<lambda> MDP xs u. do {
      let xmin = op_1_lb_nn; 
      (_,xmin) \<leftarrow> WHILET (\<lambda>(t, xmin). t < St_nth_uid MDP u) (\<lambda> (t, xmin). do{ 
        xmin \<leftarrow> do{
  
          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_lb_impl MDP xs t;
          RETURN (op_min_lb val xmin)
  
        };
        ASSERT (t < length (tTr MDP));
        RETURN (t + 1,xmin)
      }) (St_nth_lid MDP u,xmin);
      RETURN xmin
    })"
    sepref_register get_state_val_lb_impl

    definition "get_state_val_ub_impl = (\<lambda> MDP xs u. do {
      let xmin = op_1_ub_nn; 
      (_,xmin) \<leftarrow> WHILET (\<lambda>(t, xmin). t < St_nth_uid MDP u) (\<lambda> (t, xmin). do{ 
        xmin \<leftarrow> do{
  
          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_ub_impl MDP xs t;
          RETURN (op_min_ub val xmin)
  
        };
        ASSERT (t < length (tTr MDP));
        RETURN (t + 1,xmin)
      }) (St_nth_lid MDP u,xmin);
      RETURN xmin
    })"
    sepref_register get_state_val_ub_impl


    definition "updated_state_val_gs_impl = (\<lambda> MDP xs ys. do {
      let N' = b_assn_open_block_fun N (\<lambda> N. N);
      nfoldli (rev [0..<N']) (\<lambda>_. True) (\<lambda> u (xs,ys). do {
        ASSERT (u < N \<and> N_len xs \<and> N_len ys);
        let u' = op_bound_val (\<lambda>i. i < N) u;
        if isA MDP u' then RETURN (xs,ys) 
        else if isT MDP u' then RETURN (xs,ys) 
        else do {
          xmin \<leftarrow> get_state_val_lb_impl MDP xs u';
          ymin \<leftarrow> get_state_val_ub_impl MDP ys u';
          RETURN (xs[u:=xmin],ys[u:=ymin])
        }
      }) (xs,ys)
    })"
    sepref_register updated_state_val_gs_impl
    subsubsection \<open>Reduction\<close>

    definition "is_trivial_impl MDP D u = do{
      (_,flag) \<leftarrow> WHILET (\<lambda>(t, flag). t < St_nth_uid MDP u \<and> flag) (\<lambda> (t, flag). do{
        ASSERT (t < length (tTr MDP) - Suc 0);
        (_,flag) \<leftarrow> WHILET (\<lambda>(b, flag). b < Tr_nth MDP (Suc t) \<and> \<not>flag) (\<lambda> (b, flag). do{
          ASSERT (b < length (tBr MDP) \<and> (\<exists> i < length D. u \<in> D ! i) \<and> (\<exists> i < length D. tBr MDP ! b \<in> D ! i));
          RETURN (Suc b, \<not>op_in_eq_mec D u (Br_nth MDP b))
        }) (Tr_nth MDP t,False);
        RETURN (Suc t, flag)
      }) (St_nth_lid MDP u,True);
      RETURN flag
    }"

    definition "make_sink_noop DS u = DS"
    subsection \<open>Extraction proofs\<close>

    subsubsection \<open>Interval Iteration\<close>
    lemma get_state_val_opt_lb_impl_refine:
      assumes INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
      assumes UB: "u < N"
      assumes NXS: "N_len xs"
      shows "get_state_val_lb_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> modest_mdp_ii_inf_def.get_state_val_opt St Tr Br Pr xs u"
    proof -

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .
      have II: "modest_mdp_input_invar N St Tr Br Pr Av Ta" using INV by (simp add: modest_mdp_ii_invar_inf_def)

      define f where "f \<equiv> (\<lambda> MDP xs u. do {
        let xmin = 1; 
        xmin \<leftarrow> WHILE_intv (tSt MDP) u (\<lambda> t xmin. do{
  
          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_lb_impl MDP xs t;
          RETURN (inf val xmin)
  
        }) xmin;
        RETURN xmin
      })"

      have "get_state_val_lb_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> f (St,Tr,Br,Pr,Av,Ta) xs u"
        unfolding f_def get_state_val_lb_impl_def WHILE_intv_def St_nth_uid_alt St_nth_lid_alt
        apply (clarsimp simp: Real.inf_real_def op_min_lb_def op_1_lb_nn_def)
        apply(refine_vcg Refine_Basic.bind_mono(1) while.WHILE_mono_prover_rule(3))
        subgoal by blast
        subgoal by blast
        subgoal using UB uid_sorted_intvs[OF sorted_St] St_in_bound 
          by (fastforce simp: refine_pw_simps pw_le_iff N_DEF intro!: ) 
        subgoal 
          by fast
        subgoal
          by presburger
        done

      also have "f (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> modest_mdp_ii_inf_def.get_state_val_opt St Tr Br Pr xs u"
        unfolding f_def modest_mdp_ii_inf_def.get_state_val_opt_def
        apply (clarsimp simp flip: FOREACH_intv_def)
        apply (refine_vcg WHILE_intv_refine[where ?R=Id, simplified] while.ibind_mono)
        (*TODO why do I need bind_mono here, usually this happens automatically*)
        by (auto simp: sorted_St UB[unfolded N_DEF] intro!: get_trans_val_lb_impl_refine[OF II] NXS)

      finally show ?thesis .
    qed

    lemma get_state_val_opt_ub_impl_refine:
      assumes INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
      assumes UB: "u < N"
      assumes NXS: "N_len xs"
      shows "get_state_val_ub_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> modest_mdp_ii_inf_def.get_state_val_opt St Tr Br Pr xs u"
    proof -

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .
      have II: "modest_mdp_input_invar N St Tr Br Pr Av Ta" using INV by (simp add: modest_mdp_ii_invar_inf_def)

      define f where "f \<equiv> (\<lambda> MDP xs u. do {
        let xmin = 1; 
        xmin \<leftarrow> WHILE_intv (tSt MDP) u (\<lambda> t xmin. do{
  
          ASSERT (t < length (tTr MDP) - Suc 0);
          val \<leftarrow> get_trans_val_ub_impl MDP xs t;
          RETURN (inf val xmin)
  
        }) xmin;
        RETURN xmin
      })"

      have "get_state_val_ub_impl (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> f (St,Tr,Br,Pr,Av,Ta) xs u"
        unfolding f_def get_state_val_ub_impl_def WHILE_intv_def St_nth_uid_alt St_nth_lid_alt
        apply (clarsimp simp: Real.inf_real_def op_min_ub_def op_1_ub_nn_def)
        apply(refine_vcg Refine_Basic.bind_mono(1) while.WHILE_mono_prover_rule(3))
        subgoal by blast
        subgoal by blast
        subgoal using UB uid_sorted_intvs[OF sorted_St] St_in_bound 
          by (fastforce simp: refine_pw_simps pw_le_iff N_DEF intro!: ) 
        subgoal 
          by fast
        subgoal
          by presburger
        done

      also have "f (St,Tr,Br,Pr,Av,Ta) xs u
        \<le> modest_mdp_ii_inf_def.get_state_val_opt St Tr Br Pr xs u"
        unfolding f_def modest_mdp_ii_inf_def.get_state_val_opt_def
        apply (clarsimp simp flip: FOREACH_intv_def)
        apply (refine_vcg WHILE_intv_refine[where ?R=Id, simplified] while.ibind_mono)
        (*@TODO why do I need bind_mono here, usually this happens automatically*)
        by (auto simp: sorted_St UB[unfolded N_DEF] intro!: get_trans_val_ub_impl_refine[OF II] NXS)

      finally show ?thesis .
        
    qed
    lemma updated_state_val_gs_impl_refine: 
      assumes INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
      shows "updated_state_val_gs_impl (St,Tr,Br,Pr,Av,Ta) xs ys \<le>
      modest_mdp_ii_inf_def.updated_state_val_gs N St Tr Br Pr Av Ta xs ys"
    proof -

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      have B: "(rev [0..<N], rev [0..<N]) \<in> \<langle>Id\<rangle>list_rel"
        by auto

      show ?thesis
        unfolding updated_state_val_gs_impl_def modest_mdp_ii_inf_def.updated_state_val_gs_def IT_nfoldli_eq
        apply (clarsimp simp: b_assn_open_block_fun_def)

        apply(rule nfoldli_refine[where ?R=Id, simplified])
        apply(vc_solve solve: B)
        apply(refine_vcg)
        apply(vc_solve simp: isT_alt isA_alt )
        apply(refine_vcg bind_mono(1) order_trans[OF get_state_val_opt_lb_impl_refine] order_trans[OF get_state_val_opt_ub_impl_refine])
        by(auto simp: INV)

    qed

    subsubsection \<open>Reduction\<close>

    lemma is_trivial_impl_refine: 
      assumes INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
      assumes UB: "u < N"
      shows "is_trivial_impl (St,Tr,Br,Pr,Av,Ta) D u \<le> is_trivial D u"
    proof -

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      define f :: "modest_mdp \<Rightarrow> _" where "f = (\<lambda> MDP. do{
        WHILEc_intv (tSt MDP) u (\<lambda> flag. flag) (\<lambda>t flag. do{
          ASSERT (t < length (tTr MDP) - Suc 0);
          WHILEc_intv (tTr MDP) t (\<lambda> flag. \<not>flag) (\<lambda>b flag. do{
            ASSERT (b < length (tBr MDP) \<and> (\<exists> i < length D. u \<in> D ! i) \<and> (\<exists> i < length D. Br ! b \<in> D ! i));
            RETURN (\<not>op_in_eq_mec D u (Br ! b))
          }) False
        }) True
      })"

      have "is_trivial_impl (St,Tr,Br,Pr,Av,Ta) D u \<le> f (St,Tr,Br,Pr,Av,Ta)"
        unfolding is_trivial_impl_def f_def WHILEc_intv_def St_nth_uid_def St_nth_lid_def Tr_nth_def 
          b_assn_open_block_fun2_def b_assn_open_block_fun_def
        apply clarsimp
        apply (refine_vcg Refine_Basic.bind_mono(1) while.WHILE_mono_prover_rule(3))
        apply(vc_solve)
        apply (refine_vcg Refine_Basic.bind_mono(1) while.WHILE_mono_prover_rule(3))
        apply (vc_solve simp: Br_nth_def b_assn_open_block_fun_def)
        apply refine_vcg
        by blast

      also have "... \<le> is_trivial D u"
        unfolding f_def is_trivial_def
        apply (clarsimp simp flip: FOREACHc_intv_def)
        apply (refine_vcg WHILEc_intv_refine[where ?R=Id, simplified] while.ibind_mono)
        using sorted_St sorted_Tr UB N_DEF by auto

      finally show ?thesis .
    qed

    lemma make_sink_noop_alt: "make_sink_noop (St,Tr,Br,Pr,Av,Ta) u = make_sink u"
      unfolding make_sink_noop_def make_sink_def by(rule refl)
  end
  subsection \<open>Assertions\<close>


  definition "Modest_mdp_inf_assn N = hr_comp (modest_init_mdp_env_defs.Modest_mdp_assn_aux N) (modest_mdp_inf_rel N)"

  definition "Modest_mdp_inf_DS_assn N DS = hr_comp (modest_init_mdp_env_defs.Modest_mdp_assn_aux N) (modest_mdp_inf_DS_rel N DS)"

  lemma Modest_mdp_inf_assn_DS: "Modest_mdp_inf_assn N M Ei = (EXS DS. Modest_mdp_inf_DS_assn N DS M Ei)"
    unfolding Modest_mdp_inf_assn_def Modest_mdp_inf_DS_assn_def
      modest_mdp_inf_DS_rel_def modest_mdp_inf_rel_def
    apply(cases M)
    by(auto simp: in_br_conv fun_eq_iff hr_comp_def sep_algebra_simps)
  context interval_iteration_inf_env_defs
  begin

    lemma init_ub_impl_refine:
      assumes REL: "(DS, M) \<in> modest_mdp_inf_rel N"
      shows "init_ub_impl DS \<le> \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_init_ub M)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta" and [simp]: "M = modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr" 
        unfolding DDEF modest_mdp_inf_rel_def modest_mdp_input_invar_def by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      show ?thesis 
        apply(rule order_trans[OF init_ub_impl_alt])
        apply (simp add: DDEF)
        apply(rule init_ub_refine)
        done
    qed

    lemma init_lb_impl_refine:
      assumes REL: "(DS, M) \<in> modest_mdp_inf_rel N"
      shows "init_lb_impl DS \<le> \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_init_lb M)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_input_invar N St Tr Br Pr Av Ta" and [simp]: "M = modest_mdp_input_def.\<M>_\<alpha> N St Tr Br Av Ta Pr"
        unfolding DDEF modest_mdp_inf_rel_def modest_mdp_ii_invar_inf_def by(auto simp: in_br_conv)

      from INV interpret modest_mdp_input_invar N St Tr Br Pr Av Ta .

      show ?thesis 
        apply(rule order_trans[OF init_lb_impl_alt])
        apply (simp add: DDEF)
        apply(rule init_lb_refine)
        done
    qed

    lemma get_state_val_lb_impl_refine_aux:
      assumes NAV: "\<not> op_is_avoid \<M> u"
      assumes NTA: "\<not> op_is_target \<M> u"
      assumes XU: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> x v \<le> 1)"
      assumes XL: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> 0 \<le> x v)"
      assumes REL: "(DS, \<M>) \<in> modest_mdp_inf_rel N"
      assumes XREL: "(xs, x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes UREL: "(ui, u) \<in> node_rel' N"
      shows "get_state_val_lb_impl DS xs ui
       \<le> RETURN (op_state_val \<M> x u)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast
        
      from REL have INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)


      from XREL have NX: "N_len xs"
        unfolding list_fun_rel_def N_len_def by(auto simp:  in_br_conv)

      from UREL have UIN: "ui < N"
        by(auto)

      with UREL have US: "u \<in> states M\<^sub>0_\<alpha>"
        by(simp add: states_M\<^sub>0_\<alpha>)

      show ?thesis
        using NAV NTA XU XL 
        by(auto simp: vDom_alt DDEF intro!: order_trans[OF get_state_val_opt_lb_impl_refine[OF INV UIN NX] get_state_val_opt_refine[OF UREL XREL US]])

    qed

    lemma get_state_val_ub_impl_refine_aux:
      assumes NAV: "\<not> op_is_avoid \<M> u"
      assumes NTA: "\<not> op_is_target \<M> u"
      assumes XU: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> x v \<le> 1)"
      assumes XL: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> 0 \<le> x v)"
      assumes REL: "(DS, \<M>) \<in> modest_mdp_inf_rel N"
      assumes XREL: "(xs, x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes UREL: "(ui, u) \<in> node_rel' N"
      shows "get_state_val_ub_impl DS xs ui
       \<le> RETURN (op_state_val \<M> x u)"
    proof -
        
      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast
        
      from REL have INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_input_def.\<M>_\<alpha>_def modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)


      from XREL have NX: "N_len xs"
        unfolding list_fun_rel_def N_len_def by(auto simp: in_br_conv)

      from UREL have UIN: "ui < N"
        by(auto)

      with UREL have US: "u \<in> states M\<^sub>0_\<alpha>"
        by(simp add: states_M\<^sub>0_\<alpha>)

      show ?thesis
        using NAV NTA XU XL 
        by(auto simp: vDom_alt DDEF intro!: order_trans[OF get_state_val_opt_ub_impl_refine[OF INV UIN NX] get_state_val_opt_refine[OF UREL XREL US]])
    qed


    lemma updated_state_val_gs_impl_refine_aux:
      assumes REL: "(DS, \<M>) \<in> modest_mdp_inf_rel N"
      assumes XREL: "(xs, x) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes YREL: "(ys, y) \<in> \<langle>node_rel' N, Id\<rangle>list_fun_rel N"
      assumes XU: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> x v \<le> 1)"
      assumes XL: "(\<And>v. v \<in> states (to_mdpc \<M>) \<Longrightarrow> y v \<le> 1)"
      shows "updated_state_val_gs_impl DS xs ys \<le> 
      \<Down> (\<langle>node_rel' N, Id\<rangle>list_fun_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) (mop_state_vals_gs \<M> x y)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_input_def.\<M>_\<alpha>_def modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)


      show ?thesis
        by(auto simp: DDEF intro!: XL XU order_trans[OF updated_state_val_gs_impl_refine[OF INV] updated_state_val_min_gs_refine[OF _ _ XREL YREL]])
    qed

    lemma is_trivial_impl_refine_aux: 
      assumes REL: "(DS, \<M>) \<in> modest_mdp_inf_rel N"
      assumes DREL: "(Di,D) \<in> Id"
      assumes UREL: "(ui,u) \<in> node_rel' N"
      assumes D: "set D = mec_decomp' M'" "states M' = states (to_mdpc \<M>)" "distinct D"
      assumes UCM: "u \<notin> avoids \<M>" "u \<notin> targets \<M>"
      shows "is_trivial_impl DS Di ui \<le> RETURN (op_is_trivial \<M> D u)"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)


      from UREL UCM have UCM': "ui \<in> Cm"
        unfolding Cm_def by auto

      show ?thesis
        unfolding DDEF
        apply(rule order_trans[OF is_trivial_impl_refine])
        using INV apply presburger
        using UREL apply simp
        apply(rule order_trans[OF is_trivial_correct[of _ _ M']])
        using UCM' apply presburger
        using DREL D UREL by (auto)
    qed

    lemma makeA_refine:
      assumes CMP: "u \<notin> targets \<M>"
      assumes REL: "(DS, \<M>) \<in> modest_mdp_inf_rel N"
      assumes UN: "u < N"
      shows "(makeA DS u, op_make_avd_sink \<M> u) \<in> modest_mdp_inf_rel N"
    proof -

      obtain St Tr Br Pr Av Ta where DDEF: "DS = (St,Tr,Br,Pr,Av,Ta)"
        apply(cases DS) by blast

      from REL have INV: "modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)

      from INV interpret modest_mdp_ii_invar_inf N St Tr Br Pr Av Ta .

      from REL have [simp]: "to_mdpc \<M> = M\<^sub>0_\<alpha>" "avoids \<M> = Av" "targets \<M> = Ta" "\<M> = \<M>_\<alpha>"
        unfolding DDEF modest_mdp_inf_rel_def 
        by(auto simp: in_br_conv)

      
      have A: "makeA (St,Tr,Br,Pr,Av,Ta) u = make_avd_sink u"
        unfolding makeA_def make_avd_sink_def by simp

      have B: "u \<in> states M\<^sub>0_\<alpha>"
        by(auto simp: UN states_M\<^sub>0_\<alpha>)

      show ?thesis
        unfolding modest_mdp_inf_rel_def 
        using CMP make_avd_sink_\<alpha>[of u] make_avd_sink_invar[of u]
        by(auto simp: B DDEF in_br_conv make_sink_noop_def 
          simp flip: A)
    qed


    interpretation modest_mdp_ii_inf_def .


    definition "get_state_val_pre = (\<lambda> ((\<M>,x),u). \<not>op_is_avoid \<M> u \<and> \<not> op_is_target \<M> u \<and> (\<forall>v \<in> states (to_mdpc \<M>). x v \<le> 1) \<and> (\<forall>v \<in> states (to_mdpc \<M>). 0 \<le> x v))"

    definition "upd_state_val_pre = (\<lambda> ((\<M>,x),y). (\<forall>v \<in> states (to_mdpc \<M>). x v \<le> 1) \<and> (\<forall>v \<in> states (to_mdpc \<M>). y v \<le> 1))"

    definition "is_trivial_pre = (\<lambda> ((\<M>,D),u). (\<exists>M'. set D = mec_decomp' M' \<and> states M' = states (to_mdpc \<M>)) \<and> distinct D \<and> u \<notin> avoids \<M> \<and> u \<notin> targets \<M>)"

    definition "make_avd_sink_pre = (\<lambda> (\<M>,u). u \<notin> targets \<M>)"

    lemma isA_correct:  "(isA, op_is_avoid) \<in> modest_mdp_inf_rel N \<rightarrow> node_rel' N \<rightarrow> bool_rel"
      apply(refine_vcg)
      by(auto simp: isA_alt modest_mdp_input_invar.is_avoid_state_alt modest_mdp_ii_invar_inf_def modest_mdp_inf_rel_def in_br_conv)

    lemma isT_correct: "(isT, op_is_target) \<in> modest_mdp_inf_rel N \<rightarrow> node_rel' N \<rightarrow> bool_rel"
      apply(refine_vcg)
      by(auto simp: isT_alt modest_mdp_input_invar.is_target_state_alt modest_mdp_ii_invar_inf_def modest_mdp_inf_rel_def in_br_conv)
                              
    lemma init_ub_impl_correct: "(init_ub_impl, mop_init_ub) \<in> modest_mdp_inf_rel N \<rightarrow> \<langle>\<langle>node_rel' N, Id\<rangle>list_fun_rel N\<rangle>nres_rel"
      apply(refine_vcg) by (auto dest!: init_ub_impl_refine)

    lemma init_lb_impl_correct: "(init_lb_impl, mop_init_lb) \<in> modest_mdp_inf_rel N \<rightarrow> \<langle>\<langle>node_rel' N, Id\<rangle>list_fun_rel N\<rangle>nres_rel"
      apply(refine_vcg) by (auto dest!: init_lb_impl_refine) 
      
    lemma get_state_val_lb_impl_correct:  "(uncurry2 get_state_val_lb_impl, uncurry2 (RETURN ooo op_state_val)) \<in> [get_state_val_pre]\<^sub>f 
      ((modest_mdp_inf_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r node_rel' N) \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply(rule frefI)
      apply(refine_vcg)
      by(auto simp: get_state_val_pre_def intro!: get_state_val_lb_impl_refine_aux)

    lemma get_state_val_ub_impl_correct: "(uncurry2 get_state_val_ub_impl, uncurry2 (RETURN ooo op_state_val)) \<in> [get_state_val_pre]\<^sub>f 
      ((modest_mdp_inf_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r node_rel' N) \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply(rule frefI)
      apply(refine_vcg)
      by(auto simp: get_state_val_pre_def intro!: get_state_val_ub_impl_refine_aux)

    lemma updated_state_val_gs_impl_correct: "(uncurry2 updated_state_val_gs_impl, uncurry2 (mop_state_vals_gs)) \<in> [upd_state_val_pre]\<^sub>f 
      ((modest_mdp_inf_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N) \<rightarrow> \<langle>\<langle>node_rel' N, Id\<rangle>list_fun_rel N \<times>\<^sub>r \<langle>node_rel' N, Id\<rangle>list_fun_rel N\<rangle>nres_rel"
      apply(rule frefI)
      apply(refine_vcg)
      by(auto simp: upd_state_val_pre_def intro!: updated_state_val_gs_impl_refine_aux)

    lemma is_trivial_impl_correct: "(uncurry2 is_trivial_impl, uncurry2 (RETURN ooo op_is_trivial)) 
      \<in> [is_trivial_pre]\<^sub>f ((modest_mdp_inf_rel N \<times>\<^sub>r Id) \<times>\<^sub>r node_rel' N) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      apply(rule frefI)
      apply(refine_vcg)
      by(force simp: is_trivial_pre_def intro: is_trivial_impl_refine_aux)

    lemma makeA_correct: "(uncurry makeA, uncurry op_make_avd_sink) \<in> [make_avd_sink_pre]\<^sub>f
      (modest_mdp_inf_rel N \<times>\<^sub>r node_rel' N) \<rightarrow> modest_mdp_inf_rel N"
      by(rule frefI; auto simp: makeA_refine make_avd_sink_pre_def)

  end
  locale interval_iteration_inf_env = interval_iteration_env + interval_iteration_inf_env_defs
  begin

    sepref_definition makeA_ll is "uncurry (RETURN oo makeA)" :: "Modest_mdp_assn_aux\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a Modest_mdp_assn_aux"
      unfolding makeA_def Modest_mdp_assn_aux_def
      by sepref
    concrete_definition(in -) makeA_ll' [llvm_code] is interval_iteration_inf_env.makeA_ll_def
    lemmas makeA_ll_hnr [sepref_fr_rules] = makeA_ll.refine[unfolded makeA_ll'.refine[OF interval_iteration_inf_env_axioms]]


    sepref_definition makeT_ll is "uncurry (RETURN oo makeA)" :: "Modest_mdp_assn_aux\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a Modest_mdp_assn_aux"
      unfolding makeA_def Modest_mdp_assn_aux_def
      by sepref
    concrete_definition(in -) makeT_ll' [llvm_code] is interval_iteration_inf_env.makeT_ll_def
    lemmas makeT_ll_hnr [sepref_fr_rules] = makeT_ll.refine[unfolded makeT_ll'.refine[OF interval_iteration_inf_env_axioms]]
    sepref_definition get_state_val_opt_lb_ll is "uncurry2 get_state_val_lb_impl" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a lb_reach_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nn_real_lb_assn"
      unfolding get_state_val_lb_impl_def St_nth_uid_alt[symmetric] PR_CONST_def
      unfolding St_nth_lid_alt[symmetric]
      apply (annot_snat_const "TYPE(size_T)")
      supply[elim] = Suc_N_leq_max less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      apply sepref
      done
    concrete_definition(in -) get_state_val_opt_lb_inf_ll' [llvm_code] is interval_iteration_inf_env.get_state_val_opt_lb_ll_def
    lemmas get_state_val_opt_lb_ll_hnr[sepref_fr_rules] = get_state_val_opt_lb_ll.refine[unfolded get_state_val_opt_lb_inf_ll'.refine[OF interval_iteration_inf_env_axioms]]
    

    sepref_definition get_state_val_opt_ub_ll is "uncurry2 get_state_val_ub_impl" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a ub_reach_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nn_real_ub_assn"
      unfolding get_state_val_ub_impl_def St_nth_uid_alt[symmetric] PR_CONST_def
      unfolding St_nth_lid_alt[symmetric]
      apply (annot_snat_const "TYPE(size_T)")
      supply[elim] = Suc_N_leq_max less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated]
      apply sepref
      done
    concrete_definition(in -) get_state_val_opt_ub_inf_ll' [llvm_code] is interval_iteration_inf_env.get_state_val_opt_ub_ll_def
    lemmas get_state_val_opt_ub_ll_hnr[sepref_fr_rules] = get_state_val_opt_ub_ll.refine[unfolded get_state_val_opt_ub_inf_ll'.refine[OF interval_iteration_inf_env_axioms]]
    

    sepref_definition updated_state_val_gs_impl_ll is "uncurry2 updated_state_val_gs_impl" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a lb_reach_assn\<^sup>d *\<^sub>a ub_reach_assn\<^sup>d \<rightarrow>\<^sub>a (lb_reach_assn \<times>\<^sub>a ub_reach_assn)"
      unfolding updated_state_val_gs_impl_def nfoldli_rev_upt_by_while
      apply (annot_snat_const "TYPE(size_T)")
      supply[elim] = Suc_N_leq_max 
      supply[simp] = modest_mdp_input_def.N_len_def
      apply sepref
      done
    concrete_definition(in -) updated_state_val_gs_impl_inf_ll' [llvm_code] is interval_iteration_inf_env.updated_state_val_gs_impl_ll_def
    lemmas updated_state_val_gs_impl_ll_hnr = updated_state_val_gs_impl_ll.refine[unfolded updated_state_val_gs_impl_inf_ll'.refine[OF interval_iteration_inf_env_axioms]]
    

    interpretation disj_set_list_tuple_env N N ni ni
      apply unfold_locales using n_impl by auto

    lemma mec_map_eq_set_mem_preI: 
      "i<length D \<Longrightarrow> Br ! b \<in> D ! i \<Longrightarrow> mec_map_eq_mec_mem_pre D (Br_nth (St,Tr,Br,Pr,Av,Ta) b)"
      "i<length D \<Longrightarrow> u \<in> D ! i \<Longrightarrow> mec_map_eq_mec_mem_pre D u"
      unfolding mec_map_eq_mec_mem_pre_def Br_nth_def b_assn_open_block_fun_def by auto


    sepref_definition is_trivial_impl_ll is "uncurry2 is_trivial_impl" :: "Modest_mdp_assn_aux\<^sup>k *\<^sub>a mec_map_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding is_trivial_impl_def
      supply [elim] = less_trans_Suc[OF _ Modest_mdp_assn_boundsD(2), rotated] 
        less_trans_Suc[OF _ Modest_mdp_assn_boundsD(1), rotated] mec_map_eq_set_mem_preI
      apply sepref
      done
    concrete_definition(in -) is_trivial_impl_ll' [llvm_code] is interval_iteration_inf_env.is_trivial_impl_ll_def
    lemmas is_trivial_impl_ll_hnr = is_trivial_impl_ll.refine[unfolded is_trivial_impl_ll'.refine[OF interval_iteration_inf_env_axioms]]
 

    sepref_definition make_sink_noop_ll is "uncurry (RETURN oo make_sink_noop)" :: "Modest_mdp_assn_aux\<^sup>d *\<^sub>a  node_assn\<^sup>k \<rightarrow>\<^sub>a Modest_mdp_assn_aux"
      unfolding make_sink_noop_def 
      apply sepref
      done
    concrete_definition(in -) make_sink_noop_ll' [llvm_code] is interval_iteration_inf_env.make_sink_noop_ll_def
    lemmas make_sink_noop_ll_hnr = make_sink_noop_ll.refine[unfolded make_sink_noop_ll'.refine[OF interval_iteration_inf_env_axioms]]
  end



  context interval_iteration_inf_env
  begin



    context 
      notes [fcomp_norm_unfold] = f_triple_aux Modest_mdp_inf_assn_def[symmetric] 
        output_ub_assn_alt[symmetric] output_lb_assn_alt[symmetric]
    begin
 
      lemmas mop_init_lb_hnr[sepref_fr_rules] = init_lb_ll_hnr[FCOMP init_lb_impl_correct]
      lemmas mop_init_ub_hnr[sepref_fr_rules] = init_ub_ll_hnr[FCOMP init_ub_impl_correct]

      lemmas mop_state_vals_gs_hnr[sepref_fr_rules] = updated_state_val_gs_impl_ll_hnr[FCOMP updated_state_val_gs_impl_correct, folded mop_state_vals_gs_inf_def]

      lemmas op_is_avoid_hnr[sepref_fr_rules] = isA_ll_hnr[FCOMP isA_correct]
      lemmas op_is_target_hnr[sepref_fr_rules] = isT_ll_hnr[FCOMP isT_correct]

      lemmas is_trivial_impl_hnr[sepref_fr_rules] = is_trivial_impl_ll_hnr[FCOMP is_trivial_impl_correct]
      lemmas makeA_hnr[sepref_fr_rules] = makeA_ll_hnr[FCOMP makeA_correct]

    end

  end


  context modest_init_mdp_env_defs
  begin

    definition "collapse_to_mec_block = (\<lambda>\<M> f. f (to_mdpc \<M>))"

    lemma Modest_MDP_ent_mdp_inf: "pure_part (Modest_mdp_inf_DS_assn N DS \<M> ss) 
      \<Longrightarrow> Modest_MDP_DS_assn DS M ss 
      \<turnstile> Modest_mdp_inf_DS_assn N DS \<M> ss"
      unfolding Modest_MDP_DS_assn_def Modest_mdp_inf_DS_assn_def
      apply(erule hr_comp_entails_unique_dom) 
      unfolding modest_mdp_inf_DS_rel_def modest_mdp_input_DS_rel_def
      by auto

    lemma Modest_mdp_inf_ent_MDP: "Modest_mdp_inf_DS_assn N DS \<M> ss \<turnstile> Modest_MDP_DS_assn DS (to_mdpc \<M>) ss"
      unfolding Modest_mdp_inf_DS_assn_def Modest_MDP_DS_assn_def
      apply(rule hr_comp_alt_rel)
      unfolding modest_mdp_inf_DS_rel_def modest_mdp_input_DS_rel_def modest_mdp_input_def.\<M>_\<alpha>_def
      by(auto simp: in_br_conv to_mdpc.abs_eq modest_mdp_ii_invar_inf_def modest_mdp_input_invar_def)


    lemma hn_collapse_to_mec_block:
      assumes FR: "\<Gamma> \<turnstile> hn_ctxt (Modest_mdp_inf_DS_assn N DS) p' p ** \<Gamma>1"
      assumes Pair: "\<And> a1' a1. hn_refine (hn_ctxt (Modest_MDP_DS_assn DS) a1' a1 \<and>* \<Gamma>1) (f a1) (\<Gamma>1' a1' a1) R CP (f' a1')"
      assumes FR2: "\<And>a1' a1. \<Gamma>1' a1' a1 \<turnstile> hn_ctxt (Modest_MDP_DS_assn DS) a1' a1 ** \<Gamma>2'"  
      shows "hn_refine \<Gamma> (f p) (hn_ctxt (Modest_mdp_inf_DS_assn N DS) p' p ** \<Gamma>2')
        R CP (collapse_to_mec_block$p'$(\<lambda>\<^sub>2 x. f' x))"
      apply(rule hn_refine_cons_pre[OF FR])
      unfolding autoref_tag_defs PROTECT2_def hr_comp_def 
      apply(cases p')
      apply (clarsimp simp: collapse_to_mec_block_def hn_ctxt_def sep_conj_exists hnr_pre_ex_conv)
      apply(sepref_to_hoare)
      apply(rule htriple_pure_preI)
      apply(drule pure_part_split_conj, clarify)+
      supply [vcg_rules] = Pair[THEN hn_refineD, unfolded hn_ctxt_def, THEN htriple_ent_pre[OF conj_entails_mono2[OF Modest_mdp_inf_ent_MDP]]]
      apply vcg
      apply(rule ENTAILS_trans_pre)  
      apply(sep_drule FR2)
      unfolding hn_ctxt_def
      apply(erule conj_entails_mono2[OF conj_entails_mono2[OF Modest_MDP_ent_mdp_inf]])
      apply vcg'
      done
  
    lemma collapse_to_mec_block_mono: 
      "\<lbrakk>\<And>a. f a \<le> f' a\<rbrakk> \<Longrightarrow> collapse_to_mec_block x f \<le> collapse_to_mec_block x f'"
      unfolding collapse_to_mec_block_def
      apply(cases x)
      by auto
  
    lemma collapse_to_mec_block_arity: "collapse_to_mec_block \<equiv> \<lambda>\<^sub>2x f. SP collapse_to_mec_block$x$(\<lambda>\<^sub>2a. f$a)"
      by simp
  
    lemma collapse_to_mec_block_comb:  
      "collapse_to_mec_block$x$f = Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP collapse_to_mec_block$x$f)"
      by simp
  
    lemma collapse_to_mec_block_mono_flat: 
      "\<lbrakk>\<And>a. flat_ge (f a) (f' a)\<rbrakk> \<Longrightarrow> flat_ge (collapse_to_mec_block x f) (collapse_to_mec_block x f')"
      unfolding collapse_to_mec_block_def
      apply(cases x) by simp
  
    lemma collapse_to_mec_block_SPLIT_rule:
      assumes "f (to_mdpc \<M>) \<le> SPEC P"
      shows "collapse_to_mec_block \<M> f \<le> SPEC P"  
      using assms(1) unfolding collapse_to_mec_block_def 
      by simp
  
    lemma collapse_to_mec_split_refine:
      assumes "f' (to_mdpc \<M>') \<le> \<Down>R (f (to_mdpc \<M>))"
      shows "collapse_to_mec_block \<M>' f' \<le>\<Down>R (collapse_to_mec_block \<M> f)"
      unfolding collapse_to_mec_block_def
      using assms
      by auto

  end

  context modest_init_mdp_env_defs
  begin

    definition "compute_mecs_mat \<equiv> (\<lambda>\<M>. collapse_to_mec_block \<M> (\<lambda> M. do{ 
      ASSERT(states M = {0..<N} \<and> Finite_MDP M); mec_algo_defs.compute_MEC_spec M
    }))"

    definition "compute_mecs_pre = (\<lambda> \<M>. states (to_mdpc \<M>) = {0..<N} \<and> Finite_MDP (to_mdpc \<M>))"

    lemma compute_mecs_mat_refine: "(compute_mecs_mat, op_compute_mecs) \<in> [compute_mecs_pre]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
      unfolding compute_mecs_mat_def collapse_to_mec_block_def op_compute_mecs_def compute_mecs_pre_def
      apply(rule frefI)
      by (auto intro!: nres_relI)


    concrete_definition (in -) compute_MEC_ll' [llvm_code] is compute_MEC_fine_impl_ll'_def[of ni' for ni']

  end

  context modest_init_mdp_env
  begin
  
    lemmas compute_MEC_fine_impl_ll'_hnr[unfolded compute_MEC_ll'.refine, sepref_fr_rules] 
      = modest_init_mdp_env.compute_MEC_fine_impl_ll'_hnr[OF modest_init_mdp_env_axioms]


    interpretation disj_set_list_tuple_defs N N ni ni
      apply(unfold_locales)
      done


    context
      notes [sepref_comb_rules] = hn_collapse_to_mec_block
      and [sepref_monadify_arity] = collapse_to_mec_block_arity
      and [sepref_monadify_comb] = collapse_to_mec_block_comb
    begin

      sepref_definition compute_mecs_mat_impl_ll is "compute_mecs_mat" :: "[compute_mecs_pre]\<^sub>a (Modest_mdp_inf_DS_assn N DS)\<^sup>k \<rightarrow> mec_map_assn "
        unfolding compute_mecs_mat_def compute_mecs_pre_def
        apply sepref
        done

    end



    lemma compute_mecs_mat_impl_hnr: "(compute_mecs_mat_impl_ll, op_compute_mecs) \<in> [compute_mecs_pre]\<^sub>a (Modest_mdp_inf_assn N)\<^sup>k \<rightarrow> mec_map_assn"
    proof -

      note REF = compute_mecs_mat_impl_ll.refine[FCOMP compute_mecs_mat_refine, to_hnr]

      show ?thesis
        apply(rule hfrefI)
        apply simp
        unfolding Modest_mdp_inf_assn_DS hnr_pre_ex_conv
        apply (rule allI)
        apply(sepref_to_hoare)
        supply [vcg_rules] = REF[THEN hn_refineD, unfolded hn_ctxt_def, simplified]
        by vcg

    qed

    concrete_definition (in -) compute_mecs_mat_impl_ll' [llvm_code] is modest_init_mdp_env.compute_mecs_mat_impl_ll_def
    lemmas [sepref_fr_rules] = compute_mecs_mat_impl_hnr[unfolded compute_mecs_mat_impl_ll'.refine[OF modest_init_mdp_env_axioms]]

    interpretation disj_set_list_tuple_defs N N ni ni .
    interpretation disj_set_list_tuple_env N N ni ni
      unfolding disj_set_list_tuple_env_def using n_impl by satx
                                                          
    sepref_definition compute_MEC_sorted_ll is "compute_MEC_sorted" :: "[\<lambda>M. compute_mecs_pre M]\<^sub>a (Modest_mdp_inf_assn N)\<^sup>k \<rightarrow> mec_map_assn"
      unfolding compute_MEC_sorted_def
      by sepref

  end


end